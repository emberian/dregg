//! Integration tests for production hardening features.
//!
//! These tests verify:
//! - Message size limits (oversized messages rejected without OOM)
//! - Heartbeat/keepalive (dead connections detected and dropped)
//! - Rate limiting (burst traffic throttled after bucket exhaustion)
//! - Graceful shutdown (active connections get CapGoodbye)
//! - Connection metrics tracking
//! - Independent per-connection rate limits
//! - Bounded backpressure (slow readers don't exhaust memory)

use pyana_wire::codec::{self, read_message_with_limit, write_message};
use pyana_wire::connection::PeerConnection;
use pyana_wire::hardening::{
    ConnectionMetrics, DEFAULT_MAX_MESSAGE_SIZE, HardeningConfig, RateLimiter, ShutdownCoordinator,
    message_cost,
};
use pyana_wire::message::{AuthorizationRequest, PROTOCOL_VERSION, WireMessage};
use pyana_wire::server::{NoopVerifier, PeerRole, SiloConfig, SiloServer};

use std::sync::Arc;
use std::time::Duration;

#[cfg(test)]
mod tests {
    use super::*;

    // =========================================================================
    // Test 1: Oversized message rejected (doesn't OOM)
    // =========================================================================

    #[tokio::test]
    async fn oversized_message_rejected_no_oom() {
        // Configure a server with a very small message size limit
        let hardening = HardeningConfig::new().with_max_message_size(1024); // 1KB limit
        let config = SiloConfig::new("size-limit-test")
            .with_verifier(Arc::new(NoopVerifier))
            .with_hardening(hardening);
        let server = SiloServer::new("127.0.0.1:0".parse().unwrap(), config);

        let (addr_tx, addr_rx) = tokio::sync::oneshot::channel();
        tokio::spawn(async move {
            server.run_with_addr(addr_tx).await.unwrap();
        });

        let addr = addr_rx.await.unwrap();
        let mut client = PeerConnection::connect(&addr.to_string()).await.unwrap();

        // Handshake first
        client
            .send(WireMessage::Hello {
                node_id: [0x11; 32],
                node_name: "big-sender".to_string(),
                protocol_version: PROTOCOL_VERSION,
                capabilities: vec![],
            })
            .await
            .unwrap();
        let _welcome = client.recv().await.unwrap();

        // Send a message that exceeds the 1KB limit when serialized
        // A PresentToken with a 2KB proof will definitely exceed 1KB
        let big_proof = vec![0xAB; 2048];
        let request = AuthorizationRequest::new("resource", "read", "alice");
        let msg = WireMessage::PresentToken {
            proof: big_proof,
            request,
            federation_root: [0; 32],
        };

        // Write the oversized message directly (bypassing client-side checks)
        let frame = codec::encode(&msg).unwrap();
        use tokio::io::AsyncWriteExt;
        let stream = tokio::net::TcpStream::connect(&addr.to_string())
            .await
            .unwrap();
        let (mut reader, mut writer) = tokio::io::split(stream);

        // Send Hello first
        let hello = WireMessage::Hello {
            node_id: [0x22; 32],
            node_name: "oversized-client".to_string(),
            protocol_version: PROTOCOL_VERSION,
            capabilities: vec![],
        };
        write_message(&mut writer, &hello).await.unwrap();
        let _welcome = codec::read_message(&mut reader).await.unwrap();

        // Now send the oversized frame
        writer.write_all(&frame).await.unwrap();
        writer.flush().await.unwrap();

        // Server should respond with an error about the size
        let response = codec::read_message(&mut reader).await.unwrap();
        match response {
            WireMessage::Error { code, message } => {
                assert_eq!(code, pyana_wire::hardening::ERROR_MESSAGE_TOO_LARGE);
                assert!(
                    message.contains("too large"),
                    "expected 'too large' in error message, got: {message}"
                );
            }
            other => panic!("expected Error, got {other:?}"),
        }
    }

    // =========================================================================
    // Test 2: Message exactly at limit accepted, one byte over rejected
    // =========================================================================

    #[tokio::test]
    async fn message_size_boundary() {
        // Use a duplex stream to test the codec-level limit directly
        let (mut client, mut server) = tokio::io::duplex(65536);

        // A small message should pass through a 1MB limit
        let small_msg = WireMessage::Ping {
            seq: 1,
            timestamp: 100,
        };
        write_message(&mut client, &small_msg).await.unwrap();
        let decoded = read_message_with_limit(&mut server, DEFAULT_MAX_MESSAGE_SIZE)
            .await
            .unwrap();
        assert_eq!(small_msg, decoded);

        // Now test with a very tight limit: message that's just barely too big
        let (mut client2, mut server2) = tokio::io::duplex(65536);
        let msg = WireMessage::PresentToken {
            proof: vec![0u8; 100], // ~100 byte proof
            request: AuthorizationRequest::new("x", "y", "z"),
            federation_root: [0; 32],
        };
        // Serialize to know actual size
        let serialized = postcard::to_stdvec(&msg).unwrap();
        let actual_size = serialized.len();

        // Set limit to exactly the size: should pass
        write_message(&mut client2, &msg).await.unwrap();
        let result = read_message_with_limit(&mut server2, actual_size).await;
        assert!(result.is_ok(), "message at exact limit should be accepted");

        // Set limit to one less: should fail
        let (mut client3, mut server3) = tokio::io::duplex(65536);
        write_message(&mut client3, &msg).await.unwrap();
        let result = read_message_with_limit(&mut server3, actual_size - 1).await;
        assert!(
            matches!(result, Err(codec::CodecError::MessageTooLarge { .. })),
            "message one byte over limit should be rejected"
        );
    }

    // =========================================================================
    // Test 3: Heartbeat - no pong within timeout -> disconnected
    // =========================================================================

    #[tokio::test]
    async fn heartbeat_timeout_disconnects() {
        // Configure very short heartbeat for testing
        let hardening = HardeningConfig::new()
            .with_heartbeat(Duration::from_millis(100), Duration::from_millis(300));
        let config = SiloConfig::new("heartbeat-test")
            .with_verifier(Arc::new(NoopVerifier))
            .with_hardening(hardening);
        let server = SiloServer::new("127.0.0.1:0".parse().unwrap(), config);

        let (addr_tx, addr_rx) = tokio::sync::oneshot::channel();
        tokio::spawn(async move {
            server.run_with_addr(addr_tx).await.unwrap();
        });

        let addr = addr_rx.await.unwrap();

        // Connect and handshake but then go silent (don't respond to pings)
        let stream = tokio::net::TcpStream::connect(&addr.to_string())
            .await
            .unwrap();
        let (mut reader, mut writer) = tokio::io::split(stream);

        let hello = WireMessage::Hello {
            node_id: [0x33; 32],
            node_name: "silent-client".to_string(),
            protocol_version: PROTOCOL_VERSION,
            capabilities: vec![],
        };
        write_message(&mut writer, &hello).await.unwrap();
        let _welcome = codec::read_message(&mut reader).await.unwrap();

        // The server will send a Ping after heartbeat_interval (100ms).
        // We will NOT respond with a Pong.
        // After heartbeat_timeout (300ms) from the ping, server should disconnect.

        // Wait for the server to send a Ping
        let ping = tokio::time::timeout(Duration::from_secs(2), codec::read_message(&mut reader))
            .await
            .expect("should receive ping within 2s")
            .unwrap();
        assert!(
            matches!(ping, WireMessage::Ping { .. }),
            "expected Ping, got {ping:?}"
        );

        // Don't respond with Pong. Wait for disconnect or error message.
        // The server should eventually disconnect us.
        let result =
            tokio::time::timeout(Duration::from_secs(5), codec::read_message(&mut reader)).await;

        match result {
            Ok(Ok(WireMessage::Error { code, .. })) => {
                assert_eq!(code, pyana_wire::hardening::ERROR_HEARTBEAT_TIMEOUT);
            }
            Ok(Ok(WireMessage::Ping { .. })) => {
                // Server may send additional pings before timing out.
                // Wait longer for the actual disconnect.
                let final_result =
                    tokio::time::timeout(Duration::from_secs(5), codec::read_message(&mut reader))
                        .await;
                match final_result {
                    Ok(Ok(WireMessage::Error { code, .. })) => {
                        assert_eq!(code, pyana_wire::hardening::ERROR_HEARTBEAT_TIMEOUT);
                    }
                    Ok(Err(codec::CodecError::ConnectionClosed)) => {
                        // Also acceptable: server closed the connection
                    }
                    other => panic!("expected heartbeat timeout error or close, got {other:?}"),
                }
            }
            Ok(Err(codec::CodecError::ConnectionClosed)) => {
                // Server closed the connection after heartbeat timeout
            }
            Err(_) => panic!("timed out waiting for server to disconnect dead client"),
            other => panic!("unexpected result: {other:?}"),
        }
    }

    // =========================================================================
    // Test 4: Rate limit - burst of messages throttled after bucket empty
    // =========================================================================

    #[tokio::test]
    async fn rate_limit_throttles_burst() {
        // Very strict rate limit: 5 tokens max, 1 refill/sec
        let hardening = HardeningConfig::new()
            .with_rate_limit(5, 1)
            .with_heartbeat(Duration::from_secs(60), Duration::from_secs(120)); // long heartbeat to avoid interference
        let config = SiloConfig::new("rate-limit-test")
            .with_verifier(Arc::new(NoopVerifier))
            .with_hardening(hardening);
        let server = SiloServer::new("127.0.0.1:0".parse().unwrap(), config);

        let (addr_tx, addr_rx) = tokio::sync::oneshot::channel();
        let _federation_root = server.state().await.federation_root;
        tokio::spawn(async move {
            server.run_with_addr(addr_tx).await.unwrap();
        });

        let addr = addr_rx.await.unwrap();

        let mut client = PeerConnection::connect(&addr.to_string()).await.unwrap();

        // Handshake
        client
            .send(WireMessage::Hello {
                node_id: [0x44; 32],
                node_name: "burst-client".to_string(),
                protocol_version: PROTOCOL_VERSION,
                capabilities: vec![],
            })
            .await
            .unwrap();
        let _welcome = client.recv().await.unwrap();

        // Ping costs 1 token. Send 5 pings rapidly (uses all tokens).
        let mut accepted_count = 0u32;
        let mut rejected_count = 0u32;

        for i in 0..10 {
            client
                .send(WireMessage::Ping {
                    seq: i,
                    timestamp: 0,
                })
                .await
                .unwrap();

            let response = client.recv_timeout(Duration::from_secs(2)).await.unwrap();

            match response {
                WireMessage::Pong { .. } => accepted_count += 1,
                WireMessage::Error { code, .. }
                    if code == pyana_wire::hardening::ERROR_RATE_LIMITED =>
                {
                    rejected_count += 1;
                }
                other => panic!("unexpected response #{i}: {other:?}"),
            }
        }

        // With 5 tokens and each Ping costing 1, at least 5 should succeed
        // and at least some should be rejected
        assert!(
            accepted_count >= 5,
            "expected at least 5 accepted, got {accepted_count}"
        );
        assert!(
            rejected_count > 0,
            "expected some rejections after bucket exhausted, got none"
        );
    }

    // =========================================================================
    // Test 5: Graceful shutdown - active connections get CapGoodbye
    // =========================================================================

    #[tokio::test]
    async fn graceful_shutdown_sends_goodbye() {
        let hardening = HardeningConfig::new()
            .with_grace_period(Duration::from_secs(2))
            .with_heartbeat(Duration::from_secs(60), Duration::from_secs(120));
        let config = SiloConfig::new("shutdown-test")
            .with_verifier(Arc::new(NoopVerifier))
            .with_hardening(hardening);
        let server = SiloServer::new("127.0.0.1:0".parse().unwrap(), config);

        let shutdown_coord = Arc::clone(server.shutdown_coordinator());
        let (addr_tx, addr_rx) = tokio::sync::oneshot::channel();
        tokio::spawn(async move {
            server.run_with_addr(addr_tx).await.unwrap();
        });

        let addr = addr_rx.await.unwrap();
        let mut client = PeerConnection::connect(&addr.to_string()).await.unwrap();

        // Handshake
        client
            .send(WireMessage::Hello {
                node_id: [0x55; 32],
                node_name: "shutdown-client".to_string(),
                protocol_version: PROTOCOL_VERSION,
                capabilities: vec![],
            })
            .await
            .unwrap();
        let _welcome = client.recv().await.unwrap();

        // Give the server a moment to register the connection
        tokio::time::sleep(Duration::from_millis(50)).await;

        // Initiate shutdown
        shutdown_coord.initiate_shutdown();

        // The client should receive a CapGoodbye message
        let response = tokio::time::timeout(Duration::from_secs(5), client.recv())
            .await
            .expect("should receive goodbye within 5s")
            .unwrap();

        match response {
            WireMessage::CapGoodbye { reason, .. } => {
                assert_eq!(reason, Some("server shutting down".to_string()));
            }
            other => panic!("expected CapGoodbye, got {other:?}"),
        }
    }

    // =========================================================================
    // Test 6: Metrics tracked correctly
    // =========================================================================

    #[test]
    fn metrics_tracked_correctly() {
        let rl = RateLimiter::new(100, 20);
        let mut metrics = ConnectionMetrics::new(PeerRole::Anonymous, rl);

        assert_eq!(metrics.messages_received, 0);
        assert_eq!(metrics.messages_sent, 0);
        assert_eq!(metrics.bytes_received, 0);
        assert_eq!(metrics.bytes_sent, 0);

        // Record some activity
        metrics.record_receive(256);
        metrics.record_receive(512);
        metrics.record_send(128);

        assert_eq!(metrics.messages_received, 2);
        assert_eq!(metrics.bytes_received, 768);
        assert_eq!(metrics.messages_sent, 1);
        assert_eq!(metrics.bytes_sent, 128);

        // Uptime should be very short
        assert!(metrics.uptime() < Duration::from_secs(1));

        // Idle duration should be very short (just recorded activity)
        assert!(metrics.idle_duration() < Duration::from_millis(100));
    }

    // =========================================================================
    // Test 7: Multiple connections have independent rate limits
    // =========================================================================

    #[tokio::test]
    async fn independent_rate_limits_per_connection() {
        // Strict rate limit: 3 tokens, very slow refill
        let hardening = HardeningConfig::new()
            .with_rate_limit(3, 1)
            .with_heartbeat(Duration::from_secs(60), Duration::from_secs(120));
        let config = SiloConfig::new("independent-rl-test")
            .with_verifier(Arc::new(NoopVerifier))
            .with_hardening(hardening);
        let server = SiloServer::new("127.0.0.1:0".parse().unwrap(), config);

        let (addr_tx, addr_rx) = tokio::sync::oneshot::channel();
        tokio::spawn(async move {
            server.run_with_addr(addr_tx).await.unwrap();
        });

        let addr = addr_rx.await.unwrap();

        // Connect two clients
        let mut client1 = PeerConnection::connect(&addr.to_string()).await.unwrap();
        let mut client2 = PeerConnection::connect(&addr.to_string()).await.unwrap();

        // Handshake both
        for (client, name) in [(&mut client1, "client1"), (&mut client2, "client2")] {
            client
                .send(WireMessage::Hello {
                    node_id: [0x66; 32],
                    node_name: name.to_string(),
                    protocol_version: PROTOCOL_VERSION,
                    capabilities: vec![],
                })
                .await
                .unwrap();
            let _welcome = client.recv().await.unwrap();
        }

        // Exhaust client1's rate limit
        for i in 0..5 {
            client1
                .send(WireMessage::Ping {
                    seq: i,
                    timestamp: 0,
                })
                .await
                .unwrap();
            let _ = client1.recv_timeout(Duration::from_secs(1)).await;
        }

        // client2 should still have a fresh rate limit
        client2
            .send(WireMessage::Ping {
                seq: 100,
                timestamp: 0,
            })
            .await
            .unwrap();
        let response = client2.recv_timeout(Duration::from_secs(2)).await.unwrap();

        // client2's first message should succeed (its bucket is full)
        assert!(
            matches!(response, WireMessage::Pong { seq: 100, .. }),
            "client2 should have independent rate limit, got: {response:?}"
        );
    }

    // =========================================================================
    // Test 8: Slow reader - bounded channel prevents memory growth
    // =========================================================================

    #[test]
    fn bounded_channel_prevents_memory_growth() {
        // Test that the outgoing channel is bounded at the expected capacity
        let (tx, _rx) = pyana_wire::hardening::outgoing_channel();
        assert_eq!(
            tx.max_capacity(),
            pyana_wire::hardening::OUTGOING_CHANNEL_CAPACITY
        );

        // Try to fill the channel
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();

        rt.block_on(async {
            let (tx, _rx) = pyana_wire::hardening::outgoing_channel();

            // Fill the channel to capacity
            for i in 0..pyana_wire::hardening::OUTGOING_CHANNEL_CAPACITY {
                let msg = pyana_wire::hardening::OutgoingMessage::Wire(WireMessage::Ping {
                    seq: i as u64,
                    timestamp: 0,
                });
                tx.send(msg).await.unwrap();
            }

            // Next send should fail (channel full) with try_send
            let overflow_msg = pyana_wire::hardening::OutgoingMessage::Wire(WireMessage::Ping {
                seq: 999,
                timestamp: 0,
            });
            let result = tx.try_send(overflow_msg);
            assert!(
                result.is_err(),
                "channel should be full after {cap} messages",
                cap = pyana_wire::hardening::OUTGOING_CHANNEL_CAPACITY
            );
        });
    }

    // =========================================================================
    // Test 9: Shutdown coordinator lifecycle
    // =========================================================================

    #[test]
    fn shutdown_coordinator_lifecycle() {
        let coord = ShutdownCoordinator::new([0xAA; 32], Duration::from_secs(5));
        assert!(!coord.is_shutting_down());
        assert_eq!(coord.active_count(), 0);

        coord.register_connection();
        coord.register_connection();
        assert_eq!(coord.active_count(), 2);

        let count = coord.initiate_shutdown();
        assert_eq!(count, 2);
        assert!(coord.is_shutting_down());

        coord.unregister_connection();
        assert_eq!(coord.active_count(), 1);
    }

    // =========================================================================
    // Test 10: Rate limiter token bucket behavior
    // =========================================================================

    #[test]
    fn rate_limiter_token_bucket() {
        let mut rl = RateLimiter::new(10, 5);
        assert_eq!(rl.available_tokens(), 10);

        // Consume all tokens
        for _ in 0..10 {
            assert!(rl.try_consume(1));
        }
        assert_eq!(rl.available_tokens(), 0);
        assert!(!rl.try_consume(1));

        // Verify expensive messages cost more
        let mut rl2 = RateLimiter::new(10, 5);
        // SubmitRevocation costs 5
        let revocation = WireMessage::SubmitRevocation {
            token_id: "tok".to_string(),
            authority: pyana_wire::message::PublicKey([0; 32]),
            authority_sig: pyana_wire::message::Signature([0; 64]),
            nonce: [0; 16],
            timestamp: 0,
        };
        let cost = message_cost(&revocation);
        assert_eq!(cost, 5);
        assert!(rl2.try_consume(cost)); // 10 -> 5
        assert!(rl2.try_consume(cost)); // 5 -> 0
        assert!(!rl2.try_consume(cost)); // can't afford another 5
    }

    // =========================================================================
    // Test 11: HardeningConfig builder
    // =========================================================================

    #[test]
    fn hardening_config_builder_works() {
        let config = HardeningConfig::new()
            .with_max_message_size(512 * 1024)
            .with_rate_limit(50, 10)
            .with_heartbeat(Duration::from_secs(15), Duration::from_secs(45))
            .with_channel_capacity(32)
            .with_grace_period(Duration::from_secs(3));

        assert_eq!(config.max_message_size, 512 * 1024);
        assert_eq!(config.rate_limit_max_tokens, 50);
        assert_eq!(config.rate_limit_refill_rate, 10);
        assert_eq!(config.heartbeat_interval, Duration::from_secs(15));
        assert_eq!(config.heartbeat_timeout, Duration::from_secs(45));
        assert_eq!(config.outgoing_channel_capacity, 32);
        assert_eq!(config.shutdown_grace_period, Duration::from_secs(3));
    }
}
