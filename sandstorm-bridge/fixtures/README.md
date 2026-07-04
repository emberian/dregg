# sandstorm-bridge fixtures

Drop a real signed catalog `.spk` here as `sample.spk` to run the real-catalog
differential harness (`tests/real_spk_fixture.rs`). A representative one lives at
`snoopy:~/dregg-share/sample.spk` (canonical magic `8fc6cdef451aea96`); fetch it with:

```
scp snoopy:~/dregg-share/sample.spk sandstorm-bridge/fixtures/sample.spk
```

The harness skips cleanly when `sample.spk` is absent, so the suite stays green
until the artifact lands. When present it verifies the real container header and
emits the differential signal for the Cap'n Proto `Archive`-wire swap (step ④ of
`docs/SANDSTORM-DEVNET-READY.md`). `sample.spk` itself is intentionally not
committed (it is a third-party package; keep it out of git).
