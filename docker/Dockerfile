FROM rust:latest AS builder
# Install nightly toolchain matching rust-toolchain.toml
RUN rustup toolchain install nightly-2026-01-01 && rustup default nightly-2026-01-01
WORKDIR /build
COPY . .
RUN cargo build --release -p pyana-node

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates && rm -rf /var/lib/apt/lists/*
COPY --from=builder /build/target/release/pyana-node /usr/local/bin/
ENTRYPOINT ["pyana-node"]
