FROM rust:1.82-slim AS builder
WORKDIR /build
COPY . .
RUN cargo build --release -p pyana-node

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates && rm -rf /var/lib/apt/lists/*
COPY --from=builder /build/target/release/pyana-node /usr/local/bin/
ENTRYPOINT ["pyana-node"]
