# Pyana Devnet

Launch a local 4-node federation with one command.

## Quick Start

```bash
./docker/start-devnet.sh
```

This will:
1. Generate genesis configuration (keys + genesis.json) in `docker/devnet-config/`
2. Build the Docker image
3. Start 4 validator nodes + an nginx explorer frontend

## Endpoints

| Service    | URL                    | Description                |
|------------|------------------------|----------------------------|
| Node 0     | http://localhost:8420  | API + faucet enabled       |
| Node 1     | http://localhost:8421  | API                        |
| Node 2     | http://localhost:8422  | API                        |
| Node 3     | http://localhost:8423  | API                        |
| Explorer   | http://localhost:3000  | Block explorer UI          |

## Faucet

Node 0 has the faucet enabled. Request computrons for any cell:

```bash
curl -X POST http://localhost:8420/api/faucet \
  -H 'Content-Type: application/json' \
  -d '{"recipient": "<64-hex-char-cell-id>", "amount": 1000}'
```

Rate limit: 1 request per recipient cell per minute. Max 10000 per request.

## Manual Genesis

Generate configuration without Docker:

```bash
cargo run --release -p pyana-node -- genesis \
  --validators 4 \
  --epoch-length 1000 \
  --checkpoint-interval 100 \
  --output ./devnet-config/
```

## Stop

```bash
docker compose -f docker/docker-compose.yml down
```

## Logs

```bash
docker compose -f docker/docker-compose.yml logs -f
docker compose -f docker/docker-compose.yml logs -f node-0
```

## Reset

Remove all data volumes and regenerate:

```bash
docker compose -f docker/docker-compose.yml down -v
rm -rf docker/devnet-config/
./docker/start-devnet.sh
```
