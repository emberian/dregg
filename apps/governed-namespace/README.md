# Governed Namespace

A **governed capability registry and service mesh** demonstrating four integrated
capabilities:

1. **DFA-governed routing** -- URL-style path prefixes compiled into a deterministic
   state machine, controlling which paths are accessible and what permissions are needed.
   The DFA router is the ACL for the entire system.

2. **Capability registry** -- Services (not just files) are mounted at governed paths.
   A directory is a programmable introduction service. Registering yourself in a
   directory = making your services discoverable. The DFA router controls WHO can
   register WHERE.

3. **VFS (content-addressed storage)** -- Files stored by their blake3 hash (nameless
   writes). The hash IS the address; knowledge of the hash IS authority to read.

4. **Route governance** -- The routing table is a committed data structure. Changes
   require threshold voting (2n/3+1) by registered participants. History of all
   amendments is preserved.

## Key insight

Directories don't just store file blobs -- they store CAPABILITIES (sturdy refs to
any kind of service). A mount point is a governed introduction: the namespace vouches
that a particular sturdy ref lives at a particular path, and the DFA routing table
determines who can mount where and who can discover what.

This makes the governed namespace a **service mesh** where:
- The DAO controls what paths exist (`/services/*`, `/public/*`, `/members/*`)
- The DFA classification determines who can mount at each path
- Discovery is scoped by the caller's auth level (you can only find what you can see)
- Services are identified by sturdy refs (`pyana://` URIs) -- bearer capabilities

## How it differs from traditional service discovery

| Traditional | Governed Namespace |
|---|---|
| Filenames + directories | Content hashes (blake3) + mount paths |
| ACLs (user/group/other) | DFA route classification |
| Admin changes access | Threshold vote changes access |
| Trust the server | Verify the commitment |
| Share via URL | Share via `pyana://` sturdy ref |
| DNS/consul for services | DFA-governed mount + tag discovery |
| Static service registry | CAS-versioned mount with governance |

## DAO use case

1. DAO deploys namespace with routes: `/public/*`, `/members/*`, `/treasury/*`, `/proposals/*`
2. Member uploads to `/public/readme.txt` -- anyone can read via content hash
3. Alice mounts her oracle service: `POST /registry/mount { path: "/public/services/alice/price-oracle", kind: "oracle", ... }`
4. Bob discovers oracle services: `GET /registry/discover?tag=oracle&tag=prices`
5. Bob resolves the path: `GET /registry/resolve/public/services/alice/price-oracle` -- gets the sturdy ref
6. Bob enlivens the sturdy ref and starts querying Alice's oracle directly
7. Governance proposal: "Add `/grants/*` route for the new grants program"
8. 4-of-5 participants vote approve -- route goes live atomically

## Running

```bash
cargo run -p governed-namespace
# Listens on 0.0.0.0:3000 by default (override with LISTEN env var)
```

## API

### Registry (capability service mesh)

```
POST   /registry/mount            -- mount a service at a named path (CAS semantics)
DELETE /registry/unmount/:path    -- remove a service entry
GET    /registry/discover?tag=X   -- find services by tag (all tags must match)
GET    /registry/resolve/:path    -- resolve name -> sturdy ref (the "introduction")
PUT    /registry/update/:path     -- update a mounted service (version CAS)
GET    /registry/health/:path     -- check if mounted service is alive
```

#### Mount request body

```json
{
    "path": "/public/services/alice/price-oracle",
    "name": "price-oracle",
    "kind": "oracle",
    "sturdy_ref": "pyana://alice-fed/oracle-cell/abc123...",
    "owner": "0101010101...01",
    "expected_version": 0,
    "tags": ["oracle", "prices", "defi"],
    "description": "Real-time price feeds for ETH, BTC, SOL",
    "expires_at": null,
    "health_endpoint": "/health"
}
```

#### Mount semantics (CAS)

- `expected_version: 0` for new mounts (creates at version 1)
- `expected_version: N` for updates (increments to N+1, fails if current != N)
- Mount path must be within a route prefix the caller has authority for
- DFA classification determines: can this caller mount here?

#### Service kinds

- `storage` -- can store/retrieve blobs
- `compute` -- can execute computations
- `oracle` -- provides external data
- `factory` -- creates new capabilities
- `sub_directory` -- recursive namespace
- `custom("name")` -- application-defined

### File storage (capability-secure, nameless)

```
POST   /files              -- body = raw bytes, returns {hash, size, new}
GET    /files/:hash        -- returns raw bytes (knowledge of hash = authority)
PUT    /files/:hash        -- body = new content, returns {old_hash, new_hash, old_nullified}
DELETE /files/:hash        -- returns {deleted, nullifier}
```

### Route management

```
GET  /routes             -- current route table + commitment + version
POST /routes/propose     -- {proposer, routes: [...], description}
POST /routes/vote        -- {voter, proposal_id, approve: bool}
GET  /routes/commitment  -- {commitment, version}
```

### DFA-routed namespace access

```
GET  /namespace/*path    -- classify path, read file (X-Content-Hash header)
POST /namespace/*path    -- classify path, write file (body = content)
```

Auth level set via `X-Auth-Level` header: `admin`, `member`, `multisig:N`, or omit for anonymous.

### Governance

```
GET /governance/constitution  -- participants, threshold, routes_commitment
GET /governance/proposals     -- pending + all proposals + amendment history
```

### Sharing

```
POST /share/:hash  -- export file as pyana:// sturdy ref URI
```

## Integration with routing

The routing table determines which prefixes exist and who can use them:

- `/services/*` might be MembersOnly (only federation members can mount)
- `/public/*` might be open (anyone can mount, but governance can remove)
- `/treasury/*` requires multisig to mount services handling funds

The DFA router is the ACL for the registry, not just for file access. When you
`POST /registry/mount`, the path you're mounting at is classified by the DFA.
If you don't have sufficient auth for that route class, the mount is denied.

Discovery is similarly scoped: `GET /registry/discover?tag=oracle` only returns
services mounted at paths the caller can see. An anonymous caller won't discover
services mounted under `/members/*`.

## Circuit provability

Every operation maps to a provable STARK statement:

| Operation | Circuit statement |
|---|---|
| Upload | `blake3(content) = H` (preimage knowledge) |
| Read | `I possess H` (capability presentation) |
| Splice | `H_new = blake3(patch) AND H_old was live` |
| Delete | `nullifier = blake3(H \|\| "nullify")` |
| Classify | `DFA(path) = class` using table with commitment `C` |
| Mount | `DFA(path) = class AND auth >= class.required` |
| Resolve | `DFA(path) = class AND entry exists at path` |
| Vote | `I am participant P AND signed proposal Q` |
| Amend | `Proposal Q reached threshold, C_old -> C_new` |

## Configuration

| Env var | Default | Description |
|---|---|---|
| `LISTEN` | `0.0.0.0:3000` | Bind address |
| `PYANA_ADMIN_TOKEN` | (open mode) | Admin bearer token |
| `NAMESPACE_PARTICIPANTS` | 5 dev participants | JSON array of `{id, name, weight}` |
| `NAMESPACE_FEDERATION_ID` | derived from "governed-namespace-demo" | 64 hex chars |
