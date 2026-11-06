# tree-check certificate format (v1)

What `lake exe tree-check verify <cert.json>` reads (`metatheory/TreeCheck.lean`,
`metatheory/Dregg2/Tree/Instance.lean`). A JSON envelope; every **value** inside it is the
canonical CBOR of a model value, lowercase hex, read by the proved `Value.ofCanonicalBytes`
(decode, map into the model, require `WF`, re-encode, compare bytes). Digests, keys and roots are
lowercase hex. The envelope reader (`Lean.Json`) is outside the theorems; a malformed envelope
exits 2, never 0.

## Hashes

| name | definition | used for |
|---|---|---|
| node `H` | `SHAKE256("dregg.tree.node.v1" ‖ 0x00 ‖ frame, 32)` | Merkle tree digests |
| flat `F` | `SHAKE256("dregg.tree.flat.v1" ‖ 0x00 ‖ encode(v), 32)` | schemas, byte tables |
| mmr `h` | `int_be(SHAKE256("dregg.tree.mmr.v1" ‖ 0x00 ‖ enc(arr(map intItem l)), 32))` | the corpus MMR (`mrootC`, the algorithm of `Lightclient/MMR.lean`) |

Frames (CBOR items, `Merkle.Frame.item`): a scalar `v` is `[0, item(v)]`; an array is
`[1, [bstr d₀, …]]`; an object is `[2, {text k₀: bstr d₀, …}]` in the object's (canonical) key
order. `digest(v) = H(enc(frame(v)))`. MMR leaves are the record roots read big-endian as
naturals; the root is written as 32 big-endian bytes.

## Values

`JVal` (`Value.lean`) to CBOR (RFC 8949 §4.2.1): null/false/true = `f6`/`f4`/`f5`; integers major
0/1 within 64 bits, else tag 2/3 bignum (minimal bytes); a non-integer decimal `m·10^e`
(`e<0`, `10∤m`) is tag 4 `[e, m]`; strings major 3 (valid UTF-8, escapes decoded, no
normalization); arrays major 4; objects major 5 with keys strictly increasing in bytewise order of
their encodings (no duplicates). The projection from JSON text is `Json.parse`
(`tree-check project <file>` prints `{"cbor","tree_root","flat_digest"}`).

## Openings

```
OP := {"here": "<cbor hex>"}                       the subtree at this point, in full
    | {"arr": ["<digest>", ...], "rest": OP}       array frame; the path's next step is {"idx": i}
    | {"obj": [["<key hex>", "<digest>"], ...], "rest": OP}   object frame; next step {"key": hex}
    | {"absent_arr": ["<digest>", ...]}             the next step is a key, or an index ≥ length
    | {"absent_obj": [["<key hex>", "<digest>"], ...]}   the next step is an index, or a missing key
PATH := [{"key": "<hex>"} | {"idx": n}, ...]
```

## Statements and receipts

```
{"statement": {"kind": "schema", "tree_root": D, "schema_digest": D, "verdict": true|false},
 "receipt":   {"tree": V, "schema": V, "run": RUN}}
RUN := {"q": "0110…"} | {"q": "0110…", "kids": [RUN, ...]}      one bit per schema definition

{"statement": {"kind": "field", "tree_root": D, "path": PATH, "table_digest": D,
               "verdict": "absent"|"non_string"|"accept"|"reject"},
 "receipt":   {"opening": OP, "table": V}}

{"statement": {"kind": "corpus", "mmr_root": D, "n": N,
               "query": [{"path": PATH, "table_digest": D}, ...], "count": C},
 "receipt":   {"tables": [V, ...],
               "records": [{"root": D, "refute": {"j": j, "opening": OP}}
                         | {"root": D, "full": [OP, ...]} , ...]}}
```

A schema is the JSON value `{"defs": [DEF, ...], "root": n, "tables": [TABLE, ...]}`; a DEF uses
only `type enum pattern minimum maximum properties required additionalProperties items minItems
maxItems allOf anyOf`, with sub-schemas named by index (`properties: {"k": 3}`); any other key is
refused. A TABLE is `{"num_states", "transitions", "start", "accepting"}` (the `dfa` crate's shape,
`transitions[s*256+b]`); it decides the WHOLE string.

A corpus record MATCHES when every conjunct's path holds a string its table accepts. `refute`
evidences a non-match with one conjunct whose verdict is not `accept`; `full` gives one opening
per conjunct, in order, all `accept`. `count` is the number of `full` records.
