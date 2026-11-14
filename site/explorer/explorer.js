/**
 * dregg explorer — cells, turns, receipt chains.
 *
 * DESIGN NOTE (why this does not look like Etherscan)
 * ---------------------------------------------------
 * A block explorer's model is: blocks contain transactions, transactions move
 * balances between accounts. dregg's model is none of those three things.
 *
 *   * State lives in CELLS, which are simultaneously the account and the
 *     contract: a balance, a nonce, a capability table, optionally a program.
 *   * History is made of TURNS. A turn is the exercise of an attenuable
 *     proof-carrying token over owned state, and it leaves a RECEIPT.
 *   * Receipts chain PER AGENT (`previous_receipt_hash` is set from the
 *     agent's own last receipt), so "the history" is a bundle of chains, not
 *     one ledger line.
 *   * Blocks exist, but as a leaderless DAG — a blocklace — where a block
 *     names a SET of predecessors and most blocks are heartbeats carrying no
 *     turn. Ordering, not accounting.
 *
 * Rendering that as a linear block list with a transaction count would be
 * false in four separate places, so this page renders the actual objects.
 *
 * HONESTY RULES this file follows
 * -------------------------------
 *   1. Four states are distinguished and never collapsed: NO NODE CONFIGURED,
 *      NODE UNREACHABLE, NODE EMPTY, NODE HAS DATA. An empty table is never
 *      drawn to stand in for any of the first three.
 *   2. Nothing is rendered that was not read from the node this run. There is
 *      no sample data, no placeholder row, no "example" object.
 *   3. Anything the page checks itself is labeled with what the check
 *      establishes; anything it cannot check is listed as not checked.
 */

import { verifyLedgerRoot, LEDGER_ROOT_CONTEXT, blake3, bytesToHex } from "/explorer/blake3.js";

// ---------------------------------------------------------------------------
// tiny DOM helpers
// ---------------------------------------------------------------------------

const $ = (sel) => document.querySelector(sel);

/** Escape for text interpolation into innerHTML. */
function esc(s) {
  return String(s === null || s === undefined ? "" : s)
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;");
}

/** Abbreviate a 64-hex id for a table cell, keeping both ends. */
function shortHex(h, head = 8, tail = 6) {
  const s = String(h || "");
  if (s.length <= head + tail + 1) return s;
  return `${s.slice(0, head)}…${s.slice(-tail)}`;
}

function ts(unixSeconds) {
  if (!unixSeconds) return "—";
  try {
    return new Date(Number(unixSeconds) * 1000).toISOString().replace("T", " ").slice(0, 19);
  } catch {
    return String(unixSeconds);
  }
}

// ---------------------------------------------------------------------------
// the node hop
// ---------------------------------------------------------------------------

/**
 * The prefix node routes are read under. Two deployments share this one file:
 *
 *   * SITE — the web tier serves this page at /explorer/ and reaches a remote
 *     node through its GET-only, path-allowlisted hop at /explorer/node/.
 *   * NODE — the node serves this page itself, at /. It IS the origin, so a
 *     route is read directly and no hop exists.
 *
 * Which one is in force is DECLARED by the server in /explorer/target, never
 * inferred from the URL: a wrong guess here would read nothing and render as
 * "unreachable", which is the one failure mode this page exists to keep apart
 * from "empty".
 */
let HOP = "/explorer/node/";

/**
 * Fetch one node route through the read-only hop.
 *
 * Returns a tagged result rather than throwing, because the DIFFERENCE between
 * failure modes is information this page must render: a 404 from the node
 * ("no checkpoint exists yet") is not a 502 ("the node is not answering") is
 * not a 503 ("no node is configured at all").
 */
async function nodeGet(path, params) {
  const qs = params ? `?${new URLSearchParams(params)}` : "";
  let res;
  try {
    res = await fetch(`${HOP}${path}${qs}`, { headers: { accept: "application/json" } });
  } catch (e) {
    return { kind: "transport", detail: String(e) };
  }
  let body = null;
  const text = await res.text();
  try {
    body = text ? JSON.parse(text) : null;
  } catch {
    return { kind: "not-json", status: res.status, detail: text.slice(0, 400) };
  }
  if (res.ok) return { kind: "ok", body };
  if (body && body.explorer_error) {
    return { kind: body.explorer_error, status: res.status, detail: body.detail || "" };
  }
  return { kind: "node-status", status: res.status, body };
}

// ---------------------------------------------------------------------------
// shared empty / failure renderings
// ---------------------------------------------------------------------------

/**
 * The "there is nothing here yet" block. It must always say what WOULD appear
 * and what makes it appear — an empty table with a headline is indistinguishable
 * from a broken query.
 */
function emptyState(headline, prose, willAppear) {
  const items = (willAppear || []).map((l) => `<li>${l}</li>`).join("");
  return `<div class="empty">
    <div class="headline">${esc(headline)}</div>
    <p>${prose}</p>
    ${items ? `<p style="margin-bottom:0.2rem">What will appear here:</p><ul>${items}</ul>` : ""}
  </div>`;
}

/** Render a failed read in a way that names which failure it was. */
function failState(r, what) {
  switch (r.kind) {
    case "no-node-configured":
      return emptyState(
        "NO NODE CONFIGURED",
        `This explorer is not pointed at a node, so there is no chain to read — this is
         <em>not</em> the same as a chain with nothing on it. Set <code>DREGG_NODE_URL</code>
         on the web server and reload.`,
        [],
      );
    case "node-unreachable":
      return `<div class="empty"><div class="headline">NODE UNREACHABLE</div>
        <p>The configured node did not answer, so ${esc(what)} is unknown — not empty.</p>
        <p class="err">${esc(r.detail)}</p></div>`;
    case "path-not-allowed":
      return `<div class="empty"><div class="headline">ROUTE NOT ON THE ALLOWLIST</div>
        <p class="err">${esc(r.detail)}</p></div>`;
    case "node-status":
      return `<div class="empty"><div class="headline">NODE RETURNED HTTP ${esc(r.status)}</div>
        <p>${esc(what)} could not be read. The node answered, but with an error status.</p></div>`;
    default:
      return `<div class="empty"><div class="headline">READ FAILED</div>
        <p class="err">${esc(r.kind)} ${esc(r.detail || "")}</p></div>`;
  }
}

// ---------------------------------------------------------------------------
// 1. posture
// ---------------------------------------------------------------------------

function factCard(k, v, cls, note) {
  return `<div class="fact"><span class="k">${esc(k)}</span>
    <span class="v ${cls || ""}">${esc(v)}</span>
    ${note ? `<span class="n">${note}</span>` : ""}</div>`;
}

function renderPosture(status, producer) {
  const s = status;
  const out = [];

  // "healthy" is a real trap: the node reports healthy=false when consensus is
  // attached but no block has been produced yet. Rendering a red dot and
  // stopping would be a misreading, so the note explains the actual predicate.
  out.push(
    factCard(
      "healthy",
      s.healthy ? "yes" : "no",
      s.healthy ? "good" : "warn",
      s.healthy
        ? "consensus is attached and the DAG has a tip."
        : `the node's own predicate is "a blocklace handle is attached AND the DAG has a tip".
           consensus_live is <code>${esc(String(s.consensus_live))}</code> and dag_height is
           <code>${esc(String(s.dag_height))}</code> — so this reads "no block produced yet",
           not "the node is broken".`,
    ),
  );

  out.push(
    factCard(
      "state producer",
      s.state_producer || "—",
      s.state_producer === "lean" ? "good" : "warn",
      s.state_producer === "lean"
        ? `the VERIFIED Lean executor installs the committed post-state for turns touching only
           root-agreeing effects; the Rust executor runs as a logged cross-check.`
        : `the legacy Rust executor is authoritative (<code>DREGG_LEAN_PRODUCER=0</code>).`,
    ),
  );

  const covered = Number(s.producer_root_agreeing_effects || 0);
  const total = producer && Array.isArray(producer.mappable_effects) && Array.isArray(producer.unmappable_effects)
    ? producer.mappable_effects.length + producer.unmappable_effects.length
    : null;
  out.push(
    factCard(
      "swap-safe effects",
      total ? `${covered} / ${total}` : String(covered),
      "info",
      `effect kinds for which the verified producer installs its post-state. A turn touching any
       other kind falls back to the Rust producer <em>for that turn</em>, with a logged reason.
       This number is the honest width of "verified execution" here.`,
    ),
  );

  out.push(
    factCard(
      "full-turn proving",
      s.full_turn_proving ? "ON" : "off",
      s.full_turn_proving ? "good" : "warn",
      s.full_turn_proving
        ? `every committed turn produces a full-turn STARK and acceptance is gated on it verifying.`
        : `turns are committed WITHOUT a full-turn STARK on the commit path. Receipts below may
           still carry an async attestation; "has_proof" reports that, not this.`,
    ),
  );

  out.push(
    factCard("federation mode", s.federation_mode || "—", "", `peers: ${esc(String(s.peer_count))}`),
  );

  out.push(
    factCard(
      "dag height",
      String(s.dag_height),
      "",
      `every block, heartbeats included. This is the honest "how tall is the lace" number.`,
    ),
  );
  out.push(
    factCard(
      "attested height",
      String(s.latest_height),
      "",
      `advances only on turn-bearing finality, so it legitimately sits at 0 while the DAG grows.
       These are two different numbers and neither is "the block height".`,
    ),
  );

  let html = `<div class="posture">${out.join("")}</div>`;

  if (producer && producer.summary) {
    html += `<div class="drawer"><dl class="kv">
      <dt>producer summary</dt><dd>${esc(producer.summary)}</dd>
    </dl></div>`;
  }
  return html;
}

// ---------------------------------------------------------------------------
// 2. committed activity
// ---------------------------------------------------------------------------

/**
 * The typed proof status, rendered without laundering.
 *
 * `node/src/state.rs` is explicit that "null/absent proof material must not be
 * read as proved", and the enum has seven variants — only ONE of which is
 * `proved`. Collapsing them into a "verified" tick is precisely the claim this
 * repo keeps deleting, so each variant gets its own words.
 */
function proofStatusPill(s) {
  switch (s) {
    case "proved":
      return '<span class="pill ok" title="a STARK attestation is attached to this committed turn">proved</span>';
    case "proof_pending":
      return '<span class="pill warn" title="committed; an accepted async job is generating the succinct attestation">proof pending</span>';
    case "not_required":
      return '<span class="pill mute" title="coordination turn: executor/committee signature attestation, not a validity proof">not required</span>';
    case "unattested":
      return '<span class="pill mute">unattested</span>';
    case "missing_pre_state":
      return '<span class="pill bad">missing pre-state</span>';
    case "proof_generation_failed":
      return '<span class="pill bad">proof generation FAILED</span>';
    case "not_committed":
      return '<span class="pill bad">not committed</span>';
    default:
      return `<span class="pill mute">${esc(String(s || "unknown"))}</span>`;
  }
}

function renderEvents(events) {
  if (!events.length) {
    return emptyState(
      "NOTHING HAS BEEN COMMITTED",
      `The node answered and its committed-event log is empty. No turn has been applied here.`,
      [
        `one row per committed turn: which cell it touched and which effects it applied`,
        `a typed proof status — <code>proved</code> is one of seven values, and the other six are
         not it`,
        `the block height the turn committed at`,
      ],
    );
  }
  const rows = events
    .slice()
    .reverse()
    .map(
      (e) => `<tr>
      <td class="num">${esc(String(e.height))}</td>
      <td>${e.status === "committed" ? '<span class="pill ok">committed</span>' : '<span class="pill bad">rejected</span>'}</td>
      <td>${proofStatusPill(e.proof_status)}</td>
      <td class="id"><a href="#verify" data-cell="${esc(e.cell_id)}" class="hex">${esc(shortHex(e.cell_id, 10, 6))}</a></td>
      <td>${(e.effects || []).map((f) => `<span class="pill info">${esc(f)}</span>`).join(" ") || "—"}</td>
      <td class="hex dim">${esc(shortHex(e.turn_hash, 10, 6))}</td>
      <td>${esc(ts(e.timestamp))}</td>
    </tr>`,
    )
    .join("");
  return `<div class="tbl-scroll"><table>
    <thead><tr><th>height</th><th>status</th><th>proof</th><th>cell</th><th>effects</th>
    <th>turn</th><th>time</th></tr></thead><tbody>${rows}</tbody></table></div>
    <p class="hint" style="margin-top:0.6rem;margin-bottom:0">${events.length} committed event(s).
    "Proved" here means a STARK is attached to that turn — it is not a statement about this node's
    execution tier, which is the posture panel's job.</p>`;
}

// ---------------------------------------------------------------------------
// 3. cells
// ---------------------------------------------------------------------------

function renderCells(cells) {
  if (!cells.length) {
    return emptyState(
      "NO CELLS IN THE LEDGER",
      `The node answered, and its ledger holds zero cells. Nothing owns state here yet.`,
      [
        `one row per <b>cell</b> — the unit of owned state (balance, nonce, capability table)`,
        `a <code>program</code> marker when the cell constrains what may be done to it
         (Predicate / Cases / Circuit)`,
        `a <code>delegate</code> marker when authority over the cell has been delegated`,
      ],
    );
  }
  const rows = cells
    .map(
      (c) => `<tr>
      <td class="id"><a href="#verify" data-cell="${esc(c.id)}" class="hex">${esc(shortHex(c.id, 10, 8))}</a></td>
      <td class="num">${esc(String(c.balance))}</td>
      <td class="num">${esc(String(c.nonce))}</td>
      <td class="num">${esc(String(c.capability_count))}</td>
      <td>${c.has_program ? '<span class="pill info">program</span>' : '<span class="pill mute">plain</span>'}</td>
      <td>${c.has_delegate ? '<span class="pill warn">delegated</span>' : "—"}</td>
    </tr>`,
    )
    .join("");
  return `<div class="tbl-scroll"><table>
    <thead><tr><th>cell id</th><th>balance</th><th>nonce</th><th>caps</th><th>program</th><th>delegate</th></tr></thead>
    <tbody>${rows}</tbody></table></div>
    <p class="hint" style="margin-top:0.6rem;margin-bottom:0">${cells.length} cell(s). Click an id to
    fetch and check its inclusion proof.</p>`;
}

// ---------------------------------------------------------------------------
// 3. receipt chains
// ---------------------------------------------------------------------------

/**
 * Group receipts by agent and check each agent's chain link IN THE BROWSER.
 *
 * WHY THIS CHECK IS VALID, precisely:
 *
 *   * `previous_receipt_hash` is the SUBMITTING AGENT's chain head. The
 *     executor's map "advances ONLY for the submitting agent"
 *     (turn/src/executor/mod.rs), so other agents' turns landing in between do
 *     not disturb it. Chaining is per-agent, full stop.
 *   * `/api/receipts` returns a CONTIGUOUS SUFFIX of the global chain — the
 *     handler takes `chain.iter().enumerate().rev().take(50)`. Contiguity is
 *     what makes this sound: because no receipt inside the window is missing,
 *     one agent's receipts within the window are consecutive *in that agent's
 *     own chain*, even though their global indices are not adjacent.
 *
 * So every receipt except the earliest one held for each agent is checkable.
 * The earliest is not: its predecessor may simply be older than the window, and
 * calling that a break would be a false alarm.
 *
 * This checks the chain's SHAPE over bytes this node just served. It is not a
 * signature check, and it cannot tell you the node's chain is the one a quorum
 * agreed on — both stated on the page.
 */
function groupAndCheckChains(receipts) {
  const byAgent = new Map();
  for (const r of receipts) {
    if (!byAgent.has(r.agent)) byAgent.set(r.agent, []);
    byAgent.get(r.agent).push(r);
  }
  const chains = [];
  for (const [agent, list] of byAgent) {
    list.sort((a, b) => Number(a.chain_index) - Number(b.chain_index));
    let breaks = 0;
    let checkable = 0;
    for (let i = 0; i < list.length; i++) {
      const r = list[i];
      if (i === 0) {
        // The earliest receipt we hold for this agent. Its predecessor may be
        // off the front of the window, so the link is not assertable — unless
        // the receipt itself declares it has no predecessor, which is a real
        // and checkable claim: this is the agent's first turn.
        r._link = r.previous_receipt_hash ? "window-edge" : "genesis";
        continue;
      }
      const prev = list[i - 1];
      checkable++;
      if (r.previous_receipt_hash && r.previous_receipt_hash === prev.receipt_hash) {
        r._link = "linked";
      } else {
        r._link = "broken";
        breaks++;
      }
    }
    chains.push({ agent, list, breaks, checkable });
  }
  chains.sort((a, b) => Number(b.list[0].timestamp || 0) - Number(a.list[0].timestamp || 0));
  return chains;
}

function proofPill(r) {
  if (r.has_proof) return '<span class="pill ok">proof attached</span>';
  if (r.proof_status) return proofStatusPill(r.proof_status);
  return '<span class="pill mute">no proof attached</span>';
}

function renderReceipts(receipts, cellCount, eventCount) {
  if (!receipts.length) {
    // Two facts this empty state must NOT hide.
    //
    // (1) `/api/receipts` reads the CIPHERCLERK receipt chain, which is not the
    //     same population as "turns that committed". A faucet transfer, for
    //     one, commits and emits an event and lands in a turn-bearing block
    //     while leaving this chain empty. Printing "no turns have been taken"
    //     over an event log that says otherwise would be a flat lie, so the
    //     headline is about the CHAIN and the contradiction is stated.
    // (2) Cells can exist that no receipt accounts for (genesis / seeding).
    const contradiction =
      eventCount > 0
        ? `<p><b>But ${eventCount} turn(s) HAVE committed</b> — see the activity panel above. This
           route serves the cipherclerk receipt chain specifically, and a turn can commit without
           being written to it (the devnet faucet path is one). So the honest reading is "this
           chain is empty", <em>not</em> "nothing has happened".</p>`
        : "";
    const stateButNoTurns =
      cellCount > 0
        ? `<p>The ledger also holds ${cellCount} cell(s) — state that no receipt on this node
           accounts for. On a devnet that is usually genesis or a seeding path writing cells
           directly rather than through committed turns. Worth knowing, not worth hiding.</p>`
        : "";
    return emptyState(
      eventCount > 0 ? "THE RECEIPT CHAIN IS EMPTY" : "NO RECEIPTS — NO TURNS HAVE BEEN TAKEN",
      `The node answered and its cipherclerk receipt chain holds nothing.
       ${contradiction} ${stateButNoTurns}`,
      [
        `one chain per <b>agent</b>, newest first, each receipt linked to the agent's previous one`,
        `the state transition each turn made: <code>pre_state → post_state</code>`,
        `whether the executor signed it, whether a STARK is attached, and how many witnesses it has`,
        `a red rail wherever a chain link fails to check`,
      ],
    );
  }

  const chains = groupAndCheckChains(receipts);
  const totalBreaks = chains.reduce((n, c) => n + c.breaks, 0);
  const totalCheckable = chains.reduce((n, c) => n + c.checkable, 0);

  const banner =
    totalCheckable === 0
      ? `<p class="hint">Every receipt shown is the only one in its agent's window, so no chain
         link was assertable here. Nothing was checked — and nothing is claimed.</p>`
      : totalBreaks === 0
        ? `<p class="hint"><span class="pill ok">${totalCheckable} link(s) checked, 0 broken</span>
           — each checked receipt's <code>previous_receipt_hash</code> equals the preceding
           receipt's <code>receipt_hash</code>. This checks the chain's <em>shape</em> over data
           this node served; it is not a signature check and does not establish that the node's
           chain is the one a quorum agreed on.</p>`
        : `<p class="hint"><span class="pill bad">${totalBreaks} broken link(s)</span> of
           ${totalCheckable} checked. A break means a receipt names a predecessor that is not the
           receipt before it.</p>`;

  const body = chains
    .map((c) => {
      const items = c.list
        .slice()
        .reverse()
        .map((r) => {
          const broken = r._link === "broken";
          const linkNote =
            r._link === "genesis"
              ? '<span class="pill mute">chain start</span>'
              : r._link === "window-edge"
                ? '<span class="pill mute" title="its predecessor is older than the 50-receipt window this route serves, so the link is not assertable here">predecessor outside window</span>'
                : r._link === "linked"
                  ? '<span class="pill ok">link checks</span>'
                  : '<span class="pill bad">LINK BROKEN</span>';
          return `<div class="link ${broken ? "broken" : ""}">
            <div class="rail"><span class="node"></span></div>
            <div class="rcpt ${broken ? "broken" : ""}">
              <div class="top">
                <span class="h">#${esc(String(r.chain_index))} ${esc(shortHex(r.receipt_hash, 10, 8))}</span>
                ${linkNote}
                <span class="pill ${r.finality === "Final" ? "ok" : "warn"}">${esc(r.finality || "?")}</span>
                ${proofPill(r)}
                ${r.executor_signed ? '<span class="pill ok">executor signed</span>' : '<span class="pill mute">unsigned</span>'}
                ${Number(r.witness_count) > 0 ? `<span class="pill info">${esc(String(r.witness_count))} witness(es)</span>` : ""}
                ${r.was_encrypted ? '<span class="pill info">encrypted path</span>' : ""}
                ${r.was_burn ? '<span class="pill warn">burn — supply did not balance</span>' : ""}
              </div>
              <div class="transition">
                ${esc(shortHex(r.pre_state, 10, 8))}<span class="arrow">→</span>${esc(shortHex(r.post_state, 10, 8))}
              </div>
              <div class="meta">
                <span>turn ${esc(shortHex(r.turn_hash, 10, 8))}</span>
                <span>${esc(String(r.action_count))} action(s)</span>
                <span>${esc(String(r.computrons_used))} computrons</span>
                <span>${esc(ts(r.timestamp))}</span>
              </div>
              ${broken ? `<div class="breaknote">names predecessor ${esc(shortHex(r.previous_receipt_hash, 10, 8))}, but the receipt before it hashes to something else.</div>` : ""}
            </div>
          </div>`;
        })
        .join("");
      return `<div class="chain-agent">
        <div class="who">agent <b>${esc(shortHex(c.agent, 12, 10))}</b> — ${c.list.length} receipt(s)</div>
        ${items}
      </div>`;
    })
    .join("");

  return `${banner}${body}
    <p class="hint" style="margin-bottom:0">This route serves the most recent 50 receipts of the
    node's chain, so a chain shown here may be a window into a longer one.</p>`;
}

// ---------------------------------------------------------------------------
// 3b. the receipt-log commitment
// ---------------------------------------------------------------------------

/**
 * The empty-MMR root, as the node's own hasher defines it: `blake3` over the
 * arity-0 domain tag from `dregg-query/src/mmr.rs`. Recomputing it here is what
 * lets an EMPTY log be reported as a checked fact instead of a shrug — the two
 * readings of `len: 0` (nothing has happened / the log was lost) are the exact
 * pair this panel exists to keep apart.
 */
const MMR_EMPTY_TAG = "dregg-query-mmr-v1:empty";

function renderIndexHead(head, eventCount, receiptCount) {
  const checks = [];
  const len = Number(head.len || 0);
  const root = String(head.root || "");

  // --- the root ------------------------------------------------------------
  if (len === 0) {
    const expected = bytesToHex(blake3(MMR_EMPTY_TAG));
    checks.push(
      root.toLowerCase() === expected
        ? checkRow(
            "pass",
            "the served root is the root of an EMPTY log",
            `Your browser hashed <code>${esc(MMR_EMPTY_TAG)}</code> with its own BLAKE3 and got
             <code>${esc(expected)}</code>, which is the root the node served. Establishes: the node
             is committing to a log with nothing in it — it did not serve a stale or arbitrary root
             and call it empty.`,
          )
        : checkRow(
            "fail",
            "the served root is the root of an EMPTY log",
            `The node reports <code>len: 0</code>, but its root is <code>${esc(root)}</code> and an
             empty log's root is <code>${esc(expected)}</code>. Those two answers contradict each
             other.`,
          ),
    );
  } else {
    checks.push(
      checkRow(
        "skip",
        "recompute the root from the log",
        `The root commits to ${len} receipt(s), and this page did not fetch them to re-fold it.
         Doing so takes the certified slices at <code>/api/receipts/index/range</code>, which carry
         the openings that make omission detectable; this panel reads only the head.`,
      ),
    );
  }

  // --- the signature -------------------------------------------------------
  checks.push(
    checkRow(
      "skip",
      "the node's signature over this head",
      `The head is signed by <code>${esc(shortHex(head.signer, 10, 8))}</code> and the signature is
       served, but nothing on this page verifies it. Believing it means believing that key is this
       node's — a binding this page has no way to establish. Treat the signature as
       <em>evidence you could take elsewhere</em>, not as something checked here.`,
    ),
  );

  // --- the consensus anchor ------------------------------------------------
  // The node signs an explicitly UNANCHORED framing when it holds no attested
  // root: null block id, height 0, zero ledger root. That is a distinct claim
  // from an anchored one, and rendering it as "height 0" alone would read as a
  // young chain rather than as "pinned to nothing".
  const zeroRoot = /^0*$/.test(String(head.merkle_root || ""));
  const anchored = head.block_id !== null && head.block_id !== undefined && !zeroRoot;
  checks.push(
    anchored
      ? checkRow(
          // Not a tick: this is READ off the response, not checked. The claim
          // that the signature covers these coordinates is only worth anything
          // once the signature is verified, and the row above says it was not.
          "skip",
          "the head names attested consensus coordinates",
          `It reports blocklace block <code>${esc(shortHex(head.block_id, 10, 8))}</code> at height
           ${esc(String(head.height))}, ledger root <code>${esc(shortHex(head.merkle_root, 10, 8))}</code>.
           The node's signing message covers those coordinates, so a verifier that checks the
           signature learns the node cannot re-anchor this log elsewhere without producing a second,
           conflicting one. This page did not check the signature, so for now these are reported
           values, not established ones.`,
        )
      : checkRow(
          "warn",
          "the head is explicitly UNANCHORED",
          `This node holds no attested root yet, so it signed the unanchored framing — null block
           id, height 0, zero ledger root. The signature is real and the root still binds the log,
           but nothing ties that log to a position any committee agreed on.`,
        ),
  );

  // --- the cross-check the two routes make possible ------------------------
  // `/api/events` and this head describe the same activity from different
  // stores. When they disagree the disagreement IS the finding, and the shape
  // of it says which failure it is.
  if (len === 0 && eventCount > 0) {
    checks.push(
      checkRow(
        "warn",
        "this empty log disagrees with the committed-event log",
        `The receipt index is empty while the node reports ${eventCount} committed event(s). An
         empty index alongside a non-empty event log means <em>the receipt log did not survive</em>
         — not that nothing ever happened. Read the panel above, not this root, for what this node
         has done.`,
      ),
    );
  } else if (len > 0 && eventCount === 0) {
    checks.push(
      checkRow(
        "warn",
        "the committed-event log is empty and this one is not",
        `This root binds ${len} receipt(s) while <code>/api/events</code> reports nothing. The event
         log is a bounded in-memory window and does not survive a restart; the receipt log does.
         Observed directly on a restarted node — so an empty "What has happened" panel above is a
         statement about that window, not about this node's history.`,
      ),
    );
  } else if (len > 0 && len < receiptCount) {
    checks.push(
      checkRow(
        "fail",
        "the committed length is smaller than the receipts served",
        `The head commits to ${len} receipt(s) but <code>/api/receipts</code> served
         ${receiptCount}. A root cannot bind fewer entries than the log it is taken over.`,
      ),
    );
  }

  const cards = [
    factCard(
      "receipts committed",
      String(len),
      len > 0 ? "good" : "warn",
      `the number of log entries this root binds — derived by the node, and pinned by the root
       itself, which encodes the length in its peak structure.`,
    ),
    factCard(
      "receipt-log root",
      shortHex(root, 12, 10),
      "info",
      `<code>${esc(root)}</code>`,
    ),
    anchored
      ? factCard(
          "anchored at height",
          String(head.height),
          "good",
          `ledger root <code>${esc(shortHex(head.merkle_root, 10, 8))}</code>, blocklace block
           <code>${esc(shortHex(head.block_id, 10, 8))}</code>.`,
        )
      : factCard(
          "consensus anchor",
          "none",
          "warn",
          `signed as explicitly unanchored — no attested root exists to pin this log to.`,
        ),
    factCard(
      "signed by",
      shortHex(head.signer, 8, 6),
      "info",
      `federation <code>${esc(shortHex(head.federation_id, 8, 6))}</code>. Not verified on this
       page — see below.`,
    ),
  ].join("");

  return `<div class="posture">${cards}</div>
    <ul class="checks" style="margin-top:0.9rem">${checks.join("")}</ul>`;
}

// ---------------------------------------------------------------------------
// 4. the blocklace DAG
// ---------------------------------------------------------------------------

function renderLace(blocks, status) {
  if (!blocks.length) {
    const consensus = status && status.consensus_live;
    return emptyState(
      "NO BLOCKS IN THE LACE",
      consensus
        ? `Consensus is attached (<code>consensus_live: true</code>) but no block has been produced
           yet, so the DAG is empty. This is the state a freshly started node sits in before its
           first heartbeat.`
        : `Consensus is not running on this node, so there is no local blocklace to show.`,
      [
        `blocks as DAG vertices, positioned by their creator's sequence`,
        `an edge per <code>predecessor</code> — a block names a SET, which is why this is a lace
         and not a chain`,
        `heartbeat blocks distinguished from turn-bearing ones`,
        `the vote count each block carries against its quorum threshold`,
      ],
    );
  }

  // Bounded window: the most recent 40 blocks, laid out with x = creator
  // sequence and y = a lane per creator. Edges are the real `predecessors`.
  const win = blocks.slice(-40);
  const byHash = new Map(win.map((b) => [b.block_hash, b]));
  const creators = [...new Set(win.map((b) => b.proposer))];
  const lane = new Map(creators.map((c, i) => [c, i]));
  const heights = [...new Set(win.map((b) => Number(b.height)))].sort((a, b) => a - b);
  const col = new Map(heights.map((h, i) => [h, i]));

  const DX = 62, DY = 46, PAD = 26, R = 7;
  const w = PAD * 2 + Math.max(1, col.size - 1) * DX;
  const h = PAD * 2 + Math.max(1, lane.size - 1) * DY;
  const pos = (b) => ({
    x: PAD + col.get(Number(b.height)) * DX,
    y: PAD + lane.get(b.proposer) * DY,
  });

  const edges = [];
  for (const b of win) {
    const p1 = pos(b);
    for (const pred of b.predecessors || []) {
      const pb = byHash.get(pred);
      if (!pb) continue; // predecessor outside the window — do not draw a fake edge
      const p0 = pos(pb);
      edges.push(
        `<line x1="${p0.x}" y1="${p0.y}" x2="${p1.x}" y2="${p1.y}" stroke="rgba(232,224,208,0.16)" stroke-width="1"/>`,
      );
    }
  }
  const dots = win
    .map((b) => {
      const p = pos(b);
      const heartbeat = b.kind === "heartbeat";
      const fill = heartbeat ? "#4a453e" : b.kind === "checkpoint" ? "#6ba3c7" : "#5b8a5a";
      const title = `${b.kind} · height ${b.height} · view ${b.view} · ${b.num_votes}/${b.qc_threshold} votes\n${b.block_hash}`;
      return `<circle cx="${p.x}" cy="${p.y}" r="${R}" fill="${fill}" stroke="rgba(232,224,208,0.25)" stroke-width="1"><title>${esc(title)}</title></circle>`;
    })
    .join("");

  const kinds = {};
  for (const b of blocks) kinds[b.kind] = (kinds[b.kind] || 0) + 1;
  const kindLine = Object.entries(kinds)
    .map(([k, n]) => `${esc(k)}: ${n}`)
    .join(" · ");

  return `<div class="dag"><svg width="${w}" height="${h}" viewBox="0 0 ${w} ${h}" role="img"
     aria-label="blocklace DAG, most recent ${win.length} blocks">${edges.join("")}${dots}</svg></div>
    <div class="dag-legend">
      <span><i style="background:#5b8a5a"></i> turn-bearing</span>
      <span><i style="background:#4a453e"></i> heartbeat</span>
      <span><i style="background:#6ba3c7"></i> checkpoint</span>
      <span>one row per creator · x = creator sequence</span>
    </div>
    <p class="hint" style="margin-top:0.6rem;margin-bottom:0">${blocks.length} block(s) in the lace
    (${esc(kindLine)}); the ${win.length} most recent are drawn. Edges to predecessors outside this
    window are not drawn rather than drawn to nowhere.</p>`;
}

// ---------------------------------------------------------------------------
// 5. attested roots
// ---------------------------------------------------------------------------

function renderRoots(roots) {
  if (!roots.length) {
    return emptyState(
      "NO ATTESTED ROOT YET",
      `No quorum-attested ledger root exists on this node. Until one does, a cell-inclusion proof
       below can still be folded and checked for internal consistency, but it is anchored to
       nothing — the pane will say so.`,
      [
        `one row per attested root: a commitment to the WHOLE ledger at that height`,
        `the signature count the node holds against the threshold that root required`,
        `whether the root is structurally complete`,
      ],
    );
  }
  const rows = roots
    .slice()
    .sort((a, b) => Number(b.height) - Number(a.height))
    .map(
      (r) => `<tr>
      <td class="num">${esc(String(r.height))}</td>
      <td class="hex">${esc(shortHex(r.merkle_root, 12, 10))}</td>
      <td class="num">${esc(String(r.signatures))}</td>
      <td class="num">${esc(String(r.quorum))} / ${esc(String(r.threshold))}</td>
      <td>${r.structurally_complete ? '<span class="pill ok">complete</span>' : '<span class="pill warn">incomplete</span>'}</td>
      <td>${esc(ts(r.timestamp))}</td>
    </tr>`,
    )
    .join("");
  return `<div class="tbl-scroll"><table>
    <thead><tr><th>height</th><th>ledger root</th><th>sigs held</th><th>quorum / threshold</th>
    <th>structure</th><th>time</th></tr></thead><tbody>${rows}</tbody></table></div>
    <p class="hint" style="margin-top:0.6rem;margin-bottom:0">These are counts the node reports.
    The route does not serve the signature bytes, so neither this page nor any other anonymous
    reader can verify the quorum from it — only display it.</p>`;
}

// ---------------------------------------------------------------------------
// 6. verification
// ---------------------------------------------------------------------------

function checkRow(state, what, means) {
  const mark = state === "pass" ? "✓" : state === "fail" ? "✗" : state === "warn" ? "!" : "–";
  return `<li class="${state}"><span class="mark">${mark}</span>
    <div><div class="what">${what}</div><div class="means">${means}</div></div></li>`;
}

/**
 * Fetch a cell-inclusion proof and check it here, in the reader's browser.
 *
 * What the node serves is the FULL sorted leaf set of the current ledger plus
 * the flat root it folds to. There is no Merkle opening — the "proof" is the
 * whole set — so the check is: refold the set, compare, and look for the target
 * id inside it.
 */
async function runVerify(cellId) {
  const out = $("#verify-out");
  out.innerHTML = `<span class="loading">fetching proof for ${esc(shortHex(cellId, 10, 8))}…</span>`;

  const r = await nodeGet(`api/cell/${cellId}/proof`);
  if (r.kind !== "ok") {
    out.innerHTML = failState(r, "the inclusion proof");
    return;
  }
  const p = r.body;
  const leaves = Array.isArray(p.leaves) ? p.leaves : [];

  // `total_leaves` was added to this response later; a node predating it simply
  // omits the field. Treat "absent" as "unknown", never as "0".
  const totalKnown = typeof p.total_leaves === "number";
  const total = totalKnown ? p.total_leaves : null;
  const windowed = totalKnown && total !== leaves.length;

  const checks = [];
  const notChecked = [];

  // --- check 1: does the served leaf set fold to the served root? -----------
  if (windowed) {
    checks.push(
      checkRow(
        "skip",
        "fold the ledger root from the leaves",
        `The node returned a WINDOW of ${leaves.length} leaves out of ${total}. The root folds the
         whole set, so it cannot be reproduced from a window — page through with
         <code>leaf_offset</code>/<code>leaf_limit</code> to check this.`,
      ),
    );
  } else {
    const v = verifyLedgerRoot(leaves, p.merkle_root);
    if (!v.ok) {
      checks.push(checkRow("fail", "fold the ledger root from the leaves", esc(v.error)));
    } else if (v.matched) {
      checks.push(
        checkRow(
          "pass",
          `fold the ledger root from the leaves — <code>${esc(LEDGER_ROOT_CONTEXT)}</code>`,
          `Your browser hashed the ${v.count} leaves with its own BLAKE3 and got
           <code>${esc(v.root)}</code>, which is the root the node served. Establishes: the served
           root really is the fold of the served leaf set — the node did not hand you a root
           belonging to some other ledger. Change one byte of one leaf and this fails.`,
        ),
      );
    } else if (v.staleDomain) {
      // Two separate facts, and collapsing them into one red ✗ would misreport
      // an honest older node as a liar. The fold DID reproduce the served root —
      // integrity holds — it just did so under a superseded domain.
      checks.push(
        checkRow(
          "pass",
          `fold the ledger root from the leaves — <code>${esc(v.matchedContext)}</code>`,
          `Your browser hashed the ${v.count} leaves with its own BLAKE3 and reproduced the root
           the node served. Establishes: the served root really is the fold of the served leaf set.
           Integrity holds — see the next line for which domain it holds under.`,
        ),
      );
      checks.push(
        checkRow(
          "warn",
          `…but under <code>${esc(v.matchedContext)}</code>, not the current <code>${esc(LEDGER_ROOT_CONTEXT)}</code>`,
          `Ledger-root domain separation is versioned, and this node folds under a superseded
           domain — it was built before the current epoch. Under the current domain this leaf set
           folds to <code>${esc(v.root)}</code> instead. This is version skew, not a lie: the node
           is self-consistent, but its root is not comparable with a current node's.`,
        ),
      );
    } else {
      checks.push(
        checkRow(
          "fail",
          "fold the ledger root from the leaves",
          `Your browser folded the ${v.count} leaves to <code>${esc(v.root)}</code>, but the node
           served <code>${esc(p.merkle_root)}</code>, and no known ledger-root domain reproduces the
           served value. The leaf set and the root do not belong together.`,
        ),
      );
    }
  }

  // --- check 2: is the target cell actually a leaf? -------------------------
  const want = String(cellId).toLowerCase();
  const hit = leaves.find((l) => Array.isArray(l) && String(l[0]).toLowerCase() === want);
  if (hit) {
    checks.push(
      checkRow(
        "pass",
        "the requested cell is a leaf of that set",
        `Found <code>${esc(want)}</code> in the leaf set with leaf hash
         <code>${esc(hit[1])}</code>. Establishes: this cell is a member of the set that folds to
         the root above.`,
      ),
    );
  } else if (windowed) {
    checks.push(
      checkRow(
        "skip",
        "the requested cell is a leaf of that set",
        `Not in the returned window — page through the remaining leaves to settle it.`,
      ),
    );
  } else {
    checks.push(
      checkRow(
        p.cell && p.cell.found ? "fail" : "skip",
        "the requested cell is a leaf of that set",
        p.cell && p.cell.found
          ? `The node says this cell EXISTS but it is not in the leaf set it served. Those two
             answers contradict each other.`
          : `The node reports no such cell (<code>found: false</code>), and it is correspondingly
             absent from the leaf set. Consistent — but there is nothing to prove inclusion of.`,
      ),
    );
  }

  // --- check 3: is that root the one a quorum attested? --------------------
  const attested = p.attested_merkle_root || "";
  if (!attested) {
    checks.push(
      checkRow(
        "skip",
        "the root is quorum-attested",
        `The node holds NO attested root at all (<code>attested_merkle_root</code> is empty). The
         fold above is internally consistent but anchored to nothing — no quorum has committed to
         this ledger state. On a chain with no finalized turns this is the expected reading.`,
      ),
    );
  } else if (attested === p.merkle_root && Number(p.quorum) >= Number(p.threshold)) {
    checks.push(
      checkRow(
        "pass",
        "the root is the latest quorum-attested root",
        `The served root equals <code>attested_merkle_root</code> at height
         ${esc(String(p.attested_height))}, with ${esc(String(p.quorum))} of
         ${esc(String(p.threshold))} required signatures. Establishes: the ledger you just folded
         is the one this node reports a quorum attested — <em>as reported by this node</em>.`,
      ),
    );
  } else {
    checks.push(
      checkRow(
        "fail",
        "the root is the latest quorum-attested root",
        `The served ledger root <code>${esc(shortHex(p.merkle_root, 12, 10))}</code> is not the
         latest attested root <code>${esc(shortHex(attested, 12, 10))}</code> (height
         ${esc(String(p.attested_height))}, ${esc(String(p.quorum))}/${esc(String(p.threshold))}
         signatures). The node is serving live ledger state that finality has not caught up to —
         which is normal, and means this read is not consensus-backed.`,
      ),
    );
  }

  // --- what this page did NOT check ----------------------------------------
  notChecked.push(
    `<b>That the leaf hash matches the cell shown.</b> A leaf is
     <code>BLAKE3(postcard(cell))</code>, and re-deriving it needs the cell's exact postcard
     encoding, which is not on the wire. A node could serve a truthful root and leaf set while
     misdescribing the cell's contents beside it, and this page would not catch it.`,
  );
  notChecked.push(
    `<b>The quorum signatures.</b> This response carries signature <em>counts</em>, not signature
     bytes — and no public route serves the bytes. "Quorum-attested" above is this node's own
     report about itself, not something you or this page verified.`,
  );
  notChecked.push(
    `<b>That this node's ledger is the federation's.</b> Everything here is one node's answer.
     Checking that requires reading a second node and comparing roots.`,
  );
  notChecked.push(
    `<b>Any STARK.</b> The full-turn proof lives at <code>/api/turn/{hash}/proof</code> and
     verifying it is not a browser operation; the tier of assurance it carries is the node's, not
     this page's.`,
  );

  const anchor = p.is_attested
    ? '<span class="pill ok">consensus-backed read</span>'
    : '<span class="pill warn">live read, not consensus-backed</span>';

  out.innerHTML = `
    <div class="drawer"><dl class="kv">
      <dt>cell</dt><dd class="hex">${esc(cellId)}</dd>
      <dt>found</dt><dd>${p.cell && p.cell.found ? "yes" : "no"}</dd>
      ${p.cell && p.cell.found ? `<dt>balance / nonce</dt><dd>${esc(String(p.cell.balance))} / ${esc(String(p.cell.nonce))}</dd>` : ""}
      ${p.cell && p.cell.found ? `<dt>program</dt><dd>${esc(p.cell.program_kind)}</dd>` : ""}
      ${p.cell && p.cell.found ? `<dt>state commitment</dt><dd class="hex">${esc(p.cell.state_commitment)}</dd>` : ""}
      ${p.cell && p.cell.last_receipt_hash ? `<dt>receipt-chain head</dt><dd class="hex">${esc(p.cell.last_receipt_hash)}</dd>` : ""}
      <dt>served root</dt><dd class="hex">${esc(p.merkle_root)}</dd>
      <dt>leaves</dt><dd>${leaves.length}${totalKnown ? ` of ${total}` : " (node did not report a total)"}</dd>
      <dt>anchor</dt><dd>${anchor}</dd>
    </dl></div>

    <ul class="checks">${checks.join("")}</ul>

    <div class="notchecked">
      <h3>Not checked here</h3>
      <ul>${notChecked.map((n) => `<li>${n}</li>`).join("")}</ul>
    </div>

    <div class="recipe">
      <h3>Check it yourself, without this page</h3>
      <pre>pip install blake3   <span class="c"># the one dependency; BLAKE3 is not in hashlib</span>

<span class="c"># the same bytes this pane just folded, straight from the node:</span>
curl -s "$NODE/api/cell/${esc(cellId)}/proof" &gt; proof.json

<span class="c"># refold the root: BLAKE3 derive_key(&lt;domain&gt;) over</span>
<span class="c">#   u64_le(leaf_count) || concat(cell_id || leaf_hash), leaves sorted by cell_id</span>
<span class="c"># (persist/src/lib.rs :: canonical_ledger_root_from_leaves)</span>
python3 - &lt;&lt;'PY'
import json, blake3
p = json.load(open('proof.json'))
lv = sorted((bytes.fromhex(a), bytes.fromhex(b)) for a, b in p['leaves'])
for ctx in ("dregg-ledger-root-v3", "dregg-ledger-root-v2"):
    h = blake3.blake3(derive_key_context=ctx)
    h.update(len(lv).to_bytes(8, 'little'))
    for i, l in lv: h.update(i); h.update(l)
    hit = " &lt;&lt;&lt; matches the node" if h.hexdigest() == p['merkle_root'] else ""
    print(f"{ctx}: {h.hexdigest()}{hit}")
print("node said            :", p['merkle_root'])
PY</pre>
      <p class="hint" style="margin:0.5rem 0 0">Both domains are tried for the same reason this pane
      tries both: a node built before the v3 epoch folds under v2, and you want to see WHICH one
      reproduces the root rather than just that something failed. If neither does, the leaf set and
      the root do not belong together.</p>
    </div>`;
}

// ---------------------------------------------------------------------------
// boot
// ---------------------------------------------------------------------------

function setConn(cls, state, url) {
  const c = $("#conn");
  c.className = `conn ${cls}`;
  c.querySelector(".state").textContent = state;
  c.querySelector(".url").textContent = url || "";
}

async function load() {
  for (const id of ["#posture", "#events", "#cells", "#receipts", "#index-head", "#lace", "#roots"]) {
    $(id).innerHTML = '<span class="loading">reading…</span>';
  }

  // Which node, if any? This is asked first and separately so "unconfigured"
  // can never be mistaken for "empty". The same answer carries the deployment:
  // a node serving its own explorer replies `self_hosted`, and reads then go
  // straight to the origin instead of through the site's hop.
  let target = { configured: false, node_url: null };
  try {
    const res = await fetch("/explorer/target");
    target = await res.json();
  } catch {
    /* fall through to the unconfigured rendering */
  }
  if (target.self_hosted) {
    HOP = "/";
    // The node cannot know the URL the browser reached it by; the origin in the
    // address bar is that URL, so report it rather than a placeholder.
    target = { configured: true, node_url: location.origin, self_hosted: true };
  }
  $("#foot-reach").innerHTML = target.self_hosted
    ? `This page is served by the node it reads, so every route above is one hop away in the
       address bar: <code>/api/cells</code>, <code>/api/events</code>, <code>/status</code>. Only
       the node's anonymous surface is read here; routes behind its bearer gate are not touched,
       and nothing on this page writes.`
    : `This page is served by the web tier, which reaches the node through a read-only hop:
       <code>/explorer/node/&lt;route&gt;</code> (for example
       <code>/explorer/node/api/cells</code>). The hop is GET-only, path-allowlisted and sends no
       credentials, so it exposes strictly less than the node's own anonymous surface. Routes the
       node keeps behind its bearer gate — including <code>/api/node/health</code>, which looks
       public but is not — are not reachable through it.`;

  if (!target.configured) {
    setConn("bad", "no node configured", `${target.env || "DREGG_NODE_URL"} is unset`);
    const msg = failState({ kind: "no-node-configured" });
    for (const id of ["#posture", "#events", "#cells", "#receipts", "#index-head", "#lace", "#roots"]) {
      $(id).innerHTML = msg;
    }
    $("#verify-out").innerHTML = msg;
    return;
  }

  setConn("warn", "reading…", target.node_url);

  const statusR = await nodeGet("status");
  if (statusR.kind !== "ok") {
    setConn("bad", statusR.kind, target.node_url);
    for (const id of ["#posture", "#events", "#cells", "#receipts", "#index-head", "#lace", "#roots"]) {
      $(id).innerHTML = failState(statusR, "this node's state");
    }
    return;
  }
  const status = statusR.body;
  setConn(
    "ok",
    `connected · dag ${status.dag_height} · attested ${status.latest_height}`,
    target.node_url,
  );

  const [producerR, eventsR, cellsR, receiptsR, headR, laceR, rootsR] = await Promise.all([
    nodeGet("api/node/producer"),
    nodeGet("api/events", { limit: "200" }),
    nodeGet("api/cells", { limit: "200" }),
    nodeGet("api/receipts"),
    nodeGet("api/receipts/index/head"),
    nodeGet("api/blocklace/blocks", { limit: "200" }),
    // ATTESTED ROOTS. This used to read `api/blocks`, which served roots under a
    // name that promises blocks; that path now serves blocks, and the roots kept
    // their own name.
    nodeGet("api/federation/roots"),
  ]);

  $("#posture").innerHTML = renderPosture(status, producerR.kind === "ok" ? producerR.body : null);

  const events = eventsR.kind === "ok" && Array.isArray(eventsR.body) ? eventsR.body : [];
  $("#events").innerHTML =
    eventsR.kind === "ok" ? renderEvents(events) : failState(eventsR, "the committed-event log");

  const cells = cellsR.kind === "ok" && Array.isArray(cellsR.body) ? cellsR.body : [];
  $("#cells").innerHTML =
    cellsR.kind === "ok" ? renderCells(cells) : failState(cellsR, "the cell list");

  const receipts = receiptsR.kind === "ok" && Array.isArray(receiptsR.body) ? receiptsR.body : [];
  $("#receipts").innerHTML =
    receiptsR.kind === "ok"
      ? renderReceipts(receipts, cells.length, events.length)
      : failState(receiptsR, "the receipt chain");

  $("#index-head").innerHTML =
    headR.kind === "ok" && headR.body
      ? renderIndexHead(headR.body, events.length, receipts.length)
      : failState(headR, "the signed receipt-log head");

  $("#lace").innerHTML =
    laceR.kind === "ok"
      ? renderLace(Array.isArray(laceR.body) ? laceR.body : [], status)
      : failState(laceR, "the blocklace");

  $("#roots").innerHTML =
    rootsR.kind === "ok"
      ? renderRoots(Array.isArray(rootsR.body) ? rootsR.body : [])
      : failState(rootsR, "the attested roots");

  // Verification pane: seed it with a real cell if there is one, but do NOT
  // auto-run — the reader should see the check happen.
  if (cells.length && !$("#verify-id").value) {
    $("#verify-id").value = cells[0].id;
  }
  if (!cells.length) {
    $("#verify-out").innerHTML = emptyState(
      "NOTHING TO PROVE INCLUSION OF",
      `The ledger holds no cells, so there is no cell-inclusion proof to fetch. The check below
       still works the moment one exists — paste any cell id.`,
      [
        `the fold of the ledger root from the returned leaves, recomputed in your browser`,
        `whether the cell is a leaf of that set`,
        `whether that root is the one a quorum attested — and what that does not establish`,
      ],
    );
  }
}

$("#refresh").addEventListener("click", () => load());

$("#verify-form").addEventListener("submit", (e) => {
  e.preventDefault();
  const id = $("#verify-id").value.trim().toLowerCase();
  if (!/^[0-9a-f]{64}$/.test(id)) {
    $("#verify-out").innerHTML =
      '<p class="err">a cell id is exactly 64 hex characters.</p>';
    return;
  }
  runVerify(id);
});

// Clicking a cell id fills the verify box and runs the check.
document.addEventListener("click", (e) => {
  const a = e.target.closest("a[data-cell]");
  if (!a) return;
  e.preventDefault();
  const id = a.getAttribute("data-cell");
  $("#verify-id").value = id;
  $("#panel-verify").scrollIntoView({ behavior: "smooth", block: "start" });
  runVerify(id);
});

load();
