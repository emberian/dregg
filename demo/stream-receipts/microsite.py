"""Render the 'So far' microsite page from stream-check follower logs (no transcript contents).

    python3 microsite.py <live_dir> <big_dir> <viol_dir> <out.html>

Each dir is a run of run.sh / stream-monitor + `stream-check verify` whose follow.log (or
verify.log) holds one JSON line per accepted window. Only roots, states, counts, hash counts,
bytes and microseconds are read; the window files (raw transcript lines) are never opened.
"""
import html
import json
import statistics as st
import sys


def rows(path):
    out = []
    for line in open(path):
        if line.startswith("{"):
            out.append(json.loads(line))
    return out


def last_line(path):
    return [l.strip() for l in open(path) if l.strip()][-1]


def svg_series(series, w=700, h=190, ylab="", colors=("#9fc55b", "#e56f3d"), ymax=None, logy=False):
    """series: list of (label, [y...]) sharing an x index 1..n."""
    n = max(len(s) for _, s in series)
    ymax = ymax or max(max(s) for _, s in series) * 1.08
    pad_l, pad_b, pad_t = 52, 26, 10
    iw, ih = w - pad_l - 10, h - pad_b - pad_t

    def X(i):
        return pad_l + iw * (i / max(n - 1, 1))

    def Y(v):
        return pad_t + ih * (1 - min(v, ymax) / ymax)

    parts = [f'<svg viewBox="0 0 {w} {h}" role="img" aria-label="{html.escape(ylab)}" '
             f'style="width:100%;height:auto;display:block">']
    for frac in (0, .5, 1):
        y = pad_t + ih * (1 - frac)
        parts.append(f'<line x1="{pad_l}" x2="{w-10}" y1="{y:.1f}" y2="{y:.1f}" stroke="rgba(242,237,223,.12)"/>')
        parts.append(f'<text x="{pad_l-6}" y="{y+4:.1f}" text-anchor="end" fill="#77796f" '
                     f'font-size="10" font-family="ui-monospace,monospace">{ymax*frac:,.0f}</text>')
    parts.append(f'<text x="{pad_l}" y="{h-6}" fill="#77796f" font-size="10" font-family="ui-monospace,monospace">window 1</text>')
    parts.append(f'<text x="{w-10}" y="{h-6}" text-anchor="end" fill="#77796f" font-size="10" '
                 f'font-family="ui-monospace,monospace">window {n}</text>')
    for (label, s), c in zip(series, colors):
        pts = " ".join(f"{X(i):.1f},{Y(v):.1f}" for i, v in enumerate(s))
        parts.append(f'<polyline fill="none" stroke="{c}" stroke-width="1.6" points="{pts}"/>')
    parts.append("</svg>")
    legend = " · ".join(f'<span style="color:{c}">■</span> {html.escape(l)}' for (l, _), c in zip(series, colors))
    return "".join(parts), legend


def main():
    live_dir, big_dir, viol_dir, out = sys.argv[1:5]
    live = rows(f"{live_dir}/verify.log")
    big = rows(f"{big_dir}/verify.log")
    viol = rows(f"{viol_dir}/verify.log")
    live_accept = last_line(f"{live_dir}/verify.log")
    big_n = big[-1]["n1"]
    hashes = [r["hashes"] for r in big]
    peaks = [r["peaks"] for r in big]
    us = [r["check_us"] for r in big]
    nspb = [r["check_us"] * 1000 / r["bytes"] for r in big]
    cum = []
    acc = 0
    for r in big:
        acc += r["check_us"]
        cum.append(acc / 1000)
    med_ms = st.median(us) / 1000
    q = len(big) // 4
    quart = [st.median(nspb[a:b]) for a, b in ((0, q), (q, 2 * q), (2 * q, 3 * q), (3 * q, len(big)))]
    hash_svg, hash_leg = svg_series([("hash calls per window", hashes)], ylab="hash calls per window", ymax=400)
    time_svg, time_leg = svg_series([("one window, incremental (ms)", [u / 1000 for u in us]),
                                     ("re-check from genesis (ms, cumulative)", cum)],
                                    ylab="milliseconds per window", colors=("#9fc55b", "#e56f3d"))
    v_first = next(r for r in viol if r["verdict"] == "viol")

    def row(r):
        return (f"<tr><td>{r['k']}</td><td>[{r['n0']}, {r['n1']})</td><td>{r['verdict']}</td>"
                f"<td>{'yes' if r['tripped'] else 'no'}</td><td>{'yes' if r['waiting'] else 'no'}</td>"
                f"<td>{r['marks']}</td><td>{r['last_mark']}</td><td>{r['hashes']}</td>"
                f"<td><code>{r['root'][:12]}…</code></td></tr>")

    live_rows = "".join(row(r) for r in (live[:3] + live[-3:] if len(live) > 6 else live))
    viol_rows = "".join(row(r) for r in viol)
    css = open(__file__.replace("microsite.py", "microsite.css")).read()
    page = f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <meta name="color-scheme" content="dark">
  <title>So far</title>
  <meta name="description" content="A live Claude Code session, a Büchi policy, and a receipt every hundred events that a Lean follower checks without re-reading the past.">
  <meta name="theme-color" content="#10110c">
  <style>{css}</style>
</head>
<body>
<main class="page">
  <header class="masthead">
    <a class="brand" href="../">dregg microsites</a>
    <span class="issue">Automata · streaming receipts</span>
  </header>

  <section class="titleblock">
    <p class="kicker">Initiative 11 · L3</p>
    <h1>So<br><span>far.</span></h1>
    <p class="dek">A Claude Code session writes its transcript one line at a time. Every hundred
    lines a receipt says what a policy automaton has seen: the state it is in, how often its
    acceptance condition has been met, whether anything has gone irrecoverably wrong, and the root
    of a Merkle mountain range over every line so far. A follower written in Lean checks each
    receipt against the previous one, in work that depends on the window, not on the session's
    length.</p>
  </section>

  <h2>The policy.</h2>
  <p>Two clauses, as one deterministic Büchi automaton (the product of a safety monitor and a
  liveness automaton, <code>prod_accepts_iff</code>):</p>
  <div class="notclaims">
    <div class="nc"><div class="x">□</div><p><strong>Safety.</strong> No Bash call runs a command
    the operator has forbidden: <code>git stash</code>, <code>git add -A</code>,
    <code>pkill -f</code> / <code>-x</code>, <code>killall</code>, <code>kill -u</code>. Wrappers
    such as <code>sudo</code>, <code>bash -c</code> and <code>ssh host '…'</code> are peeled. Once
    tripped, tripped for ever.</p></div>
    <div class="nc"><div class="x">◇</div><p><strong>Liveness.</strong> Every human prompt is
    eventually followed by assistant text. Accepting: no prompt waiting. Büchi: accepting
    infinitely often.</p></div>
  </div>
  <p>No finite prefix can say a liveness clause holds: whatever has happened, the assistant could
  fall silent for ever (<code>respLive_is_liveness</code>). So the verdict is three-valued.
  <strong>viol</strong> is final and means every infinite continuation is rejected
  (<code>verdict_viol_sound</code>, <code>verdict_monotone</code>). Otherwise it is
  <strong>unknown</strong>, and that is a real "?": both outcomes stay possible
  (<code>unknown_is_genuine</code>). What the receipts carry for the liveness clause instead is
  exact: the number of accepting positions so far, which is unbounded exactly when the
  infinite session is accepted (<code>buchi_iff_count_unbounded</code>), and the last accepting
  position, so the current wait is certified to be at most <code>n − last</code> events.</p>

  <h2>The receipts, <em>live.</em></h2>
  <p>This lane's own session transcript, tailed while the lane was still writing it: the producer
  cut a window every hundred lines as they appeared and a Lean follower checked them as they
  landed. When the producer was stopped the whole chain was checked once more, from genesis,
  against an independently computed root. That run's last line:</p>
  <pre>{html.escape(live_accept)}</pre>
  <div class="tablewrap"><table>
    <tr><th>k</th><th>positions</th><th>verdict</th><th>tripped</th><th>waiting</th><th>marks</th><th>last mark</th><th>hashes</th><th>root</th></tr>
    {live_rows}
  </table></div>
  <p>The root a log owner would publish was computed separately, from the source transcript's
  first {live[-1]['n1']:,} lines, and the chain was re-verified against it
  (<code>stream-check verify --anchor</code>). Without that anchor the chain proves only that the
  receipts match the windows it was shown: a producer that deletes a line before cutting windows
  and recomputes every receipt passes the chain check, and the demo shows the anchor refusing it
  (<code>anchored_is_genuine</code>).</p>

  <h2>A violation, and <em>after.</em></h2>
  <p>Another real session, replayed. At position {v_first['last_mark'] + 1} the agent ran
  <code>git add -A</code> in a freshly initialised repository. Window {v_first['k']} says
  <strong>viol</strong>, and no later window could say anything else.</p>
  <div class="tablewrap"><table>
    <tr><th>k</th><th>positions</th><th>verdict</th><th>tripped</th><th>waiting</th><th>marks</th><th>last mark</th><th>hashes</th><th>root</th></tr>
    {viol_rows}
  </table></div>

  <h2>Cost, <em>counted.</em></h2>
  <p>The largest session on this machine, {big_n:,} transcript lines (44.9 MB), replayed through
  the same producer and follower in {len(big)} windows. Per window the follower spends 2·w hash
  calls on the entries (their digests and their leaves), one per carry, and one per peak to bag the
  root. The peaks grow as log n ({peaks[0]} at the start, {max(peaks)} at the end); nothing else
  does.</p>
  <figure>{hash_svg}<figcaption>{hash_leg} · min {min(hashes)}, max {max(hashes)}</figcaption></figure>
  <p>Clock time per window is dominated by hashing and parsing the window's own bytes: median
  {med_ms:.1f} ms per window, {st.median(nspb):.0f} ns per byte. By quarter of the session the
  median was {quart[0]:.0f}, {quart[1]:.0f}, {quart[2]:.0f} and {quart[3]:.0f} ns per byte; the
  middle quarters ran while other builds loaded the same laptop, which is noise, not growth. The
  orange line is what a verifier without the previous receipt pays at each window: everything so
  far, again.</p>
  <figure>{time_svg}<figcaption>{time_leg}</figcaption></figure>

  <h2>Which leg is <em>which.</em></h2>
  <div class="notclaims">
    <div class="nc"><div class="x">1</div><p><strong>Proved (Lean, axioms propext / choice /
    Quot.sound).</strong> <code>window_sound</code>: an accepted receipt states exactly the
    automaton's run over the committed window, its counters and the MMR range it occupies.
    <code>windows_compose</code>: a chain accepted from genesis tracks the whole log; for every
    infinite continuation the state and counter are the infinite run's; a viol is a bad prefix;
    any range answer against any log with the final root is the monitored log's, every position
    present, unless a named hash collision occurred. Falsifiers: a dropped position, a dropped
    violating position, swapped windows, a flag-DFA reading and a counter reading of
    acceptance.</p></div>
    <div class="nc"><div class="x">2</div><p><strong>Executed.</strong> The follower is
    <code>lake exe stream-check</code>: Lean compiled to native code, deciding by the very
    function the theorems are about. Its hash is a pure-Lean BLAKE3; the Rust producer computes the
    same roots independently and stops if they ever differ.</p></div>
    <div class="nc"><div class="x">3</div><p><strong>Not proved.</strong> That the classifier
    means what its prose says: it reads command text syntactically (no <code>eval</code>,
    variables or scripts). That BLAKE3 has no collisions. The Rust audit read
    (<code>verify_range</code>) corresponds to the Lean range check by documentation only.</p></div>
  </div>

  <h2>What this does <em>not</em> claim.</h2>
  <div class="notclaims">
    <div class="nc"><div class="x">✗</div><p>that the session satisfies the liveness clause ·
    nothing finite can</p></div>
    <div class="nc"><div class="x">✗</div><p>succinctness · the follower reads each window's
    lines. A follower that sees only receipts needs the window proved in a circuit; counted
    (about 9,100 Poseidon2 permutations per 100 median-sized entries), not built</p></div>
    <div class="nc"><div class="x">✗</div><p>a checkpoint join · the follower starts at genesis;
    no theorem lets it adopt a stranger's receipt k</p></div>
    <div class="nc"><div class="x">✗</div><p>first-order obligations · "every tool call gets its
    result" needs a register per open call; the alphabet here is four symbols</p></div>
    <div class="nc"><div class="x">✗</div><p>a perfect shell reader · three rounds of
    adversarial audit by a second model (gpt-6-astra) closed every blocker and major finding; two
    minor classifier gaps remain on record (quoting inside substitutions, <code>env -S</code> and
    long <code>sudo</code> options)</p></div>
  </div>

  <div class="stance"><p><strong>Private by construction.</strong> This page shows roots, states,
  counts and timings. The transcript lines stay on the machine that wrote them; checking these
  receipts yourself needs them.</p></div>

  <footer><span>breadstuffs · metatheory/Dregg2/Stream · demo/stream-receipts</span><span>2026-11-06</span></footer>
</main>
</body>
</html>
"""
    open(out, "w").write(page)


if __name__ == "__main__":
    main()
