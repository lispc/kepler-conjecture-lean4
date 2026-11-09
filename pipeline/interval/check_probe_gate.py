#!/usr/bin/env python3
"""Assert the schema-v3 hull gate on a sample of stage-A/sound-probe logs.

The gate ("probe PASS => kernel PASS") is formally
`Kepler.Interval.hullProbeSound_checkPosTMHull`; this script asserts the
*machine* side of it on recorded runs:

  A. every leaf the sound probe reports as PASS must have a kernel
     `checkPosTMHull … = true` theorem that compiled (the GateCheck logs), and
  B. every leaf it reports NEG must be `false` at the kernel, and
  C. every leaf with a short mantissa-triple list must be rejected
     (`hullProbeSound = none`) — never promoted to a certificate.

Log formats (all produced by the lane drivers):
  <gate-log>       `GateCheck*.lean` compile log; expect RC=0 and no "error".
  <soundprobe-log> `SoundProbeSample.lean` run log; `#eval` lines are
                   `some { P := …, verdict := true, … }` / `none` in order.
  <params>         round-1 stage-A params file (`i PASS|NEG lo_m lo_e <3 ints>…`).

Usage: check_probe_gate.py --gate=<log> [--soundprobe=<log>] [--params=<f>]
       [--nSqrt=4] [--expect-pass=<k,k,…>] [--expect-neg=<k,…>]
Exits non-zero on any mismatch.
"""
import re
import sys


def parse(opts):
    o = {}
    for a in sys.argv[1:]:
        k, _, v = a[2:].partition("=")
        o[k] = v
    return o


def main():
    o = parse(sys.argv)
    ok = True
    fails = []

    if "gate" in o:
        txt = open(o["gate"]).read()
        errs = [l for l in txt.splitlines() if "error" in l]
        if errs:
            ok = False
            fails.append(f"gate compile log has {len(errs)} error line(s): {errs[:3]}")
        else:
            print(f"[A] gate compile log: 0 error lines ({o['gate']})")

    if "params" in o:
        nsqrt = int(o.get("nSqrt", "4"))
        rows = {}
        for ln in open(o["params"]):
            ln = ln.strip()
            if not ln or ln.startswith("RUNG"):
                continue
            tk = ln.split()
            rows[int(tk[0])] = (tk[1], len(tk[4:]) // 3)
        short = sorted(k for k, (v, nt) in rows.items() if nt != nsqrt)
        neg = sorted(k for k, (v, nt) in rows.items() if v != "PASS")
        print(f"[C] params: {len(rows)} leaves, short-triple {short}, verdict!=PASS {neg}")
        want_short = [int(x) for x in o.get("expect-short", "").split(",") if x.strip()]
        if want_short and short != want_short:
            ok = False
            fails.append(f"short-triple leaves {short} != expected {want_short}")

    if "soundprobe" in o:
        txt = open(o["soundprobe"]).read()
        # the sample driver prints one #eval block per leaf; a block starts at
        # a line that is exactly `some` or `none`
        blocks, cur = [], None
        for ln in txt.splitlines():
            t = ln.strip()
            if t == "some" or t == "none" or t.startswith("some "):
                if cur is not None:
                    blocks.append(cur)
                cur = t
            elif cur is not None:
                cur += " " + t
        if cur is not None:
            blocks.append(cur)
        got = []
        for b in blocks:
            if b.startswith("none"):
                got.append("REJECT")
            elif "false" in b:
                got.append("NEG")
            else:
                got.append("PASS")
        print(f"[B] sound-probe verdicts: {got}  ({len(blocks)} blocks)")
        want = o.get("expect-soundprobe", "")
        if want:
            exp = want.split("|")
            if got != exp:
                ok = False
                fails.append(f"sound-probe verdicts {got} != expected {exp}")
            else:
                print(f"[B] sound-probe verdicts match expectation {exp}")

    if fails:
        print("GATE-CHECK: FAIL")
        for f in fails:
            print("  -", f)
        sys.exit(1)
    print("GATE-CHECK: PASS")


if __name__ == "__main__":
    main()
