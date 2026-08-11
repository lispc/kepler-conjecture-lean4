#!/usr/bin/env python3
"""Re-shard failed coarse shard groups at finer granularity.

For each coarse group (gsize=100) whose shard file failed (fuel exhausted),
generate fine shard files (gsize_fine per file, higher fuel) under
CertShards/<Name>R/K*.lean with theorem prefix <name>r_, then rewrite
Cert<Name>.lean with a mixed-granularity dispatch: fine branches for the
failed ranges, coarse branches (existing shardE theorems) elsewhere.

Usage: reshardgen.py <p> <Name> <gsize_fine> <fuel> <failed_start,failed_start,...>
           [<gsize_coarse> [wireonly]]

`wireonly` (any nonempty string): do not (re)generate fine shard files, only
rewrite the wiring (fine shards already exist, e.g. PentR).
"""
import math
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from shardgen import frontier_length, shard_file  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[2]
LEAN = ROOT / "lean" / "Kepler" / "Graphs"


def mixed_dispatch(name, length, failed, gfine, gcoarse):
    """Nested dite-chain over mixed coarse/fine blocks."""
    lower = name.lower()
    blocks = []  # (start, cnt, prefix)
    start = 0
    while start < length:
        cnt = min(gcoarse, length - start)
        if start in failed:
            for s in range(start, start + cnt, gfine):
                blocks.append((s, min(gfine, start + cnt - s), lower + "r"))
        else:
            blocks.append((start, cnt, lower))
        start += cnt
    lines = []
    for i, (s, cnt, prefix) in enumerate(blocks):
        kw = "if" if i == 0 else "else if"
        lines.append(f"      {kw} h{i} : j < {s + cnt} then")
        lo = "Nat.zero_le j" if i == 0 else f"le_of_not_gt h{i - 1}"
        lines.append(f"        {prefix}_shardE_{s} j")
        lines.append(f"          (List.mem_range'_1.mpr ⟨{lo}, h{i}⟩)")
    lines.append("      else")
    lines.append(f"        absurd hj h{len(blocks) - 1}")
    return "\n".join(lines), blocks


def main():
    p = int(sys.argv[1])
    name = sys.argv[2]
    gfine = int(sys.argv[3])
    fuel = int(sys.argv[4])
    failed = {int(x) for x in sys.argv[5].split(",")}
    gcoarse = int(sys.argv[6]) if len(sys.argv) > 6 else 100
    wireonly = len(sys.argv) > 7
    length = frontier_length(name)
    lower = name.lower()

    # fine shard files, sequentially numbered over the failed ranges
    shard_dir = LEAN / "CertShards" / f"{name}R"
    shard_dir.mkdir(parents=True, exist_ok=True)
    k = 0
    for start in sorted(failed):
        cnt = min(gcoarse, length - start)
        for s in range(start, start + cnt, gfine):
            c = min(gfine, start + cnt - s)
            if not wireonly:
                (shard_dir / f"K{k:03d}.lean").write_text(
                    shard_file(p, name, fuel, s, c, lower + "r"))
            k += 1
    nfine = k

    # rewrite Cert<Name>.lean: imports + dispatch
    wiring = LEAN / f"Cert{name}.lean"
    txt = wiring.read_text()

    coarse_ok = []
    start = 0
    while start < length:
        if start not in failed:
            coarse_ok.append(start // gcoarse)
        start += gcoarse
    imports = "\n".join(
        [f"import Kepler.Graphs.CertShards.{name}.K{k:03d}" for k in coarse_ok]
        + [f"import Kepler.Graphs.CertShards.{name}R.K{k:03d}" for k in range(nfine)])
    txt, n = re.subn(
        r"import Kepler\.Graphs\.CertShards\." + name + r"\.K\d{3}\n"
        r"(?:import Kepler\.Graphs\.CertShards\." + name + r"\.K\d{3}\n?)*",
        imports + "\n", txt, count=1)
    assert n == 1, "import block not found"

    dispatch, _ = mixed_dispatch(name, length, failed, gfine, gcoarse)
    txt, n = re.subn(
        r"      if h0 : j < \d+ then.*?      else\n        absurd hj h\d+\n",
        dispatch + "\n", txt, count=1, flags=re.S)
    assert n == 1, "dispatch block not found"

    wiring.write_text(txt)
    print(f"{name}R: {nfine} fine shard files (group {gfine}), fuel {fuel}, "
          f"coarse ok blocks: {len(coarse_ok)}")


if __name__ == "__main__":
    main()
