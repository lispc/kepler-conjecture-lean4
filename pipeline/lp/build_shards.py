#!/usr/bin/env python3
"""build_shards.py — parallel builder for sharded LP certificates.

Lake has no job-level parallelism for independent modules in this toolchain,
and Lean's package-root module resolution (`SearchPath.findWithExt`: the first
LEAN_PATH entry containing the `Kepler/` directory captures *all* `Kepler.*`
modules) rules out separate output trees. So shard oleans are written to the
canonical location `.lake/build/lib/lean/Kepler/LP/<Mod>/` — the same place
lake itself would put them — via a process pool of `lake env lean` calls.
(We only *add* new module artifacts; no existing cache entry is touched.)

Stages (Data must already be built via `lake build Kepler.LP.<mod>.Data`):
  1. all `Cols<i>.lean` shards in parallel (`--procs`)
  2. `Assembly.lean` (imports every shard)

Usage: build_shards.py <Mod> [--procs N] [--only i,j,...]
Example: build_shards.py Pilot204880136538 --procs 96
"""

import argparse
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
LEAN_DIR = REPO / "lean"
OLEANS = LEAN_DIR / ".lake/build/lib/lean"


def compile_file(src: Path, name: str) -> tuple[str, float, str]:
    """Compile one .lean file; olean/ilean go to the canonical .lake path.

    Idempotent: skips when the olean exists and is newer than the source."""
    rel = src.relative_to(LEAN_DIR).with_suffix("")
    out = OLEANS / rel
    if (out.with_suffix(".olean")).exists() and \
            (out.with_suffix(".olean")).stat().st_mtime >= src.stat().st_mtime:
        return (f"{name} skip (cached)", 0.0, "")
    out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    proc = subprocess.run(
        ["lake", "env", "lean", str(src),
         "-o", str(out) + ".olean", "-i", str(out) + ".ilean"],
        cwd=LEAN_DIR, capture_output=True, text=True)
    dt = time.time() - t0
    status = "ok" if proc.returncode == 0 else "FAIL"
    err = (proc.stdout + proc.stderr)[-3000:] if proc.returncode != 0 else ""
    return (f"{name} {status} {dt:8.1f}s", dt, err)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("mod")
    ap.add_argument("--procs", type=int, default=96)
    ap.add_argument("--only", default=None, help="comma-separated shard indices")
    args = ap.parse_args()

    mod_dir = LEAN_DIR / "Kepler/LP" / args.mod
    shards = sorted(mod_dir.glob("Cols*.lean"))
    if args.only:
        keep = {f"Cols{int(i):03d}.lean" for i in args.only.split(",")}
        shards = [s for s in shards if s.name in keep]
    if not shards:
        print(f"no Cols*.lean in {mod_dir}", file=sys.stderr)
        return 1

    t0 = time.time()
    print(f"[build_shards] {len(shards)} shards, {args.procs} procs", flush=True)
    times, fails = [], []
    with ThreadPoolExecutor(max_workers=args.procs) as pool:
        futs = [pool.submit(compile_file, s, s.stem) for s in shards]
        done = 0
        for f in futs:
            msg, dt, err = f.result()
            times.append(dt)
            done += 1
            if err:
                fails.append(msg + "\n" + err)
            if done % 25 == 0 or done == len(shards):
                print(f"[build_shards] {done}/{len(shards)} "
                      f"({time.time() - t0:.0f}s wall)", flush=True)
    for msg in fails:
        print(msg, flush=True)
    times.sort()
    wall = time.time() - t0
    print(f"[build_shards] shards: n={len(times)} min={times[0]:.1f}s "
          f"med={times[len(times) // 2]:.1f}s max={times[-1]:.1f}s "
          f"sum={sum(times):.0f}s wall={wall:.0f}s", flush=True)
    if fails:
        return 1
    if args.only:
        print("[build_shards] --only given: skipping Assembly", flush=True)
        return 0

    print("[build_shards] building Assembly ...", flush=True)
    msg, dt, err = compile_file(mod_dir / "Assembly.lean", "Assembly")
    print(msg, flush=True)
    if err:
        print(err, flush=True)
        return 1
    print(f"[build_shards] total wall {time.time() - t0:.0f}s "
          f"(Data build not included)", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
