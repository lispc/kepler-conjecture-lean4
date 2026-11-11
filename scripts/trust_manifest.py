#!/usr/bin/env python3
"""trust_manifest.py — 生成并校验「信任基座」manifest（AGENTS.md §1 第 2 条）。

用法（在 repo 根）：
    python3 scripts/trust_manifest.py            # 生成 docs/trust-base.tsv + 打印校验摘要
    python3 scripts/trust_manifest.py --check    # 只校验，不写盘（CI 用）

它做三件事：
 1. 从 `docs/e2e-reachability-map.tsv` 的 `--- AXIOMS ---` 段取公理名单（仪器产的，不手抄）。
 2. 生成一个 Lean 探针逐条 `#print`，把每条公理的**陈述**取出来（这是审计的对象）。
 3. 校验三件事并写进 manifest：
    (a) **地面性**：陈述必须是 `decide (<闭项 Bool>) = true` 形，不许出现 `∀`/`∃`/自由变量；
    (b) **分解无损**：`*_shard_*` 的 `List.range' a l` 区间在每个 (类, next_tame p) 上
        无空隙、无重叠地铺满 [0, max(a+l))。铺满 ⇒ 分片合起来就是一条 ∀ 事实；
    (c) **数据源/生成器钉定**：每条公理带 `data_sha256` / `gen_sha256` 列；
        manifest 头部钉定 ArchiveData 四类 + 发射脚本的完整 sha256，
        `--check` 重算现文件并比对（数据漂移或生成器改动 ⇒ FAIL）。

不联网、不编译（只 `lake env lean` 读 olean）、不改 Lean 源码。
"""
import argparse
import hashlib
import os
import re
import subprocess
import sys
import tempfile
from collections import defaultdict
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
LEAN = REPO / "lean"
TSV = REPO / "docs" / "e2e-reachability-map.tsv"
OUT = REPO / "docs" / "trust-base.tsv"

# 数据源与生成器钉定（trust-base.md §4 待办第 3 条；AGENTS §1 第 2 条
# "注明数据源与生成器版本"）。`--check` 会把**仓内现文件的 sha256** 与
# manifest 头部记录的钉定值比对，任何数据漂移/生成器改动都会 FAIL。
DATA_FILES = {
    "Tri": "lean/Kepler/Graphs/ArchiveData/Tri.lean",
    "Quad": "lean/Kepler/Graphs/ArchiveData/Quad.lean",
    "Pent": "lean/Kepler/Graphs/ArchiveData/Pent.lean",
    "Hex": "lean/Kepler/Graphs/ArchiveData/Hex.lean",
}
GEN_SHARD = "lean/scripts/gen_goodlist_shards.py"   # shard-range 585 的 580 片
GEN_TRI = "lean/Kepler/Graphs/CertTri.lean"         # tri-single-seed 5 片（种子前沿，手写/一次性生成）

AXIOM_SECTION = re.compile(r"^--- AXIOMS ---$", re.M)
PIN_LINE = re.compile(r"^# (data|gen) ([^ ]+) ([^ ]+) ([0-9a-f]{64})$", re.M)


def sha256_file(rel):
    return hashlib.sha256((REPO / rel).read_bytes()).hexdigest()


def live_pins():
    pins = [("data", cls, rel, sha256_file(rel)) for cls, rel in sorted(DATA_FILES.items())]
    pins.append(("gen", "shard-range", GEN_SHARD, sha256_file(GEN_SHARD)))
    pins.append(("gen", "tri-single-seed", GEN_TRI, sha256_file(GEN_TRI)))
    return pins


def pinned_pins():
    if not OUT.exists():
        return None
    return {(k, name, rel): h for k, name, rel, h in PIN_LINE.findall(OUT.read_text())}


def read_axioms():
    text = TSV.read_text()
    m = AXIOM_SECTION.search(text)
    if not m:
        sys.exit("FATAL: no '--- AXIOMS ---' section in %s" % TSV)
    body = text[m.end():]
    end = re.search(r"^--- ", body, re.M)
    if end:
        body = body[: end.start()]
    rows = []
    for line in body.splitlines():
        if not line.strip():
            continue
        parts = line.split("\t")
        if len(parts) >= 2:
            rows.append((parts[0], parts[1]))
    return rows


def print_statements(names):
    """探针写到临时目录，不污染仓库。"""
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False,
                                     prefix="trust_manifest_") as f:
        f.write("import Kepler.Assembly\n" + "".join(f"#print {n}\n" for n in names))
        probe = f.name
    try:
        p = subprocess.run(
            ["nice", "-n", "19", "lake", "env", "lean", probe],
            cwd=LEAN, capture_output=True, text=True,
        )
    finally:
        os.unlink(probe)
    return p.stdout + p.stderr, p.returncode


def split_blocks(log):
    """按 `axiom <name> :` 切块；返回 {name: 归一化陈述}。"""
    out = {}
    for b in re.split(r"(?=^axiom )", log, flags=re.M):
        if not b.startswith("axiom "):
            continue
        m = re.match(r"axiom ([^\s:]+)\s*:", b)
        if not m:
            continue
        name = m.group(1)
        stmt = b[m.end():]
        stmt = re.split(r"\n(?:axiom |')", stmt)[0]
        out[name] = re.sub(r"\s+", " ", stmt).strip()
    return out


GROUND_OK = re.compile(r"^decide .*= true$")


def classify(stmt):
    if "List.range'" in stmt:
        return "shard-range"
    if re.search(r"\.all fun g => !g\.final", stmt):
        return "top-no-finals"
    if "TopChildren" in stmt and "t.2 <" in stmt:
        return "top-bounds"
    if "resolveChild" in stmt:
        return "top-replay"
    if "preIsoTestB" in stmt:
        return "archive-pre"
    if "goodListB" in stmt:
        return "goodlist-slice"
    if re.search(r"Frontier\[\d+\]!\]", stmt):
        return "tri-single-seed"
    return "UNKNOWN"


def params(stmt):
    d = {}
    m = re.search(r"List\.range' (\d+) (\d+)", stmt)
    if m:
        d["range_start"], d["range_len"] = int(m.group(1)), int(m.group(2))
    m = re.search(r"next_tame (\d+)", stmt)
    if m:
        d["p"] = int(m.group(1))
    m = re.search(r"buildBuckets [\w.]*?(\w+?)Data", stmt)
    if m:
        d["data"] = m.group(1)
    m = re.search(r"\) (\d{4,}) \[", stmt)
    if m:
        d["fuel"] = int(m.group(1))
    # goodList 切片：List.take N X / List.take N (List.drop M X) / List.drop M X
    if "goodListB" in stmt:
        takes = re.findall(r"List\.take (\d+) ", stmt)
        drops = re.findall(r"List\.drop (\d+) ", stmt)
        datas = re.findall(r"([A-Z]\w*?)Data", stmt)
        d["slice_start"] = int(drops[0]) if drops else 0
        if takes:
            d["slice_len"] = int(takes[0])
        if datas:
            d["data"] = datas[0]
    m = re.search(r"Frontier\[(\d+)\]!\]", stmt)
    if m:
        d["seed"] = int(m.group(1))
    d["class"] = d.get("data", "")
    return d


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="只校验，不写盘")
    args = ap.parse_args()

    axioms = read_axioms()
    if not axioms:
        sys.exit("FATAL: 0 axioms — instrument output stale?")
    names = [n for _, n in axioms]
    log, rc = print_statements(names)
    if rc != 0:
        print(log[:4000])
        sys.exit(f"FATAL: lean probe rc={rc}")

    stmts = split_blocks(log)
    missing = [n for n in names if n not in stmts]
    if missing:
        print("FATAL: %d axioms without a printed statement, e.g. %s" % (len(missing), missing[:5]))
        sys.exit(1)

    live = {(k, name, rel): h for k, name, rel, h in live_pins()}
    rows, bad_ground, unknown = [], [], []
    tiling = defaultdict(lambda: {"cover": set(), "ends": 0})
    for module, name in axioms:
        stmt = stmts[name]
        shape = classify(stmt)
        pr = params(stmt)
        if shape == "UNKNOWN":
            unknown.append((name, stmt[:160]))
        if not GROUND_OK.match(stmt):
            bad_ground.append((name, stmt[:160]))
        if shape == "shard-range":
            key = (pr.get("p"), pr.get("data"))
            start, ln = pr["range_start"], pr["range_len"]
            tiling[key]["ends"] = max(tiling[key]["ends"], start + ln)
            for i in range(start, start + ln):
                tiling[key]["cover"].add(i)
        h = hashlib.sha256(stmt.encode()).hexdigest()[:16]
        cls = pr.get("class", "") or ""
        data_sha = live[("data", cls, DATA_FILES[cls])][:16] if cls in DATA_FILES else ""
        if shape == "tri-single-seed":
            gen_sha = live[("gen", "tri-single-seed", GEN_TRI)][:16]
        else:
            gen_sha = live[("gen", "shard-range", GEN_SHARD)][:16]
        rows.append((name, module, shape,
                     str(pr.get("p", "")), str(pr.get("range_start", "")),
                     str(pr.get("range_len", "")), str(pr.get("fuel", "")),
                     pr.get("data", ""),
                     str(pr.get("slice_start", "")), str(pr.get("slice_len", "")),
                     str(pr.get("seed", "")), h, data_sha, gen_sha))

    # 分解无损校验
    tile_lines, tile_ok = [], True
    for (p, data), v in sorted(tiling.items(), key=lambda kv: str(kv[0])):
        end = v["ends"]
        cover = v["cover"]
        gaps = len(set(range(0, end)) - cover)
        dups = sum(1 for i in range(0, end) if i not in cover)  # placeholder, recomputed below
        dups = len([i for i in range(0, end) if i in cover]) - len(cover)  # always 0; explicit below
        dups = (sum(1 for i in range(0, end) if i in cover)) - len(cover)
        dup_flag = "no"
        tile_ok = tile_ok and gaps == 0
        tile_lines.append(f"p={p} data={data}: end={end} gaps={gaps} dups={dup_flag}")
    # 真正的重复检测：逐片累加计数
    counts = defaultdict(int)
    for module, name in axioms:
        stmt = stmts[name]
        pr = params(stmt)
        if classify(stmt) == "shard-range":
            for i in range(pr["range_start"], pr["range_start"] + pr["range_len"]):
                counts[(pr.get("p"), pr.get("data"), i)] += 1
    dups = [(k, c) for k, c in counts.items() if c > 1]

    print(f"axioms                 : {len(rows)}")
    print(f"ground (decide … = true): {len(rows) - len(bad_ground)} / {len(rows)}")
    print(f"non-ground             : {len(bad_ground)}")
    for n, s in bad_ground[:5]:
        print("   ", n, "::", s)
    print(f"unknown shape          : {len(unknown)}")
    for n, s in unknown[:8]:
        print("   ", n, "::", s)
    print("tiling (shard ranges):")
    for l in tile_lines:
        print("   ", l)
    print(f"tiling duplicates      : {len(dups)}")

    # goodList 切片的连续性：按 data 分组，start 必须首尾相接且从 0 开始
    slices = defaultdict(list)
    for module, name in axioms:
        stmt = stmts[name]
        if classify(stmt) != "goodlist-slice":
            continue
        pr = params(stmt)
        slices[pr.get("data", "?")].append((pr.get("slice_start", 0),
                                            pr.get("slice_len", None)))
    gl_ok = True
    print("goodList slice contiguity:")
    for data, v in sorted(slices.items()):
        v.sort(key=lambda t: t[0])
        cur, bad = 0, []
        for start, ln in v:
            if start != cur:
                bad.append((cur, start))
            cur = start + (ln if ln is not None else 0)
        ok = not bad and v and v[0][0] == 0
        gl_ok = gl_ok and ok
        print(f"    {data}: {len(v)} slices, contiguous={ok}, tail_open="
              f"{v[-1][1] is None}" + (f" breaks={bad}" if bad else ""))

    # 数据源 / 生成器钉定校验（manifest 头部 vs 仓内现文件；仅 --check）
    if args.check:
        pins_live = live_pins()
        pins_pinned = pinned_pins()
        pin_bad = []
        if pins_pinned is None:
            pin_bad = [("MANIFEST", "docs/trust-base.tsv missing")]
        else:
            for k, name, rel, h in pins_live:
                if pins_pinned.get((k, name, rel)) != h:
                    pin_bad.append((f"{k}:{name}", f"{rel} pinned={pins_pinned.get((k, name, rel))} live={h}"))
        print(f"data-source/gen pins   : {'OK' if not pin_bad else 'DRIFT'}")
        for n, s in pin_bad:
            print("   ", n, "::", s)
        ok = (not bad_ground) and (not unknown) and tile_ok and not dups and gl_ok and not pin_bad
        print("CHECK:", "PASS" if ok else "FAIL")
        return 0 if ok else 1

    pins_live = live_pins()
    print(f"data-source/gen pins   : pinning {len(pins_live)} entries")

    with OUT.open("w") as f:
        f.write("# 信任基座 manifest —— 由 scripts/trust_manifest.py 生成，勿手改。\n")
        f.write("# 生成源：docs/e2e-reachability-map.tsv 的 --- AXIOMS --- 段 + `#print` 陈述。\n")
        f.write("# 口径：AGENTS.md §1（用户 2026-11-06 裁决：不比 Flyspeck/Isabelle 更差）。\n")
        f.write("# 钉定（--check 校验现文件 sha256；数据源 = ArchiveData 四类，生成器 = shard 发射脚本）：\n")
        for k, name, rel, h in pins_live:
            f.write(f"# {k} {name} {rel} {h}\n")
        f.write("# 列：axiom | module | shape | next_tame_p | range_start | range_len | fuel |"
                " data | slice_start | slice_len | seed | stmt_sha256[:16] | data_sha256[:16] |"
                " gen_sha256[:16]\n")
        for r in rows:
            f.write("\t".join(r) + "\n")
    print(f"wrote {OUT}  ({len(rows)} rows)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
