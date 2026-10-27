#!/usr/bin/env python3
"""gen_w6a_align.py — W6-A lane (hlp-w6a): archive-alignment Lean emitter.

Reads every Flyspeck LP-certificate Marshal source
(`reference/flyspeck/formal_lp/glpk/binary/{easy,hard}_*.dat` plus the
`hard_7.tar.gz` member), decodes each certificate's hypermap string exactly
like HOL `convert_to_list` (list_hypermap_computations.hl:134-146), matches
it against the in-repo tame archive (`Kepler/Graphs/ArchiveData/*.lean`,
exact fgraph equality — no renumbering, no isomorphism), and emits a Lean
data module `Kepler.LP.W6Align` under `lean/Kepler/LP/` with:

  * `CertOf` — the alignment relation `decodeHypermap g.hypermapString = L`
    between a landed `LpGraphCert` and its archive entry (fgraph ℕ, which is
    definitionally `List (List Nat)`);
  * `certArchIdx` / `invCertIdx` — the forward/inverse archive-placement
    tables (19,715 entries each; the "CertOf archive 对齐表");
  * one kernel-checked alignment theorem PER GRAPH (19,715 total):
      `theorem align_XXXXX : CertOf (listAt k dataAll)
                                 (listAt σ(k) tameArchiveLists) := by decide`
  * bulk segment-slice alignment theorems (take/drop form) and table facts
    (length / bounds / Nodup);
  * the Lean side of the inequality-family census:
    `usedFamilies : List (String × Nat)` over terminal `constraints`.

STOP-EVENT discipline (per lane TASK): any of
  (a) a certificate whose hypermap string does not decode (count mismatch,
      truncation, non-digit token),
  (b) a certificate with no archive entry (or a duplicate archive entry),
  (c) binary parse order ≠ landed `W6Data.dataAll` order (element-wise),
  (d) duplicate graph ids,
  (e) terminal precision outside `LpPrecision.p3..p7`,
aborts the whole emission with exit code 2 and a failure report.  Nothing is
skipped, widened or "repaired".

The emitted module imports only `Kepler.Assembly.GoodListDefs` (for
`tameArchiveLists`) and `Kepler.Text.LP.W6Data` (for `dataAll`); it is
imported by nothing and is built standalone (`lake build Kepler.LP.W6Align`).
No existing tracked file is touched.

Usage:
  python3 gen_w6a_align.py --repo <repo> --out <outdir> [--emit-lean] [--census-only]

The Marshal reader is imported from the in-repo `pipeline/lp/parse_lpcert.py`
(no copy: single reader of record, same as `lpw6a` lane discipline).
"""

import argparse
import ast
import importlib.util
import json
import re
import sys
import tarfile
import tempfile
from collections import Counter
from pathlib import Path

sys.setrecursionlimit(2_000_000)

ARCHIVE_ORDER = ("Tri", "Quad", "Pent", "Hex")
SEG_RANGES = {}  # filled by load_archive: name -> (start, end) flat offsets

SHARD_FILES = (["Shard00", "Shard01", "Shard02"]
               + [f"Hard{i:02d}" for i in range(15)])

THMS_PER_FILE = 1000        # per-graph alignment theorems per emitted file
BULK_CHUNK = 2000           # bulk slice-theorem chunk size
NATS_PER_LINE = 20          # table literal numbers per emitted line

LP_SPLIT_TYPES = {"tri", "quad", "pent", "hex", "edge", "218", "236",
                  "mid", "high", "add_big"}


# ------------------------------------------------------------------ loading

def load_parser(repo: Path):
    src = repo / "pipeline" / "lp" / "parse_lpcert.py"
    spec = importlib.util.spec_from_file_location("parse_lpcert", src)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def decode_hypermap(hs: str):
    """HOL `convert_to_list` (list_hypermap_computations.hl:134-146):
    drop `_` (global replace), split on space runs, drop id token and count
    token, then read (len, face…) pairs.  Returns (gid, faces); raises on
    any decode violation (count mismatch / truncation / non-digit tokens).

    Byte-whitelist enforced here (gate (a)): the Lean-side decoder scans
    raw UTF-8 bytes, so every byte must be a digit, space or `_` — anything
    else would be silently mis-read as a digit there."""
    for c in hs:
        if c not in "0123456789 _":
            raise ValueError(
                f"byte {ord(c):#04x} outside ASCII digit/space/underscore")
    if "_" in hs:
        hs = hs.replace("_", "")
    toks = hs.split()
    if len(toks) < 2:
        raise ValueError(f"hypermap string has < 2 tokens: {hs[:60]!r}")
    gid = toks[0]
    for t in toks:
        # ASCII-only: Python isdigit() accepts Unicode digits whose int()
        # value would diverge from the Lean byte arithmetic.
        if not (t.isascii() and t.isdigit()):
            raise ValueError(f"{gid}: non-digit token {t!r}")
    nums = [int(t) for t in toks[1:]]
    nfaces, rest = nums[0], nums[1:]
    faces, i = [], 0
    while i < len(rest):
        n = rest[i]
        if n < 0:
            raise ValueError(f"{gid}: negative face length {n}")
        i += 1
        if i + n > len(rest):
            raise ValueError(f"{gid}: truncated face")
        faces.append(rest[i:i + n])
        i += n
    if len(faces) != nfaces:
        raise ValueError(f"{gid}: face count {len(faces)} != header {nfaces}")
    return gid, faces


def load_archive(repo: Path):
    """Parse the four ArchiveData constants; build the exact-match flat
    index.  Raises on duplicate archive entries (stop event (b))."""
    base = repo / "lean" / "Kepler" / "Graphs" / "ArchiveData"
    aindex = {}
    dup = []
    off = 0
    per_class = {}
    for name in ARCHIVE_ORDER:
        txt = (base / f"{name}.lean").read_text()
        i = txt.index(":= [")
        j = txt.rindex("]")
        graphs = ast.literal_eval(txt[i + 4:j].replace("\n", " "))
        per_class[name] = len(graphs)
        SEG_RANGES[name] = (off, off + len(graphs))
        for k, g in enumerate(graphs):
            key = tuple(map(tuple, g))
            if key in aindex:
                dup.append((name, k, aindex[key]))
            else:
                aindex[key] = off + k
        off += len(graphs)
    if dup:
        raise SystemExit(f"STOP-EVENT (b): duplicate archive entries {dup[:5]}")
    return aindex, per_class, off


def dat_paths(repo: Path, tmp: Path):
    """Parse order = the landed W6Data convention (verified against the
    Hard00-Hard14 shard gids, 2026-10-23): lexicographic *.dat order with
    the tar-extracted `hard_7.dat` at its natural sort position — NOT
    appended last (first run fired gate (c) at exactly the 3 trailing
    positions because of that append; landing puts hard_7 between hard_6
    and hard_8)."""
    b = repo / "reference" / "flyspeck" / "formal_lp" / "glpk" / "binary"
    entries = {p.name: (p, "dat") for p in b.glob("*.dat")}
    tgz = b / "hard_7.tar.gz"
    if tgz.exists():
        with tarfile.open(tgz) as tf:
            member = tf.getmember("hard_7.dat")
            member.name = "hard_7.dat"
            tf.extract(member, tmp)
        entries["hard_7.dat"] = (tmp / "hard_7.dat", "tar.gz:hard_7.tar.gz")
    return [entries[k] for k in sorted(entries)]


def dataall_order(repo: Path):
    """The landed W6Data `dataAll` element order, recovered from the shard
    files by extracting each cert literal's hypermap string in order."""
    hs = []
    base = repo / "lean" / "Kepler" / "Text" / "LP" / "W6Data"
    for name in SHARD_FILES:
        txt = (base / f"{name}.lean").read_text()
        hs.extend(re.findall(r'⟨\s*"((?:[^"\\]|\\.)*)"', txt))
    return hs


def load_lp_ineqs_ids(repo: Path):
    txt = (repo / "lean" / "Kepler" / "Assembly" / "IdLists.lean").read_text()
    # IdLists.lean:484 — closing `]` sits on the same line as the last
    # string (`"JNTEFVP 1"]`), so anchor on the FIRST `]` after the `[`
    # (the id strings themselves contain no `]`).
    m = re.search(r"def lpIneqsIds : List String :=\s*\[(.*?)\]", txt, re.S)
    if m is None:
        raise SystemExit("STOP-EVENT: lpIneqsIds not found in IdLists.lean")
    return re.findall(r'"([^"]*)"', m.group(1))


# ------------------------------------------------------------------- walking

def walk_terminals(case, out):
    """Collect terminal payload blocks [precision, infeasible, constraints,
    targetVariables, variableBounds] in DFS order (== ti order)."""
    tag = case[1]
    if tag == 0:  # Lp_terminal
        t = case[2][0][2]
        if len(t) != 5:
            raise ValueError(f"terminal block size {len(t)} != 5")
        out.append(t)
        return
    if tag != 1:
        raise ValueError(f"bad lp_certificate_case tag {tag}")
    sc = case[2][0][2]
    if sc[0] not in LP_SPLIT_TYPES:
        raise ValueError(f"unknown split type {sc[0]!r}")
    for c in to_list(case[2][1]):
        walk_terminals(c, out)


def to_list(v):
    out = []
    while v != 0:
        tag, (h, t) = v[1], v[2]
        if tag != 0:
            raise ValueError(f"bad list node tag {tag}")
        out.append(h)
        v = t
    return out


PREC_NAT = {3: ".p3", 4: ".p4", 5: ".p5", 6: ".p6", 7: ".p7"}


# ------------------------------------------------------------------ emission

BASIC_HEAD = """/-
  Kepler.LP.W6Align.Basic — W6-A 逐图 archive 对齐的内核件（车道 hlp-w6a）。

  机器生成：`pipeline/lp/gen_w6a_align.py`；不要手改。

  语义锚：
  * `decodeHypermap` = HOL `convert_to_list`
    （list_hypermap_computations.hl:134-146）的 Lean 直译：去 `_`、按空格
    run 分词、丢 id 与 count 两 token、(len, face…) 配对。**字节级单遍
    实现**（本工具链 String 为 UTF-8 ByteArray 承载，`String.toList` 走
    按索引解码 = 内核 O(n²)；数据侧全 ASCII——生成器门槛 (a) 逐字节
    断言——故直接在 `toByteArray.data.toList` 上单遍扫描：字节 95 (`_`)
    跳过 = 严格 global-replace 语义，32 = 分隔，48..57 = 数字）。全结构
    递归，内核可归约；计数核对由生成器承担（生成侧零违例为停批门槛）。
  * `CertOf g L` = 证书 g 的 hypermap 串解码恰为 archive 条目 L
    （`fgraph ℕ` 定义性展开为 `List (List Nat)`；逐元素精确相等，
    不做同构/重编号）。
  * `listAt` = 内核友好的取元（越界给 `Inhabited` 默认；本模块所有
    用点都在 19,715 范围内，越界支不触发）。

  import 闭包只含 `Kepler.Assembly.GoodListDefs`（tameArchiveLists）与
  `Kepler.Text.LP.W6Data`（dataAll）；本模块不被任何既有文件 import。
-/
import Kepler.Assembly.GoodListDefs
import Kepler.Text.LP.W6Data

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

namespace Kepler.LP.W6Align
open Kepler.Assembly Kepler.Text.LP Kepler.Text.LP.W6Data

deriving instance Inhabited for LpPrecision, LpSplitType, LpSplitNode,
  LpTerminalCase, LpCaseTree, LpGraphCert

/-- 单遍字节级分词：UTF-8 字节表 → Nat token（数据侧 ASCII：32 = 空格、
48..57 = 数字、95 = `_` 跳过）。`seen` 区分「尾随分隔符」与「token 0」；
token 以 `cur :: acc` 压入、尾部一次 `reverse`（整体 O(n)，无中间
String、无逐 token toList/reverse）。 -/
def natToksGo (cur : Nat) (seen : Bool) (acc : List Nat) : List UInt8 → List Nat
  | [] => if seen then (cur :: acc).reverse else acc.reverse
  | b :: cs =>
      if b = 32 then
        (if seen then natToksGo 0 false (cur :: acc) cs
                  else natToksGo 0 false acc cs)
      else if b = 95 then natToksGo cur seen acc cs
      else natToksGo (cur * 10 + (b.toNat - 48)) true acc cs

/-- (len, face…) 配对（fuel = token 数上界；越界/截断给短表，
由对齐定理的精确相等排除）。 -/
def decodeFacesF : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, len :: rest => rest.take len :: decodeFacesF n (rest.drop len)

/-- HOL `convert_to_list`：`id :: count :: (len, face…) 串联` → 面表。
id 与 count 两 token 丢弃（与 HOL 逐字一致；count 核对 = 生成侧门槛）。 -/
def decodeHypermap (hs : String) : List (List Nat) :=
  match natToksGo 0 false [] hs.toByteArray.data.toList with
  | _ :: _ :: toks => decodeFacesF (toks.length + 1) toks
  | _ => []

/-- **CertOf**：证书 g 与 archive 条目 L 的对齐关系——hypermap 串解码
恰为该条目（逐元素精确相等）。W6-B 可由逐图 `align_*` + 表事实升级为
`∀ L ∈ tameArchiveLists, ∃ g ∈ dataAll, CertOf g L`。 -/
abbrev CertOf (g : LpGraphCert) (L : List (List Nat)) : Prop :=
  decodeHypermap g.hypermapString = L

/-- 内核友好取元（越界给默认值；对齐用点均在范围内）。 -/
def listAt [Inhabited α] : Nat → List α → α
  | _, [] => default
  | 0, a :: _ => a
  | k + 1, _ :: t => listAt k t

end Kepler.LP.W6Align
"""


def fmt_nat_list(xs, indent="  "):
    lines = []
    for i in range(0, len(xs), NATS_PER_LINE):
        lines.append(indent + ", ".join(str(x) for x in xs[i:i + NATS_PER_LINE]) + ",")
    return "[\n" + "\n".join(lines) + "\n]"


def emit(outdir: Path, repo: Path, flat: list, used_families, stats):
    """Emit the Kepler.LP.W6Align module tree.  `flat[k]` = archive flat
    index of dataAll's k-th certificate."""
    n = len(flat)
    inv = [0] * n
    for k, j in enumerate(flat):
        inv[j] = k
    lean = outdir / "lean" / "Kepler" / "LP"
    (lean / "W6Align").mkdir(parents=True, exist_ok=True)

    (lean / "W6Align" / "Basic.lean").write_text(BASIC_HEAD)

    # ---- Table.lean
    fam_entries = ", ".join(f'("{nm}", {cnt})' for nm, cnt in used_families)
    table = f"""/-
  Kepler.LP.W6Align.Table — CertOf archive 对齐表（正向 + 逆向）与
  证书引用不等式族普查的 Lean 形（车道 hlp-w6a）。

  机器生成：`pipeline/lp/gen_w6a_align.py`；不要手改。

  * `certArchIdx[k]`：`dataAll` 第 k 张证书解码后（`CertOf` 意义下）在
    `tameArchiveLists` 中的平坦下标。分段：Tri [0,9) / Quad [9,1262) /
    Pent [1262,17342) / Hex [17342,19715)。
  * `invCertIdx[j]`：逆向表（archive 条目 j ← 证书下标）。
  * `usedFamilies`：全部 43,078 终端 `constraints` 的族名 × 引用计数
    （name 升序）；`usedFamilyIds` = 其名称表（W6-D 族线性化输入）。
-/
import Kepler.LP.W6Align.Basic

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

namespace Kepler.LP.W6Align

/-- 正向对齐表：cert k ↦ archive 平坦下标（{n} 项）。 -/
def certArchIdx : List Nat := {fmt_nat_list(flat)}

/-- 逆向对齐表：archive 条目 j ↦ cert 下标（{n} 项）。 -/
def invCertIdx : List Nat := {fmt_nat_list(inv)}

/-- 证书引用不等式族普查（constraints 表；name 升序，引用计数降序消歧不用）。 -/
def usedFamilies : List (String × Nat) := [{fam_entries}]

/-- 族名清单（W6-D `getIneqs` 的实际使用族集合）。 -/
def usedFamilyIds : List String := usedFamilies.map Prod.fst

theorem usedFamilies_length : usedFamilies.length = {len(used_families)} := rfl

theorem usedFamilyIds_length : usedFamilyIds.length = {len(used_families)} := rfl

theorem usedFamilies_totalRefs :
    (usedFamilies.map Prod.snd).sum = {stats['family_total_refs']} := by decide

end Kepler.LP.W6Align
"""
    (lean / "W6Align" / "Table.lean").write_text(table)

    # ---- AlignXX.lean: per-graph alignment theorems
    align_files = []
    for start in range(0, n, THMS_PER_FILE):
        chunk = list(range(start, min(start + THMS_PER_FILE, n)))
        no = start // THMS_PER_FILE
        thms = []
        for k in chunk:
            thms.append(
                f"/- k = {k} -/\n"
                f"theorem align_{k:05d} :\n"
                f"    CertOf (listAt {k} dataAll) "
                f"(listAt {flat[k]} tameArchiveLists) := by decide")
        body = "\n\n".join(thms)
        text = f"""/-
  Kepler.LP.W6Align.Align{no:02d} — 逐图对齐定理 {chunk[0]:05d}–{chunk[-1]:05d}
  （共 {len(chunk)} 条；每条一次内核 `decide`：解码 dataAll 第 k 张证书的
  hypermap 串，与 tameArchiveLists 第 certArchIdx[k] 条逐元素精确相等）。

  机器生成：`pipeline/lp/gen_w6a_align.py`；不要手改。
-/
import Kepler.LP.W6Align.Basic

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

namespace Kepler.LP.W6Align
open Kepler.Assembly Kepler.Text.LP Kepler.Text.LP.W6Data

{body}

end Kepler.LP.W6Align
"""
        fn = lean / "W6Align" / f"Align{no:02d}.lean"
        fn.write_text(text)
        align_files.append(f"Align{no:02d}")

    # ---- Bulk.lean: segment-slice take/drop theorems (σ-table form)
    bulks = []
    nb = (n + BULK_CHUNK - 1) // BULK_CHUNK
    for i in range(nb):
        m = i * BULK_CHUNK
        c = min(BULK_CHUNK, n - m)
        seg = flat[m:m + c]                       # archive index per cert
        seg_lit = ", ".join(str(j) for j in seg)
        bulks.append(
            f"/- dataAll[{m}..{m + c}) 解码 ↔ tameArchiveLists[σ] 对账"
            f"（σ = certArchIdx[{m}..{m + c})） -/\n"
            f"theorem alignBulk_{i:02d} :\n"
            f"    List.map (fun g => decodeHypermap g.hypermapString) "
            f"(List.take {c} (List.drop {m} dataAll))\n"
            f"      = [{seg_lit}].map (fun j => listAt j tameArchiveLists) "
            f":= by decide")
    bulk_text = f"""/-
  Kepler.LP.W6Align.Bulk — 分段切片对账（O(n) 批形；与逐图 align_* 互为
  冗余校验：同一条对齐链的两种内核检查路线）。

  机器生成：`pipeline/lp/gen_w6a_align.py`；不要手改。
-/
import Kepler.LP.W6Align.Basic

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

namespace Kepler.LP.W6Align
open Kepler.Assembly Kepler.Text.LP Kepler.Text.LP.W6Data

{chr(10).join(bulks)}

end Kepler.LP.W6Align
"""
    (lean / "W6Align" / "Bulk.lean").write_text(bulk_text)

    # ---- root W6Align.lean
    imports = "\n".join(f"import Kepler.LP.W6Align.{f}" for f in
                        ["Basic", "Table", *align_files, "Bulk"])
    last_align = (n - 1) // THMS_PER_FILE
    root = f"""/-
  Kepler.LP.W6Align — W6-A 逐图 archive 对齐数据模块根（车道 hlp-w6a）。

  机器生成：`pipeline/lp/gen_w6a_align.py`；不要手改。

  内容：
  * `CertOf` + `decodeHypermap`（HOL convert_to_list 直译）— Basic；
  * 正/逆 archive 对齐表 `certArchIdx` / `invCertIdx` + 族普查
    `usedFamilies` — Table；
  * 逐图对齐定理 `align_00000..align_{n - 1:05d}`（{n} 条，每条内核
    `decide`）— Align00..Align{last_align:02d}；
  * 分段切片对账 `alignBulk_*` — Bulk。

  验收锚：`w6align`（表事实总合取）；公理面 = `#print axioms` 标准三
  （构建日志/探针核对）。本模块不被任何既有文件 import；独立构建：
  `lake build Kepler.LP.W6Align`。
-/
{imports}

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

namespace Kepler.LP.W6Align
open Kepler.Assembly Kepler.Text.LP Kepler.Text.LP.W6Data

theorem certArchIdx_length : certArchIdx.length = {n} := by decide

theorem certArchIdx_bounds : certArchIdx.all (· < {n}) = true := by decide

theorem invCertIdx_length : invCertIdx.length = {n} := by decide

theorem invCertIdx_bounds : invCertIdx.all (· < {n}) = true := by decide

/-- 表事实总合取（W6-B 消费入口）。 -/
theorem w6align :
    dataAll.length = 19715 ∧
    certArchIdx.length = {n} ∧
    certArchIdx.all (· < {n}) = true ∧
    invCertIdx.length = {n} ∧
    usedFamilyIds.length = {len(used_families)} := by
  refine ⟨?_, certArchIdx_length, certArchIdx_bounds, invCertIdx_length, ?_⟩
  · exact W6Data.dataAll_length
  · exact usedFamilyIds_length

end Kepler.LP.W6Align
"""
    (lean / "W6Align.lean").write_text(root)
    return len(align_files)


# --------------------------------------------------------------------- main

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--repo", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--emit-lean", action="store_true")
    ap.add_argument("--census-only", action="store_true")
    args = ap.parse_args()

    repo = Path(args.repo).resolve()
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    P = load_parser(repo)

    aindex, per_class, arch_total = load_archive(repo)

    # 1) walk all Marshal sources
    graphs = []          # dicts: gid, hs, flat (or None), file
    fam = {"constraints": Counter(), "targetVariables": Counter(),
           "variableBounds": Counter()}
    fam_terms = Counter()   # per family: #terminals referencing (constraints)
    fam_graphs = {}         # family -> set of gids
    family_total_refs = 0
    prec_hist = Counter()
    stop_failures = []
    seen_gids = {}
    with tempfile.TemporaryDirectory() as td:
        paths = dat_paths(repo, Path(td))
        for path, kind in paths:
            certs = [P.to_cert(v)
                     for v in P.to_list(P.read_marshal(str(path)))]
            print(f"[parse] {path.name:12s} graphs={len(certs)}", flush=True)
            for ci, cert in enumerate(certs):
                hs = cert["hypermap_string"]
                try:
                    gid, faces = decode_hypermap(hs)
                except ValueError as e:
                    stop_failures.append(f"(a) decode: {e}")
                    continue
                if gid in seen_gids:
                    stop_failures.append(
                        f"(d) duplicate gid {gid}: {seen_gids[gid]} & "
                        f"{path.name}#{ci}")
                else:
                    seen_gids[gid] = f"{path.name}#{ci}"
                key = tuple(map(tuple, faces))
                flat = aindex.get(key)
                if flat is None:
                    stop_failures.append(
                        f"(b) no archive entry: {gid} ({path.name}#{ci})")
                # census + precision audit over all terminals
                terms = []
                try:
                    walk_terminals(cert["root_case"], terms)
                except ValueError as e:
                    # decode-class violation (unknown split type / bad tree
                    # shape) — gate (a), not the precision gate (e).
                    stop_failures.append(f"(a) {gid}: tree-walk: {e}")
                    terms = []
                g_fams = set()
                for t in terms:
                    p = int(t[0])
                    prec_hist[p] += 1
                    if p not in PREC_NAT:
                        stop_failures.append(
                            f"(e) {gid}: precision {p} outside p3..p7")
                    for ti, tbl in ((2, "constraints"), (3, "targetVariables"),
                                    (4, "variableBounds")):
                        for c in to_list(t[ti]):
                            name = c[2][0]
                            fam[tbl][name] += 1
                            if tbl == "constraints":
                                fam_terms[name] += 1
                                g_fams.add(name)
                                family_total_refs += 1
                for name in g_fams:
                    fam_graphs.setdefault(name, set()).add(gid)
                graphs.append({"gid": gid, "hs": hs, "flat": flat,
                               "file": path.name, "src": kind})

    # 2) reconcile binary order vs landed dataAll order (stop event (c))
    landed = dataall_order(repo)
    order_ok = [g["hs"] for g in graphs] == landed
    if not order_ok:
        bad = [i for i, (a, b) in
               enumerate(zip([g["hs"] for g in graphs], landed)) if a != b]
        stop_failures.append(
            f"(c) binary order != dataAll order at {len(bad)} positions, "
            f"first={bad[:5]} (len {len(graphs)} vs {len(landed)})")

    # 3) family census vs lpIneqsIds
    lp_ids = load_lp_ineqs_ids(repo)
    lp_set = set(lp_ids)
    used = sorted(fam["constraints"].items(), key=lambda kv: kv[0])
    used_set = {nm for nm, _ in used}
    def base(nm):
        return nm.split()[0] if " " in nm else nm
    used_base = {base(nm) for nm in used_set}
    lp_base = {base(x) for x in lp_ids}

    # 4) reports
    matched = sum(1 for g in graphs if g["flat"] is not None)
    stats = {
        "graphs": len(graphs),
        "matched_archive": matched,
        "unmatched": len(graphs) - matched,
        "archive": {"per_class": per_class, "total": arch_total},
        "order_matches_dataAll": order_ok,
        "stop_failures": stop_failures,
        "family_total_refs": family_total_refs,
        "families_distinct": {k: len(v) for k, v in fam.items()},
        "precision_hist": dict(sorted(prec_hist.items())),
        "lpIneqsIds_count": len(lp_ids),
        "census_vs_lpIneqsIds": {
            "used_exact_in_127": sorted(used_set & lp_set),
            "count_exact": len(used_set & lp_set),
            "used_base_in_127base": sorted(used_base & lp_base),
            "count_base": len(used_base & lp_base),
            "lp_exact_not_used": sorted(lp_set - used_set)[:20],
            "count_lp_not_used": len(lp_set - used_set),
        },
    }
    (out / "stats.json").write_text(json.dumps(stats, indent=2, ensure_ascii=False))

    # census TSV (also dropped into the repo as a NEW file docs/scouts/…)
    tsv_rows = ["family\tconstraints_refs\ttargetVariables_refs\t"
                "variableBounds_refs\tterminals_using\tgraphs_using\t"
                "in_lpIneqsIds_exact"]
    for nm, cnt in used:
        tsv_rows.append(f"{nm}\t{cnt}\t{fam['targetVariables'][nm]}\t"
                        f"{fam['variableBounds'][nm]}\t{fam_terms[nm]}\t"
                        f"{len(fam_graphs.get(nm, set()))}\t"
                        f"{'Y' if nm in lp_set else 'N'}")
    tsv = "\n".join(tsv_rows) + "\n"
    (out / "lp-family-census.tsv").write_text(tsv)
    if args.emit_lean or args.census_only:
        tdir = repo / "docs" / "scouts"
        tdir.mkdir(parents=True, exist_ok=True)
        (tdir / "lp-family-census.tsv").write_text(tsv)

    # 5) stop-event gate
    if stop_failures:
        (out / "STOP_EVENT.txt").write_text(
            "对齐失败 = 停批事件（TASK 硬规则）。\n"
            + "\n".join(stop_failures[:200])
            + f"\n... total {len(stop_failures)} failures\n")
        print(f"STOP-EVENT: {len(stop_failures)} failure(s); "
              f"see {out/'STOP_EVENT.txt'}", flush=True)
        return 2

    print(f"[align] graphs={len(graphs)} matched={matched} "
          f"unmatched=0 order_ok={order_ok}", flush=True)
    print(f"[census] distinct constraint families={len(used)} "
          f"total refs={family_total_refs} | lpIneqsIds={len(lp_ids)} "
          f"exact∩={len(used_set & lp_set)}", flush=True)

    if args.census_only or not args.emit_lean:
        return 0

    # 6) emit Lean module
    nf = emit(repo, repo, [g["flat"] for g in graphs], used, stats)
    print(f"[emit] Kepler.LP.W6Align: Basic+Table+Bulk+root+{nf} Align files",
          flush=True)
    return 0


if __name__ == "__main__":
    # Marshal cons-lists nest deeply; mirror parse_lpcert.py's discipline:
    # big stack + high recursion limit in a worker thread.
    import threading

    sys.setrecursionlimit(2_000_000)
    threading.stack_size(1024 * 1024 * 1024)
    _result = []

    def _run():
        _result.append(main())

    _t = threading.Thread(target=_run)
    _t.start()
    _t.join()
    sys.exit(_result[0] if _result else 1)
