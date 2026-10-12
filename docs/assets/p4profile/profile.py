#!/usr/bin/env python3
"""
Phase 4 92-prep 族成分画像 — 主画像脚本（v2）
输入（只读）：
  /tmp/p4wave1/ineqs_prep_ast.json                                   812 prep 记录（含 AST）
  /Users/zhangzhuo/repos/kepler-conjecture-lean4/pipeline/interval/out/defs.json
  /Users/zhangzhuo/repos/kepler-conjecture-lean4/pipeline/interval/out/residue16.txt
输出：
  /tmp/p4profile/profile_out/families.tsv        209 家族全表
  /tmp/p4profile/profile_out/records_classified.json  逐记录
  stdout：分布表 / 路由分配 / residue16 交叉 / R3 靶标清单
口径注记：
  * 五桶分类（任务口径，FormalVerifier.tex 支持集 sqrt/atn/acs/pi）：
      poly / ite / sqrt / atn-acs / mixed = 旗标集合并。
  * defs.json 已知截断残片（closure155.md 记录）按 nonlin_def.hl 原文打补丁：
      mud_*_x_v1 = mu_y · √(delta_*_x)              -> sqrt
      mudLs_*_x  = mu6_x · (有理式(δ_sub))          -> poly
      gamma3_x   = vol_x − vol3f_456 (√δ+sol/dih)   -> sqrt+atnacs+ite
      gamma23_full8_x / gamma23_keep135_x = gamma3_x + dih_x 组合 -> sqrt+atnacs+ite
  * 结构标注（路由相关）：
      inv_sqrtdelta : app 名含 div_sqrtdelta（1/√δ，δ 过零病灶，QZECFIC 型）
      gamma23       : gamma23_full8_x / gamma23_keep135_x / gamma3f_x_div_sqrtdelta
                      （TEWNSCJ/QZECFIC 病灶载体）
      mud_sqrt      : mud_*_x_v1（√δ_sub，"delta top issue" 族载体）
      sqrt_delta_num: vol_x / vol3_x_sqrt 等（√δ 仅在分子；BIX 实证 R2 可闭）
      sqrt_var      : √x 型（gchi*/eta2*/sqrt_x*；正底，TM-hull 可吸）
      disj          : 记录体含顶层析取 \\/（R2 域切分标记，BIX 型）
      nonstrict     : 含 <=（R4 角点候选）
  * 路由分配（静态画像口径，实验锚点）：
      R1 = poly（TADIAMB 实证）
      R3 = 命中 inv_sqrtdelta ∨ gamma23 ∨ mud_sqrt（δ 过零病灶；TEWNSCJ/QZECFIC 实证出局）
      R2 = 其余非 poly（BIX 实证：BB 切分 + ite-hull2 + TM 临界带可闭）
      R4 = 非严格 <= 角点（GRKIBMP B V2 手证先例；不占核时）
      灵敏度上界：√δ-num-only 记录若 R2 失败亦需 R3 兜底，单列。
"""
import json
import re
import os
from collections import Counter, defaultdict

PREP = "/tmp/p4wave1/ineqs_prep_ast.json"
DEFS = "/Users/zhangzhuo/repos/kepler-conjecture-lean4/pipeline/interval/out/defs.json"
RES16 = "/Users/zhangzhuo/repos/kepler-conjecture-lean4/pipeline/interval/out/residue16.txt"
OUTDIR = "/tmp/p4profile/profile_out"
os.makedirs(OUTDIR, exist_ok=True)

SQRT_P = {"sqrt"}; ATN_P = {"atn", "atn2", "acs"}; ITE_P = {"abs"}
OTH_P = {"asn", "sin", "cos", "tan", "ln", "log", "exp", "azim", "inv", "sgn", "dist", "norm"}

# ---- defs.json + 手工补丁（HOL 原文口径）----
defs_raw = json.load(open(DEFS))
defs = {k: v.get("body_ast") for k, v in defs_raw.items()}
PATCH_FLAGS = {
    "mud_135_x_v1": {"sqrt"}, "mud_126_x_v1": {"sqrt"}, "mud_234_x_v1": {"sqrt"},
    "mudLs_234_x": set(), "mudLs_126_x": set(), "mudLs_135_x": set(),
    "gamma3_x": {"sqrt", "atnacs", "ite"},
    "gamma23_full8_x": {"sqrt", "atnacs", "ite"},
    "gamma23_keep135_x": {"sqrt", "atnacs", "ite"},
}
def_flags = {}
def_unknown = {}
def _walk_def(name, body, stack=()):
    if name in def_flags:
        return def_flags[name], def_unknown[name]
    f, u = set(), set()
    if name in PATCH_FLAGS:
        f = set(PATCH_FLAGS[name])
    else:
        _walk(body, f, u, stack + (name,))
    def_flags[name] = frozenset(f); def_unknown[name] = frozenset(u)
    return def_flags[name], def_unknown[name]

def _walk(n, f, u, stack):
    if isinstance(n, dict):
        if "op" in n:
            for v in n.get("args", []): _walk(v, f, u, stack)
            return
        if "app" in n:
            name = n["app"]
            if name in defs:
                if name in stack:
                    pass  # 环：忽略
                else:
                    sf, su = _walk_def(name, defs[name], stack)
                    f.update(sf); u.update(su)
            elif name in SQRT_P: f.add("sqrt")
            elif name in ATN_P: f.add("atnacs")
            elif name in ITE_P: f.add("ite")
            elif name in OTH_P: f.add("otherf")
            else: u.add(name)
            for v in n.get("args", []): _walk(v, f, u, stack)
            return
        if "if" in n:
            f.add("ite")
            for k in ("if", "cond", "then", "else"):
                if k in n: _walk(n[k], f, u, stack)
            return
        if "let" in n:
            l = n["let"]; _walk(l.get("val"), f, u, stack); _walk(l.get("body"), f, u, stack)
            return
        for v in n.values(): _walk(v, f, u, stack)
        return
    if isinstance(n, list):
        for v in n: _walk(v, f, u, stack)

for _n, _b in defs.items():
    _walk_def(_n, _b)

# ---- 结构标注：按 app 名 ----
def app_names(node, acc):
    if isinstance(node, dict):
        if "app" in node: acc.add(node["app"])
        for v in node.values(): app_names(v, acc)
    elif isinstance(node, list):
        for v in node: app_names(v, acc)
    return acc

def has_op(node, op):
    if isinstance(node, dict):
        if node.get("op") == op: return True
        return any(has_op(v, op) for v in node.values())
    if isinstance(node, list):
        return any(has_op(v, op) for v in node)
    return False

INV_SQRTDELTA_RE = re.compile(r"div_sqrtdelta")
MUD_RE = re.compile(r"^mud_\d{3}_x_v1$")
GAMMA23 = {"gamma23_full8_x", "gamma23_keep135_x", "gamma3f_x_div_sqrtdelta"}
SQRT_DELTA_NUM = {"vol_x", "vol3_x_sqrt", "vol3f_x_sqrt2_lmplus", "vol3f_x_lfun"}
SQRT_VAR_HINT = ("gchi", "eta2_", "sqrt_x", "acs_sqrt", "arclength_x")

def structural(apps):
    s = set()
    if any(INV_SQRTDELTA_RE.search(a) for a in apps): s.add("inv_sqrtdelta")
    if apps & GAMMA23: s.add("gamma23")
    if any(MUD_RE.match(a) for a in apps): s.add("mud_sqrt")
    if apps & SQRT_DELTA_NUM: s.add("sqrt_delta_num")
    if any(a.startswith(p) for a in apps for p in SQRT_VAR_HINT): s.add("sqrt_var")
    return s

def classify(flags):
    core = flags & {"sqrt", "atnacs", "ite"}
    if not core: return "poly"
    if len(core) == 1:
        return {"sqrt": "sqrt", "atnacs": "atn-acs", "ite": "ite"}[next(iter(core))]
    return "mixed"

def route(cls, st):
    if "nonstrict" in st: return "R4"
    if cls == "poly": return "R1"
    if st & {"inv_sqrtdelta", "gamma23", "mud_sqrt"}: return "R3"
    return "R2"

def top_disj(n):
    """顶层 \\/ 布尔链的析取支数（1=无析取）"""
    if isinstance(n, dict) and n.get("op") == "\\/":
        return sum(top_disj(a) for a in n["args"])
    return 1

# ---- 逐记录 ----
recs = json.load(open(PREP))["records"]
out = []
for r in recs:
    fam = r["idv"][len("prep-"):].strip().split()[0]
    f, u = set(), set()
    _walk(r["body_ast"], f, u, ())
    apps = app_names(r["body_ast"], set())
    st = structural(apps)
    st_rec = set(st)
    if has_op(r["body_ast"], "\\/"): st_rec.add("disj")
    if has_op(r["body_ast"], "<="): st_rec.add("nonstrict")
    cls = classify(f)
    out.append({
        "idv": r["idv"], "family": fam, "line": r["line"],
        "class": cls, "flags": sorted(f), "struct": sorted(st_rec),
        "route": route(cls, st_rec),
        "disjuncts": top_disj(r["body_ast"]),
        "unknown_apps": sorted(u),
        "apps": sorted(a for a in apps if not a.startswith("proj_") and a not in ("unit6", "constant6", "scalar6", "compose6", "mk_456", "rotate4", "rotate5", "rotate6", "constant6", "delta_x", "rho_x", "delta_126_x", "delta_135_x", "delta_234_x", "delta_x4")),
        "nvars": len(r["bounds"]),
    })
json.dump(out, open(f"{OUTDIR}/records_classified.json", "w"), ensure_ascii=False, indent=1)

# ---- 家族聚合 ----
fam2recs = defaultdict(list)
for o in out: fam2recs[o["family"]].append(o)

# residue16 交叉（先于家族聚合，供 res16 标注）
res16_raw = [l.strip() for l in open(RES16) if l.strip() and not l.startswith("#")]
RES16_HITS = set()
res16_cross = []
for entry in res16_raw:
    base = entry.split()[0]
    hits = [f for f in fam2recs if f == base or f.split("-")[0] == base]
    RES16_HITS.update(hits)
    res16_cross.append((entry, hits))

fam_rows = []
for fam, rs in fam2recs.items():
    classes = Counter(r["class"] for r in rs)
    routes = Counter(r["route"] for r in rs)
    st_all = set().union(*[set(r["struct"]) for r in rs])
    flags_all = set().union(*[set(r["flags"]) for r in rs])
    # 纯 sqrt 族：所有记录核心旗标 ⊆ {sqrt} 且至少一条非 poly
    core_ok = all(set(r["flags"]) & {"sqrt", "atnacs", "ite"} <= {"sqrt"} for r in rs)
    pure_sqrt = core_ok and any(r["class"] != "poly" for r in rs)
    fam_rows.append({
        "family": fam, "n": len(rs),
        "classes": dict(classes), "routes": dict(routes),
        "flags": sorted(flags_all), "struct": sorted(st_all),
        "pure_sqrt": pure_sqrt,
        "res16": fam in RES16_HITS,
    })
fam_rows.sort(key=lambda x: (-x["n"], x["family"]))

# residue16 交叉
res16_raw = [l.strip() for l in open(RES16) if l.strip() and not l.startswith("#")]
RES16_HITS = set()
res16_cross = []
for entry in res16_raw:
    base = entry.split()[0]
    hits = [f for f in fam2recs if f == base or f.split("-")[0] == base]
    RES16_HITS.update(hits)
    res16_cross.append((entry, hits))
for fr in fam_rows:
    fr["res16"] = fr["family"] in RES16_HITS

json.dump(fam_rows, open(f"{OUTDIR}/families.json", "w"), ensure_ascii=False, indent=1)

# ---- 打印 ----
W = 100
print("=" * W)
print("① 全量分布（812 记录 / 209 家族）——任务口径五桶")
print("=" * W)
cc = Counter(o["class"] for o in out)
famclass = defaultdict(set)
for o in out: famclass[o["class"]].add(o["family"])
print(f"{'类别':10s} {'记录数':>6s} {'占比':>7s} {'家族数':>6s}  说明")
note = {
    "poly": "纯多项式/有理（R1，TADIAMB 口径）",
    "ite": "纯 ite/guard 无超越（空！ite 均与 sqrt+atn 并存于 mixed）",
    "sqrt": "仅 sqrt 无 atn/acs（正底 √x 或 √δ-num 型）",
    "atn-acs": "仅 atan/acos 无 sqrt（空！）",
    "mixed": "多类并存（sqrt+atn2(+ite) 为主流：dih/gchi/vol 形态）",
}
for k in ["poly", "ite", "sqrt", "atn-acs", "mixed"]:
    print(f"{k:10s} {cc.get(k,0):6d} {cc.get(k,0)/len(out)*100:6.1f}% {len(famclass[k]):6d}  {note.get(k,'')}")

print()
print("=" * W)
print("② 结构标注分布（路由相关；一条记录可多标）")
print("=" * W)
sc = Counter()
for o in out:
    for s in o["struct"]: sc[s] += 1
desc = {
    "inv_sqrtdelta": "1/√δ 型（δ 过零病灶，QZECFIC 实证 TM 出局）",
    "gamma23": "gamma23_full8/keep135/gamma3f_div_sqrtdelta（TEWNSCJ/QZECFIC 病灶）",
    "mud_sqrt": "mud_*_v1 = mu·√δ_sub（delta-top-issue 族）",
    "sqrt_delta_num": "√δ 仅分子（vol_x 型；BIX 实证 R2 可闭）",
    "sqrt_var": "√x 型（gchi/eta2/sqrt_x；正底）",
    "disj": "顶层析取 \\/（R2 域切分标记）",
    "nonstrict": "含 <= 非严格（R4 角点候选）",
}
for k, v in sc.most_common():
    print(f"{k:16s} {v:5d} ({v/len(out)*100:5.1f}%)  {desc.get(k,'')}")

print()
print("=" * W)
print("③ 路由分配预估（静态画像口径；核时为 M3 Pro 单核标定外推）")
print("=" * W)
rc = Counter(o["route"] for o in out)
n = len(out)
print(f"{'路由':4s} {'记录':>5s} {'占比':>7s}  武器                                     估时口径")
est = {
    "R1": ("TM（TADIAMB 251k 叶 100% @101.2s）", "10-101.2s/件"),
    "R2": ("BB 域切分 + ite-hull2 + TM 临界带（BIX split 49,869 叶 @86.7s / TM @142.4s / 裸 54.8s）", "55-142.4s/切分件"),
    "R3": ("第三武器（未建）：radicand 零等值面预切分 / t=√u 换元", "87-142s/TM 件 × radicand 域因子 2-8（纯外推）"),
    "R4": ("手证（GRKIBMP B V2 角点四段先例）", "0 核时（人工）"),
}
for k in ["R1", "R2", "R3", "R4"]:
    print(f"{k}: {rc.get(k,0):4d} ({rc.get(k,0)/n*100:5.1f}%)  {est[k][0]}\n     估时口径: {est[k][1]}")
print()
pieces = {k: sum(o["disjuncts"] for o in out if o["route"] == k) for k in ["R1", "R2", "R3"]}
print(f"切分件数（按顶层析取支数）: R1={pieces['R1']}  R2={pieces['R2']}  R3={pieces['R3']}")
lo = {"R1": 10, "R2": 55}; hi = {"R1": 101.2, "R2": 142.4}
for k in ["R1", "R2"]:
    print(f"{k} 核时: {pieces[k]}件 × [{lo[k]},{hi[k]}]s = {pieces[k]*lo[k]/3600:.1f} - {pieces[k]*hi[k]/3600:.1f} core-h")
r3_dom_lo, r3_dom_hi = 2, 8
print(f"R3 核时(未建武器外推): {pieces['R3']}件 × {r3_dom_lo}-{r3_dom_hi} radicand 域 × [87,142.4]s = "
      f"{pieces['R3']*r3_dom_lo*87/3600:.0f} - {pieces['R3']*r3_dom_hi*142.4/3600:.0f} core-h（不含 W4-W5 R&D 工程成本）")
r23 = rc.get("R3", 0)
print()
print(f"R3 严格占比: {r23/n*100:.1f}% ({r23}/{n})  <5% 降级线 = {0.05*n:.0f} 条")
sdn = sum(1 for o in out if "sqrt_delta_num" in o["struct"] and o["route"] == "R2")
print(f"灵敏度上界: R2 中 √δ-num-only {sdn} 条若 ite-hull2 失效需 R3 兜底 -> R3 上界 {(r23+sdn)/n*100:.1f}%")
# R3 实证/疑似分组
EVID = {"TEWNSCJ", "QZECFIC", "7550003505"}
r3 = [o for o in out if o["route"] == "R3"]
r3e = [o for o in r3 if o["family"] in EVID]; r3s = [o for o in r3 if o["family"] not in EVID]
print(f"R3 分组: 实证组（TEWNSCJ/QZECFIC W2 实测 radicand 病 + 7550003505 delta-top 构造性 δ→0）= {len(r3e)} 条/3 家族；"
      f"疑似组（gamma23 携带但 W2 病症为 guard 主导或未实测）= {len(r3s)} 条/{len(set(o['family'] for o in r3s))} 家族")
print("疑似组家族:", ",".join(sorted(set(o["family"] for o in r3s))))
print("注: IXPOTPA/PEMKWKU/TXQTPVC 的 W2 TM invalid 主因=guard跨0（IXPOTPA TM 全 valid）-> 建议先走 R2 武器实测再升级 R3")

print()
print("=" * W)
print("④ residue16 交叉（16 条真残余的 prep 族邻居：同族大概率同病）")
print("=" * W)
for entry, hits in res16_cross:
    detail = []
    for h in hits:
        rs = fam2recs[h]
        cl = Counter(r["class"] for r in rs)
        rt = Counter(r["route"] for r in rs)
        detail.append(f"{h}(n={len(rs)},{dict(cl)},路由{dict(rt)})")
    print(f"{entry:24s} -> {'; '.join(detail) if detail else '（无同名 prep 族）'}")

print()
print("=" * W)
print("⑤ R3 第三武器（W4）靶标清单 —— 命中 δ 过零载体（inv_sqrtdelta ∨ gamma23 ∨ mud_sqrt）的家族")
print("=" * W)
r3_fams = [fr for fr in fam_rows if fr["routes"].get("R3")]
print(f"{'家族':22s} {'n':>3s}  classes                      结构标注")
for fr in sorted(r3_fams, key=lambda x: -x["n"]):
    print(f"{fr['family']:22s} {fr['n']:3d}  {str(fr['classes']):28s} {','.join(fr['struct'])}")
print(f"\n合计: {len(r3_fams)} 家族 / {sum(f['n'] for f in r3_fams)} 记录")

print()
print("=" * W)
print("⑥ 纯 sqrt 族（全记录核心旗标 ⊆ {sqrt}，无 atn/acs）——第三武器换元直用型")
print("=" * W)
ps = [fr for fr in fam_rows if fr["pure_sqrt"]]
for fr in sorted(ps, key=lambda x: -x["n"]):
    print(f"{fr['family']:22s} n={fr['n']:3d}  routes={fr['routes']}  struct={','.join(fr['struct'])}")
print(f"合计: {len(ps)} 家族 / {sum(f['n'] for f in ps)} 记录")

print()
print("=" * W)
print("⑦ 209 家族全表（前 40 行；全量见 families.tsv）")
print("=" * W)
print(f"{'家族':22s} {'n':>4s}  classes                              route分布            结构标注")
for fr in fam_rows[:40]:
    print(f"{fr['family']:22s} {fr['n']:4d}  {str(fr['classes']):36s} {str(fr['routes']):18s} {','.join(fr['struct'])}")

# TSV 全量
with open(f"{OUTDIR}/families.tsv", "w") as fh:
    fh.write("family\tn\tclasses\troutes\tflags\tstruct\tpure_sqrt\tres16\n")
    for fr in fam_rows:
        fh.write(f"{fr['family']}\t{fr['n']}\t{json.dumps(fr['classes'])}\t{json.dumps(fr['routes'])}\t{','.join(fr['flags'])}\t{','.join(fr['struct'])}\t{fr['pure_sqrt']}\t{fr['res16']}\n")

# 未解析 app 汇总
un = Counter()
for o in out:
    for a in o["unknown_apps"]: un[a] += 1
if un:
    print()
    print("未解析 app（展开遇到，旗标可能低估）:", dict(un.most_common()))
