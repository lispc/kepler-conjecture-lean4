#!/bin/bash
# =============================================================================
# 549 全量重演管线 v1 —— run_full.sh（single 类生产验证片 → 全量 launch 编排）
#
# 三阶段流水（每 shard 20 叶）：
#   [0] manifest  tight 证书普查池 → master manifest（叶盒+params 槽位+类标）
#   [1] select    --class/--start/--count/--stride 抽叶 → shard 分配
#   [2] stagea    stage-A 批探针，rung 阶梯轮次（128→512→2048；回退叶全部层
#                 在新 rung 重证、旧轮行作废——与 cmd_batch 轮次语义一致）
#   [3] merge     终态收敛：逐叶 PASS/FAIL+分层归因+params 回填 →
#                 final/{der,cert,face,full}.jsonl（emit 直读，rung 一致性过滤）
#   [4] locheck   done@128 抽样 vs 2048 口径对账（verdict 翻转+loBound 指数）；
#                 flagged 叶保守排除（重触发 merge）
#   [5] emit      shard 出题 → namespace 重命名 C549ProdS{NNNN} → Cases/
#   [6] build     逐模块 `lake build Kepler.Interval.Cases.<M>`（≤JOBS 路；
#                 exit0 + 零裸 error + 零 sorryAx ⇒ shard PASS）
#   [7] report    slice_report.json + 吞吐/磁盘外推
#
# 断点续跑：一切产物按 shard/stage 落盘、校验后复用；重跑只处理 pending。
# 状态词汇：叶 pending/probe/PASS/FAIL；shard pending/probe/emitted/built/PASS/FAIL
#           （status.jsonl 每 shard 一行，原子重写）。
#
# 用法：
#   run_full.sh --class=single --start=0 --count=1000 --jobs=12 \
#               [--a-jobs=16] [--stride=0(auto)] [--shard=20] [--tag=val]
#               [--case=...] [--cert=...] [--pool=...] [--work=...]
#               [--phases=manifest,select,stagea,merge,locheck,emit,build,report]
#               [--locheck-n=60] [--no-native]
# 纪律：nice -19；stage-A ≤16 路 lean；decide 构建 ≤12 路；栈无限；不做 git。
# =============================================================================
set -u
export PATH="$HOME/.elan/bin:$PATH"
ulimit -s unlimited
REPO=/home/scroll/repos/kepler-conjecture-lean4
INT=$REPO/pipeline/interval
CASE=$INT/out/cases/5490182221.json
CERT=/tmp/opencode/probe549/cert549_tight.json
POOL=/tmp/opencode/mv/census_full.jsonl
CLASS=single; START=0; COUNT=0; STRIDE=0; JOBS=12; AJOBS=16; SHARD=20
TAG=val; WORK=""; WORK_GIVEN=0
PHASES=manifest,select,stagea,merge,locheck,emit,build,report
LOCHECK_N=60; NATIVE=1
GRAN=-80; RUNG_OUT=-80; RUNGS="128 512 2048"
export WORK REPO

for a in "$@"; do
  case "$a" in
    --class=*) CLASS="${a#*=}";; --start=*) START="${a#*=}";;
    --count=*) COUNT="${a#*=}";; --stride=*) STRIDE="${a#*=}";;
    --jobs=*) JOBS="${a#*=}";; --a-jobs=*) AJOBS="${a#*=}";;
    --shard=*) SHARD="${a#*=}";; --tag=*) TAG="${a#*=}";;
    --case=*) CASE="${a#*=}";; --cert=*) CERT="${a#*=}";; --pool=*) POOL="${a#*=}";;
    --work=*) WORK="${a#*=}"; WORK_GIVEN=1;; --phases=*) PHASES="${a#*=}";;
    --locheck-n=*) LOCHECK_N="${a#*=}";; --no-native) NATIVE=0;;
    *) echo "unknown arg $a" >&2; exit 2;;
  esac
done
[ -n "$WORK" ] || WORK=$INT/out/prod549/$TAG
export CASE CERT
mkdir -p "$WORK/shards" "$WORK/locheck" "$WORK/builds"
: > "$WORK/taskfails.log"
echo "$(date +%F' '%T) run_full start tag=$TAG class=$CLASS start=$START count=$COUNT stride=$STRIDE shard=$SHARD jobs=$JOBS ajobs=$AJOBS work=$WORK"

phase_mark() { python3 - "$WORK/phase_timings.json" "$1" <<'PY'
import json,sys,time
p,t=sys.argv[1],sys.argv[2]
try: d=json.load(open(p))
except Exception: d={}
d.setdefault(t,[]).append(round(time.time(),1))
json.dump(d,open(p,"w"))
PY
}
has_phase() { case ",$PHASES," in *",$1,"*) return 0;; *) return 1;; esac; }

# ---------- [0] manifest ----------
phase_manifest() {
  [ -s "$WORK/master.manifest.jsonl" ] && { echo "manifest: exists, skip"; return 0; }
  python3 - "$POOL" "$CERT" "$WORK/master.manifest.jsonl" <<'PY'
import json,os,sys
pool,cert,out=sys.argv[1:4]
rows=[json.loads(l) for l in open(pool) if l.strip()]
meta,body=rows[0],rows[1:]
if os.path.realpath(meta.get("cert","")) != os.path.realpath(cert):
    sys.exit(f"pool {pool} cert mismatch ({meta.get('cert')} != {cert}) — 需以 tight 证书重跑 emit_mono.py boxes 生成普查池")
nc={"single":0,"straddle":0}
tmp=out+".tmp"
with open(tmp,"w") as f:
    m=dict(meta); m.update(schema="manifest549", pool=pool)
    f.write(json.dumps(m)+"\n")
    for r in body:
        cls="single" if r.get("mode") in ("then","else") else "straddle"
        nc[cls]+=1
        f.write(json.dumps(dict(idx=r["idx"], mode=r["mode"], cls=cls,
                                box=r["box"], status="pending", params=None))+"\n")
    m["cls_counts"]=nc
os.replace(tmp,out)
print(f"manifest: total {len(body)} = single {nc['single']} + straddle {nc['straddle']} -> {out}")
PY
}

# ---------- [1] select ----------
phase_select() {
  [ -s "$WORK/selection.jsonl" ] && { echo "select: exists, skip"; return 0; }
  python3 - "$WORK" "$CLASS" "$START" "$COUNT" "$STRIDE" "$SHARD" <<'PY'
import json,os,sys
work,cls,start,count,stride,shard=sys.argv[1:7]
start,count,stride,shard=int(start),int(count),int(stride),int(shard)
rows=[json.loads(l) for l in open(f"{work}/master.manifest.jsonl") if l.strip()]
meta,body=rows[0],rows[1:]
pool=[r for r in body if r["cls"]==cls or cls=="all"]
if stride<=0: stride=max(1,len(pool)//count) if count>0 else 1
sel=[pool[i] for i in range(start,len(pool),stride)]
if count>0: sel=sel[:count]
os.makedirs(f"{work}/shards",exist_ok=True)
nsh=max(1,-(-len(sel)//shard)) if sel else 0
sm=dict(schema="selection549",cls=cls,start=start,count=count,stride=stride,
        pool_size=len(pool),selected=len(sel),shards=nsh,shard_size=shard,
        master=f"{work}/master.manifest.jsonl")
with open(f"{work}/selection.jsonl","w") as f:
    f.write(json.dumps(sm)+"\n")
    for i,r in enumerate(sel):
        r["shard"]=i//shard+1; r["pool_pos"]=i
        f.write(json.dumps(r)+"\n")
bysh={}
for r in sel: bysh.setdefault(r["shard"],[]).append(r)
for k,rs in sorted(bysh.items()):
    d=f"{work}/shards/S{k}"; os.makedirs(d,exist_ok=True)
    with open(f"{d}/census_r128.jsonl","w") as f:
        f.write(json.dumps(dict(meta,sampled=len(rs),shard=k,note="round-128 工作集"))+"\n")
        for r in rs:
            f.write(json.dumps(dict(idx=r["idx"],cidx=r["idx"],mode=r["mode"],
                                    box=r["box"]))+"\n")
print(f"select: pool {len(pool)} stride {stride} start {start} -> {len(sel)} leaves, {nsh} shards")
PY
}

# ---------- stage-A 任务队列 ----------
validate_task() { # stage census out derdir|-
  [ -s "$3" ] || return 1
  python3 - "$1" "$2" "$3" "$4" <<'PY'
import json,sys
stage,cz,out,dd=sys.argv[1:5]
ls=[l for l in open(out) if l.strip()]
m=json.loads(ls[0]); assert str(m.get("schema","")).startswith("probe549")
rows=[json.loads(l) for l in ls[1:]]
assert rows and all(isinstance(r.get("idx"),int) for r in rows)
ws={json.loads(l)["idx"] for l in open(cz).readlines()[1:] if l.strip()}
got={}
for r in rows: got.setdefault(r["idx"],[]).append(r)
if stage in ("der","cert","full"):
    want=1 if stage!="der" else 1
    for i in ws:
        assert len(got.get(i,[]))>=want, f"missing rows idx {i}"
elif stage=="face":
    ddi={json.loads(l)["idx"] for l in open(dd) if l.strip()} if dd!="-" else set()
    for i in (ddi & ws):
        assert i in got, f"missing face row idx {i}"
PY
}
task_one() { # k stage rung census out derdir|-
  local k=$1 stage=$2 rung=$3 cz=$4 out=$5 dd=${6:--}
  validate_task "$stage" "$cz" "$out" "$dd" && return 0
  local extra=""; [ "$dd" != "-" ] && extra="--der=$dd"
  local route=""; [ "$stage" = "cert" ] && route="--route=interval"
  local att
  for att in 1 2; do
    (cd "$INT" && nice -n 19 python3 emit_mono.py probe "$CASE" "$cz" "$stage" \
        --rung="$rung" --rung-out=$RUNG_OUT --gran=$GRAN $route $extra \
        --out="$out" --tag=g"$k" > "$out.log" 2>&1) && validate_task "$stage" "$cz" "$out" "$dd" && return 0
    sleep 2
  done
  echo "$(date +%T) TASKFAIL k=$k stage=$stage rung=$rung out=$out" >> "$WORK/taskfails.log"; return 1
}
run_queue() { # $1=tasks  $2=par
  [ -s "$1" ] || { echo "queue empty: $1"; return 0; }
  local n=0 line
  while read -r line; do
    [ -z "$line" ] && continue
    task_one $line &
    n=$((n+1)); [ $((n % $2)) -eq 0 ] && wait -n
  done < "$1"
  wait
}

# ---------- [2] stagea（rung 阶梯轮次） ----------
phase_stagea() {
  local R
  # 派生态工作集清空重算（自愈：判定行 jsonl 保留复用，仅 census_r{512,2048} 重生成）
  find "$WORK/shards" -name "census_r512.jsonl" -delete 2>/dev/null
  find "$WORK/shards" -name "census_r2048.jsonl" -delete 2>/dev/null
  for R in $RUNGS; do
    python3 - "$WORK" "$R" der <<'PY'
import json,os,sys
work,rung,stage=sys.argv[1],sys.argv[2],sys.argv[3]
out=[]
for s in sorted(os.listdir(f"{work}/shards")):
    cz=f"{work}/shards/{s}/census_r{rung}.jsonl"
    if not os.path.exists(cz): continue
    nrow=max(0,len(open(cz).readlines())-1)
    if nrow==0: continue
    o=f"{work}/shards/{s}/r{rung}_{stage}.jsonl"
    out.append(f"{s[1:]} {stage} {rung} {cz} {o} -")
open(f"{work}/tasks.txt","w").write("\n".join(out)+"\n")
print(f"stagea r{rung} {stage}: {len(out)} shard-tasks")
PY
    run_queue "$WORK/tasks.txt" "$AJOBS"
    python3 - "$WORK" "$R" <<'PY'
import json,os,sys
work,rung=sys.argv[1],sys.argv[2]
def rd(p):
    if not os.path.exists(p): return []
    return [json.loads(l) for l in open(p) if l.strip()][1:]
tasks=[]
for s in sorted(os.listdir(f"{work}/shards")):
    d=f"{work}/shards/{s}"
    cz=f"{d}/census_r{rung}.jsonl"
    if not os.path.exists(cz): continue
    ws=[json.loads(l) for l in open(cz) if l.strip()][1:]
    der=rd(f"{d}/r{rung}_der.jsonl")
    dpass={}
    for r in der:
        if r["v"]=="PASS": dpass.setdefault(r["idx"],set()).add(r["dir"])
    dpass={i:("lo" if "lo" in v else "hi") for i,v in dpass.items()}
    with open(f"{d}/r{rung}_derdir.jsonl","w") as f:
        for i,v in sorted(dpass.items()):
            f.write(json.dumps(dict(idx=i,dir=v,v="PASS"))+"\n")
    if dpass:
        tasks.append(f"{s[1:]} face {rung} {cz} {d}/r{rung}_face.jsonl {d}/r{rung}_derdir.jsonl")
    tasks.append(f"{s[1:]} cert {rung} {cz} {d}/r{rung}_cert.jsonl -")
    tasks.append(f"{s[1:]} full {rung} {cz} {d}/r{rung}_full.jsonl -")
    print(f"stagea {s} r{rung}: workset {len(ws)} der_pass {len(dpass)}",file=sys.stderr)
open(f"{work}/tasks.txt","w").write("\n".join(tasks)+"\n")
PY
    # face 波（依赖本轮 der 方向）
    run_queue "$WORK/tasks.txt" "$AJOBS"
    # 轮次收敛：不完备叶 → 下一 rung 工作集；末轮不再下发
    python3 - "$WORK" "$R" <<'PY'
import json,os,sys
work,rung=sys.argv[1],sys.argv[2]
NXT={"128":"512","512":"2048","2048":None}[rung]
def rd(p):
    if not os.path.exists(p): return []
    return [json.loads(l) for l in open(p) if l.strip()][1:]
for s in sorted(os.listdir(f"{work}/shards")):
    d=f"{work}/shards/{s}"
    cz=f"{d}/census_r{rung}.jsonl"
    if not os.path.exists(cz): continue
    ws=[json.loads(l) for l in open(cz) if l.strip()][1:]
    der=rd(f"{d}/r{rung}_der.jsonl"); cert=rd(f"{d}/r{rung}_cert.jsonl")
    face=rd(f"{d}/r{rung}_face.jsonl")
    dpass={i for i in {r["idx"] for r in der} if any(x["v"]=="PASS" and x["idx"]==i for x in der)}
    call={}
    for r in cert: call.setdefault(r["idx"],[]).append(r["v"]=="PASS")
    fpass={r["idx"] for r in face if r["v"]=="PASS"}
    nxt=[r for r in ws if not (r["idx"] in dpass and call.get(r["idx"]) and all(call[r["idx"]]) and r["idx"] in fpass)]
    if NXT:
        ncz=f"{d}/census_r{NXT}.jsonl"
        if nxt:
            meta=[json.loads(l) for l in open(cz) if l.strip()][0]
            with open(ncz,"w") as f:
                f.write(json.dumps(dict(meta,sampled=len(nxt),note=f"回退轮 rung {NXT} 工作集"))+"\n")
                for r in nxt: f.write(json.dumps(r)+"\n")
        elif os.path.exists(ncz):
            os.remove(ncz)
    print(f"stagea {s} r{rung}: workset {len(ws)} complete {len(ws)-len(nxt)} pending {len(nxt)}")
PY
  done
}

# ---------- [3] merge（终态收敛 + final 判定文件 + manifest 回填） ----------
phase_merge() {
  python3 - "$WORK" <<'PY'
import json,os,sys
work=sys.argv[1]
def rd(p):
    if not os.path.exists(p): return []
    return [json.loads(l) for l in open(p) if l.strip()][1:]
stages=("der","cert","face","full")
tot=dict(sel=0,passn=0,fail=0)
for s in sorted(os.listdir(f"{work}/shards")):
    d=f"{work}/shards/{s}"
    if not os.path.exists(f"{d}/census_r128.jsonl"): continue
    ws=[json.loads(l) for l in open(f"{d}/census_r128.jsonl") if l.strip()][1:]
    idxs=[r["idx"] for r in ws]
    allr={st:{} for st in stages}
    for st in stages:
        for rung in ("128","512","2048"):
            for r in rd(f"{d}/r{rung}_{st}.jsonl"):
                allr[st].setdefault(r["idx"],[]).append(r)
    fl=f"{d}/leafstate.json"
    st=json.load(open(fl)) if os.path.exists(fl) else {}
    # locheck flagged 集（重跑 merge 时保持排除；final 文件同步剔除）
    flagged=set()
    lc=f"{work}/locheck/locheck_report.json"
    if os.path.exists(lc):
        flagged=set(json.load(open(lc)).get("flagged",[]))
    for i in idxs:
        v=st.get(i)
        fr=str(v["rung"]) if (v and v["state"]=="pass") else None
        if fr is None:
            rgs=[int(r.get("rung",128)) for g in allr.values() for r in g.get(i,[])]
            fr=str(max(rgs) if rgs else 128)
        finals={st2:[r for r in allr[st2].get(i,[]) if str(r.get("rung",128))==fr]
                for st2 in stages}
        if not (v and v["state"]=="pass"):
            der_ok=any(r["v"]=="PASS" for r in finals["der"])
            cert_ok=bool(finals["cert"]) and all(r["v"]=="PASS" for r in finals["cert"])
            face_ok=any(r["v"]=="PASS" for r in finals["face"])
            if der_ok and cert_ok and face_ok:
                dl="lo" if any(r.get("dir")=="lo" and r["v"]=="PASS" for r in finals["der"]) else "hi"
                st[i]=dict(state="pass",rung=int(fr),dir=dl)
            else:
                layer="der" if not der_ok else ("face" if not face_ok else "cert")
                st[i]=dict(state="fail",layer=layer,rung=int(fr),
                           der=der_ok,cert=cert_ok,face=face_ok)
            v=st[i]
        # params 槽位（终 rung 判定行；pass 叶才填三叶证书）
        pr=v.get("params") or {}
        drs=[r for r in finals["der"] if r["v"]=="PASS"]
        if drs and "der" not in pr:
            pick=[r for r in drs if r.get("dir")==v.get("dir","lo")] or drs
            pr["der"]=pick[0].get("trip")
        fcs=[r for r in finals["face"] if r["v"]=="PASS"]
        if fcs and "face" not in pr: pr["face"]=fcs[0].get("trip")
        if finals["cert"] and "cert" not in pr:
            byci={}
            for r in finals["cert"]:
                if r["v"]=="PASS": byci.setdefault(r["ci"],[]).append(r)
            if byci: pr["cert"]=[byci[c][0].get("trip") for c in sorted(byci)]
        frl=finals["full"]
        if frl: pr["full"]=dict(v=frl[0]["v"],trip=frl[0].get("trip"))
        v["params"]=pr
    # locheck flagged 保守排除（重跑 merge 时保持）
    for i in flagged:
        if i in st and st[i].get("state")=="pass":
            st[i]=dict(state="fail",layer="locheck",rung=st[i]["rung"],
                       reason="locheck flagged（保守排除）")
    # final 判定文件（逐叶终 rung 行；emit 直读；flagged 叶剔除）
    for st2 in stages:
        with open(f"{d}/final_{st2}.jsonl","w") as f:
            f.write(json.dumps(dict(schema=f"probe549-{st2}",shard=s,
                                    note="终轮判定行（逐叶 rung 一致性过滤）"))+"\n")
            for i in idxs:
                if i in flagged: continue
                fr=str(st[i]["rung"])
                for r in allr[st2].get(i,[]):
                    if str(r.get("rung",128))==fr: f.write(json.dumps(r)+"\n")
    json.dump(st,open(fl,"w"))
    npass=sum(1 for i in idxs if st[i]["state"]=="pass")
    tot["sel"]+=len(idxs); tot["passn"]+=npass; tot["fail"]+=len(idxs)-npass
    if not os.path.exists(f"{d}/shardstate"):
        open(f"{d}/shardstate","w").write("probe\n")
print(f"merge: selected {tot['sel']} PASS {tot['passn']} ({tot['passn']/max(1,tot['sel']):.1%}) FAIL {tot['fail']}")
PY
  python3 - "$WORK" <<'PY'
import json,os,sys
work=sys.argv[1]
st={}
for s in sorted(os.listdir(f"{work}/shards")):
    fl=f"{work}/shards/{s}/leafstate.json"
    if os.path.exists(fl):
        for i,v in json.load(open(fl)).items(): st[int(i)]=v
src=f"{work}/master.manifest.jsonl"; tmp=src+".tmp"
with open(src) as f, open(tmp,"w") as g:
    g.write(f.readline())
    for ln in f:
        r=json.loads(ln); v=st.get(r["idx"])
        if v: r["status"]=v["state"]; r["params"]=v.get("params")
        g.write(json.dumps(r)+"\n")
os.replace(tmp,src)
print(f"manifest: {len(st)} leaf statuses backfilled")
PY
}

# ---------- [4] locheck（done@128 抽样 vs 2048 口径） ----------
phase_locheck() {
  [ -s "$WORK/locheck/locheck_report.json" ] && { echo "locheck: exists, skip"; return 0; }
  python3 - "$WORK" "$LOCHECK_N" <<'PY'
import json,os,sys
work,n=sys.argv[1],int(sys.argv[2])
done128=[]
for s in sorted(os.listdir(f"{work}/shards")):
    ls=f"{work}/shards/{s}/leafstate.json"
    if not os.path.exists(ls): continue
    for i,v in json.load(open(ls)).items():
        if v.get("state")=="pass" and v.get("rung")==128:
            done128.append((int(i),f"{work}/shards/{s}"))
if not done128:
    print("locheck: no done@128 leaves"); sys.exit(0)
step=max(1,len(done128)//max(1,n)); sample=done128[::step][:n]
selr=[json.loads(l) for l in open(f"{work}/selection.jsonl") if l.strip()]
smeta=selr[0]; sels={r["idx"]:r for r in selr[1:]}
srows=[sels[i] for i,_ in sample if i in sels]
# meta 取 shard census（携带 j/counts——probe/emit 依赖）
cmeta=None
for i,sh in sample:
    cz=f"{sh}/census_r128.jsonl"
    if os.path.exists(cz):
        cmeta=json.loads(open(cz).readline()); break
if cmeta is None:
    print("locheck: no census meta found"); sys.exit(1)
with open(f"{work}/locheck/census_locheck.jsonl","w") as f:
    f.write(json.dumps(dict(cmeta,sampled=len(srows),note="locheck 抽样"))+"\n")
    for r in srows:
        f.write(json.dumps(dict(idx=r["idx"],cidx=r["idx"],mode=r["mode"],box=r["box"]))+"\n")
dd=[]
for i,sh in sample:
    fp=f"{sh}/final_der.jsonl"
    if not os.path.exists(fp): continue
    for r in [json.loads(l) for l in open(fp) if l.strip()][1:]:
        if r["idx"]==i and r["v"]=="PASS":
            dd.append(dict(idx=i,dir=r["dir"],v="PASS")); break
with open(f"{work}/locheck/derdir.jsonl","w") as f:
    for r in dd: f.write(json.dumps(r)+"\n")
json.dump(dict(sample=[i for i,_ in sample]),open(f"{work}/locheck/sample.json","w"))
print(f"locheck: sample {len(srows)} -> 2048 face re-probe")
PY
  [ -s "$WORK/locheck/census_locheck.jsonl" ] || return 0
  python3 - "$WORK" <<'PY'
import json,os,sys
work=sys.argv[1]
ls=[l for l in open(f"{work}/locheck/census_locheck.jsonl") if l.strip()]
meta,rows=ls[0],ls[1:]
q=-(-len(rows)//6)
tasks=[]
for p in range(6):
    ch=rows[p*q:(p+1)*q]
    if not ch: continue
    fp=f"{work}/locheck/census_part{p}.jsonl"
    with open(fp,"w") as f:
        f.write(json.dumps(dict(json.loads(meta),note=f"locheck part{p}"))+"\n")
        f.writelines(ch)
    tasks.append(f"0 face 2048 {fp} {work}/locheck/r2048_face_{p}.jsonl {work}/locheck/derdir.jsonl")
open(f"{work}/tasks.txt","w").write("\n".join(tasks)+"\n")
PY
  run_queue "$WORK/tasks.txt" "$AJOBS"
  python3 - "$WORK" <<'PY'
import json,os,sys
work=sys.argv[1]
ls=[l for l in open(f"{work}/locheck/census_locheck.jsonl") if l.strip()]
rows={json.loads(l)["idx"] for l in ls[1:]}
chk={}
for p in range(6):
    fp=f"{work}/locheck/r2048_face_{p}.jsonl"
    if os.path.exists(fp):
        for r in [json.loads(l) for l in open(fp) if l.strip()][1:]: chk[r["idx"]]=r
ref={}
for s in sorted(os.listdir(f"{work}/shards")):
    fp=f"{work}/shards/{s}/final_face.jsonl"
    if os.path.exists(fp):
        for r in [json.loads(l) for l in open(fp) if l.strip()][1:]:
            if r["idx"] in rows: ref[r["idx"]]=r
flips=[];ebad=[];mbad=[]
for i,c in sorted(chk.items()):
    b=ref.get(i)
    if b is None: continue
    if (b["v"]=="PASS")!=(c["v"]=="PASS"):
        flips.append(i)
    elif b["v"]=="PASS":
        # lb 漂移（两 rung 均为内核精确验证的 sound 下界，序不固定）→ 信息性
        if b.get("lb_e")!=c.get("lb_e"): ebad.append(i)
        elif b.get("lb_m")!=c.get("lb_m"): mbad.append(i)
rep=dict(schema="locheck549",sample=len(chk),base_rung=128,check_rung=2048,
         flips=flips,lb_e_mismatch=ebad,lb_m_mismatch=mbad,
         suspect=[],flagged=sorted(set(flips)),
         criterion="flag = verdict flip only（两 rung 下界均 sound，lb 漂移为信息性）")
json.dump(rep,open(f"{work}/locheck/locheck_report.json","w"),indent=1)
print(f"locheck: sample {len(chk)} flips {len(flips)} suspect {len(suspect)} lb_e漂移 {len(ebad)} lb_m漂移 {len(mbad)} flagged {len(rep['flagged'])}")
if len(chk)==0:
    sys.exit("locheck: 2048 对账探针零回传（任务失败，禁止视为通过）")
PY
  # flagged → 保守排除后重收敛
  if python3 -c "import json,sys; sys.exit(0 if json.load(open('$WORK/locheck/locheck_report.json'))['flagged'] else 1)" 2>/dev/null; then
    echo "locheck: flagged > 0 — 重触发 merge（保守排除）"
    phase_merge
  fi
}

# ---------- [5] emit ----------
phase_emit() {
  python3 - "$WORK" "$NATIVE" <<'PY' > "$WORK/emit_tasks.txt"
import json,os,sys
work,native=sys.argv[1],int(sys.argv[2])
for s in sorted(os.listdir(f"{work}/shards"),key=lambda x:int(x[1:])):
    d=f"{work}/shards/{s}"; k=int(s[1:])
    if not os.path.exists(f"{d}/leafstate.json"): continue
    st=json.load(open(f"{d}/leafstate.json"))
    npass=sum(1 for v in st.values() if v["state"]=="pass")
    if npass==0: continue
    print(f"{k} {npass} {native if k==1 else 0}")
PY
  local k npass native d nsb mod
  while read -r k npass native; do
    d="$WORK/shards/S$k"
    mod=$(printf "C549ProdS%04d" "$k")
    [ -f "$REPO/lean/Kepler/Interval/Cases/${mod}.lean" ] && { echo "emit S$k: exists, skip"; continue; }
    nsb="${mod}T"
    mkdir -p "$d/em"
    (cd "$INT" && nice -n 19 python3 emit_mono.py emit "$CASE" "$d/census_r128.jsonl" \
        --der="$d/final_der.jsonl" --face="$d/final_face.jsonl" --cert="$d/final_cert.jsonl" \
        --full="$d/final_full.jsonl" --out-dir="$d/em" --shard=$SHARD \
        --cert-route=interval --ns-prefix="$nsb" > "$d/emit.log" 2>&1) || \
      { echo "emit S$k FAILED"; echo "$(date +%T) EMITFAIL $k" >> "$WORK/taskfails.log"; continue; }
    sed "s/${nsb}1/${mod}/g" "$d/em/${nsb}1.lean" > "$REPO/lean/Kepler/Interval/Cases/${mod}.lean"
    [ -f "$d/em/${nsb}.manifest.json" ] && mv "$d/em/${nsb}.manifest.json" "$d/${mod}.manifest.json"
    [ -f "$d/em/${nsb}.emitstats.json" ] && mv "$d/em/${nsb}.emitstats.json" "$d/${mod}.emitstats.json"
    echo "$mod $k $npass main" >> "$WORK/modules.txt"
    if [ "$native" = "1" ]; then
      (cd "$INT" && nice -n 19 python3 emit_mono.py emit "$CASE" "$d/census_r128.jsonl" \
          --der="$d/final_der.jsonl" --face="$d/final_face.jsonl" --cert="$d/final_cert.jsonl" \
          --full="$d/final_full.jsonl" --out-dir="$d/em" --shard=$SHARD \
          --cert-route=interval --ns-prefix="$nsb" --native-ctl > "$d/emit_native.log" 2>&1) && \
        sed "s/${nsb}NativeCtl/${mod}NativeCtl/g" "$d/em/${nsb}NativeCtl.lean" \
          > "$REPO/lean/Kepler/Interval/Cases/${mod}NativeCtl.lean" && \
        echo "${mod}NativeCtl $k 20 native" >> "$WORK/modules.txt"
    fi
    [ -f "$d/shardstate" ] || echo "probe" > "$d/shardstate"
    echo "emit S$k -> ${mod}.lean ($npass leaves)"
  done < "$WORK/emit_tasks.txt"
}

# ---------- [6] build ----------
build_one() { # $1=module
  local M=$1
  local LOG="$WORK/builds/$M.log"
  if grep -qs "^$M " "$WORK/builds/summary.txt"; then echo "build $M: done, skip"; return 0; fi
  local t0=$(date +%s.%N)
  (cd "$REPO/lean" && ulimit -s unlimited && /usr/bin/time -f "RSS %M KB" \
     nice -n 19 lake build "Kepler.Interval.Cases.$M") > "$LOG" 2>&1
  local rc=$?
  local t1=$(date +%s.%N)
  local rss errs ax sorry
  rss=$(grep -oE "RSS [0-9]+ KB" "$LOG" | tail -1 | grep -oE "[0-9]+")
  errs=$(grep -cE "^error" "$LOG")
  ax=$(grep -c "depends on axioms" "$LOG")
  sorry=$(grep -c "sorryAx" "$LOG")
  echo "$M $rc $(echo "$t1 - $t0" | bc) ${rss:-NA} $errs $ax $sorry" >> "$WORK/builds/summary.txt"
}
phase_build() {
  [ -s "$WORK/modules.txt" ] || { echo "build: no modules"; return 0; }
  export -f build_one
  cut -d' ' -f1 "$WORK/modules.txt" | \
    xargs -P "$JOBS" -n1 -I{} bash -c 'build_one "$@"' _ {}
  python3 - "$WORK" <<'PY'
import json,os,sys
work=sys.argv[1]
mods=[l.split() for l in open(f"{work}/modules.txt") if l.strip()]
summ={}
if os.path.exists(f"{work}/builds/summary.txt"):
    for l in open(f"{work}/builds/summary.txt"):
        t=l.split()
        if t: summ[t[0]]=t
stat={}
for M,k,n,kind in mods:
    r=summ.get(M)
    ok = bool(r) and r[1]=="0" and r[4]=="0" and r[6]=="0"
    d=f"{work}/shards/S{k}"
    ss=f"{d}/shardstate"
    if kind=="main" and r:
        cur=open(ss).read().strip() if os.path.exists(ss) else "built"
        new="PASS" if ok else "FAIL"
        if cur in ("PASS","FAIL"): new=cur
        open(ss,"w").write(new+"\n")
    stat[M]=dict(shard=int(k),kind=kind,leaves=int(n),
                 rc=(int(r[1]) if r else None),
                 wall_s=(float(r[2]) if r else None),
                 rss_kb=(int(r[3]) if r and r[3]!="NA" else None),
                 error_lines=(int(r[4]) if r else None),
                 axiom_lines=(int(r[5]) if r else None),
                 sorry_lines=(int(r[6]) if r else None))
json.dump(stat,open(f"{work}/build_stats.json","w"),indent=1)
nmain=[v for v in stat.values() if v["kind"]=="main"]
nbad=sum(1 for v in nmain if v["rc"]!=0)
nerr=sum(1 for v in nmain if (v["error_lines"] or 0)>0)
print(f"build: {len(nmain)} main modules, rc!=0: {nbad}, 裸 error 行>0: {nerr}")
PY
}

# ---------- status（每 shard 一行，原子重写） ----------
write_status() {
  python3 - "$WORK" "$REPO" <<'PY'
import json,os,sys
work,repo=sys.argv[1],sys.argv[2]
try: bs=json.load(open(f"{work}/build_stats.json"))
except FileNotFoundError: bs={}
rows=[]
sd=f"{work}/shards"
if os.path.isdir(sd):
    for s in sorted(os.listdir(sd),key=lambda x:int(x[1:])):
        d=f"{sd}/{s}"; k=int(s[1:])
        if not os.path.exists(f"{d}/census_r128.jsonl"): continue
        st=json.load(open(f"{d}/leafstate.json")) if os.path.exists(f"{d}/leafstate.json") else {}
        npass=sum(1 for v in st.values() if v["state"]=="pass")
        mod=f"C549ProdS{k:04d}"
        state=open(f"{d}/shardstate").read().strip() if os.path.exists(f"{d}/shardstate") else "pending"
        if os.path.exists(f"{repo}/lean/Kepler/Interval/Cases/{mod}.lean") and state=="probe":
            state="emitted"
        b=bs.get(mod) or {}
        rows.append(dict(shard=k,state=state,leaves=len(st),leaves_pass=npass,
                         leaves_fail=len(st)-npass,module=mod,
                         build_rc=b.get("rc"),build_wall_s=b.get("wall_s"),
                         rss_kb=b.get("rss_kb")))
tmp=f"{work}/status.jsonl.tmp"
with open(tmp,"w") as f:
    for r in rows: f.write(json.dumps(r)+"\n")
os.replace(tmp,f"{work}/status.jsonl")
print(f"status: {len(rows)} shards -> status.jsonl")
PY
}

# ---------- [7] report ----------
phase_report() {
  python3 - "$WORK" "$CLASS" "$AJOBS" "$JOBS" <<'PY'
import json,os,sys,statistics,collections
work,cls,ajobs,jobs=sys.argv[1],sys.argv[2],int(sys.argv[3]),int(sys.argv[4])
selr=[json.loads(l) for l in open(f"{work}/selection.jsonl") if l.strip()]
smeta=selr[0]; n_sel=len(selr)-1
leaf=collections.Counter(); layers=collections.Counter(); rungs=collections.Counter()
fullv=collections.Counter(); ms=collections.Counter(); msn=collections.Counter()
shards=[]
for s in sorted(os.listdir(f"{work}/shards"),key=lambda x:int(x[1:])):
    d=f"{work}/shards/{s}"
    if not os.path.exists(f"{d}/leafstate.json"): continue
    st=json.load(open(f"{d}/leafstate.json"))
    npass=sum(1 for v in st.values() if v["state"]=="pass")
    lay=collections.Counter(v.get("layer") for v in st.values() if v["state"]=="fail")
    rg=collections.Counter(str(v.get("rung")) for v in st.values() if v["state"]=="pass")
    state=open(f"{d}/shardstate").read().strip() if os.path.exists(f"{d}/shardstate") else "pending"
    shards.append(dict(shard=int(s[1:]),leaves=len(st),leaves_pass=npass,
                       leaves_fail=len(st)-npass,layers=dict(lay),rungs=dict(rg),state=state))
    for v in st.values():
        leaf[v["state"]]+=1
        if v["state"]=="fail": layers[v.get("layer","?")]+=1
        if v["state"]=="pass": rungs[str(v.get("rung"))]+=1
        pr=v.get("params") or {}
        if pr.get("full"): fullv[pr["full"].get("v")]+=1
for stname in ("der","cert","face","full"):
    for s in sorted(os.listdir(f"{work}/shards")):
        fp=f"{work}/shards/{s}/final_{stname}.jsonl"
        if not os.path.exists(fp): continue
        for r in [json.loads(l) for l in open(fp) if l.strip()][1:]:
            if r["v"]!="FAIL":
                ms[stname]+=r.get("ms",0); msn[stname]+=1
build=None
if os.path.exists(f"{work}/build_stats.json"):
    bs=json.load(open(f"{work}/build_stats.json"))
    main=[(M,v) for M,v in bs.items() if v["kind"]=="main"]
    nat=[(M,v) for M,v in bs.items() if v["kind"]=="native"]
    bw=[v["wall_s"] for _,v in main if v["wall_s"]]
    brss=[v["rss_kb"] for _,v in main if v["rss_kb"]]
    nleaf=sum(v["leaves"] for _,v in main)
    build=dict(modules=len(main),leaves=nleaf,
               wall_med=round(statistics.median(bw),1) if bw else None,
               wall_min=round(min(bw),1) if bw else None,
               wall_max=round(max(bw),1) if bw else None,
               rss_med_mb=round(statistics.median(brss)/1024,2) if brss else None,
               rss_max_mb=round(max(brss)/1024,2) if brss else None,
               s_per_leaf=round(sum(bw)/nleaf,1) if nleaf and bw else None,
               native=(dict(wall_s=nat[0][1]["wall_s"],leaves=nat[0][1]["leaves"],
                            s_per_leaf=round(nat[0][1]["wall_s"]/nat[0][1]["leaves"],1))
                       if nat else None))
    src=[];ol=[]
    for M,_ in main:
        p=f"/home/scroll/repos/kepler-conjecture-lean4/lean/Kepler/Interval/Cases/{M}.lean"
        o=f"/home/scroll/repos/kepler-conjecture-lean4/lean/.lake/build/lib/lean/Kepler/Interval/Cases/{M}.olean"
        if os.path.exists(p): src.append(os.path.getsize(p))
        if os.path.exists(o): ol.append(os.path.getsize(o))
    build["src_kb_per_leaf"]=round(sum(src)/1024/nleaf,1) if src and nleaf else None
    build["olean_kb_per_leaf"]=round(sum(ol)/1024/nleaf,1) if ol and nleaf else None
try:
    pt=json.load(open(f"{work}/phase_timings.json"))
    def pdur(k):
        v=pt.get(k,[]); e=pt.get(k+"_end",[])
        return round(e[-1]-v[0],1) if v and e else None
    phw={k:pdur(k) for k in ("manifest","select","stagea","merge","locheck","emit","build","report")}
except Exception: phw={}
n_all=max(1,sum(leaf.values()))
stageA_core=sum(ms[st] for st in ("der","cert","face","full"))/1000/n_all
rep=dict(tag=os.path.basename(work), cls=cls, selection=smeta, selected=n_sel,
         leaf=dict(leaf), pass_rate=round(leaf["pass"]/n_all,4),
         fail_layers=dict(layers), rung_dist=dict(rungs), fullbox=dict(fullv),
         stageA_ms_sums=dict(ms), stageA_ms_n=dict(msn),
         stageA_core_s_per_leaf=round(stageA_core,2),
         build=build, phase_wall_s=phw, shards=shards,
         extrapolate=dict(pool_single=165219, budget=dict(a_jobs=ajobs,build_jobs=jobs),
                          stageA_wall_h=round(165219*stageA_core/ajobs/3600,1)))
if build and build.get("s_per_leaf"):
    emitted=int(165219*leaf["pass"]/n_all)
    rep["extrapolate"].update(
      est_emitted=emitted, est_shards=int(-(-emitted//20)),
      build_core_h=round(emitted*build["s_per_leaf"]/3600,1),
      build_wall_h=round(emitted*build["s_per_leaf"]/jobs/3600,1),
      src_gb=round(emitted*(build.get("src_kb_per_leaf") or 0)/1024/1024,2),
      olean_gb=round(emitted*(build.get("olean_kb_per_leaf") or 0)/1024/1024,2))
json.dump(rep,open(f"{work}/slice_report.json","w"),indent=1,ensure_ascii=False)
print(json.dumps({k:rep[k] for k in ("selected","leaf","pass_rate","fail_layers","rung_dist",
                                     "fullbox","stageA_ms_sums","stageA_core_s_per_leaf",
                                     "build","phase_wall_s","extrapolate")},
                 indent=1,ensure_ascii=False))
print(f"-> {work}/slice_report.json")
PY
}

T0=$(date +%s)
for ph in manifest select stagea merge locheck emit build report; do
  has_phase "$ph" || continue
  phase_mark "$ph"
  if ! phase_"$ph"; then
    write_status
    echo "$(date +%F' '%T) PHASE $ph FAILED — abort（重跑 run_full.sh 断点续跑）"
    exit 1
  fi
  phase_mark "${ph}_end"
  write_status
  echo "$(date +%F' '%T) phase $ph done (+$(( $(date +%s) - T0 ))s)"
done
write_status
echo "$(date +%F' '%T) run_full COMPLETE (+$(( $(date +%s) - T0 ))s)"
