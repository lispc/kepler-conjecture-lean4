/-
  orphan_histogram.lean — orphan-scout lane A: 按模块的孤儿直方图（2026-11-03）

  纯测量（零证明、零仓库改动；standalone，不用 lake）。复用
  global_reach_map.lean v2 的多根 union 口径，对 K_UNIVERSE 求差得 ORPHANS，
  输出按模块直方图（module → 孤儿数 + kind 构成）。机械证书层
  （Interval.Cases / Graphs.CertShards / Shard / CertTri..Hex 模块，或
  `_native_decide` 声明）单列 GENERATED 一节，不入主直方图。

  根集合 = e2e 1 + PackingConcl `*_discharged` + LocalConcl `*_discharged`
  + 章capstone 2（修正全名 `Kepler.Text.OXLZLEZ` /
  `Kepler.Text.PACKING_CHAPTER_MAIN_CONCLUSION`，修复 v2 运行时的笔误跳过）
  = 156 根族。

  额外输出：
    - CALIB：e2e 单根 K_REACH / K_SORRIED（仪器校准对照线）。
    - WIRE：不在 e2e 锥内的根 r 的 |closure(r) − C_e2e|（把 r 接线进 e2e
      的精确新增树节点；覆盖「LocalConcl/PackingConcl 未入 e2e 的
      discharged 根」与 2 个 capstone）。
    - PAIR_HINT：孤儿里 `_concl` / `_discharged` / `_pc` / `_version2`
      后缀声明去后缀配对（正本是否存在 / 是否已在树内；仅提示，
      造边需另附 docstring/文件头/HOL 锚证据）。
    - RDWKARC：名字含 rdwkarc（大小写不敏感）声明的树内/树外状态，
      以及相对 e2e 锥 / union 的精确接线增量（PA19 整文件孤儿探针）。
    - KEPLER_MODULES：env.header 全部 Kepler 模块名（供与源码文件清单
      离线 diff，找连 env 都进不来的整文件孤儿）。

  用法：
    LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) \
      nice -n 19 lean lean/scripts/orphan_histogram.lean > /tmp/orphan_hist.out
  冒烟：ORPHAN_WIRE_LIMIT=8 只对前 8 个非锥根做 WIRE BFS（其余仍全跑）。

  口径：静态 proof-term 遍历；`ConstantInfo.value? true`；只跟踪
  `Kepler.*` / `_private.Kepler.*`；import = Kepler + Kepler.Assembly +
  Kepler.Text.PackingConcl（与 global_reach_map.lean 同宇宙）。
  olean 口径 = 测量时刻共享 .lake（HEAD a522078c 附近；PA15 已闭、T0 已落库，
  olean 是否含其 kit 态以构建时刻为准）。
-/
import Kepler
import Kepler.Assembly
import Kepler.Text.PackingConcl

open Lean

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- 名字根分量为 `Kepler`（`Kepler.*`）。不分配 String，供 2M 级扫描用。 -/
partial def rootIsKepler : Name → Bool
  | .str .anonymous s => s == "Kepler"
  | .str p _ => rootIsKepler p
  | .num p _ => rootIsKepler p
  | .anonymous => false

/-- 名字根分量为 `_private.Kepler`（`_private.Kepler.*`）。 -/
partial def rootIsPrivateKepler : Name → Bool
  | .str (.str .anonymous "_private") "Kepler" => true
  | .str p _ => rootIsPrivateKepler p
  | .num p _ => rootIsPrivateKepler p
  | .anonymous => false

def isKeplerName (n : Name) : Bool :=
  rootIsKepler n || rootIsPrivateKepler n

def isSorryAx (n : Name) : Bool :=
  n == `sorryAx || n == `Lean.sorryAx

/-- 声明所属模块；`getModuleIdxFor?` 缺失时退化为名字前缀。 -/
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none =>
    match n with
    | .str p _ => p
    | _ => n

/-- 最后一段分量（不分配整串）。 -/
def lastNamePart : Name → String
  | .str _ s => s
  | .num _ i => toString i
  | .anonymous => ""

/-- 把 `A.B.C` 字符串切成 Name。 -/
def parseName (s : String) : Name :=
  (s.splitOn ".").foldl (fun acc c => Name.str acc c) Name.anonymous

def sortNames (a : Array Name) : Array Name :=
  a.qsort (fun x y => x.toString < y.toString)

/-- 机械证书层判定（与 e2e_reach_map.lean 同口径）。 -/
def isGeneratedModule (m : Name) : Bool :=
  let s := m.toString
  s.contains "Interval.Cases" || s.contains "Graphs.CertShards" ||
  s.contains "Shard" || s.contains "CertTri" || s.contains "CertQuad" ||
  s.contains "CertPent" || s.contains "CertHex"

def isGeneratedDecl (m : Name) (n : Name) : Bool :=
  isGeneratedModule m || (n.toString).contains "_native_decide"

/-- kind 列（直方图列序）：0 axiom / 1 def / 2 theorem / 3 opaque /
    4 quot / 5 induct / 6 ctor / 7 rec -/
def kindIdx : ConstantInfo → Nat
  | .axiomInfo _ => 0
  | .defnInfo _ => 1
  | .thmInfo _ => 2
  | .opaqueInfo _ => 3
  | .quotInfo _ => 4
  | .inductInfo _ => 5
  | .ctorInfo _ => 6
  | .recInfo _ => 7

/-- 从 seeds 出发 BFS（展开全部值、子边只收 Kepler）。seen 预置 preload
（不重遍、不计入 fresh）。返回 (fresh Kepler 名集合, 直接 sorry 声明数,
访问声明总数)。 -/
partial def bfsNew (env : Environment) (seeds : List Name)
    (preload : Std.HashSet Name) : Std.HashSet Name × Nat × Nat :=
  let rec go (fuel : Nat) (stack : List Name) (seen : Std.HashSet Name)
      (fresh : Std.HashSet Name) (sor : Nat) (tot : Nat) :
      Std.HashSet Name × Nat × Nat :=
    match fuel with
    | 0 => (fresh, sor, tot)
    | fuel + 1 =>
      match stack with
      | [] => (fresh, sor, tot)
      | n :: rest =>
        if seen.contains n then
          go fuel rest seen fresh sor tot
        else
          let seen := seen.insert n
          let fresh := if isKeplerName n then fresh.insert n else fresh
          match env.find? n with
          | none => go fuel rest seen fresh sor (tot + 1)
          | some ci =>
            match ci.value? true with
            | none => go fuel rest seen fresh sor (tot + 1)
            | some v =>
              let cs := v.getUsedConstants
              let sor :=
                if isKeplerName n && cs.any isSorryAx then sor + 1 else sor
              let newOnes := cs.foldl (init := ([] : List Name))
                (fun ns x => if isKeplerName x && !seen.contains x then x :: ns else ns)
              go fuel (newOnes ++ rest) seen fresh sor (tot + 1)
  go 10000000 seeds preload {} 0 0

structure Scan1 where
  pck : Array Name := #[]
  loc : Array Name := #[]
  rdwk : Array Name := #[]
deriving Inhabited

/-- 全常数扫描 #1：枚举 discharged 根 + rdwkarc 探针名字。 -/
def scan1 (env : Environment) : Scan1 :=
  env.constants.fold
    (fun (acc : Scan1) n _ =>
      let last := lastNamePart n
      let acc :=
        if last.endsWith "_discharged" then
          let m := moduleOf env n
          if m == `Kepler.Text.PackingConcl then { acc with pck := acc.pck.push n }
          else if m == `Kepler.Text.LocalConcl then { acc with loc := acc.loc.push n }
          else acc
        else acc
      if (lastNamePart n).toLower.contains "rdwkarc" then
        { acc with rdwk := acc.rdwk.push n }
      else acc)
    {}

structure HistState where
  univ : Nat := 0
  hist : Std.HashMap Name (Array Nat) := {}
  ghist : Std.HashMap Name (Array Nat) := {}
  pairs : Array (Name × Name) := #[]
deriving Inhabited

def isPairSuffix (s : String) : Bool :=
  s.endsWith "_concl" || s.endsWith "_discharged" ||
  s.endsWith "_pc" || s.endsWith "_version2"

def mainRun : CoreM Unit := do
  let env ← getEnv
  let e2e : Name := `Kepler.Assembly.the_kepler_conjecture_from_interfaces
  let manual : Array Name := #[
    `Kepler.Text.OXLZLEZ,
    `Kepler.Text.PACKING_CHAPTER_MAIN_CONCLUSION]
  let e1 := scan1 env
  let pck := sortNames e1.pck
  let loc := sortNames e1.loc
  IO.println s!"ROOTS_PACKINGCONCL_ENUMERATED {pck.size}"
  IO.println s!"ROOTS_LOCALCONCL_ENUMERATED {loc.size}"
  let mut manualPresent : Array Name := #[]
  for n in manual do
    if (env.find? n).isSome then
      manualPresent := manualPresent.push n
    else
      IO.println s!"ROOT_SKIP {n} (not found in env)"
  IO.println s!"ROOTS_CAPSTONE_MANUAL_PRESENT {manualPresent.size} / {manual.size}"
  let mut roots : Array Name := #[e2e]
  for n in manualPresent ++ pck ++ loc do
    if !(roots.contains n) then
      roots := roots.push n
  IO.println s!"ROOTS_TOTAL {roots.size}"

  -- 1. e2e 锥（校准线）
  let r0 := bfsNew env [e2e] {}
  let cone := r0.1
  IO.println s!"CALIB ROOT {e2e}"
  IO.println s!"CALIB K_REACH {cone.size}"
  IO.println s!"CALIB K_SORRIED {r0.2.1}"
  IO.println s!"CALIB TOTAL_VALUE_DECLS {r0.2.2}"

  -- 2. 非锥根的 WIRE 增量
  let wireLimit : Nat :=
    match ← IO.getEnv "ORPHAN_WIRE_LIMIT" with
    | some s => s.toNat?.getD 0
    | none => 0
  let nonCone := roots.filter (fun r => !(cone.contains r))
  IO.println s!"ROOTS_NOT_IN_CONE {nonCone.size} / {roots.size}"
  let mut wires : Array (Name × Name × Nat) := #[]
  let mut done := 0
  for r in nonCone do
    if wireLimit == 0 || done < wireLimit then
      let rr := bfsNew env [r] cone
      wires := wires.push (r, moduleOf env r, rr.1.size)
      done := done + 1
  let wiresSorted := wires.qsort (fun a b => a.2.2 > b.2.2)
  IO.println "--- WIRE ---"
  for (r, m, inc) in wiresSorted do
    IO.println s!"WIRE {r}\t{m}\tincrement {inc}"

  -- 3. union（= e2e 锥 ∪ 其余根的 fresh；单次 BFS，preload cone）
  let ru := bfsNew env nonCone.toList cone
  let unionFresh := ru.1
  let unionKReach := cone.size + unionFresh.size
  let unionSet := unionFresh.toList.foldl (fun s n => s.insert n) cone
  IO.println "--- UNION ---"
  IO.println s!"UNION K_REACH {unionKReach}"
  IO.println s!"UNION K_SORRIED_E2E_CONE {r0.2.1}"
  IO.println s!"UNION K_SORRIED_FRESH {ru.2.1}"
  IO.println s!"UNION K_SORRIED_TOTAL {r0.2.1 + ru.2.1}"

  -- 4. 孤儿直方图（全常数扫描 #2：universe + per-module kind 计数 + 配对候选）
  let st := env.constants.fold
    (fun (acc : HistState) n ci =>
      if !isKeplerName n then acc else
      let acc := { acc with univ := acc.univ + 1 }
      if cone.contains n || unionFresh.contains n then acc else
      let m := moduleOf env n
      let k := kindIdx ci
      let gen := isGeneratedDecl m n
      let tbl := if gen then acc.ghist else acc.hist
      let arr := tbl.getD m #[0, 0, 0, 0, 0, 0, 0, 0]
      let arr := arr.set! k ((arr.getD k 0) + 1)
      let tbl := tbl.insert m arr
      let acc := if gen then { acc with ghist := tbl } else { acc with hist := tbl }
      let last := lastNamePart n
      if isPairSuffix last then
        { acc with pairs := acc.pairs.push (n, m) }
      else acc)
    {}
  IO.println s!"K_UNIVERSE {st.univ}"
  IO.println s!"ORPHANS_TOTAL {st.univ - unionKReach}"

  let histSorted := st.hist.toArray.qsort (fun a b =>
    (a.2.foldl (· + ·) 0) > (b.2.foldl (· + ·) 0))
  IO.println "--- ORPHAN HISTOGRAM (non-generated; module / total / theorem def axiom opaque ctor rec induct quot) ---"
  let mut ge500 := 0
  let mut idx := 0
  for (m, arr) in histSorted do
    let tot := arr.foldl (· + ·) 0
    let line := s!"{m}\t{tot}\t{arr.getD 2 0}\t{arr.getD 1 0}\t{arr.getD 0 0}\t{arr.getD 3 0}\t{arr.getD 6 0}\t{arr.getD 7 0}\t{arr.getD 5 0}\t{arr.getD 4 0}"
    if idx < 10 then
      IO.println s!"TOP_ORPHAN_MODULE {idx + 1}\t{line}"
    if tot >= 500 then
      IO.println s!"GE500 {line}"
      ge500 := ge500 + 1
    IO.println s!"HIST {line}"
    idx := idx + 1
  IO.println s!"ORPHAN_MODULES_TOTAL {histSorted.size}"
  IO.println s!"MODULES_GE500 {ge500}"

  let ghistSorted := st.ghist.toArray.qsort (fun a b =>
    (a.2.foldl (· + ·) 0) > (b.2.foldl (· + ·) 0))
  let gtotal := ghistSorted.foldl (fun acc t => acc + (t.2.foldl (· + ·) 0)) 0
  IO.println "--- GENERATED CERT LAYER (separate; excluded from histogram) ---"
  IO.println s!"GENERATED_ORPHANS_TOTAL {gtotal}"
  IO.println s!"GENERATED_ORPHAN_MODULES {ghistSorted.size}"
  let mut gi := 0
  for (m, arr) in ghistSorted do
    if gi < 10 then
      let tot := arr.foldl (· + ·) 0
      IO.println s!"GENERATED_TOP {m}\t{tot}\tthm={arr.getD 2 0}\tdef={arr.getD 1 0}\tctor={arr.getD 6 0}\trec={arr.getD 7 0}\tinduct={arr.getD 5 0}\taxiom={arr.getD 0 0}"
    gi := gi + 1

  -- 5. PAIR_HINTS（孤儿后缀配对；仅提示，造边需另附证据）
  IO.println "--- PAIR_HINTS ---"
  let mut ph := 0
  for (n, m) in st.pairs do
    if ph < 200 then
      let s := n.toString
      let cands : List String :=
        if s.endsWith "_concl_discharged" then
          [(s.dropEnd "_discharged".length).copy, (s.dropEnd "_concl_discharged".length).copy]
        else if s.endsWith "_concl" then [(s.dropEnd "_concl".length).copy]
        else if s.endsWith "_discharged" then [(s.dropEnd "_discharged".length).copy]
        else if s.endsWith "_pc" then [(s.dropEnd "_pc".length).copy]
        else if s.endsWith "_version2" then [(s.dropEnd "_version2".length).copy]
        else []
      for c in cands do
        let cn := parseName c
        if (env.find? cn).isSome then
          let inTree := unionSet.contains cn
          IO.println s!"PAIR {n}\t-> {c}\texists=true\tinTree={inTree}\tmodule={m}"
          ph := ph + 1
  IO.println s!"PAIR_HINTS_PRINTED {ph}"

  -- 6. RDWKARC 探针（PA19 整文件孤儿）
  IO.println "--- RDWKARC ---"
  IO.println s!"RDWKARC_NAMES {e1.rdwk.size}"
  for n in sortNames e1.rdwk do
    let m := moduleOf env n
    let sorried :=
      match env.find? n with
      | some ci =>
        match ci.value? true with
        | some v => v.getUsedConstants.any isSorryAx
        | none => false
      | none => false
    let inCone := cone.contains n
    let inUnion := unionSet.contains n
    let mut incCone := 0
    let mut incUnion := 0
    if !inCone then
      incCone := (bfsNew env [n] cone).1.size
    if !inUnion then
      incUnion := (bfsNew env [n] unionSet).1.size
    IO.println s!"RDWKARC {n}\t{m}\tinCone={inCone}\tinUnion={inUnion}\tsorried={sorried}\tincrementVsCone={incCone}\tincrementVsUnion={incUnion}"

  -- 7. env Kepler 模块清单（供与源码文件清单离线 diff）
  IO.println "--- KEPLER_MODULES ---"
  for m in env.header.moduleNames do
    if rootIsKepler m || rootIsPrivateKepler m then
      IO.println s!"MODULE {m}"
  IO.println "--- END ---"

#eval show CoreM Unit from mainRun
