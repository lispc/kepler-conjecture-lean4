/-
  shadow_map.lean — orphan-scout lane B: e2e 直源影子子树估计（2026-11-03）

  纯测量（零证明、零仓库改动；standalone，不用 lake）。

  对 e2e 根（默认 `Kepler.Assembly.the_kepler_conjecture_from_interfaces`，
  可用 REACH_ROOT 覆盖）的每条直接 sorryAx 源 D，估计
  shadow(D) = 若 D 被真证、会新进入锥内的 Kepler 声明数。

  口径（模块代理，与工单一致）：
    - shadow(M) := |closure(valued(M) ∖ C_e2e) − C_e2e| —— 模块 M 内全部
      有值声明中不在当前 e2e 锥内的那部分的可达闭包 = 若 M 的债被「用 M
      自己的全部材料」填平、能新进锥的节点数上限（unlock ceiling）。
      优化：锥内声明的闭包 ⊆ 锥，故种子只需取 valued(M) ∖ C_e2e。
    - alloc(D) := shadow(M) / nSources(M) —— 按模块内源数均摊（真证明之间
      会重叠，模块合计是上界不是和）。
    - 纯 stub（值里只有 sorryAx）与混合源（已有部分骨架，keplerRef 计数）
      分开标注；混合源kc=0 的纯 stub 解锁潜力最大。

  已知局限（写进交付口径）：模块代理测的是「M 自己的未用材料」；
  Assembly 类消费桩的填证收益（引用别的模块材料）不在本口径内——
  那类源按「债务缩减、低 K_REACH 增益」单独归档。

  输出：
    - CALIB：e2e 根指标。
    - SOURCES：全部直源（module / name / pureStub / keplerRefs / parent）。
    - SHADOW_MODULE：module / nSources / nSeeds / shadow / allocPerSource。
    - SHADOW_SOURCE_TOP20：按 alloc 排序的源。

  用法：
    LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) \
      nice -n 19 lean lean/scripts/shadow_map.lean > /tmp/shadow_map.out
  冒烟：REACH_ROOT=Kepler.Text.<small root> SHADOW_MODULE_LIMIT=3。
  口径：import Kepler.Assembly（与 e2e_reach_map.lean 同宇宙）；
  olean 口径 = 测量时刻共享 .lake。
-/
import Kepler.Assembly

open Lean

set_option maxHeartbeats 0
set_option maxRecDepth 100000

partial def rootIsKepler : Name → Bool
  | .str .anonymous s => s == "Kepler"
  | .str p _ => rootIsKepler p
  | .num p _ => rootIsKepler p
  | .anonymous => false

partial def rootIsPrivateKepler : Name → Bool
  | .str (.str .anonymous "_private") "Kepler" => true
  | .str p _ => rootIsPrivateKepler p
  | .num p _ => rootIsPrivateKepler p
  | .anonymous => false

def isKeplerName (n : Name) : Bool :=
  rootIsKepler n || rootIsPrivateKepler n

def isSorryAx (n : Name) : Bool :=
  n == `sorryAx || n == `Lean.sorryAx

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none =>
    match n with
    | .str p _ => p
    | _ => n

def parseName (s : String) : Name :=
  (s.splitOn ".").foldl (fun acc c => Name.str acc c) Name.anonymous

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

structure ConeRes where
  kReach : Nat := 0
  total : Nat := 0
  sources : Array (Name × Bool × Nat × String) := #[]  -- (name, pureStub, keplerRefs, kind)
  names : Std.HashSet Name := {}
  parents : Std.HashMap Name Name := {}
deriving Inhabited

/-- e2e 锥 BFS（collect names + parents + 直源分类）。 -/
partial def e2eBfs (env : Environment) (root : Name) : ConeRes :=
  let rec go (fuel : Nat) (stack : List (Name × Nat)) (seen : Std.HashSet Name)
      (r : ConeRes) : ConeRes :=
    match fuel with
    | 0 => r
    | fuel + 1 =>
      match stack with
      | [] => r
      | (n, _d) :: rest =>
        if seen.contains n then go fuel rest seen r
        else
          let seen := seen.insert n
          let r :=
            if isKeplerName n then
              { r with kReach := r.kReach + 1, names := r.names.insert n }
            else r
          match env.find? n with
          | none => go fuel rest seen r
          | some ci =>
            match ci.value? true with
            | none => go fuel rest seen r
            | some v =>
              let cs := v.getUsedConstants
              let isSor := cs.any isSorryAx
              let kc := cs.foldl (fun acc c => if isKeplerName c then acc + 1 else acc) 0
              let r :=
                if isSor && isKeplerName n then
                  { r with sources := r.sources.push (n, cs.all isSorryAx, kc, kindOf ci) }
                else r
              let (parents, newOnes) := cs.foldl
                (init := (r.parents, ([] : List (Name × Nat))))
                (fun (acc : Std.HashMap Name Name × List (Name × Nat)) c =>
                  let (par, ns) := acc
                  if isKeplerName c && !seen.contains c then
                    let par := if par.contains c then par else par.insert c n
                    (par, (c, 0) :: ns)
                  else acc)
              go fuel (newOnes ++ rest) seen
                { r with parents, total := r.total + 1 }
  go 10000000 [(root, 0)] {} {}

/-- 从 seeds 出发 BFS（seen 预置 preload）；返回 fresh Kepler 名集合大小。 -/
partial def bfsNewSize (env : Environment) (seeds : List Name)
    (preload : Std.HashSet Name) : Nat :=
  let rec go (fuel : Nat) (stack : List Name) (seen : Std.HashSet Name)
      (cnt : Nat) : Nat :=
    match fuel with
    | 0 => cnt
    | fuel + 1 =>
      match stack with
      | [] => cnt
      | n :: rest =>
        if seen.contains n then go fuel rest seen cnt
        else
          let seen := seen.insert n
          let cnt := if isKeplerName n then cnt + 1 else cnt
          match env.find? n with
          | none => go fuel rest seen cnt
          | some ci =>
            match ci.value? true with
            | none => go fuel rest seen cnt
            | some v =>
              let cs := v.getUsedConstants
              let newOnes := cs.foldl (init := ([] : List Name))
                (fun ns x => if isKeplerName x && !seen.contains x then x :: ns else ns)
              go fuel (newOnes ++ rest) seen cnt
  go 10000000 seeds preload 0

structure SeedState where
  univ : Nat := 0
  valued : Nat := 0
  seeds : Std.HashMap Name (Array Name) := {}
deriving Inhabited

def defaultRoot : Name := `Kepler.Assembly.the_kepler_conjecture_from_interfaces

def mainRun : CoreM Unit := do
  let env ← getEnv
  let root ← match ← IO.getEnv "REACH_ROOT" with
    | some s => pure (parseName s)
    | none => pure defaultRoot
  let modLimit : Nat :=
    match ← IO.getEnv "SHADOW_MODULE_LIMIT" with
    | some s => s.toNat?.getD 0
    | none => 0

  -- 1. e2e 锥 + 直源
  let cr := e2eBfs env root
  let cone := cr.names
  IO.println s!"CALIB ROOT {root}"
  IO.println s!"CALIB K_REACH {cr.kReach}"
  IO.println s!"CALIB SOURCES {cr.sources.size}"
  IO.println s!"CALIB TOTAL_VALUE_DECLS {cr.total}"

  -- 2. 直源清单
  IO.println "--- SOURCES ---"
  for (n, ps, kc, k) in cr.sources do
    let m := moduleOf env n
    let par := cr.parents.getD n n
    IO.println s!"SOURCE {m}\t{n}\t{k}\tpureStub={ps}\tkeplerRefs={kc}\tparent={par}"

  -- 3. 源按模块分组
  let mut srcByMod : Std.HashMap Name (Array Name) := {}
  for (n, _, _, _) in cr.sources do
    let m := moduleOf env n
    let arr := srcByMod.getD m (#[] : Array Name)
    srcByMod := srcByMod.insert m (arr.push n)
  IO.println s!"SOURCE_MODULES {srcByMod.toArray.size}"

  -- 4. 全常数扫描：universe + valued + 非锥有值声明按模块分桶
  let st := env.constants.fold
    (fun (acc : SeedState) n ci =>
      if !isKeplerName n then acc else
      let acc := { acc with univ := acc.univ + 1 }
      match ci.value? true with
      | none => acc
      | some _ =>
        let acc := { acc with valued := acc.valued + 1 }
        if cone.contains n then acc else
        let m := moduleOf env n
        let arr := acc.seeds.getD m (#[] : Array Name)
        { acc with seeds := acc.seeds.insert m (arr.push n) })
    {}
  IO.println s!"K_UNIVERSE {st.univ}"
  IO.println s!"VALUED_KEPLER_DECLS {st.valued}"

  -- 5. 每含源模块 shadow(M)（unlock ceiling）
  IO.println "--- SHADOW_MODULE (module / nSources / nSeeds / shadow / allocPerSource) ---"
  let mut rows : Array (Name × Nat × Nat × Nat × Nat) := #[]
  let mut mi := 0
  for (m, srcs) in srcByMod.toArray do
    if modLimit == 0 || mi < modLimit then
      let seeds := st.seeds.getD m (#[] : Array Name)
      let sh := bfsNewSize env seeds.toList cone
      let alloc := sh / srcs.size
      rows := rows.push (m, srcs.size, seeds.size, sh, alloc)
      IO.println s!"SHADOW_MODULE {m}\t{srcs.size}\t{seeds.size}\t{sh}\t{alloc}"
      mi := mi + 1
  let rowsSorted := rows.qsort (fun a b => a.2.2.2.2 > b.2.2.2.2)
  let shadowSum := rows.foldl (fun acc t => acc + t.2.2.2.1) 0
  IO.println s!"SHADOW_MODULE_COUNT {rowsSorted.size}"
  IO.println s!"SHADOW_SUM_UPPERBOUND {shadowSum}"

  -- 6. 源级 top20（alloc 排序，kc 次序）
  let mut srows : Array (Nat × Name × Name × Bool × Nat × String × Name) := #[]
  for (n, ps, kc, k) in cr.sources do
    let m := moduleOf env n
    let alloc := match rows.find? (fun t => t.1 == m) with
      | some t => t.2.2.2.2
      | none => 0
    let par := cr.parents.getD n n
    srows := srows.push (alloc, n, m, ps, kc, k, par)
  let srowsSorted := srows.qsort (fun a b =>
    a.1 > b.1 || (a.1 == b.1 && a.2.2.2.2.1 > b.2.2.2.2.1))
  IO.println "--- SHADOW_SOURCE_TOP20 (alloc / name / module / kind / pureStub / keplerRefs / parent) ---"
  let mut rank := 0
  for (alloc, n, m, ps, kc, k, par) in srowsSorted do
    if rank < 20 then
      IO.println s!"SHADOW_SOURCE {rank + 1}\t{alloc}\t{n}\t{m}\t{k}\tpureStub={ps}\tkeplerRefs={kc}\tparent={par}"
      rank := rank + 1
  IO.println "--- END ---"

#eval show CoreM Unit from mainRun
