/-
  e2e_reach_map.lean — proof-term 可达性地图（v2, 2026-11-03）

  从 ROOT 出发，遍历 proof-term 的常量依赖（只跟踪 `Kepler.*` /
  `_private.Kepler.*`），输出「树」指标。ROOT 默认 =
  `Kepler.Assembly.the_kepler_conjecture_from_interfaces`（e2e 根）。

  v2 指标（口径见 docs/e2e-reachability-map.md §0/§5）：
    - K_REACH    可达 Kepler 声明数（distinct，树节点；含 axiom/opaque）
    - K_SORRIED  值里**直接**含 `sorryAx` 的可达声明（债务源）
    - K_AXIOM    可达 Kepler 公理（含 `native_decide` 的 `*_native_decide.ax_*`）
    - K_MODULES  可达声明所在的不同模块数
    - K_UNIVERSE 当前 env 中全部 Kepler 声明数（COVERAGE 分母；=
                 `import` 闭包载入的 Kepler 声明总数）
    - COVERAGE   K_REACH / K_UNIVERSE
    - TOTAL       legacy 计数：**有值**的可达声明数（= 旧
                 `TOTAL_REACHABLE_KEPLER_DECLS`）。旧名不再使用：它**不是**
                 “Kepler 声明数”，也不再与 K_REACH 同义（差值为 axiom/opaque
                 等无值声明）。

  用法（standalone，不用 lake）：
    LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) \
      REACH_ROOT=Kepler.Text.SomeRoot \
      lean lean/scripts/e2e_reach_map.lean > /tmp/reachmap.out
  不设 `REACH_ROOT` 时用 e2e 根。e2e 仪器校准：HEAD 上 `SORRIED` 应为 123
  （与 docs/e2e-reachability-map.tsv 对齐；注意 .lake 可能含并行车道污染的
  olean，见 docs/e2e-reachability-map.md §5 “仪器校准”）。

  口径：静态 proof-term 遍历；`ConstantInfo.value? true`（theorem/opaque 值都
  展开，与 `#print axioms` 的闭包一致）；父边是首次 BFS 命中，不是唯一父。
  证明项里的死分支也会被计入（内核仍要检查）。
-/
import Kepler.Assembly

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

/-- `Kepler.*` / `_private.Kepler.*` 判定（树只认这些节点）。 -/
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

/-- 把 `A.B.C` 字符串切成 Name（不依赖 `String.toName`）。 -/
def parseName (s : String) : Name :=
  (s.splitOn ".").foldl (fun acc c => Name.str acc c) Name.anonymous

/-- 声明种类（DUMP_TREE 表用）。 -/
def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

/-- 机械证书层判定（页面默认折叠成聚合节点）：模块名含 `Interval.Cases` /
`Graphs.CertShards` / `Shard` / `CertTri|Quad|Pent|Hex`，或声明名含
`_native_decide`。 -/
def isGeneratedModule (m : Name) : Bool :=
  let s := m.toString
  s.contains "Interval.Cases" || s.contains "Graphs.CertShards" ||
  s.contains "Shard" || s.contains "CertTri" || s.contains "CertQuad" ||
  s.contains "CertPent" || s.contains "CertHex"

/-- 口径 II（2026-11-04 用户裁）：汇报头部指标剔除机器证书 shard 树
`Kepler.Interval.Cases.*`（人工数学 + Graphs/Assembly 证书轴保留在口径内）。 -/
def isCasesModule (m : Name) : Bool :=
  (m.toString).startsWith "Kepler.Interval.Cases"

def isGeneratedDecl (m : Name) (n : Name) : Bool :=
  isGeneratedModule m || (n.toString).contains "_native_decide"

/-- DUMP_TREE=1 时的节点行；`childCount` / `extCount` 是**直接**依赖的原始
出现次数（同一常量在值里出现两次就计两次）。`depth` = 首次访问深度（DFS
栈序，不是最小 BFS 深度）。 -/
structure NodeRow where
  name : Name
  module : Name
  kind : String
  directSorry : Bool
  childCount : Nat
  extCount : Nat
  depth : Nat
  generated : Bool
  treeChildCount : Nat := 0
deriving Inhabited

structure MapResult where
  /-- distinct 可达 Kepler 声明数（含 axiom/opaque） -/
  kReach : Nat := 0
  /-- legacy：有值的可达声明数（旧 TOTAL_REACHABLE_KEPLER_DECLS） -/
  total : Nat := 0
  sorries : Array (Name × Name) := #[]
  axioms : Array (Name × Name) := #[]
  modules : Std.HashSet Name := {}
  /-- 口径 II 直方图：模块 → 可达 Kepler 声明数。 -/
  moduleCounts : Std.HashMap Name Nat := {}
  parents : Std.HashMap Name Name := {}
  nodes : Array NodeRow := #[]
deriving Inhabited

partial def reach (env : Environment) (root : Name) (dump : Bool := false) : MapResult :=
  let rec go (fuel : Nat) (stack : List (Name × Nat)) (seen : Std.HashSet Name)
      (r : MapResult) : MapResult :=
    match fuel with
    | 0 => r
    | fuel + 1 =>
      match stack with
      | [] => r
      | (n, d) :: rest =>
        if seen.contains n then
          go fuel rest seen r
        else
          let seen := seen.insert n
          match env.find? n with
          | none => go fuel rest seen r
          | some ci =>
            let isK := isKeplerName n
            let r :=
              if isK then
                { r with
                  kReach := r.kReach + 1
                  modules := r.modules.insert (moduleOf env n)
                  moduleCounts :=
                    let m := moduleOf env n
                    r.moduleCounts.insert m (r.moduleCounts.getD m 0 + 1) }
              else r
            match ci.value? true with
            | none =>
              let r :=
                if isK then
                  match ci with
                  | .axiomInfo _ => { r with axioms := r.axioms.push (n, moduleOf env n) }
                  | _ => r
                else r
              let r :=
                if dump && isK then
                  let row : NodeRow :=
                    { name := n, module := moduleOf env n, kind := kindOf ci
                      directSorry := false, childCount := 0, extCount := 0
                      depth := d, generated := isGeneratedDecl (moduleOf env n) n }
                  { r with nodes := r.nodes.push row }
                else r
              go fuel rest seen r
            | some v =>
              let cs := v.getUsedConstants
              let isSor := cs.any isSorryAx
              let r :=
                if isSor && isK then
                  { r with sorries := r.sorries.push (n, moduleOf env n) }
                else r
              let (parents, newOnes) := cs.foldl (init := (r.parents, ([] : List (Name × Nat))))
                (fun (acc : Std.HashMap Name Name × List (Name × Nat)) c =>
                  let (par, ns) := acc
                  if isKeplerName c && !seen.contains c then
                    let par := if par.contains c then par else par.insert c n
                    (par, (c, d + 1) :: ns)
                  else acc)
              let r :=
                if dump && isK then
                  let kdeps := cs.foldl (fun acc c => if isKeplerName c then acc + 1 else acc) 0
                  let row : NodeRow :=
                    { name := n, module := moduleOf env n, kind := kindOf ci
                      directSorry := isSor, childCount := kdeps
                      extCount := cs.size - kdeps
                      depth := d, generated := isGeneratedDecl (moduleOf env n) n }
                  { r with nodes := r.nodes.push row }
                else r
              go fuel (newOnes ++ rest) seen
                { r with parents, total := r.total + 1 }
  go 10000000 [(root, 0)] {} {}

/-- env 中全部 Kepler 声明数（COVERAGE 分母）。 -/
def keplerUniverseSize (env : Environment) : Nat :=
  env.constants.fold (fun acc n _ => if isKeplerName n then acc + 1 else acc) 0

/-- 口径 II：`Kepler.Interval.Cases.*` 之外的 env Kepler 声明数。 -/
def keplerUniverseSizeXCases (env : Environment) : Nat :=
  env.constants.fold
    (fun acc n _ => if isKeplerName n && !isCasesModule (moduleOf env n) then acc + 1 else acc) 0

def defaultRoot : Name := `Kepler.Assembly.the_kepler_conjecture_from_interfaces

#eval show CoreM Unit from do
  let env ← getEnv
  let root ← match ← IO.getEnv "REACH_ROOT" with
    | some s => pure (parseName s)
    | none => pure defaultRoot
  let dump := (← IO.getEnv "DUMP_TREE").isSome
  let r := reach env root dump
  let univ := if dump then 0 else keplerUniverseSize env
  IO.println s!"ROOT {root}"
  IO.println s!"K_REACH {r.kReach}"
  IO.println s!"K_SORRIED {r.sorries.size}"
  IO.println s!"K_AXIOM {r.axioms.size}"
  IO.println s!"K_MODULES {r.modules.size}"
  if dump then
    IO.println "K_UNIVERSE SKIPPED_DUMP_TREE"
    IO.println "COVERAGE SKIPPED_DUMP_TREE"
    IO.println "K_UNIVERSE_XCASES SKIPPED_DUMP_TREE"
  else
    IO.println s!"K_UNIVERSE {univ}"
    IO.println s!"COVERAGE {r.kReach} / {univ}"
    IO.println s!"K_UNIVERSE_XCASES {keplerUniverseSizeXCases env}"
  let xreach := r.moduleCounts.fold (fun acc m c => if isCasesModule m then acc else acc + c) 0
  let xsor := r.sorries.foldl (fun acc (_, m) => if isCasesModule m then acc else acc + 1) 0
  let xax := r.axioms.foldl (fun acc (_, m) => if isCasesModule m then acc else acc + 1) 0
  IO.println s!"K_REACH_XCASES {xreach}"
  IO.println s!"K_SORRIED_XCASES {xsor}"
  IO.println s!"K_AXIOM_XCASES {xax}"
  IO.println s!"TOTAL_VALUE_DECLS {r.total}"
  IO.println s!"LEGACY_TOTAL_REACHABLE_KEPLER_DECLS {r.total}"
  IO.println s!"SORRIED {r.sorries.size}"
  IO.println s!"AXIOMS {r.axioms.size}"
  IO.println "--- SORRIED ---"
  for (n, m) in r.sorries.qsort (fun a b => a.1.toString < b.1.toString) do
    let p := r.parents.getD n n
    IO.println s!"{m}\t{n}\tparent={p}"
  IO.println "--- AXIOMS ---"
  for (n, m) in r.axioms.qsort (fun a b => a.1.toString < b.1.toString) do
    IO.println s!"{m}\t{n}"
  if dump then
    let counts := r.parents.fold
      (fun acc _child parent => acc.insert parent (acc.getD parent 0 + 1))
      ({} : Std.HashMap Name Nat)
    let agg := r.nodes.foldl
      (fun acc row =>
        let m := row.module
        let (cnt, sor, md) := acc.getD m (0, 0, 0)
        acc.insert m (cnt + 1, sor + (if row.directSorry then 1 else 0), max md row.depth))
      ({} : Std.HashMap Name (Nat × Nat × Nat))
    let arr := agg.toArray
    IO.println "--- MODULE TOP30 BY NODES ---"
    IO.println "module\tnodes\tsorries\tmaxDepth\tgenerated"
    for (m, (cnt, sor, md)) in (arr.qsort (fun a b => a.2.1 > b.2.1)).extract 0 30 do
      IO.println s!"{m}\t{cnt}\t{sor}\t{md}\t{isGeneratedModule m}"
    IO.println "--- MODULE TOP10 BY SORRIES ---"
    IO.println "module\tsorries\tnodes\tmaxDepth\tgenerated"
    for (m, (cnt, sor, md)) in (arr.qsort (fun a b => a.2.2.1 > b.2.2.1)).extract 0 10 do
      IO.println s!"{m}\t{sor}\t{cnt}\t{md}\t{isGeneratedModule m}"
    IO.println s!"TREE_ROWS {r.nodes.size}"
    IO.println "--- TREE ---"
    IO.println "name\tmodule\tkind\tdirectSorryAx\tparent\tchildCount\textCount\tdepth\tgenerated\ttreeChildCount"
    for row in r.nodes do
      let p := match r.parents.get? row.name with
        | some p => p.toString
        | none => ""
      let tcc := counts.getD row.name 0
      IO.println s!"{row.name}\t{row.module}\t{row.kind}\t{row.directSorry}\t{p}\t{row.childCount}\t{row.extCount}\t{row.depth}\t{row.generated}\t{tcc}"
  if !dump then
    IO.println "--- MODULE HISTOGRAM ---"
    for (m, c) in r.moduleCounts.toArray.qsort
        (fun a b => a.2 > b.2 || (a.2 == b.2 && a.1.toString < b.1.toString)) do
      IO.println s!"{c}\t{m}"
  IO.println "--- END ---"
