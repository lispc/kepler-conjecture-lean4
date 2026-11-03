/-
  global_reach_map.lean — 全局可达图（多根）指标 v2（2026-11-03）

  根集合（ROOTS）：
    1. e2e 根 `Kepler.Assembly.the_kepler_conjecture_from_interfaces`；
    2. `Kepler.Text.PackingConcl` 模块内全部 `*_discharged`（自动枚举，
       典型 61 条 `*_concl_discharged` / `*_version2_discharged`）；
    3. `Kepler.Text.LocalConcl` 模块内全部 `*_discharged`（自动枚举，92 条）；
    4. 章 capstone 手动清单（当前：PA25 `OXLZLEZ`、
       PA25 `PACKING_CHAPTER_MAIN_CONCLUSION`；不存在的根打印 ROOT_SKIP）。

  指标（每根 + union）：
    - K_REACH    distinct 可达 Kepler 声明数（树节点；含 axiom/opaque）
    - K_SORRIED  值里直接含 `sorryAx` 的可达声明数（信息项）
    - K_AXIOM    可达 Kepler 公理数（护栏；含 native_decide ax_*）
    - K_MODULES  可达声明所在的不同模块数
    - K_UNIVERSE env 中全部 Kepler 声明数（COVERAGE 分母）
    - COVERAGE   union K_REACH / K_UNIVERSE
  另有：
    - ORPHANS：env 中 Kepler 声明但不在 union 树内的（前 50 条 + 总数）
    - SHIMS：union 树内每个 `Kepler.Text.*_concl`，若存在
      `*_concl_discharged` 或 `*_discharged` 则计为 shim（列名字 + 是否
      sorried，供人工核）

  用法（standalone，不用 lake；先确保 olean = HEAD 态，见 docs §仪器校准）：
    LEAN_PATH=<scratch-lib>:$(cat /tmp/lfainteg/asm_check/leanpath.txt) \
      lean lean/scripts/global_reach_map.lean > /tmp/global_reach.out
  测试用：`GLOBAL_ROOTS_LIMIT=3` 只跑前 3 个根（按枚举顺序，0 = 全跑）。

  口径：静态 proof-term 遍历；`ConstantInfo.value? true`；只跟踪
  `Kepler.*` / `_private.Kepler.*`；「树」只认 proof-term 可达，不认 import
  闭包（ORPHANS 就是 import 闭包减去树）。
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

structure Counts where
  kReach : Nat := 0
  total : Nat := 0
  sorried : Array Name := #[]
  axioms : Array Name := #[]
  modules : Std.HashSet Name := {}
  /-- union 专用：树节点名字集合 -/
  names : Std.HashSet Name := {}
deriving Inhabited

/-- 从多个根同时 BFS。`collect = true` 时保留全部树节点名字（union 用）。 -/
partial def reachMany (env : Environment) (roots : Array Name) (collect : Bool) : Counts :=
  let rec go (fuel : Nat) (stack : List Name) (seen : Std.HashSet Name)
      (c : Counts) : Counts :=
    match fuel with
    | 0 => c
    | fuel + 1 =>
      match stack with
      | [] => c
      | n :: rest =>
        if seen.contains n then
          go fuel rest seen c
        else
          let seen := seen.insert n
          match env.find? n with
          | none => go fuel rest seen c
          | some ci =>
            let isK := isKeplerName n
            let c :=
              if isK then
                { c with
                  kReach := c.kReach + 1
                  modules := c.modules.insert (moduleOf env n)
                  names := if collect then c.names.insert n else c.names }
              else c
            match ci.value? true with
            | none =>
              let c :=
                if isK then
                  match ci with
                  | .axiomInfo _ => { c with axioms := c.axioms.push n }
                  | _ => c
                else c
              go fuel rest seen c
            | some v =>
              let cs := v.getUsedConstants
              let isSor := cs.any isSorryAx
              let c :=
                if isSor && isK then
                  { c with sorried := c.sorried.push n }
                else c
              let newOnes := cs.foldl (init := ([] : List Name))
                (fun ns x => if isKeplerName x && !seen.contains x then x :: ns else ns)
              go fuel (newOnes ++ rest) seen { c with total := c.total + 1 }
  go 10000000 roots.toList {} {}

structure Enumerated where
  packingConcl : Array Name := #[]
  localConcl : Array Name := #[]
deriving Inhabited

/-- 枚举 `PackingConcl` / `LocalConcl` 模块内的 `*_discharged` 声明。 -/
def enumerateRoots (env : Environment) : Enumerated :=
  env.constants.fold
    (fun acc n _ =>
      if (lastNamePart n).endsWith "_discharged" then
        let m := moduleOf env n
        if m == `Kepler.Text.PackingConcl then
          { acc with packingConcl := acc.packingConcl.push n }
        else if m == `Kepler.Text.LocalConcl then
          { acc with localConcl := acc.localConcl.push n }
        else acc
      else acc)
    {}

def dedup (a : Array Name) : Array Name :=
  let (_, out) := a.foldl (init := (({} : Std.HashSet Name), (#[] : Array Name)))
    (fun (st : Std.HashSet Name × Array Name) n =>
      let (seen, out) := st
      if seen.contains n then st else (seen.insert n, out.push n))
  out

/-- 该声明值里是否直接含 sorryAx（用于 SHIMS 标注）。 -/
def isSorriedDecl (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some ci =>
    match ci.value? true with
    | some v => v.getUsedConstants.any isSorryAx
    | none => false
  | none => false

def mainRun : CoreM Unit := do
  let env ← getEnv
  let e2e : Name := `Kepler.Assembly.the_kepler_conjecture_from_interfaces
  let manual : Array Name := #[
    `Kepler.Text.OXLZLEZ,
    `Kepler.Text.PACKING_CHAPTER_MAIN_CONCLUSION]
  let enum := enumerateRoots env
  let pck := sortNames enum.packingConcl
  let loc := sortNames enum.localConcl
  IO.println s!"ROOTS_PACKINGCONCL_ENUMERATED {pck.size}"
  IO.println s!"ROOTS_LOCALCONCL_ENUMERATED {loc.size}"
  let mut manualPresent : Array Name := #[]
  for n in manual do
    if (env.find? n).isSome then
      manualPresent := manualPresent.push n
    else
      IO.println s!"ROOT_SKIP {n} (not found in env)"
  IO.println s!"ROOTS_CAPSTONE_MANUAL_PRESENT {manualPresent.size} / {manual.size}"
  let roots := dedup (#[e2e] ++ manualPresent ++ pck ++ loc)
  IO.println s!"ROOTS_TOTAL {roots.size}"
  IO.println "--- PER-ROOT ---"
  let limit : Nat :=
    match ← IO.getEnv "GLOBAL_ROOTS_LIMIT" with
    | some s => (s.toNat?.getD 0)
    | none => 0
  let rootsToRun := if limit == 0 then roots else roots.extract 0 (min limit roots.size)
  if limit != 0 then IO.println s!"ROOTS_LIMIT_APPLIED {rootsToRun.size} / {roots.size}"
  for r in rootsToRun do
    let c := reachMany env #[r] false
    IO.println s!"ROOT {r}\tK_REACH {c.kReach}\tK_SORRIED {c.sorried.size}\tK_AXIOM {c.axioms.size}\tK_MODULES {c.modules.size}\tTOTAL_VALUE_DECLS {c.total}"
  IO.println "--- UNION ---"
  let u := reachMany env roots true
  let univ := env.constants.fold (fun acc n _ => if isKeplerName n then acc + 1 else acc) 0
  IO.println s!"UNION K_REACH {u.kReach}"
  IO.println s!"UNION K_SORRIED {u.sorried.size}"
  IO.println s!"UNION K_AXIOM {u.axioms.size}"
  IO.println s!"UNION K_MODULES {u.modules.size}"
  IO.println s!"UNION TOTAL_VALUE_DECLS {u.total}"
  IO.println s!"K_UNIVERSE {univ}"
  IO.println s!"COVERAGE {u.kReach} / {univ}"
  IO.println "--- UNION SORRIED ---"
  for n in sortNames u.sorried do
    IO.println s!"{moduleOf env n}\t{n}"
  IO.println "--- UNION AXIOMS ---"
  for n in sortNames u.axioms do
    IO.println s!"{moduleOf env n}\t{n}"
  IO.println "--- ORPHANS ---"
  let orphans := env.constants.fold
    (fun acc n _ => if isKeplerName n && !u.names.contains n then acc.push n else acc)
    (#[] : Array Name)
  let orphansSorted := sortNames orphans
  let publicCount := orphansSorted.foldl
    (fun acc n => if (n.toString).startsWith "Kepler." then acc + 1 else acc) 0
  IO.println s!"ORPHANS_TOTAL {orphansSorted.size}"
  IO.println s!"ORPHANS_PUBLIC {publicCount}"
  IO.println s!"ORPHANS_PRIVATE {orphansSorted.size - publicCount}"
  IO.println "--- ORPHANS FIRST 50 ---"
  for n in orphansSorted.extract 0 (min 50 orphansSorted.size) do
    IO.println s!"{moduleOf env n}\t{n}"
  IO.println "--- SHIMS ---"
  let mut shims : Array (Name × Name × Bool) := #[]
  for n in u.names.toList do
    let last := lastNamePart n
    if last.endsWith "_concl" then
      let s := n.toString
      let c1 := parseName (s ++ "_discharged")
      let c2base := (s.dropEnd "_concl".length).copy
      let c2 := parseName (c2base ++ "_discharged")
      match env.find? c1 with
      | some _ => shims := shims.push (n, c1, isSorriedDecl env n)
      | none =>
        match env.find? c2 with
        | some _ => shims := shims.push (n, c2, isSorriedDecl env n)
        | none => pure ()
  let shimsSorted := shims.qsort (fun a b => a.1.toString < b.1.toString)
  let shimsSorried := shimsSorted.foldl (fun acc t => if t.2.2 then acc + 1 else acc) 0
  IO.println s!"SHIMS_TOTAL {shimsSorted.size}"
  IO.println s!"SHIMS_SORRIED {shimsSorried}"
  for (concl, dis, sor) in shimsSorted do
    IO.println s!"SHIM {concl}\t-> {dis}\tsorried={sor}"
  IO.println "--- END ---"

#eval show CoreM Unit from mainRun
