/-
reachable_census.lean — 会师仪表盘 v2（2026-10-10，M5″ 工具）。
命令上下文全量普查：每个常量经 `Lean.collectAxioms`（olean 预计算表查询）
判 sorryAx-tainted，按模块聚合；另列 e2e 主定理的 axiom 面。
用法：`cd lean && lake env lean scripts/reachable_census.lean`（纯只读）。
-/
import Kepler.Final
import Lean

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut names : Array Name := #[]
  for md in env.header.moduleData do
    names := names.append md.constNames
  let mut tainted : Std.HashMap Name Nat := {}
  let mut nTainted := 0
  let mut nTotal := 0
  for n in names do
    if n.isInternal then continue
    nTotal := nTotal + 1
    let axs ← Lean.collectAxioms n
    if axs.contains `sorryAx then
      nTainted := nTainted + 1
      let mname : Name :=
        match env.getModuleIdxFor? n with
        | some midx => env.header.moduleNames[midx.toNat]!
        | none => Name.mkSimple "unknown"
      tainted := tainted.insert mname (tainted.getD mname 0 + 1)
  logInfo s!"total constants: {nTotal}"
  logInfo s!"sorryAx-tainted constants: {nTainted}"
  let mut rows : Array (Name × Nat) := tainted.toArray
  IO.println "| 模块 | tainted 常量 |"
  IO.println "|---|---|"
  for (m, k) in rows.qsort fun a b => a.2 > b.2 do
    IO.println s!"| {m} | {k} |"
  let e2e ← Lean.collectAxioms `Kepler.the_kepler_conjecture_e2e
  logInfo s!"e2e axiom face: {e2e}"
