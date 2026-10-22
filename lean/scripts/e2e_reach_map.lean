/-
  e2e_reach_map.lean — 主定理 e2e 可达性地图（2026-10-22）

  从 `Kepler.Assembly.the_kepler_conjecture_from_interfaces` 出发，遍历
  proof-term 的常量依赖（只跟踪 `Kepler.*` / `_private.Kepler.*`），输出：
    - TOTAL_REACHABLE_KEPLER_DECLS：可达 Kepler 声明数；
    - SORRIED：值里直接含 `sorryAx` 的可达声明（即 e2e 债务源）；
    - AXIOMS：可达的 Kepler 公理（含 native_decide 生成的 *_native_decide.ax_*）；
    - 每个 sorry 源的第一个 BFS 父声明（parent=...），用于定位消费路径。

  用法（首次会重建 Assembly olean）：
    cd lean && lake env lean scripts/e2e_reach_map.lean > /tmp/reachmap.out
  典型落库：
    cp /tmp/reachmap.out docs/e2e-reachability-map.tsv

  口径：静态 proof-term 遍历；`ConstantInfo.value? true`（theorem/opaque 值都
  展开，与 `#print axioms` 的闭包一致）；父边是首次 BFS 命中，不是唯一父。
  624 条可达公理与 DEBT.md 2026-10-21 脊柱探针的 624 完全一致，可作为
  遍历正确性的交叉验证。
-/
import Kepler.Assembly

open Lean

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def isKeplerName (n : Name) : Bool :=
  let s := n.toString
  s.startsWith "Kepler." || s.startsWith "_private.Kepler."

def isSorryAx (n : Name) : Bool :=
  n == `sorryAx || n == `Lean.sorryAx

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none =>
    match n with
    | .str p _ => p
    | _ => n

structure MapResult where
  total : Nat
  sorries : Array (Name × Name)
  axioms : Array (Name × Name)
  parents : Std.HashMap Name Name
deriving Inhabited

partial def reach (env : Environment) (root : Name) : MapResult :=
  let rec go (fuel : Nat) (stack : List Name) (seen : Std.HashSet Name)
      (sorries axioms : Array (Name × Name)) (parents : Std.HashMap Name Name)
      (total : Nat) : MapResult :=
    match fuel with
    | 0 => { total, sorries, axioms, parents }
    | fuel + 1 =>
      match stack with
      | [] => { total, sorries, axioms, parents }
      | n :: rest =>
        if seen.contains n then
          go fuel rest seen sorries axioms parents total
        else
          let seen := seen.insert n
          match env.find? n with
          | none => go fuel rest seen sorries axioms parents total
          | some ci =>
            match ci.value? true with
            | none =>
              let axioms :=
                if isKeplerName n then
                  match ci with
                  | .axiomInfo _ => axioms.push (n, moduleOf env n)
                  | _ => axioms
                else axioms
              go fuel rest seen sorries axioms parents total
            | some v =>
              let total := total + 1
              let cs := v.getUsedConstants
              let isSor := cs.any isSorryAx
              let sorries :=
                if isSor && isKeplerName n then sorries.push (n, moduleOf env n)
                else sorries
              let (parents, newOnes) := cs.foldl (init := (parents, ([] : List Name)))
                (fun (acc : Std.HashMap Name Name × List Name) c =>
                  let (par, ns) := acc
                  if isKeplerName c && !seen.contains c then
                    let par := if par.contains c then par else par.insert c n
                    (par, c :: ns)
                  else acc)
              go fuel (newOnes ++ rest) seen sorries axioms parents total
  go 10000000 [root] {} #[] #[] {} 0

#eval show CoreM Unit from do
  let env ← getEnv
  let root : Name := `Kepler.Assembly.the_kepler_conjecture_from_interfaces
  let r := reach env root
  IO.println s!"ROOT {root}"
  IO.println s!"TOTAL_REACHABLE_KEPLER_DECLS {r.total}"
  IO.println s!"SORRIED {r.sorries.size}"
  IO.println s!"AXIOMS {r.axioms.size}"
  IO.println "--- SORRIED ---"
  for (n, m) in r.sorries.qsort (fun a b => a.1.toString < b.1.toString) do
    let p := r.parents.getD n n
    IO.println s!"{m}\t{n}\tparent={p}"
  IO.println "--- AXIOMS ---"
  for (n, m) in r.axioms.qsort (fun a b => a.1.toString < b.1.toString) do
    IO.println s!"{m}\t{n}"
  IO.println "--- END ---"
