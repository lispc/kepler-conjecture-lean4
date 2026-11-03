/-
export_e2e_tree.lean — e2e 数学层定理树导出器（2026-11-03）

从 Kepler.Assembly.the_kepler_conjecture_from_interfaces 出发，沿 proof-term
的 Kepler 依赖遍历；机械证书层（Interval.Cases / Graphs.CertShards / Shard /
CertTri..Hex）折叠为叶子，不展开其内部 200 万节点。

输出 TSV：
  name	module	kind	directSorryAx	parent	childCount	extCount	treeChildCount	generated
  E	parent	child          （DAG 边）
用法：
  cd lean
  LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt)     lean scripts/export_e2e_tree.lean > /tmp/e2e-tree-math.tsv
-/
import Kepler.Assembly

open Lean

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def isK (n : Name) : Bool :=
  let s := n.toString
  s.startsWith "Kepler." || s.startsWith "_private.Kepler."

def isSorry (n : Name) : Bool := n == `sorryAx || n == `Lean.sorryAx

def isGeneratedModule (m : Name) : Bool :=
  let s := m.toString
  s.contains "Interval.Cases" || s.contains "Graphs.CertShards" ||
  s.contains "Shard" || s.contains "CertTri" || s.contains "CertQuad" ||
  s.contains "CertPent" || s.contains "CertHex"

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none =>
    match n with
    | .str p _ => p
    | _ => n

def kindOf (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

structure Out where
  kNodes : Std.HashSet Name := {}
  parents : Std.HashMap Name Name := {}
  childCount : Std.HashMap Name Nat := {}
  childrenMap : Std.HashMap Name (List Name) := {}
  sorries : Std.HashSet Name := {}
deriving Inhabited

partial def collect (env : Environment) (root : Name) : Out :=
  let rec go (fuel : Nat) (stack : List Name) (seen : Std.HashSet Name) (o : Out) : Out :=
    match fuel with
    | 0 => o
    | fuel + 1 =>
      match stack with
      | [] => o
      | n :: rest =>
        if seen.contains n then go fuel rest seen o
        else
          let seen := seen.insert n
          match env.find? n with
          | none => go fuel rest seen o
          | some ci =>
            let o := if isK n then { o with kNodes := o.kNodes.insert n } else o
            -- 机械证书层：保留为叶子（不展开其证明项），否则 2M 节点会拖死浏览器/导出
            if isK n && isGeneratedModule (moduleOf env n) then
              let o := { o with childCount := o.childCount.insert n 0 }
              go fuel rest seen o
            else
              match ci.value? true with
              | none => go fuel rest seen o
              | some v =>
                let cs := v.getUsedConstants
                let kcs := cs.foldl (init := ([] : List Name))
                  (fun acc c => if isK c then c :: acc else acc)
                let o :=
                  if isK n then
                    let o := if cs.any isSorry then { o with sorries := o.sorries.insert n } else o
                    { o with childCount := o.childCount.insert n kcs.length,
                             childrenMap := o.childrenMap.insert n kcs }
                  else o
                let (o, newOnes) := kcs.foldl (init := (o, ([] : List Name)))
                  (fun (acc : Out × List Name) c =>
                    let (o, ns) := acc
                    if seen.contains c then (o, ns)
                    else
                      let par := if o.parents.contains c then o.parents else o.parents.insert c n
                      ({ o with parents := par }, c :: ns))
                go fuel (newOnes ++ rest) seen o
  go 10000000 [root] {} {}

#eval show CoreM Unit from do
  let env ← getEnv
  let root : Name := `Kepler.Assembly.the_kepler_conjecture_from_interfaces
  let o := collect env root
  IO.println "name\tmodule\tkind\tdirectSorryAx\tfirstBFS parent\tchildCount\textCount\ttreeChildCount\tgenerated"
  for n in o.kNodes.toList do
    match env.find? n with
    | none => pure ()
    | some ci =>
      let p := o.parents.getD n n
      let ps := if p == n then "-" else p.toString
      let sc := if o.sorries.contains n then "1" else "0"
      let cc := o.childCount.getD n 0
      let gen := if isGeneratedModule (moduleOf env n) then "1" else "0"
      IO.println s!"{n}\t{moduleOf env n}\t{kindOf ci}\t{sc}\t{ps}\t{cc}\t0\t0\t{gen}"
  for (p, cs) in o.childrenMap.toList do
    for c in cs do
      IO.println s!"E\t{p}\t{c}"
