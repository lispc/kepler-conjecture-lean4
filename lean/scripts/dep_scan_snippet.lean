-- dep_scan_snippet.lean — 追加到模块源码副本末尾，扫描当前模块常量的
-- Kepler→Kepler 直接依赖边 + 本常量字面 taint。import 后 value? 被擦除，
-- 故必须在模块自身 elaboration 环境内读取（census v3 管线第 1 段）。
open Lean Elab Command
private partial def depScanExprConsts (e : Expr) (s : NameSet) : NameSet :=
  match e with
  | .const n _ => s.insert n
  | .app f a => depScanExprConsts a (depScanExprConsts f s)
  | .lam _ t b _ => depScanExprConsts t (depScanExprConsts b s)
  | .forallE _ t b _ => depScanExprConsts t (depScanExprConsts b s)
  | .letE _ t v b _ => depScanExprConsts t (depScanExprConsts v (depScanExprConsts b s))
  | .mdata _ e => depScanExprConsts e s
  | .proj _ _ e => depScanExprConsts e s
  | _ => s

/-- 名字链深处是否含 `_private` 组件（Name 是从尾往头的链表，顶层 constructor
是最末组件，递归降到基）。 -/
private partial def depScanIsPriv : Name → Bool
  | .str p s => s == "_private" || depScanIsPriv p
  | .num p _ => depScanIsPriv p
  | _ => false

open Lean Elab Command
-- v2 (2026-10-08): private 声明的 Mangling 名(_private.<mod>.0.<全名>)带 `_`
-- 前缀, Name.isInternal 判真——v1 把全部 private 节点/边当内部名丢弃(近期
-- 工作全是 private 引理搭桥), 致 taint 图缺边且 census 少计 private tainted。
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut nE := 0
  for (n, ci) in env.constants.toList do
    if env.getModuleIdxFor? n |>.isSome then continue
    if n.isInternal && !(depScanIsPriv n) then continue
    let mut s : NameSet := {}
    s := depScanExprConsts ci.type s
    match ci.value? with
    | some v => s := depScanExprConsts v s
    | none => pure ()
    let keps := s.toList.filter (fun d =>
      (((`Kepler).isPrefixOf d) || depScanIsPriv d) && !(d == n))
    let axs ← Lean.collectAxioms n
    let taint := axs.contains `sorryAx
    if taint || !keps.isEmpty then
      nE := nE + 1
      let ti : Nat := if taint then 1 else 0
      let ds : String := String.intercalate ";" (keps.map toString)
      IO.println s!"DEP\t{n}\t{ti}\t{ds}"
  IO.println s!"SCAN_DONE {nE}"
