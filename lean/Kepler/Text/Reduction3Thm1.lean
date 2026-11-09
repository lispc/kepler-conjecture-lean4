/-
  Kepler.Text.Reduction3Thm1 — J 战役 J3 定理层 T1 批（小引理层，reduction3.hl:198-380）。

  ┌─ 批次定位 ────────────────────────────────────────────────────
  │ 定义层 D1-D3 全落（0785ce0e / c2c8ffce / 913b31d5）后的定理层首口。
  │ T1 = reduction3.hl 的「小引理层」:198-380 中**依赖最少**的 12 件：
  │   PAIR_EQ3                :198 → pairEq3
  │   take_el                 :214 → takeEl
  │   butlast_rcons           :223 → butlastRcons
  │   take1                   :235 → take1
  │   LAMBDA_TRIPLE           :243 → lambdaTriple
  │   foldl_flatten           :248 → foldlFlatten
  │   flatten_rcons_flatten   :257 → flattenRconsFlatten
  │   trans_add                :277 → transAdd
  │   rtrans1                  :331 → rtrans1
  │   nseq0                    :344 → nseqZero
  │   nseq_suc                 :352 → nseqSucc
  │   el_nseq                  :369 → elNseq
  │ 本批未含（依赖缺口/定义性平凡，见 DELIVERY §9 表）：
  │   upt_iota_simple :206 / REPLICATE_nseq :360 —— Lean 侧 `upt=iota=range'`、
  │     `nseq=replicate` 同一定义，陈述退化为 rfl（无证明内容，不另立件）；
  │   min_num_translate :291 —— 挂 T2（需 minNum 规格引理）；
  │   AQ6_INDUCT :265 —— BLOCKED：需 Spine marked_list（TameList13）+
  │     Reduction2.transform_assumption_v2_lemma（j2w1 批 E，未落）。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与实例纪律 ──────────────────────────────────────────────
  │ imports = `Kepler.Text.Reduction3DefsAssumption`（D3b，闭包含 D1-D3a）。
  │ `nseq` ↦ `List.replicate`、`rcons l z` ↦ `l ++ [z]`、`flatten` ↦
  │ `List.flatten`、`EL i l` ↦ `l.getElem i h`（在界证明入型）、
  │ `take`/`foldl`/`POWER` ↦ `List.take`/`List.foldl`/`Function.iterate`。
  │ 闭包零 `Kepler.Assembly` 主模块、零 TameSpine。零 axiom/sorry/
  │ admit/native_decide。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3DefsAssumption

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (findFaceDarts prevEl)
open Kepler.Graphs (fgraph)
open Kepler.Text.Reduction5 (Dart finalList lz ly ntrans rtrans splitNormalList
  transformList ytrans ztrans)

/-! ## §A 纯列表/元组层（:198-257） -/

/-- HOL `PAIR_EQ3`（reduction3.hl:198）：三元组外延等式拆分。 -/
theorem pairEq3 {α β γ : Type} (a b : α × β × γ) :
    a = b ↔ a.1 = b.1 ∧ a.2.1 = b.2.1 ∧ a.2.2 = b.2.2 := by
  rcases a with ⟨a1, a2, a3⟩
  rcases b with ⟨b1, b2, b3⟩
  simp [Prod.mk.injEq]

/-- HOL `take_el`（reduction3.hl:214）：
`n < sizel s ==> take (SUC n) s = rcons (take n s) (EL n s)`。 -/
theorem takeEl {α : Type} (s : List α) {n : ℕ} (h : n < s.length) :
    s.take (n + 1) = s.take n ++ [s[n]'h] :=
  List.take_succ_eq_append_getElem h

/-- HOL `butlast_rcons`（reduction3.hl:223）：`butlast (rcons xs x) = xs`。 -/
theorem butlastRcons {α : Type} (xs : List α) (x : α) :
    (xs ++ [x]).dropLast = xs :=
  List.dropLast_concat

/-- HOL `take1`（reduction3.hl:235）：`~(xs=[]) ==> take 1 xs = [HD xs]`。 -/
theorem take1 {α : Type} (xs : List α) (h : xs ≠ []) (d : α) :
    xs.take 1 = [xs.headD d] := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons a t => rfl

/-- HOL `LAMBDA_TRIPLE`（reduction3.hl:243）：三元模式 lambda 的投影展开形。 -/
theorem lambdaTriple {α β γ δ : Type} (P : α → β → γ → δ) :
    (fun (p : α × β × γ) => match p with | (x, y, z) => P x y z) =
    (fun p => P p.1 p.2.1 p.2.2) := by
  funext p
  rcases p with ⟨x, y, z⟩
  rfl

/-! ## §B foldl / flatten 组合层（:248-257） -/

/-- HOL `foldl_flatten`（reduction3.hl:248）：
`foldl (foldl f) a lls = foldl f a (flatten lls)`。 -/
theorem foldlFlatten {α β : Type} (lls : List (List α)) (f : β → α → β) (a : β) :
    lls.foldl (fun acc l => l.foldl f acc) a = lls.flatten.foldl f a := by
  induction lls generalizing a with
  | nil => rfl
  | cons l ls ih => simp [List.foldl_append, ih]

/-- HOL `flatten_rcons_flatten`（reduction3.hl:257）：
`flatten (rcons A (flatten B)) = flatten (flatten A :: B)`。 -/
theorem flattenRconsFlatten {α : Type} (A B : List (List α)) :
    (A ++ [B.flatten]).flatten = (A.flatten :: B).flatten := by
  simp [List.flatten_append]

/-! ## §C transform 塔层（:277-331） -/

/-- HOL `trans_add`（reduction3.hl:277）：transform 塔的四投影加性
（`POWER (b+a) = POWER b ∘ POWER a`，`Function.iterate_add_apply` 直投）。 -/
theorem transAdd (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
    (a b : ℕ) :
    ntrans L N r x (b + a) = ntrans L (ntrans L N r x a) (rtrans L N r x a) x b ∧
    rtrans L N r x (b + a) = rtrans L (ntrans L N r x a) (rtrans L N r x a) x b ∧
    ytrans L N r x (b + a) = ytrans L (ntrans L N r x a) (rtrans L N r x a) x b ∧
    ztrans L N r x (b + a) = ztrans L (ntrans L N r x a) (rtrans L N r x a) x b := by
  have h := Function.iterate_add_apply (transformList L x) b a (N, r)
  simp [ntrans, rtrans, ytrans, ztrans, h]

/-- HOL `rtrans1`（reduction3.hl:331）：非 final 时一步 `rtrans` 的展开形
（`transform_list` 的 else 支 → `split_normal_list` 的第二片）。
**名字消歧**：`Kepler.Text.ly`（SphereKit，ℝ→ℝ）在父命名空间遮蔽
`Reduction5.ly`，故此处全限定。 -/
theorem rtrans1 (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
    (h : ¬ finalList L r) :
    rtrans L N r x 1 =
      (splitNormalList L r (findFaceDarts L (Kepler.Text.Reduction5.ly L r x))
        (Kepler.Text.Reduction5.ly L r x) (prevEl r (lz L N r x))).2 := by
  simp [rtrans, transformList, h]

/-! ## §D nseq 层（:344-369；`nseq` ↦ `List.replicate`） -/

/-- HOL `nseq0`（reduction3.hl:344）：`nseq 0 x = []`。 -/
theorem nseqZero {α : Type} (x : α) : List.replicate 0 x = [] := rfl

/-- HOL `nseq_suc`（reduction3.hl:352）：`nseq (SUC n) x = x :: nseq n x`。 -/
theorem nseqSucc {α : Type} (n : ℕ) (x : α) :
    List.replicate (n + 1) x = x :: List.replicate n x :=
  List.replicate_succ

/-- HOL `el_nseq`（reduction3.hl:369）：`i < n ==> EL i (nseq n x) = x`
（在界前提入型，`EL` ↦ getElem 记号）。 -/
theorem elNseq {α : Type} (n : ℕ) (x : α) {i : ℕ} (h : i < n) :
    (List.replicate n x)[i]'(by simpa using h) = x := by
  simp

end Kepler.Text.Reduction3

-- 公理探针（编译即执行；目标标准三，零 sorryAx）
#print axioms Kepler.Text.Reduction3.pairEq3
#print axioms Kepler.Text.Reduction3.takeEl
#print axioms Kepler.Text.Reduction3.butlastRcons
#print axioms Kepler.Text.Reduction3.take1
#print axioms Kepler.Text.Reduction3.lambdaTriple
#print axioms Kepler.Text.Reduction3.foldlFlatten
#print axioms Kepler.Text.Reduction3.flattenRconsFlatten
#print axioms Kepler.Text.Reduction3.transAdd
#print axioms Kepler.Text.Reduction3.rtrans1
#print axioms Kepler.Text.Reduction3.nseqZero
#print axioms Kepler.Text.Reduction3.nseqSucc
#print axioms Kepler.Text.Reduction3.elNseq
