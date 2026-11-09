/-
  Kepler.Text.Reduction3Thm3 — J 战役 J3 定理层 T3 批（首段：列表机械面
  + `loop_choice2` 载体）。

  ┌─ 逐件对账（reduction3.hl）─────────────────────────────────────
  │   loop_choice2     tame_defs2.hl:722-730 → §0 loopChoice2（载体）
  │   el_core_triple   reduction3.hl:938     → §B elCoreTriple
  │   last_core_triple reduction3.hl:970     → §C lastCoreTriple
  │   dest_triple0_mem reduction3.hl:1125    → §A destTriple0Mem
  │ 三件均为**纯列表/迭代**证明（HOL 证明亦未消费 marked/is_restricted
  │ 内容——el/last_core_triple 的载体类前提仅用于 transform_count_non0，
  │ 本批以 h0 : transformCount ≠ 0 直给；批 E 落库后由
  │ `transformCountNon0`（T2）一行供给）。
  └────────────────────────────────────────────────────────────────

  ┌─ T3 剩余件裁定（侦察结论，缓 T4；AGENTS §7 不硬啃）────────────
  │ hd_vs_some_v（:998）/ last_vs_some_prev（:1067）：证明需
  │ `loop_choice2` 的 x = LAST(find_list p d) 与 minimalVertex v 的
  │ 关联理论（HOL 以 marked_list 合取 + betwn 等式链经 ASM_MESON 收口，
  │ Lean 侧需先落 `parts`/`find_list` 的 LAST 事实族），估 ~180 行，
  │ 非机械面——T4 前需专批侦察。
  │ sizel_3_concl（:846）：需 List_hypermap.mem_find_face +
  │ Pplhulj.marked_list_of_dart（链世界零命中）+ Tame_list.
  │ is_restricted_size_face（Spine 侧 TameList56:353 在册，新口径下
  │ 可跨岛引用但需单文件闭包核验）——挂 Spine 面大小事实批。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与实例纪律 ──────────────────────────────────────────────
  │ imports = `Kepler.Text.Reduction3Thm2`（定理层链）+ 
  │ `Kepler.Graphs.Plane1`（minimalFace/minimalVertex）+
  │ `Kepler.Graphs.ListAuxLemmas`（inbetween_inset）。零 axiom/sorry/
  │ admit/native_decide。junk：`LAST` ↦ `getLastD (0,0)`（非空守卫）；
  │ `the y` ↦ `y.getD 0`（isSome 守卫）。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm2
import Kepler.Text.ChainListsL1
import Kepler.Graphs.Plane1
import Kepler.Graphs.ListAuxLemmas

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (nextEl prevEl findFaceDarts)
open Kepler.Graphs (between fgraph Face Graph minimalFace minimalVertex nonFinals
  inbetween_inset)
open Kepler.Text.Reduction5 (Dart finalList parts transformCount ytrans ztrans)
open Kepler.Text.ChainLists (findList)

/-! ## §0 `loop_choice2`（tame_defs2.hl:722-730；T3/T4 共用载体）

`loop_choice2 g L N`：从 `g` 的非终面中取最小面、其最小顶点 `w`，
`v = prev_el f w`，`d = (v,w)`，`r = find_list N d`，第二分量 =
`parts L r` 中第一个含 `d` 的面的 `LAST`。 -/

/-- HOL `loop_choice2`（tame_defs2.hl:722-730）。 -/
noncomputable def loopChoice2 (g : Graph) (L : fgraph ℕ)
    (N : List (List Dart)) : List Dart × Dart :=
  let f := minimalFace (nonFinals g)
  let w := minimalVertex g f
  let v := prevEl f.vertices w
  let d : Dart := (v, w)
  let r := findList N d
  let p := parts L r
  (r, (findList p d).getLastD (0, 0))

/-! ## §A `dest_triple0_mem`（reduction3.hl:1125）

`dest_triple0` 输出中的每个 `some` 元素（值域）都落在 `f` 中，只要
初始段 `s` 的 `some` 元素落 `f`、且 `uvns` 诸三元的两端点在 `f` 中。
（`betwen` 段的成员性经 `inbetween_inset` ⊆ `f`。） -/

/-- `destTriple0` cons 展开方程（与 Thm2 私有件同体；此处复制以便本文件使用）。 -/
private theorem destTriple0_cons_eq (f : List ℕ) (s : List (Option ℕ)) (u v n : ℕ)
    (ts : List (ℕ × ℕ × ℕ)) :
    destTriple0 f s ((u, v, n) :: ts) =
      (let ns := List.replicate n (none : Option ℕ)
       if s = [] then destTriple0 f ([some u] ++ ns ++ [some v]) ts
       else
         let u0 := (s.getLastD none).getD 0
         if u0 = u then destTriple0 f (s ++ ns ++ [some v]) ts
         else if nextEl f u0 = u then
           destTriple0 f (s ++ [some u] ++ ns ++ [some v]) ts
         else
           destTriple0 f (s ++ (between f u0 u).map some ++ [some u] ++ ns
             ++ [some v]) ts) := rfl

/-- 成员不变量：`s` 中每个 `some` 元素的值在 `f` 中。 -/
private def okS (f : List ℕ) (s : List (Option ℕ)) : Prop :=
  ∀ y ∈ s, y.isSome → (y.getD 0) ∈ f

private theorem okS_append {f : List ℕ} {a b : List (Option ℕ)}
    (ha : okS f a) (hb : okS f b) : okS f (a ++ b) := by
  intro y hy hys
  rw [List.mem_append] at hy
  rcases hy with hy | hy
  · exact ha y hy hys
  · exact hb y hy hys

private theorem okS_some {f : List ℕ} {v : ℕ} (hv : v ∈ f) : okS f [some v] := by
  intro y hy _
  rw [List.mem_singleton] at hy
  subst hy
  simpa using hv

private theorem okS_none_rep (f : List ℕ) (n : ℕ) :
    okS f (List.replicate n (none : Option ℕ)) := by
  intro y hy hys
  rw [List.eq_of_mem_replicate hy] at hys
  simp at hys

private theorem okS_map_some {f g : List ℕ} (hb : ∀ z ∈ g, z ∈ f) :
    okS f (g.map some) := by
  intro y hy _
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
  simpa using hb z hz

/-- HOL `dest_triple0_mem`（reduction3.hl:1125）。 -/
theorem destTriple0Mem (uvns : List (ℕ × ℕ × ℕ)) :
    ∀ (f : List ℕ) (s : List (Option ℕ)) (x : Option ℕ),
      okS f s →
      (∀ uvn ∈ uvns, uvn.1 ∈ f ∧ uvn.2.1 ∈ f) →
      x.isSome → x ∈ destTriple0 f s uvns → (x.getD 0) ∈ f := by
  induction uvns with
  | nil =>
    intro f s x hs _ hx hmem
    exact hs x hmem hx
  | cons t ts ih =>
    obtain ⟨u, v, n⟩ := t
    intro f s x hs huvns hx hmem
    have ht := huvns (u, v, n) (List.mem_cons_self)
    have hu : u ∈ f := ht.1
    have hv : v ∈ f := ht.2
    have hts : ∀ uvn ∈ ts, uvn.1 ∈ f ∧ uvn.2.1 ∈ f :=
      fun uvn hu' => huvns uvn (List.mem_cons_of_mem _ hu')
    have hns : okS f (List.replicate n (none : Option ℕ)) := okS_none_rep f n
    rw [destTriple0_cons_eq] at hmem
    dsimp only at hmem
    by_cases h0 : s = []
    · rw [if_pos h0] at hmem
      exact ih f _ x (okS_append (okS_append (okS_some hu) hns) (okS_some hv))
        hts hx hmem
    · rw [if_neg h0] at hmem
      by_cases h1 : (s.getLastD none).getD 0 = u
      · rw [if_pos h1] at hmem
        exact ih f _ x (okS_append (okS_append hs hns) (okS_some hv)) hts hx hmem
      · rw [if_neg h1] at hmem
        by_cases h2 : nextEl f ((s.getLastD none).getD 0) = u
        · rw [if_pos h2] at hmem
          exact ih f _ x (okS_append (okS_append (okS_append hs (okS_some hu))
            hns) (okS_some hv)) hts hx hmem
        · rw [if_neg h2] at hmem
          exact ih f _ x (okS_append (okS_append (okS_append
            (okS_append hs (okS_map_some (fun z hz => inbetween_inset hz)))
            (okS_some hu)) hns) (okS_some hv)) hts hx hmem

/-! ## §B `el_core_triple`（reduction3.hl:938）

`i < transform_count` 时 `core_triple_v4` 的第 `i` 项 = `(yᵢ.1, zᵢ.1,
betwn 长)`——`triple_data_v4` 的 `range`/`map` 直算（HOL 用 EL_MAP +
el_iota）。**无条件**：载体类前提在 HOL 证明中只喂 transform_count>0，
而本结论的 `i < transform_count` 已直接给出在界。 -/

/-- HOL `el_core_triple`（reduction3.hl:938）。 -/
theorem elCoreTriple (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) (i : ℕ) (h : i < transformCount L N r x) :
    (coreTripleV4 L N r x)[i]'(by rw [coreTripleV4_length]; exact h)
      = ((ytrans L N r x i).1, (ztrans L N r x i).1,
         (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length) := by
  simp [coreTripleV4, tripleDataV4]

/-! ## §C `last_core_triple`（reduction3.hl:970）

`LAST (core_triple_v4 …) = (y_{k'}.1, z_{k'}.1, betwn 长)`，
`k' = PRE (transform_count)`。非空性以 `h0 : transformCount ≠ 0` 直给
（HOL 经 transform_count_non0 ← marked；批 E 后由 T2 的
`transformCountNon0` 代入）。 -/

/-- HOL `last_core_triple`（reduction3.hl:970）。 -/
theorem lastCoreTriple (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) (k' : ℕ) (h0 : transformCount L N r x ≠ 0)
    (hk : k' = transformCount L N r x - 1) :
    (coreTripleV4 L N r x).getLastD (0, 0, 0)
      = ((ytrans L N r x k').1, (ztrans L N r x k').1,
         (between (findFaceDarts L x) (ytrans L N r x k') (ztrans L N r x k')).length) := by
  have hlen : (coreTripleV4 L N r x).length = transformCount L N r x :=
    coreTripleV4_length L N r x
  have hpos : 0 < (coreTripleV4 L N r x).length := by
    rw [hlen]
    exact Nat.pos_of_ne_zero h0
  have hne : coreTripleV4 L N r x ≠ [] := by
    intro h
    rw [h] at hpos
    exact Nat.lt_irrefl 0 hpos
  have hidx : k' = (coreTripleV4 L N r x).length - 1 := by rw [hk, hlen]
  rw [hidx]
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne,
    List.getLast_eq_getElem hne, Option.getD_some]
  exact elCoreTriple L N r x ((coreTripleV4 L N r x).length - 1)
    (by rw [hlen]; omega)

end Kepler.Text.Reduction3

-- 公理探针（编译即执行）
#print axioms Kepler.Text.Reduction3.destTriple0Mem
#print axioms Kepler.Text.Reduction3.elCoreTriple
#print axioms Kepler.Text.Reduction3.lastCoreTriple
#check @Kepler.Text.Reduction3.loopChoice2
