/-
  Kepler.Text.Reduction3Thm5C — T5C 批：Aq12 `betwn_cap_point` 链侧重证 +
  T5 剩余 3 件 betwn 系（reduction3.hl:1665/:1742/:1767）。

  ┌─ 件目 ────────────────────────────────────────────────────────
  │ §A betwnCapPoint            AQ12.hl:987 → betwnCapPoint
  │ §B 私有 t5c_betwn_nil       Tame_list.betwn_nil（:13449）
  │    subdivSingleStepBetwn    reduction3.hl:1665 → subdivSingleStepBetwn
  │    subdivSingleStepInitialSeg :1742 → subdivSingleStepInitialSeg
  │    subdivSingleStepFinalSeg   :1767 → subdivSingleStepFinalSeg
  │ 子divDoubleSided 等 J2 件不在此列（betwn_cap_point 本身是纯列表事实，
  │ docs 续491 勘误同判）。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线差异（HOL 支撑 → Lean 现成件）───────────────────────────
  │ `betwn_cap_point` 不用 HOL 的 eq_last_next/betwn_cat_point_mem/
  │ uniq_betwn_cat_point/betwn_cat_point_last/LAST_cat 一路；直接特化
  │ `Kepler.Graphs.split_between`（ListAuxLemmas:414，强形：
  │ `(if r = u then [] else between vs r u ++ [u]) ++ between vs u v`）
  │ + `Reduction4.notBetwn1` 判负 if。语义逐字同 HOL。
  │ `uniq_betwn` ↦ `Kepler.Graphs.between_distinct`（本文件未直接消费）。
  │ `HD_BETWN2` **不需要**：改用 `Graphs.next_between`（nextVertex u ∈
  │ between u v）+ `TameSpine.nextVertexNextEl` + `betwnCapPoint` +
  │ `t5c_betwn_nil` 得 `between u v = some(nextEl u) :: between (nextEl u) v`
  │ 的用法（避免 HD 口径）。
  │ `size_induct` ↦ 核心 `Nat.strong_induction_on`（不自建）。
  └────────────────────────────────────────────────────────────────

  ┌─ 折算口径（DIFFERS）─────────────────────────────────────────
  │ `FST f` ↦ `f.vertices`；`uniq` ↦ `.Nodup`；`MEM` ↦ `∈`；
  │ `betwn` ↦ `Kepler.Graphs.between`；`MAP SOME` ↦ `.map some`；
  │ `rcons l x` ↦ `l ++ [x]`；`the` 不出现（`some v`/`prevEl` 直给）。
  │ betwnCapPoint 额外带 `[BEq α] [LawfulBEq α] [DecidableEq α]`（between 的
  │ 树内定义要求；ℕ/Dart 实例齐）。三件 betwn 系无 hfinal 槽（纯列表）。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行尾禁「减斜杠」；
  │ 公开件驼峰无前缀，私有件 `t5c_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3DefsLayer
import Kepler.Text.Reduction4
import Kepler.Graphs.ListAuxLemmas
import Kepler.Text.TameSpine.TameList3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (nextEl prevEl)
open Kepler.Graphs (Face Graph between)
open Kepler.Text.Reduction5 (Dart)
open Kepler.Text.TameLp (nextEl_mem_of_mem prevEl_mem_of_mem prevEl_nextEl nextEl_prevEl)

/-! ## §A `betwn_cap_point`（AQ12.hl:987） -/

/-- HOL `betwn_cap_point`（AQ12.hl:987）：
`uniq r ∧ l ∈ betwn r v v1 ∧ v ≠ v1 ∧ v ∈ r ∧ v1 ∈ r ⇒
betwn r v v1 = (betwn r v l ++ [l]) ++ betwn r l v1`。
由 `Kepler.Graphs.split_between`（切点形）特化 + `notBetwn1` 判负。 -/
theorem betwnCapPoint {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    {r : List α} {v v1 l : α} (hnd : r.Nodup) (hl : l ∈ between r v v1)
    (hvne : v ≠ v1) (hv : v ∈ r) (hv1 : v1 ∈ r) :
    between r v v1 = between r v l ++ [l] ++ between r l v1 := by
  have hvl : v ≠ l := fun h => Kepler.Text.TameSpine.notBetwn1 hnd hv1 (h ▸ hl)
  rw [Kepler.Graphs.split_between hnd hv hv1 hl, if_neg hvl]

/-! ## §B `betwn_nil` 私有 + 三件 betwn 系 -/

/-- HOL `betwn_nil`（tame_list.hl:13449）：
`uniq f ∧ a ≠ b ∧ a ∈ f ∧ b ∈ f ⇒ (betwn f a b = [] ↔ b = next_el f a)`。
链侧直证：`size_betwn` + `indexfOne`/`nextElIndexf` + `indexf0`（Spine 件）。 -/
private theorem t5c_betwn_nil {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    {f : List α} {a b : α} (hnd : f.Nodup) (hab : a ≠ b)
    (ha : a ∈ f) (hb : b ∈ f) :
    between f a b = [] ↔ b = nextEl f a := by
  have hlen2 : 1 < f.length := Kepler.Text.TameSpine.sizelGt1 ha hb hab
  have hne0 : Kepler.Text.TameSpine.indexf a b f ≠ 0 := fun h0 =>
    hab (Kepler.Text.TameSpine.indexfZeroEq ha hb h0)
  constructor
  · intro h
    have hsz := Kepler.Text.TameSpine.sizeBetwn hnd ha hb hab
    rw [h, List.length_nil] at hsz
    have hidx : Kepler.Text.TameSpine.indexf a b f = 1 := by omega
    exact (Kepler.Text.TameSpine.indexfOne ha hb hnd hidx).symm
  · intro h
    have hidx : Kepler.Text.TameSpine.indexf a b f = 1 := by
      rw [h]
      exact Kepler.Text.TameSpine.nextElIndexf ha (nextEl_mem_of_mem ha) hnd rfl hlen2
    have hsz := Kepler.Text.TameSpine.sizeBetwn hnd ha hb hab
    rw [hidx] at hsz
    exact List.length_eq_zero_iff.mp (by simpa using hsz)

/-- HOL `subdiv_single_step_betwn`（reduction3.hl:1665）：
`uniq (FST f) ∧ b = betwn (FST f) u v ∧ MEM u (FST f) ∧ MEM v (FST f) ∧
u ≠ v ∧ next_el (FST f) u ≠ v ⇒
foldl subdiv_single_step ((SOME u,0),f,g) (MAP SOME (betwn (FST f) u v)) =
((SOME (prev_el (FST f) v),0),f,g)`。
对 `betwn` 长度强归纳（HOL `size_induct` 同构）：`next_between` 给
`next_el u ∈ betwn u v`，`betwnCapPoint` 拆出首元，`nextVertex_next_el`
使 `subdiv_single_step` 走「等后继」支，步进余段。 -/
theorem subdivSingleStepBetwn (b : List ℕ) (f : Face) (g : Graph)
    (u v : ℕ) (hnd : f.vertices.Nodup) (hb : b = between f.vertices u v)
    (hu : u ∈ f.vertices) (hv : v ∈ f.vertices) (hne : u ≠ v)
    (hnext : nextEl f.vertices u ≠ v) :
    List.foldl subdivSingleStep ((some u, 0), f, g) (b.map some)
      = ((some (prevEl f.vertices v), 0), f, g) := by
  subst hb
  have key : ∀ N : ℕ, ∀ (f : Face) (g : Graph) (u v : ℕ),
      (between f.vertices u v).length = N →
      f.vertices.Nodup → u ∈ f.vertices → v ∈ f.vertices → u ≠ v →
      nextEl f.vertices u ≠ v →
      List.foldl subdivSingleStep ((some u, 0), f, g)
        ((between f.vertices u v).map some) = ((some (prevEl f.vertices v), 0), f, g) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro f g u v hlen hnd hu hv hne hnext
      -- 首元 = next_el u，且属于 between u v
      have hmem : nextEl f.vertices u ∈ between f.vertices u v := by
        have hnv : f.nextVertex u ≠ v := by
          intro h
          exact hnext (by rw [← Kepler.Text.TameSpine.nextVertexNextEl hu]; exact h)
        have h1 := Kepler.Graphs.next_between hnd hu hv hnv
        rwa [Kepler.Text.TameSpine.nextVertexNextEl hu] at h1
      have hw_mem : nextEl f.vertices u ∈ f.vertices := nextEl_mem_of_mem hu
      have hwne : nextEl f.vertices u ≠ v := by
        intro h
        have hvmem : v ∈ between f.vertices u v := h ▸ hmem
        exact Kepler.Text.TameSpine.notBetwn2 hnd (x := u) hvmem
      have hune : u ≠ nextEl f.vertices u := by
        intro h
        have humem : u ∈ between f.vertices u v :=
          Eq.mp (congrArg (fun x => x ∈ between f.vertices u v) h.symm) hmem
        exact Kepler.Text.TameSpine.notBetwn1 hnd (x := u) hv humem
      have hnil1 : between f.vertices u (nextEl f.vertices u) = [] :=
        (t5c_betwn_nil hnd hune hu hw_mem).mpr rfl
      have hcap := betwnCapPoint hnd hmem hne hu hv
      -- between u v = next_el u :: between (next_el u) v
      have hmap : (between f.vertices u v).map some
          = some (nextEl f.vertices u)
            :: (between f.vertices (nextEl f.vertices u) v).map some := by
        rw [hcap, hnil1, List.nil_append]
        rfl
      have hlen_decomp : (between f.vertices u v).length
          = (between f.vertices (nextEl f.vertices u) v).length + 1 := by
        rw [hcap, hnil1, List.nil_append]
        rfl
      -- 第一步走「等后继」支
      have hstep : subdivSingleStep ((some u, 0), f, g) (some (nextEl f.vertices u))
          = ((some (nextEl f.vertices u), 0), f, g) := by
        have hnv : f.nextVertex u = nextEl f.vertices u :=
          Kepler.Text.TameSpine.nextVertexNextEl hu
        simp [subdivSingleStep, hnv]
      rw [hmap, List.foldl_cons, hstep]
      by_cases hfin : nextEl f.vertices (nextEl f.vertices u) = v
      · -- 余段为空：一步收口，且 prev_el v = next_el u
        have hnil2 : between f.vertices (nextEl f.vertices u) v = [] :=
          (t5c_betwn_nil hnd hwne hw_mem hv).mpr hfin.symm
        rw [hnil2, List.map_nil, List.foldl_nil]
        have hprev : prevEl f.vertices v = nextEl f.vertices u := by
          rw [← hfin]
          exact prevEl_nextEl hnd hw_mem
        rw [hprev]
      · -- 余段强归纳
        have hlt : (between f.vertices (nextEl f.vertices u) v).length < N := by
          omega
        exact ih _ hlt f g (nextEl f.vertices u) v rfl hnd hw_mem hv hwne hfin
  exact key _ f g u v rfl hnd hu hv hne hnext

/-- HOL `subdiv_single_step_initial_seg`（reduction3.hl:1742）：
`uniq (FST f) ∧ MEM v0 (FST f) ∧ MEM u (FST f) ⇒
foldl subdiv_single_step ((NONE,0),f,g) initial_seg =
(if v0 = u then ((NONE,0),f,g) else ((SOME (prev_el (FST f) u),0),f,g))`，
`initial_seg = if v0 = u then [] else SOME v0 :: MAP SOME (betwn (FST f) v0 u)`。 -/
theorem subdivSingleStepInitialSeg (f : Face) (g : Graph) (u v0 : ℕ)
    (hnd : f.vertices.Nodup) (hv0 : v0 ∈ f.vertices) (hu : u ∈ f.vertices) :
    (let initialSeg : List (Option ℕ) :=
       if v0 = u then [] else some v0 :: (between f.vertices v0 u).map some
     List.foldl subdivSingleStep ((none, 0), f, g) initialSeg
       = if v0 = u then ((none, 0), f, g)
         else ((some (prevEl f.vertices u), 0), f, g)) := by
  dsimp only
  by_cases h : v0 = u
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    rw [List.foldl_cons]
    have hstep : subdivSingleStep ((none, 0), f, g) (some v0) = ((some v0, 0), f, g) := by
      simp [subdivSingleStep]
    rw [hstep]
    by_cases hfin : nextEl f.vertices v0 = u
    · have hnil : between f.vertices v0 u = [] :=
        (t5c_betwn_nil hnd h hv0 hu).mpr hfin.symm
      rw [hnil, List.map_nil, List.foldl_nil]
      have hprev : prevEl f.vertices u = v0 := by
        rw [← hfin]
        exact prevEl_nextEl hnd hv0
      rw [hprev]
    · exact subdivSingleStepBetwn (between f.vertices v0 u) f g v0 u hnd
        rfl hv0 hu h hfin

/-- HOL `subdiv_single_step_final_seg`（reduction3.hl:1767）：
`uniq (FST f) ∧ MEM u0 (FST f) ∧ MEM v' (FST f) ⇒
foldl subdiv_single_step ((SOME v',0),f,g) final_seg = ((SOME u0,0),f,g)`，
`final_seg = if v' = u0 then [] else rcons (MAP SOME (betwn (FST f) v' u0)) (SOME u0)`。 -/
theorem subdivSingleStepFinalSeg (f : Face) (g : Graph) (u0 v' : ℕ)
    (hnd : f.vertices.Nodup) (hu0 : u0 ∈ f.vertices) (hv' : v' ∈ f.vertices) :
    (let finalSeg : List (Option ℕ) :=
       if v' = u0 then [] else (between f.vertices v' u0).map some ++ [some u0]
     List.foldl subdivSingleStep ((some v', 0), f, g) finalSeg
       = ((some u0, 0), f, g)) := by
  dsimp only
  by_cases h : v' = u0
  · rw [if_pos h, h]
    rfl
  · rw [if_neg h]
    rw [List.foldl_append]
    by_cases hfin : nextEl f.vertices v' = u0
    · have hnil : between f.vertices v' u0 = [] :=
        (t5c_betwn_nil hnd h hv' hu0).mpr hfin.symm
      rw [hnil, List.map_nil, List.foldl_nil, List.foldl_cons, List.foldl_nil]
      have hnv : f.nextVertex v' = u0 := by
        rw [Kepler.Text.TameSpine.nextVertexNextEl hv']
        exact hfin
      simp [subdivSingleStep, hnv]
    · have hb := subdivSingleStepBetwn (between f.vertices v' u0) f g v' u0
          hnd rfl hv' hu0 h hfin
      rw [hb, List.foldl_cons, List.foldl_nil]
      have hpv : prevEl f.vertices u0 ∈ f.vertices := prevEl_mem_of_mem hu0
      have hnv : f.nextVertex (prevEl f.vertices u0) = u0 := by
        rw [Kepler.Text.TameSpine.nextVertexNextEl hpv]
        exact nextEl_prevEl hnd hu0
      simp [subdivSingleStep, hnv]

end Kepler.Text.Reduction3

-- 探针（编译即执行；目标：标准三，零 sorryAx）
#print axioms Kepler.Text.Reduction3.betwnCapPoint
#print axioms Kepler.Text.Reduction3.subdivSingleStepBetwn
#print axioms Kepler.Text.Reduction3.subdivSingleStepInitialSeg
#print axioms Kepler.Text.Reduction3.subdivSingleStepFinalSeg
