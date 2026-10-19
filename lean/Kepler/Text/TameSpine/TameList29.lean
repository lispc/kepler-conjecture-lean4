/-
  Kepler.Text.TameSpine.TameList29 — B1 Tame_list 地基批 29：段终墙 +
  quotient 章（tamespine-port-plan §4 批次表 B1 行；接续批 28 =
  TameList27.lean→TameList28.lean，批 28 终点 = HOL :11195
  （loopOfListSurj2 已落）；本批起点 = HOL :11197
  `DIH2K_IMP_PRE_SIMPLE_HYP2`。行号均按主仓 reference/flyspeck
  （commit 1ce0353）实测；任务面所给 :11205/:11207 系参考行号，主仓
  实测定名桩 :11206、quotient_bij_face_set :11209——与批 28 头注
  预记一致）。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:11197-:11244）：

  主件 1：`DIH2K_IMP_PRE_SIMPLE_HYP2` :11197-:11203（dih2k 蕴含段终墙）
  `!H k x. dih2k H k /\ ~(k=0) /\ x IN dart H ==> ~(node_map H x IN
  face H x)`。

  跳过件：:11206 `set_of_list_pairs_set_of_list = 0` 系定义桩非定理
  （批 28 头注预记），不落。

  主件 2：`quotient_bij_face_set` :11209-:11244（quotient 章主体）
  `!H NF. is_normal H NF ==> BIJ (atoms_of_loop H) NF
  (face_set (quotient H NF))`。

  定义面侦察定论（本批零新落 def——全部载体在库，逐槽记档）：
  · `dih2k`（WRGCVDR.hl:86，Wrgcvdr_cizmrrh 模块）↦ 在库
    `Kepler.Text.dih2k_p3`（LocalAuto3.lean:127，泛型 `Hypermap α` 层，
    五合取逐条同形；`Hypermap` structure 携 dart/maps，finiteness 内建，
    头注同 LocalAuto3 记档）；
  · **跨文件依赖预警（批 28 原文）解除**：`Wrgcvdr_cizmrrh.
    DIH2K_IMP_PRE_SIMPLE_HYP`（WRGCVDR.hl:589）↦ 在库
    `Kepler.Text.DIH2K_IMP_PRE_SIMPLE_HYP`（LocalAuto3.lean:1801，
    语句逐字同形 `∀ x ∈ H.darts, H.nodeMap x ∉ H.face x`）——**在库
    已有，直接复用**，批 28 预记的「全库无则首桩（库建）」分支未触发；
    axiom 审计实测标准三零 [propext, Classical.choice, Quot.sound]
    （LocalAuto3 文件内既有 sorry 系 FAN 段 :1875/:1881，不在本件依赖
    闭包内，#print axioms 探针为准）；
  · `Hypermap.node_map_and_darts`（hypermap.hl:114 `FINITE (dart H) /\
    node_map H permutes (dart H)`）↦ 零镜像：Lean `Hypermap` 的 darts
    系 `Finset`（finiteness 内建）+ `nodeMap_permutes` 结构场，HOL
    MESON 对该件的消费面在 Lean 装配中不被触及；
  · `is_normal`（hypermap.hl:8122）↦ `Hypermap.IsNormalFamily`
    （Hypermap.lean:6808，批 26 已消费面）；
  · `quotient H NF`（hypermap.hl:9342；SKOLEM n_quotient/f_quotient
    装配、不带前提）↦ `H.quotientHypermap hnf`（Hypermap.lean:7744
    非计算 def——Lean 折算把 `is_normal` 收成 `hnf : IsNormalFamily`
    显式参数，本批语句在 `is_normal` 前提下引用 quotient，折算封闭）；
  · `face_set`（hypermap.hl:167）↦ `Hypermap.faceSet`
    （Hypermap.lean:1008）；`atoms_of_loop H L`（hypermap.hl:9688）
    ↦ `H.atomsOfLoop L`（Hypermap.lean:7939）；`BIJ f s t` ↦ Mathlib
    `Set.BijOn`（Operations.lean:309 `MapsTo ∧ InjOn ∧ SurjOn`——
    HOL `BIJ = INJ ∧ SURJ` 的 INJ 已内含 maps-to 面，Lean 三槽各半，
    MapsTo 槽由 faceSet_quotient 改写补给）。

  证明层侦察定论：
  · 主件 1（:11197）HOL 证体单行 `ASM_MESON_TAC[Hypermap.
    node_map_and_darts; Wrgcvdr_cizmrrh.DIH2K_IMP_PRE_SIMPLE_HYP]`——
    Lean 面即在库件直接装配（零 tactic 项式，MESON 不镜像）。
  · 主件 2（:11209）HOL 证体：BIJ/SURJ/INJ 展开后 INJ 半走长链
    （is_normal 展开 + EXTENSION + lemma_card_dart_of_loop:6785 +
    card_dart_of_loop:6720 + lemma_in_atoms_of_loop2:9690 +
    atom_reflect:7773 + lemma_atom_sub_loop:7910 + SET_TAC），SURJ 半
    ASM_SIMP_TAC[lemmaQuotientFace:9792] + ASM_MESON。Lean 面：INJ 半
    被在库 `atomsOfLoop_inj`（Hypermap.lean:7950，hypermap.hl:9693
    lemma_atoms_of_loop_eq——其证体正是同一条长链：hnf.1 取 x +
    atom_mem_atomsOfLoop + atom_reflect + mem_darts_of_mem_atom +
    IsNormalFamily.eq_of_mem_of_mem）全量吸收；SURJ/MapsTo 两槽由
    `faceSet_quotient`（Hypermap.lean:8029，hypermap.hl:9792
    lemmaQuotientFace）双侧改写 + 集合构造器一步。零 Meson。

  依赖面：批链全批 1-28 + **首次引入 LocalAuto 层 import 边
  `Kepler.Text.LocalAuto3`**（`dih2k_p3`/`DIH2K_IMP_PRE_SIMPLE_HYP`
  在库唯一载体家；无环实测：LocalAuto3 import 树 Polytope/Fan/
  TopologyFan/PackingAuto5 零 TameSpine 引用）+ 在库 Hypermap
  IsNormalFamily/quotientHypermap/faceSet/atomsOfLoop/atomsOfLoop_inj/
  faceSet_quotient + Mathlib Set.BijOn。
  泛型幅度裁定：两主件纯 hypermap 面无列表载体牵连（HOL 语句本身
  (A) 泛型），保持泛型 α（批 25 rev2 先例；下游 :11247
  dih2k_quotient_card_NF 以例示消费）。

  诚实记账：本批两主件全部真证，零新 def、零止损件、零记账债。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git
  写操作。批 30 接续点：HOL :11247 `dih2k_quotient_card_NF`
  `!H NF x. ~(CARD(face H x)=0) /\ is_normal H NF /\
  dih2k (quotient H NF) (CARD (face H x)) ==> ~(SING NF)`（依赖
  Hypermap.lemma_finite_normal_loops:8342 + lemma_finite_atoms_of_family
  + Wrgcvdr_cizmrrh.dih2k:2773 + Hypermap.lemma_dart_invariant:412 +
  face_refl:908 + lemma_in_face_set:2727 + 本批两件；CARD_EQ_0 面 ↦
  Loop card_pos 先例批 28）。
-/

import Kepler.Text.TameSpine.TameList28
import Kepler.Text.LocalAuto3

namespace Kepler.Text.TameSpine

/-! ### §1 DIH2K_IMP_PRE_SIMPLE_HYP2（tame_list.hl:11197-:11203）——段终墙 -/

/-- **HOL `DIH2K_IMP_PRE_SIMPLE_HYP2`**（tame_list.hl:11197-:11203）
`!H k x. dih2k H k /\ ~(k=0) /\ x IN dart H ==> ~(node_map H x IN
face H x)`——dih2k 蕴含段终墙：HOL 证体单行 MESON（Hypermap.
node_map_and_darts + Wrgcvdr_cizmrrh.DIH2K_IMP_PRE_SIMPLE_HYP），Lean
面即在库 `DIH2K_IMP_PRE_SIMPLE_HYP`（LocalAuto3.lean:1801，axiom 三零
实测）直接装配；`dih2k` ↦ 在库 `dih2k_p3`（LocalAuto3.lean:127）。 -/
theorem dih2kImpPreSimpleHyp2 {α : Type*} [DecidableEq α] {H : Hypermap α}
    {k : ℕ} (hd : dih2k_p3 H k) (hk : k ≠ 0) (x : α) (hx : x ∈ H.darts) :
    (H.nodeMap : α → α) x ∉ H.face x :=
  DIH2K_IMP_PRE_SIMPLE_HYP hd hk x hx

/-! ### §2 quotient_bij_face_set（tame_list.hl:11209-:11244） -/

/-- **HOL `quotient_bij_face_set`**（tame_list.hl:11209-:11244）
`!H NF. is_normal H NF ==> BIJ (atoms_of_loop H) NF
(face_set (quotient H NF))`——正规环族的原子环到商 hypermap 面集的
双射：MapsTo/InjOn/SurjOn 三槽装配，InjOn 槽在库 `atomsOfLoop_inj`
（HOL :11220-:11239 的 lemma_card_dart_of_loop/atom_reflect/
lemma_atom_sub_loop/SET_TAC 长链被其证体同链吸收），MapsTo/SurjOn
两槽 `faceSet_quotient`（HOL lemmaQuotientFace :9792）双侧改写。 -/
theorem quotientBijFaceSet {α : Type*} [DecidableEq α] (H : Hypermap α)
    {NF : Set (Loop α)} (hnf : H.IsNormalFamily NF) :
    Set.BijOn (H.atomsOfLoop) NF (H.quotientHypermap hnf).faceSet := by
  have hFQ : (H.quotientHypermap hnf).faceSet
      = {a | ∃ L ∈ NF, a = H.atomsOfLoop L} := H.faceSet_quotient hnf
  refine ⟨?_, ?_, ?_⟩
  · -- MapsTo：atomsOfLoop L 落在商面集（HOL ASM_SIMP_TAC[lemmaQuotientFace;
    --   IN_ELIM_THM] + CONJ_TAC; MESON_TAC 支）
    intro L hL
    rw [hFQ]
    exact ⟨L, hL, rfl⟩
  · -- InjOn：环族上原子族相等 ⟹ 环相等（HOL :11220-:11239 长链被吸收）
    intro L hL L' hL' heq
    exact H.atomsOfLoop_inj hnf hL hL' heq
  · -- SurjOn：商面集每元即某环的原子族（HOL ASM_MESON_TAC 收口面）
    intro b hb
    rw [hFQ] at hb
    obtain ⟨L, hL, rfl⟩ := hb
    exact ⟨L, hL, rfl⟩

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；两主件预期标准三
[propext, Classical.choice, Quot.sound]）：
#print axioms Kepler.Text.TameSpine.dih2kImpPreSimpleHyp2
#print axioms Kepler.Text.TameSpine.quotientBijFaceSet
-/
