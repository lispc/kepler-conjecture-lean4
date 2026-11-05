/-
  Kepler.Text.TameCorrFloor — `tame_correspondence_iso` 三波施工的 **W3 第一波**：
  `reference/flyspeck/text_formalization/tame/WMLNYMD.hl` 的
  **G6（floor 机制，18 件 prove）** + **G7（sum/BIJ 助手，4 件 prove）** 的真证明移植
  （HOL :844-:1358，共 505 行 prove 体）。

  ┌─ 落点与环安全（刻意设计，非偶然）───────────────────────────────────
  │ 唯一 import = `Kepler.Text.TameLp` + `Kepler.Graphs.Tame`。
  │ 两者闭包**零** `Kepler.Assembly`（`Kepler.Assembly.GoodListDefs` 只是
  │ Assembly-free 的 def 模块；`Kepler/Graphs/*` 无 Assembly 边）。
  │ 故 `Kepler.Assembly` 可安全 import 本模块（不翻岛 74/75 的成环边）。
  │ 环自检（编排者复跑同款）：
  │   `#check @Kepler.Assembly.the_kepler_conjecture_from_interfaces`
  │   在本模块 import 闭包内必须 **unknown identifier**。
  └────────────────────────────────────────────────────────────────

  **HOL 逐件对照**（每件文档注记 HOL 行号；载体折算表：
  `sumn` ↦ `List.sum`、`nsum` ↦ 本模块 `nsum`（`Finset.sum` 包装，无限集 0）、
  `CARD` ↦ `Set.ncard`、`real` ↦ `ℝ`、`&` ↦ `Nat.cast`、`dart` ↦ `H.darts`、
  `adm_1/2/3` ↦ `TameLp.Adm1/Adm2/Adm3`、`tame_9a` ↦ `TameLp.Tame9a`、
  `tame_13a` ↦ `TameLp.Tame13a`、`face_set` ↦ `H.faceSet`、
  `squanderFace/squanderVertex/squanderTarget/excessTCount` ↦ `Kepler.Graphs.*`、
  `tgt` ↦ `Kepler.Text.tgt`、`d_tame` ↦ `Kepler.Text.dTame`、`a_tame` ↦ `TameLp.aTame`）。

  **新增本地载体**（HOL 有、Lean 侧尚无同名件；均逐字抄 HOL 体，不改既有陈述）：
  · `nsum`   = HOL `nsum = iterate (+)`（`hol-light-nat/iterate.ml:758`）
  · `nfloor` = HOL `nfloor`（`new_specification`，WMLNYMD.hl:875；Lean 取
    `⌊x*d⌋₊`，规格由 `nfloorExists` 钉死）
  · `wtFloor` / `Adm1Floor` / `Adm2Floor` / `Adm3Floor` / `Tame13aFloor`
    （WMLNYMD.hl:878/:881/:884/:890/:894 逐字）
  · `facesAtList` = HOL `faces_at_list`（`tame_defs2.hl:688-689` 逐字：
    `FILTER (MEM v) L`；`TameLp`/岛外无此列表面 def）
  · `BIJ` = HOL `BIJ`（maps-to ∧ inj ∧ surj，`pred_set.ml` 三合取）
  · `isVertexType` / `vertexPairs`：HOL `vertextypes_explicit` 结论的 15 元
    析取及其 List 形（`isVertexType` 是纯语法缩写，主陈述仍写逐字析取）。

  **纪律**：无 `axiom`/`sorry`/`admit`/`native_decide`；无既有陈述改写；
  所有 22 件验收 `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]`。
-/

import Kepler.Text.TameLp
import Kepler.Graphs.Tame

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameCorrFloor

open Classical
open Kepler.Text (Hypermap setSum dTame tgt)
open Kepler.Text.TameLp
open Kepler.Assembly (GoodList)
open Kepler.Graphs (squanderFace squanderVertex squanderTarget excessTCount)

/-! ## §0 本地载体（HOL WMLNYMD.hl:875-:896 / tame_defs2.hl:688） -/

/-- HOL `nsum = iterate (+)`（`hol-light-nat/iterate.ml:758-759`）：有限集上求
`f` 的和，无限集约定 0（与 `Kepler.Text.setSum` 同款 junk-value 约定）。 -/
noncomputable def nsum {α : Type*} (s : Set α) (f : α → ℕ) : ℕ :=
  if h : s.Finite then ∑ x ∈ h.toFinset, f x else 0

/-- HOL `nfloor`（WMLNYMD.hl:875 的 `new_specification`）：`⌊x * d⌋₊`。
规格（`&n <= x * &d ∧ x * &d < &n + &1`）由 `nfloorExists` 钉死。 -/
noncomputable def nfloor (d : ℕ) (x : ℝ) : ℕ := ⌊x * (d : ℝ)⌋₊

/-- HOL `wt_floor`（WMLNYMD.hl:878）逐字：
`if (CARD f) > 4 then squanderFace (CARD f) else nfloor 10000 (w f)`。 -/
noncomputable def wtFloor {α : Type*} (w : Set α → ℝ) (f : Set α) : ℕ :=
  if 4 < f.ncard then squanderFace f.ncard else nfloor 10000 (w f)

/-- HOL `adm_1_floor`（WMLNYMD.hl:881）逐字。 -/
def Adm1Floor {α : Type*} [DecidableEq α] (H : Hypermap α) (w : Set α → ℕ) : Prop :=
  ∀ x ∈ H.darts, squanderFace (H.face x).ncard ≤ w (H.face x)

/-- HOL `adm_2_floor`（WMLNYMD.hl:884）逐字。 -/
def Adm2Floor {α : Type*} [DecidableEq α] (H : Hypermap α) (w : Set α → ℕ) : Prop :=
  ∀ x ∈ H.darts, (setOfExceptionalMeetingNode H x).ncard = 0 →
    squanderVertex (setOfTrianglesMeetingNode H x).ncard
        (setOfQuadrilateralsMeetingNode H x).ncard ≤
      nsum (setOfFaceMeetingNode H x) w

/-- HOL `adm_3_floor`（WMLNYMD.hl:890）逐字。 -/
def Adm3Floor {α : Type*} [DecidableEq α] (H : Hypermap α) (w : Set α → ℕ) : Prop :=
  ∀ x ∈ H.darts, typeOfNode H x = (5, 0, 1) →
    excessTCount ≤ nsum (setOfTrianglesMeetingNode H x) w

/-- HOL `tame_13a_floor`（WMLNYMD.hl:894）逐字。 -/
def Tame13aFloor {α : Type*} [DecidableEq α] (H : Hypermap α) : Prop :=
  ∃ w : Set α → ℕ, Adm1Floor H w ∧ Adm2Floor H w ∧ Adm3Floor H w ∧
    nsum H.faceSet w < squanderTarget

/-- HOL `faces_at_list`（`tame_defs2.hl:688-689`）逐字：
`facesAt_list L v = FILTER (MEM v) L`（`MEM v` 是「顶点 v 属于面列表 f」）。 -/
def facesAtList (L : Kepler.Graphs.fgraph ℕ) (v : ℕ) : List (List ℕ) :=
  L.filter (fun f => decide (v ∈ f))

/-- HOL `BIJ`（`pred_set.ml`）：maps-to ∧ 单射 ∧ 满射（三合取）。 -/
def BIJ {α β : Type*} (ab : α → β) (A : Set α) (B : Set β) : Prop :=
  (∀ a ∈ A, ab a ∈ B) ∧ Set.InjOn ab A ∧ ∀ b ∈ B, ∃ a ∈ A, ab a = b

/-- `vertextypes_explicit` 结论的 15 元容许表（HOL WMLNYMD.hl:1105-1120 逐项；
纯语法缩写，`vertextypesExplicit` 的陈述仍写逐字析取）。 -/
def isVertexType (p q : ℕ) : Prop :=
  (p, q) = (0, 3) ∨ (p, q) = (0, 4) ∨ (p, q) = (1, 2) ∨ (p, q) = (1, 3) ∨
    (p, q) = (2, 1) ∨ (p, q) = (2, 2) ∨ (p, q) = (2, 3) ∨ (p, q) = (3, 1) ∨
    (p, q) = (3, 2) ∨ (p, q) = (4, 0) ∨ (p, q) = (4, 1) ∨ (p, q) = (5, 0) ∨
    (p, q) = (5, 1) ∨ (p, q) = (6, 0) ∨ (p, q) = (7, 0)

/-- `isVertexType` 的 List 形（`b_tame_explicit`/`squanderVertex_explicit` 的
默认支与表值逐项核对、以及 `adm_2_floor_adm_2` 的表算术用）。 -/
def vertexPairs : List (ℕ × ℕ) :=
  [(0, 3), (0, 4), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2),
    (4, 0), (4, 1), (5, 0), (5, 1), (6, 0), (7, 0)]

private theorem isVertexType_iff_mem {p q : ℕ} :
    isVertexType p q ↔ (p, q) ∈ vertexPairs := by
  unfold isVertexType
  simp [vertexPairs]

/-! ## §1 求和助手（`setSum` / `nsum` 换装件） -/

private theorem nsum_eq_sum {α : Type*} {s : Set α} (hs : s.Finite) (f : α → ℕ) :
    nsum s f = ∑ x ∈ hs.toFinset, f x := by
  rw [nsum, dif_pos hs]

private theorem nsum_cast_real {α : Type*} {s : Set α} (f : α → ℕ) :
    (nsum s f : ℝ) = setSum s (fun x => (f x : ℝ)) := by
  by_cases hs : s.Finite
  · rw [nsum_eq_sum hs, setSum, dif_pos hs, Nat.cast_sum]
  · rw [nsum, dif_neg hs, setSum, dif_neg hs]
    norm_num

private theorem nsum_insert {α : Type*} [DecidableEq α] {s : Set α} {a : α}
    (ha : a ∉ s) (hs : s.Finite) (f : α → ℕ) :
    nsum (insert a s) f = f a + nsum s f := by
  have hfin : (insert a s).Finite := hs.insert a
  rw [nsum_eq_sum hfin, nsum_eq_sum hs]
  rw [Set.Finite.toFinset_insert (s := s) (a := a) (hs := hfin)]
  rw [Finset.sum_insert (by rw [hs.mem_toFinset]; exact ha)]

private theorem setSum_insert {α : Type*} [DecidableEq α] {s : Set α} {a : α}
    (ha : a ∉ s) (hs : s.Finite) (f : α → ℝ) :
    setSum (insert a s) f = f a + setSum s f := by
  have hfin : (insert a s).Finite := hs.insert a
  rw [setSum, dif_pos hfin, setSum, dif_pos hs]
  rw [Set.Finite.toFinset_insert (s := s) (a := a) (hs := hfin)]
  rw [Finset.sum_insert (by rw [hs.mem_toFinset]; exact ha)]

private theorem setSum_le_of_subset {α : Type*} {S T : Set α} {f : α → ℝ}
    (hsub : S ⊆ T) (hf : ∀ x ∈ T, 0 ≤ f x) (hT : T.Finite) :
    setSum S f ≤ setSum T f := by
  have hS : S.Finite := hT.subset hsub
  rw [setSum, dif_pos hS, setSum, dif_pos hT]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_iff.2 fun x hx => hT.mem_toFinset.2 (hsub (hS.mem_toFinset.1 hx)))
    (fun x hx _ => hf x (hT.mem_toFinset.1 hx))

private theorem setSum_le {α : Type*} {s : Set α} (hs : s.Finite) {f g : α → ℝ}
    (h : ∀ x ∈ s, f x ≤ g x) : setSum s f ≤ setSum s g := by
  rw [setSum, dif_pos hs, setSum, dif_pos hs]
  exact Finset.sum_le_sum fun x hx => h x (hs.mem_toFinset.1 hx)

private theorem setSum_mul_const {α : Type*} {s : Set α} (hs : s.Finite)
    (f : α → ℝ) (c : ℝ) :
    setSum s (fun x => f x * c) = setSum s f * c := by
  rw [setSum, dif_pos hs, setSum, dif_pos hs, Finset.sum_mul]

private theorem setSum_add_one {α : Type*} {s : Set α} (hs : s.Finite)
    (g : α → ℕ) :
    setSum s (fun f => (g f : ℝ) + 1) = (nsum s g : ℝ) + (s.ncard : ℝ) := by
  have h1 : setSum s (fun f => (g f : ℝ) + 1) =
      setSum s (fun f => (g f : ℝ)) + setSum s (fun _ => (1 : ℝ)) := by
    rw [setSum, dif_pos hs, setSum, dif_pos hs, setSum, dif_pos hs,
      Finset.sum_add_distrib]
  have hc : setSum s (fun _ => (1 : ℝ)) = (s.ncard : ℝ) := by
    have hcard : hs.toFinset.card = s.ncard :=
      (Set.ncard_eq_toFinset_card s hs).symm
    rw [setSum, dif_pos hs, Finset.sum_const]
    simp only [nsmul_eq_mul, mul_one]
    exact_mod_cast hcard
  rw [h1, ← nsum_cast_real (s := s) (f := g), ← hc]

private theorem nsum_le_nsum_of_subset {α : Type*} {s t : Set α} (hsub : s ⊆ t)
    (ht : t.Finite) (f : α → ℕ) : nsum s f ≤ nsum t f := by
  have hs : s.Finite := ht.subset hsub
  rw [nsum, dif_pos hs, nsum, dif_pos ht]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_iff.2 fun x hx => ht.mem_toFinset.2 (hsub (hs.mem_toFinset.1 hx)))
    (fun x _ _ => Nat.zero_le _)

private theorem nsum_le_nsum {α : Type*} {s : Set α} (hs : s.Finite) {f g : α → ℕ}
    (h : ∀ x ∈ s, f x ≤ g x) : nsum s f ≤ nsum s g := by
  rw [nsum, dif_pos hs, nsum, dif_pos hs]
  exact Finset.sum_le_sum fun x hx => h x (hs.mem_toFinset.1 hx)

/-! ## §2 face/node 集合面助手（`faceSet` 成员表示、子集、有限性） -/

private theorem mem_faceSet_iff {α : Type*} [DecidableEq α] {H : Hypermap α}
    {f : Set α} :
    f ∈ H.faceSet ↔ ∃ x ∈ H.darts, H.face x = f := by
  simp only [Kepler.Text.Hypermap.faceSet, Kepler.Text.setOfOrbits,
    Kepler.Text.Hypermap.face, Set.mem_setOf_eq]

private theorem setOfFaceMeetingNode_subset_faceSet {α : Type*} [DecidableEq α]
    (H : Hypermap α) (x : α) : setOfFaceMeetingNode H x ⊆ H.faceSet := by
  rintro F ⟨y, hy, rfl, _⟩
  exact (Kepler.Text.Hypermap.mem_darts_iff_face_mem H y).mp hy

/-! ## §3 floor 机制（WMLNYMD.hl:844-:1303，G6 18 件） -/

/-- HOL `floor_lemma`（WMLNYMD.hl:844）：`&0 <= y ==> (?m. &m <= y /\ y < &m + &1)`。 -/
theorem floorLemma {y : ℝ} (hy : 0 ≤ y) :
    ∃ m : ℕ, (m : ℝ) ≤ y ∧ y < (m : ℝ) + 1 :=
  ⟨⌊y⌋₊, Nat.floor_le hy, Nat.lt_floor_add_one y⟩

/-- HOL `nfloor_exists`（WMLNYMD.hl:857）。 -/
theorem nfloorExists (d : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ∃ n : ℕ, (n : ℝ) ≤ x * (d : ℝ) ∧ x * (d : ℝ) < (n : ℝ) + 1 := by
  have h0 : 0 ≤ x * (d : ℝ) := mul_nonneg hx (Nat.cast_nonneg d)
  exact floorLemma h0

/-- HOL `wt_floor_nn`（WMLNYMD.hl:898）。 -/
theorem wtFloorNN {α : Type*} [DecidableEq α] {H : Hypermap α} {w : Set α → ℝ} {x : α}
    (hx : x ∈ H.darts) (hw : Adm1 H w) : 0 ≤ w (H.face x) := by
  have hd : 0 ≤ dTame (H.face x).ncard := by
    unfold dTame
    split_ifs <;> norm_num [tgt]
  have hle := hw x hx
  linarith

/-- `squanderFace n = d_tame n * 10000`（n > 4 时；WMLNYMD.hl:920-:928 的
`squanderFace`/`d_tame` 表逐值核对，HOL 用 `REWRITE_TAC[squanderFace;d_tame]`）。 -/
private theorem squanderFace_eq_dTame_mul {n : ℕ} (hn : 4 < n) :
    (squanderFace n : ℝ) = dTame n * 10000 := by
  rcases eq_or_ne n 5 with rfl | h5
  · norm_num [squanderFace, dTame]
  rcases eq_or_ne n 6 with rfl | h6
  · norm_num [squanderFace, dTame]
  · have hs : squanderFace n = squanderTarget := by
      unfold squanderFace
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hd : dTame n = tgt := by
      unfold dTame
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [hs, hd, squanderTarget]
    norm_num [tgt]

/-- HOL `wt_floor_le_wt`（WMLNYMD.hl:910）。 -/
theorem wtFloorLeWt {α : Type*} [DecidableEq α] {H : Hypermap α} {w : Set α → ℝ} {x : α}
    (hx : x ∈ H.darts) (hw : Adm1 H w) :
    (wtFloor w (H.face x) : ℝ) ≤ w (H.face x) * 10000 := by
  have hnn := wtFloorNN hx hw
  have hle := hw x hx
  unfold wtFloor
  by_cases hc : 4 < (H.face x).ncard
  · rw [if_pos hc]
    have htab : (squanderFace (H.face x).ncard : ℝ) =
        dTame (H.face x).ncard * 10000 := squanderFace_eq_dTame_mul hc
    have hmul : dTame (H.face x).ncard * 10000 ≤ w (H.face x) * 10000 :=
      mul_le_mul_of_nonneg_right hle (by norm_num)
    linarith
  · rw [if_neg hc]
    have h0 : 0 ≤ w (H.face x) * 10000 := by nlinarith
    unfold nfloor
    exact Nat.floor_le h0

/-- HOL `FINITE_set_of_face_meeting_node`（WMLNYMD.hl:1005）。 -/
theorem finiteSetOfFaceMeetingNode {α : Type*} [DecidableEq α] (H : Hypermap α) (x : α) :
    (setOfFaceMeetingNode H x).Finite :=
  (Kepler.Text.Hypermap.faceSet_finite H).subset
    (setOfFaceMeetingNode_subset_faceSet H x)

/-- HOL `FINITE_set_of_n_meeting_node`（WMLNYMD.hl:1020）。 -/
theorem finiteSetOfNMeetingNode {α : Type*} [DecidableEq α] (H : Hypermap α) (x : α) :
    (setOfTrianglesMeetingNode H x).Finite ∧
      (setOfQuadrilateralsMeetingNode H x).Finite ∧
        (setOfExceptionalMeetingNode H x).Finite := by
  have hF := finiteSetOfFaceMeetingNode H x
  refine ⟨hF.subset ?_, hF.subset ?_, hF.subset ?_⟩
  · rintro F ⟨y, hy, rfl, _, hyx⟩
    exact ⟨y, hy, rfl, hyx⟩
  · rintro F ⟨y, hy, rfl, _, hyx⟩
    exact ⟨y, hy, rfl, hyx⟩
  · rintro F ⟨y, hy, rfl, _, hyx⟩
    exact ⟨y, hy, rfl, hyx⟩

/-- `faceSet` 上的 `w` 非负（`adm_1` 的直接推论；WMLNYMD.hl:996-:1000
`SUM_SUBSET_SIMPLE` 的非负前提）。 -/
private theorem faceSet_nonneg {α : Type*} [DecidableEq α] {H : Hypermap α}
    {w : Set α → ℝ} (hw : Adm1 H w) : ∀ f ∈ H.faceSet, 0 ≤ w f := by
  intro f hf
  obtain ⟨x, hx, rfl⟩ := (mem_faceSet_iff (H := H) (f := f)).mp hf
  exact wtFloorNN hx hw

/-- HOL `total_weight_floor`（WMLNYMD.hl:942）。 -/
theorem totalWeightFloor {α : Type*} [DecidableEq α] (H : Hypermap α) (w : Set α → ℝ)
    (h1 : Adm1 H w) (htw : totalWeight H w < tgt) :
    nsum H.faceSet (wtFloor w) < squanderTarget := by
  have hfin := Kepler.Text.Hypermap.faceSet_finite H
  have hnn := faceSet_nonneg (H := H) (w := w) h1
  have hpoint : ∀ f ∈ H.faceSet, (wtFloor w f : ℝ) ≤ w f * 10000 := by
    intro f hf
    obtain ⟨x, hx, rfl⟩ := (mem_faceSet_iff (H := H) (f := f)).mp hf
    exact wtFloorLeWt hx h1
  have hle : (nsum H.faceSet (wtFloor w) : ℝ) ≤ setSum H.faceSet w * 10000 := by
    rw [nsum_cast_real]
    calc setSum H.faceSet (fun f => (wtFloor w f : ℝ))
        ≤ setSum H.faceSet (fun f => w f * 10000) := setSum_le hfin hpoint
      _ = setSum H.faceSet w * 10000 := setSum_mul_const hfin w 10000
  have hlt : (nsum H.faceSet (wtFloor w) : ℝ) < (squanderTarget : ℝ) := by
    have htw' : setSum H.faceSet w < tgt := htw
    have h1' : setSum H.faceSet w * 10000 < tgt * 10000 := by nlinarith
    have h2' : tgt * 10000 = (squanderTarget : ℝ) := by
      unfold squanderTarget Kepler.Text.tgt
      norm_num
    linarith
  exact Nat.cast_lt.mp hlt

/-- HOL `adm_1_floor_adm_1`（WMLNYMD.hl:971）。 -/
theorem adm1FloorAdm1 {α : Type*} [DecidableEq α] (H : Hypermap α) (w : Set α → ℝ)
    (h1 : Adm1 H w) (h9 : Tame9a H) : Adm1Floor H (wtFloor w) := by
  intro x hx
  have h9x := h9 x hx
  have hle := h1 x hx
  have hnn := wtFloorNN hx h1
  unfold wtFloor
  by_cases hc : 4 < (H.face x).ncard
  · rw [if_pos hc]
  · rw [if_neg hc]
    have h3 : 3 ≤ (H.face x).ncard := h9x.1
    have h4 : (H.face x).ncard ≤ 4 := by omega
    have hcases : (H.face x).ncard = 3 ∨ (H.face x).ncard = 4 := by omega
    rcases hcases with h3' | h4'
    · rw [h3', show squanderFace 3 = 0 by norm_num [squanderFace]]
      exact Nat.zero_le _
    · rw [h4', show squanderFace 4 = 2058 by norm_num [squanderFace]]
      have hd : dTame 4 ≤ w (H.face x) := by
        have := hle
        rwa [h4'] at this
      have h206 : (2058 : ℝ) ≤ w (H.face x) * 10000 := by
        have hd' : (0.206 : ℝ) ≤ w (H.face x) := by
          have h := hd
          norm_num [dTame] at h
          linarith
        nlinarith
      unfold nfloor
      exact Nat.le_floor h206

/-! ## §4 sum/BIJ 助手（WMLNYMD.hl:1305-:1358，G7 4 件） -/

/-- HOL `sumn_cons`（WMLNYMD.hl:1305）；`sumn` ↦ `List.sum`（core `List.sum_cons`）。 -/
theorem sumnCons (h : ℕ) (hs : List ℕ) : (h :: hs).sum = h + hs.sum :=
  List.sum_cons

/-- `nfloor` 的规格上界（HOL `nfloor` 的 `x*d < &n + 1`，WMLNYMD.hl:876）。 -/
private theorem le_nfloor_add_one (d : ℕ) (x : ℝ) :
    x * (d : ℝ) ≤ (nfloor d x : ℝ) + 1 := by
  unfold nfloor
  exact le_of_lt (Nat.lt_floor_add_one (x * (d : ℝ)))

/-- HOL `sumn_nsum`（WMLNYMD.hl:1313）。 -/
theorem sumnNsum {α : Type*} [DecidableEq α] (s : List α) (f : α → ℕ) (h : s.Nodup) :
    (s.map f).sum = nsum {x | x ∈ s} f := by
  induction s with
  | nil => simp [nsum]
  | cons a t ih =>
    have h' := List.nodup_cons.mp h
    rw [List.map_cons, List.sum_cons, ih h'.2]
    have hset : {x : α | x ∈ (a :: t : List α)} = insert a {x : α | x ∈ t} := by
      ext z
      simp
    have hat : a ∉ ({x : α | x ∈ t} : Set α) := by
      simp [h'.1]
    rw [hset, nsum_insert hat (List.finite_toSet t) f]

/-- `List.flatten` 的 `uniq` 提升（HOL `List_hypermap.uniq_flatten` 路线；
`uniq` ↦ `List.Nodup`，全非空成员前提来自 `good_list` 第 2 合取）。 -/
private theorem uniqFlatten {α : Type*} {L : List (List α)}
    (hun : L.flatten.Nodup) (hn : ∀ l ∈ L, l ≠ []) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons a t ih =>
    rw [List.flatten_cons] at hun
    obtain ⟨_, h2, h3⟩ := List.nodup_append.mp hun
    rw [List.nodup_cons]
    refine ⟨?_, ih h2 (fun x hx => hn x (List.mem_cons_of_mem _ hx))⟩
    intro ha
    obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil a (hn a (List.mem_cons_self ..))
    exact (h3 z hz z (List.mem_flatten.mpr ⟨a, ha, hz⟩)) rfl

/-- `list_pairs` 非空（HOL `list_pairs_empty` 槽；WMLNYMD.hl:1326
`good_list_uniq` 的 `~(h = [])` 前提）。 -/
private theorem listPairsNeNil {α : Type*} {l : List α} (hne : l ≠ []) :
    Kepler.Assembly.listPairs l ≠ [] := by
  intro hc
  have h1 : (l.drop 1 ++ l.take 1).length = l.length := by
    simp
    omega
  have h3 : (Kepler.Assembly.listPairs l).length = l.length := by
    show (l.zip (l.drop 1 ++ l.take 1)).length = l.length
    rw [List.length_zip, h1, min_self]
  rw [hc] at h3
  simp at h3
  exact hne (List.length_eq_zero_iff.mp h3.symm)

/-- HOL `good_list_uniq`（`list_hypermap-compiled.hl:839`）：`good_list L ==> uniq L`
（`uniq` ↦ `List.Nodup`）。证明走 `uniq_flatten` 直投：`GoodList.1` 即
`(L.map listPairs).flatten.Nodup`，配 `listPairsNeNil` 得 `(L.map listPairs).Nodup`，
再 `List.Nodup.of_map` 降回 `L.Nodup`。 -/
private theorem goodListNodup {L : Kepler.Graphs.fgraph ℕ} (hL : GoodList L) :
    L.Nodup := by
  have hmap : (L.map Kepler.Assembly.listPairs).Nodup := by
    refine uniqFlatten ?_ ?_
    · exact hL.1
    · intro q hq
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hq
      exact listPairsNeNil (hL.2.1 l hl)
  exact List.Nodup.of_map Kepler.Assembly.listPairs hmap

/-- HOL `uniq_facesAt_list`（WMLNYMD.hl:1330）；`uniq` ↦ `List.Nodup`。 -/
theorem uniqFacesAtList {L : Kepler.Graphs.fgraph ℕ} (hL : GoodList L) (v : ℕ) :
    (facesAtList L v).Nodup :=
  List.Nodup.filter (fun f => decide (v ∈ f)) (goodListNodup hL)

/-- HOL `BIJ_NSUM`（WMLNYMD.hl:1342）。 -/
theorem BIJNSUM {α β : Type*} (A : Set α) (B : Set β) (f : β → ℕ) (ab : α → β)
    (hA : A.Finite) (h : BIJ ab A B) :
    nsum A (f ∘ ab) = nsum B f := by
  have hB : B.Finite := by
    have himg : B = ab '' A := by
      ext b
      constructor
      · intro hb
        obtain ⟨a, ha, rfl⟩ := h.2.2 b hb
        exact ⟨a, ha, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact h.1 a ha
    rw [himg]
    exact hA.image ab
  rw [nsum, dif_pos hA, nsum, dif_pos hB]
  refine Finset.sum_bij (fun a _ => ab a) ?_ ?_ ?_ ?_
  · intro a ha
    exact hB.mem_toFinset.2 (h.1 a (hA.mem_toFinset.1 ha))
  · intro a₁ ha₁ a₂ ha₂ heq
    exact h.2.1 (hA.mem_toFinset.1 ha₁) (hA.mem_toFinset.1 ha₂) heq
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := h.2.2 b (hB.mem_toFinset.1 hb)
    exact ⟨a, hA.mem_toFinset.2 ha, rfl⟩
  · intro a ha
    rfl

/-! ## §5 显式常数表（WMLNYMD.hl:1052-:1135） -/

/-- `b_tame` 不在 15 元容许表上时为 `tgt`（`b_tame_explicit` 默认支的独立形态）。 -/
private theorem bTame_eq_tgt_of_not_mem {p q : ℕ} (h : (p, q) ∉ vertexPairs) :
    bTame p q = tgt := by
  have hnt : ¬ isVertexType p q := fun hv => h (isVertexType_iff_mem.mp hv)
  have e03 : ¬(p = 0 ∧ q = 3) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e04 : ¬(p = 0 ∧ q = 4) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e12 : ¬(p = 1 ∧ q = 2) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e13 : ¬(p = 1 ∧ q = 3) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e21 : ¬(p = 2 ∧ q = 1) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e22 : ¬(p = 2 ∧ q = 2) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e23 : ¬(p = 2 ∧ q = 3) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e31 : ¬(p = 3 ∧ q = 1) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e32 : ¬(p = 3 ∧ q = 2) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e40 : ¬(p = 4 ∧ q = 0) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e41 : ¬(p = 4 ∧ q = 1) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e50 : ¬(p = 5 ∧ q = 0) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e51 : ¬(p = 5 ∧ q = 1) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e60 : ¬(p = 6 ∧ q = 0) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e70 : ¬(p = 7 ∧ q = 0) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  unfold bTame
  rw [if_neg e03, if_neg e04, if_neg e12, if_neg e13, if_neg e21, if_neg e22, if_neg e23,
    if_neg e31, if_neg e32, if_neg e40, if_neg e41, if_neg e50, if_neg e51, if_neg e60,
    if_neg e70]

/-- `squanderVertex p q = squanderTarget`（不在 15 元表上时）。 -/
private theorem squanderVertex_eq_target_of_not_mem {p q : ℕ}
    (h : (p, q) ∉ vertexPairs) : squanderVertex p q = squanderTarget := by
  have hnt : ¬ isVertexType p q := fun hv => h (isVertexType_iff_mem.mp hv)
  have e03 : ¬(p = 0 ∧ q = 3) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e04 : ¬(p = 0 ∧ q = 4) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e12 : ¬(p = 1 ∧ q = 2) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e13 : ¬(p = 1 ∧ q = 3) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e21 : ¬(p = 2 ∧ q = 1) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e22 : ¬(p = 2 ∧ q = 2) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e23 : ¬(p = 2 ∧ q = 3) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e31 : ¬(p = 3 ∧ q = 1) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e32 : ¬(p = 3 ∧ q = 2) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e40 : ¬(p = 4 ∧ q = 0) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e41 : ¬(p = 4 ∧ q = 1) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e50 : ¬(p = 5 ∧ q = 0) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e51 : ¬(p = 5 ∧ q = 1) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e60 : ¬(p = 6 ∧ q = 0) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  have e70 : ¬(p = 7 ∧ q = 0) := by
    rintro ⟨rfl, rfl⟩; exact hnt (by unfold isVertexType; simp)
  unfold squanderVertex
  rw [if_neg e03, if_neg e04, if_neg e12, if_neg e13, if_neg e21, if_neg e22, if_neg e23,
    if_neg e31, if_neg e32, if_neg e40, if_neg e41, if_neg e50, if_neg e51, if_neg e60,
    if_neg e70]

/-- HOL `b_tame_explicit`（WMLNYMD.hl:1052）逐字（15 个表值 + 默认支）。 -/
theorem bTameExplicit :
    bTame 0 3 = 0.618 ∧ bTame 0 4 = 0.97 ∧
    bTame 1 2 = 0.656 ∧ bTame 1 3 = 0.618 ∧
    bTame 2 1 = 0.797 ∧ bTame 2 2 = 0.412 ∧ bTame 2 3 = 1.2851 ∧
    bTame 3 1 = 0.311 ∧ bTame 3 2 = 0.817 ∧
    bTame 4 0 = 0.347 ∧ bTame 4 1 = 0.366 ∧
    bTame 5 0 = 0.04 ∧ bTame 5 1 = 1.136 ∧
    bTame 6 0 = 0.686 ∧ bTame 7 0 = 1.450 ∧
    (∀ p q : ℕ, ¬((p, q) = (0, 3)) → ¬((p, q) = (0, 4)) →
      ¬((p, q) = (1, 2)) → ¬((p, q) = (1, 3)) →
      ¬((p, q) = (2, 1)) → ¬((p, q) = (2, 2)) → ¬((p, q) = (2, 3)) →
      ¬((p, q) = (3, 1)) → ¬((p, q) = (3, 2)) →
      ¬((p, q) = (4, 0)) → ¬((p, q) = (4, 1)) →
      ¬((p, q) = (5, 0)) → ¬((p, q) = (5, 1)) →
      ¬((p, q) = (6, 0)) → ¬((p, q) = (7, 0)) → bTame p q = tgt) := by
  refine ⟨by norm_num [bTame], by norm_num [bTame], by norm_num [bTame],
    by norm_num [bTame], by norm_num [bTame], by norm_num [bTame],
    by norm_num [bTame], by norm_num [bTame], by norm_num [bTame],
    by norm_num [bTame], by norm_num [bTame], by norm_num [bTame],
    by norm_num [bTame], by norm_num [bTame], by norm_num [bTame], ?_⟩
  intro p q h03 h04 h12 h13 h21 h22 h23 h31 h32 h40 h41 h50 h51 h60 h70
  have hnot : (p, q) ∉ vertexPairs := by
    intro hmem
    have hdisj : (p, q) = (0, 3) ∨ (p, q) = (0, 4) ∨ (p, q) = (1, 2) ∨
        (p, q) = (1, 3) ∨ (p, q) = (2, 1) ∨ (p, q) = (2, 2) ∨ (p, q) = (2, 3) ∨
        (p, q) = (3, 1) ∨ (p, q) = (3, 2) ∨ (p, q) = (4, 0) ∨ (p, q) = (4, 1) ∨
        (p, q) = (5, 0) ∨ (p, q) = (5, 1) ∨ (p, q) = (6, 0) ∨ (p, q) = (7, 0) :=
      isVertexType_iff_mem.mpr hmem
    rcases hdisj with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact h03 h
    · exact h04 h
    · exact h12 h
    · exact h13 h
    · exact h21 h
    · exact h22 h
    · exact h23 h
    · exact h31 h
    · exact h32 h
    · exact h40 h
    · exact h41 h
    · exact h50 h
    · exact h51 h
    · exact h60 h
    · exact h70 h
  exact bTame_eq_tgt_of_not_mem hnot

/-- HOL `squanderVertex_explicit`（WMLNYMD.hl:1075）逐字（15 个表值 + 默认支）。 -/
theorem squanderVertexExplicit :
    squanderVertex 0 3 = 6177 ∧ squanderVertex 0 4 = 9696 ∧
    squanderVertex 1 2 = 6557 ∧ squanderVertex 1 3 = 6176 ∧
    squanderVertex 2 1 = 7967 ∧ squanderVertex 2 2 = 4116 ∧
    squanderVertex 2 3 = 12846 ∧
    squanderVertex 3 1 = 3106 ∧ squanderVertex 3 2 = 8165 ∧
    squanderVertex 4 0 = 3466 ∧ squanderVertex 4 1 = 3655 ∧
    squanderVertex 5 0 = 395 ∧ squanderVertex 5 1 = 11354 ∧
    squanderVertex 6 0 = 6854 ∧ squanderVertex 7 0 = 14493 ∧
    (∀ p q : ℕ, ¬((p, q) = (0, 3)) → ¬((p, q) = (0, 4)) →
      ¬((p, q) = (1, 2)) → ¬((p, q) = (1, 3)) →
      ¬((p, q) = (2, 1)) → ¬((p, q) = (2, 2)) → ¬((p, q) = (2, 3)) →
      ¬((p, q) = (3, 1)) → ¬((p, q) = (3, 2)) →
      ¬((p, q) = (4, 0)) → ¬((p, q) = (4, 1)) →
      ¬((p, q) = (5, 0)) → ¬((p, q) = (5, 1)) →
      ¬((p, q) = (6, 0)) → ¬((p, q) = (7, 0)) →
        squanderVertex p q = squanderTarget) := by
  refine ⟨by norm_num [squanderVertex], by norm_num [squanderVertex],
    by norm_num [squanderVertex], by norm_num [squanderVertex],
    by norm_num [squanderVertex], by norm_num [squanderVertex],
    by norm_num [squanderVertex], by norm_num [squanderVertex],
    by norm_num [squanderVertex], by norm_num [squanderVertex],
    by norm_num [squanderVertex], by norm_num [squanderVertex],
    by norm_num [squanderVertex], by norm_num [squanderVertex],
    by norm_num [squanderVertex], ?_⟩
  intro p q h03 h04 h12 h13 h21 h22 h23 h31 h32 h40 h41 h50 h51 h60 h70
  have hnot : (p, q) ∉ vertexPairs := by
    intro hmem
    have hdisj : (p, q) = (0, 3) ∨ (p, q) = (0, 4) ∨ (p, q) = (1, 2) ∨
        (p, q) = (1, 3) ∨ (p, q) = (2, 1) ∨ (p, q) = (2, 2) ∨ (p, q) = (2, 3) ∨
        (p, q) = (3, 1) ∨ (p, q) = (3, 2) ∨ (p, q) = (4, 0) ∨ (p, q) = (4, 1) ∨
        (p, q) = (5, 0) ∨ (p, q) = (5, 1) ∨ (p, q) = (6, 0) ∨ (p, q) = (7, 0) :=
      isVertexType_iff_mem.mpr hmem
    rcases hdisj with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact h03 h
    · exact h04 h
    · exact h12 h
    · exact h13 h
    · exact h21 h
    · exact h22 h
    · exact h23 h
    · exact h31 h
    · exact h32 h
    · exact h40 h
    · exact h41 h
    · exact h50 h
    · exact h51 h
    · exact h60 h
    · exact h70 h
  exact squanderVertex_eq_target_of_not_mem hnot

/-- 容许表上的顶点表算术（WMLNYMD.hl:1216-:1222 的逐值 `REAL_ARITH`）：
`squanderVertex p q + p + q <= b_tame p q * 10000`（15 元逐项核对，全部取等）。 -/
private theorem svAddLeBTameMul {p q : ℕ} (hp : (p, q) ∈ vertexPairs) :
    (squanderVertex p q : ℝ) + (p : ℝ) + (q : ℝ) ≤ bTame p q * 10000 := by
  simp only [vertexPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals norm_num [squanderVertex, bTame]

/-- HOL `vertextypes_explicit`（WMLNYMD.hl:1098）。 -/
theorem vertextypesExplicit {α : Type*} [DecidableEq α] (H : Hypermap α)
    (w : Set α → ℝ) (x : α) (p q : ℕ) (htw : totalWeight H w < tgt)
    (h9 : Tame9a H) (h1 : Adm1 H w) (h2 : Adm2 H w) (hx : x ∈ H.darts)
    (hexc : (setOfExceptionalMeetingNode H x).ncard = 0)
    (hp : (setOfTrianglesMeetingNode H x).ncard = p)
    (hq : (setOfQuadrilateralsMeetingNode H x).ncard = q) :
    (p, q) = (0, 3) ∨ (p, q) = (0, 4) ∨ (p, q) = (1, 2) ∨ (p, q) = (1, 3) ∨
      (p, q) = (2, 1) ∨ (p, q) = (2, 2) ∨ (p, q) = (2, 3) ∨ (p, q) = (3, 1) ∨
      (p, q) = (3, 2) ∨ (p, q) = (4, 0) ∨ (p, q) = (4, 1) ∨ (p, q) = (5, 0) ∨
      (p, q) = (5, 1) ∨ (p, q) = (6, 0) ∨ (p, q) = (7, 0) := by
  by_contra hcon
  have hnot : (p, q) ∉ vertexPairs := fun hm => hcon (isVertexType_iff_mem.mpr hm)
  have hbt : bTame p q = tgt := bTame_eq_tgt_of_not_mem hnot
  have h2x : bTame p q ≤ setSum (setOfFaceMeetingNode H x) w := by
    have h := h2 x hx hexc
    rwa [hp, hq] at h
  have hle1 : setSum (setOfFaceMeetingNode H x) w ≤ totalWeight H w :=
    setSum_le_of_subset (setOfFaceMeetingNode_subset_faceSet H x)
      (faceSet_nonneg (H := H) (w := w) h1) (Kepler.Text.Hypermap.faceSet_finite H)
  have hfin : bTame p q ≤ totalWeight H w := h2x.trans hle1
  rw [hbt] at hfin
  linarith

/-! ## §6 容许表上的 floor 桥（WMLNYMD.hl:1137-:1303） -/

/-- HOL `no_except_empty`（WMLNYMD.hl:1137）。 -/
theorem noExceptEmpty {α : Type*} [DecidableEq α] (H : Hypermap α) (x : α)
    (h : (setOfExceptionalMeetingNode H x).ncard = 0) :
    setOfExceptionalMeetingNode H x = ∅ :=
  (Set.ncard_eq_zero (s := setOfExceptionalMeetingNode H x)
    (finiteSetOfNMeetingNode H x).2.2).mp h

/-- HOL `no_except_wfloor`（WMLNYMD.hl:1148）。 -/
theorem noExceptWfloor {α : Type*} [DecidableEq α] (H : Hypermap α) (w : Set α → ℝ)
    (x : α) (hexc : (setOfExceptionalMeetingNode H x).ncard = 0) (hx : x ∈ H.darts) :
    wtFloor w (H.face x) = nfloor 10000 (w (H.face x)) := by
  have hemp : setOfExceptionalMeetingNode H x = ∅ := noExceptEmpty H x hexc
  unfold wtFloor
  rw [if_neg]
  intro hc
  have hmem : H.face x ∈ setOfExceptionalMeetingNode H x :=
    ⟨x, hx, rfl, by omega, Kepler.Text.Hypermap.mem_node_self H x⟩
  rw [hemp] at hmem
  exact hmem

/-- HOL `set_of_exceptional_meeting_node_identity`（WMLNYMD.hl:1172，
HOL 原文 `x IN dart H /\ y IN node H x ==> ...`）。 -/
theorem setOfExceptionalMeetingNodeIdentity {α : Type*} [DecidableEq α]
    (H : Hypermap α) {x y : α} (_hx : x ∈ H.darts) (hy : y ∈ H.node x) :
    setOfExceptionalMeetingNode H x = setOfExceptionalMeetingNode H y := by
  have hnode : H.node x = H.node y := Kepler.Text.Hypermap.node_eq_of_mem H hy
  ext F
  simp only [setOfExceptionalMeetingNode, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, hz, hF, h5, hzx⟩
    exact ⟨z, hz, hF, h5, by rwa [hnode] at hzx⟩
  · rintro ⟨z, hz, hF, h5, hzy⟩
    exact ⟨z, hz, hF, h5, by rwa [← hnode] at hzy⟩

/-- HOL `set_of_n_meeting_node_union`（WMLNYMD.hl:1031）。 -/
theorem setOfNMeetingNodeUnion {α : Type*} [DecidableEq α] {H : Hypermap α} {x : α}
    (h9 : Tame9a H) :
    setOfFaceMeetingNode H x =
      setOfTrianglesMeetingNode H x ∪ setOfQuadrilateralsMeetingNode H x ∪
        setOfExceptionalMeetingNode H x := by
  ext F
  simp only [setOfFaceMeetingNode, setOfTrianglesMeetingNode,
    setOfQuadrilateralsMeetingNode, setOfExceptionalMeetingNode, Set.mem_setOf_eq,
    Set.mem_union]
  constructor
  · rintro ⟨y, hy, rfl, hyx⟩
    have hcard := h9 y hy
    have : (H.face y).ncard = 3 ∨ (H.face y).ncard = 4 ∨ 5 ≤ (H.face y).ncard := by
      omega
    rcases this with h | h | h
    · exact Or.inl (Or.inl ⟨y, hy, rfl, h, hyx⟩)
    · exact Or.inl (Or.inr ⟨y, hy, rfl, h, hyx⟩)
    · exact Or.inr ⟨y, hy, rfl, h, hyx⟩
  · intro h
    rcases h with (⟨y, hy, rfl, _, hyx⟩ | ⟨y, hy, rfl, _, hyx⟩) |
      ⟨y, hy, rfl, _, hyx⟩
    · exact ⟨y, hy, rfl, hyx⟩
    · exact ⟨y, hy, rfl, hyx⟩
    · exact ⟨y, hy, rfl, hyx⟩

/-- HOL `adm_2_floor_adm_2`（WMLNYMD.hl:1181）。 -/
theorem adm2FloorAdm2 {α : Type*} [DecidableEq α] (H : Hypermap α) (w : Set α → ℝ)
    (h9 : Tame9a H) (h1 : Adm1 H w) (h2 : Adm2 H w) (htw : totalWeight H w < tgt) :
    Adm2Floor H (wtFloor w) := by
  intro x hx hexc
  have hvt : isVertexType (setOfTrianglesMeetingNode H x).ncard
      (setOfQuadrilateralsMeetingNode H x).ncard :=
    vertextypesExplicit H w x (setOfTrianglesMeetingNode H x).ncard
      (setOfQuadrilateralsMeetingNode H x).ncard htw h9 h1 h2 hx hexc rfl rfl
  have hmem : ((setOfTrianglesMeetingNode H x).ncard,
      (setOfQuadrilateralsMeetingNode H x).ncard) ∈ vertexPairs :=
    isVertexType_iff_mem.mp hvt
  have htab := svAddLeBTameMul hmem
  have h2x : bTame (setOfTrianglesMeetingNode H x).ncard
        (setOfQuadrilateralsMeetingNode H x).ncard ≤
      setSum (setOfFaceMeetingNode H x) w := h2 x hx hexc
  have h2r : bTame (setOfTrianglesMeetingNode H x).ncard
        (setOfQuadrilateralsMeetingNode H x).ncard * 10000 ≤
      setSum (setOfFaceMeetingNode H x) w * 10000 :=
    mul_le_mul_of_nonneg_right h2x (by norm_num)
  have hSfin : (setOfFaceMeetingNode H x).Finite := finiteSetOfFaceMeetingNode H x
  have hsum_le : setSum (setOfFaceMeetingNode H x) w * 10000 ≤
      (nsum (setOfFaceMeetingNode H x) (wtFloor w) : ℝ) +
        ((setOfFaceMeetingNode H x).ncard : ℝ) := by
    rw [← setSum_mul_const hSfin w 10000]
    calc setSum (setOfFaceMeetingNode H x) (fun f => w f * 10000)
        ≤ setSum (setOfFaceMeetingNode H x)
            (fun f => (wtFloor w f : ℝ) + 1) := by
          refine setSum_le hSfin ?_
          intro f hf
          obtain ⟨y, hy, rfl, hyx⟩ := hf
          have hexcy : (setOfExceptionalMeetingNode H y).ncard = 0 := by
            rw [← setOfExceptionalMeetingNodeIdentity H hx hyx]
            exact hexc
          have hwf : wtFloor w (H.face y) = nfloor 10000 (w (H.face y)) :=
            noExceptWfloor H w y hexcy hy
          rw [hwf]
          exact le_nfloor_add_one 10000 (w (H.face y))
      _ = (nsum (setOfFaceMeetingNode H x) (wtFloor w) : ℝ) +
            ((setOfFaceMeetingNode H x).ncard : ℝ) :=
          setSum_add_one hSfin (wtFloor w)
  have hcard : (setOfFaceMeetingNode H x).ncard ≤
      (setOfTrianglesMeetingNode H x).ncard +
        (setOfQuadrilateralsMeetingNode H x).ncard := by
    have hunion := setOfNMeetingNodeUnion (H := H) (x := x) h9
    have hemp : setOfExceptionalMeetingNode H x = ∅ := noExceptEmpty H x hexc
    rw [hunion, hemp, Set.union_empty]
    exact Set.ncard_union_le _ _
  have hcardR : ((setOfFaceMeetingNode H x).ncard : ℝ) ≤
      ((setOfTrianglesMeetingNode H x).ncard : ℝ) +
        ((setOfQuadrilateralsMeetingNode H x).ncard : ℝ) := by
    exact_mod_cast hcard
  have hgoalR : (squanderVertex (setOfTrianglesMeetingNode H x).ncard
      (setOfQuadrilateralsMeetingNode H x).ncard : ℝ) ≤
      (nsum (setOfFaceMeetingNode H x) (wtFloor w) : ℝ) := by
    linarith
  exact Nat.cast_le.mp hgoalR

/-- HOL `adm_3_floor_adm_3`（WMLNYMD.hl:1246）。 -/
theorem adm3FloorAdm3 {α : Type*} [DecidableEq α] (H : Hypermap α) (w : Set α → ℝ)
    (h9 : Tame9a H) (h1 : Adm1 H w) (h3 : Adm3 H w) : Adm3Floor H (wtFloor w) := by
  intro x hx htype
  have h3x : aTame ≤ setSum (setOfTrianglesMeetingNode H x) w := h3 x hx htype
  have h5 : (setOfTrianglesMeetingNode H x).ncard = 5 := by
    have h := htype
    simp only [Kepler.Text.TameLp.typeOfNode, Prod.mk.injEq] at h
    exact h.1
  have hSfin : (setOfTrianglesMeetingNode H x).Finite :=
    (finiteSetOfNMeetingNode H x).1
  have hsum_le : setSum (setOfTrianglesMeetingNode H x) w * 10000 ≤
      (nsum (setOfTrianglesMeetingNode H x) (wtFloor w) : ℝ) +
        ((setOfTrianglesMeetingNode H x).ncard : ℝ) := by
    rw [← setSum_mul_const hSfin w 10000]
    calc setSum (setOfTrianglesMeetingNode H x) (fun f => w f * 10000)
        ≤ setSum (setOfTrianglesMeetingNode H x)
            (fun f => (wtFloor w f : ℝ) + 1) := by
          refine setSum_le hSfin ?_
          intro f hf
          obtain ⟨y, hy, rfl, hc3, _⟩ := hf
          have hwf : wtFloor w (H.face y) = nfloor 10000 (w (H.face y)) := by
            unfold wtFloor
            rw [if_neg]
            omega
          rw [hwf]
          exact le_nfloor_add_one 10000 (w (H.face y))
      _ = (nsum (setOfTrianglesMeetingNode H x) (wtFloor w) : ℝ) +
            ((setOfTrianglesMeetingNode H x).ncard : ℝ) :=
          setSum_add_one hSfin (wtFloor w)
  have h6300 : (6300 : ℝ) ≤ setSum (setOfTrianglesMeetingNode H x) w * 10000 := by
    have ha : aTame = 0.63 := rfl
    have h63 : (6300 : ℝ) = 0.63 * 10000 := by norm_num
    nlinarith
  have h5R : ((setOfTrianglesMeetingNode H x).ncard : ℝ) = 5 := by
    exact_mod_cast h5
  have hgoalR : (excessTCount : ℝ) ≤
      (nsum (setOfTrianglesMeetingNode H x) (wtFloor w) : ℝ) := by
    have he : (excessTCount : ℝ) = 6295 := by
      unfold excessTCount
      norm_num
    linarith
  exact Nat.cast_le.mp hgoalR

/-- HOL `tame_13_a_floor_tame_13_a`（WMLNYMD.hl:1293）。 -/
theorem tame13aFloorTame13a {α : Type*} [DecidableEq α] (H : Hypermap α)
    (h13 : Tame13a H) (h9 : Tame9a H) : Tame13aFloor H := by
  obtain ⟨w, ⟨h1, h2, h3⟩, htw⟩ := h13
  exact ⟨wtFloor w, adm1FloorAdm1 H w h1 h9, adm2FloorAdm2 H w h9 h1 h2 htw,
    adm3FloorAdm3 H w h9 h1 h3, totalWeightFloor H w h1 htw⟩

end Kepler.Text.TameCorrFloor
