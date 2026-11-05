/-
  Kepler.Text.TameCorrIso2 — `tame_correspondence_iso` 三波施工的 **W3 第十一波 a**：
  S4 余三件（HOL `OXAXUCS.hl:86/:408/:595`）：
  `tame11b_iso` / `tame12o_iso` / `tame13a_iso`。

  ┌─ 落点与环安全 ────────────────────────────────────────────────
  │ 唯一 import = `Kepler.Text.TameCorrIso`（→ …，闭包零
  │ `Kepler.Assembly` 本体）。环自检：
  │   `#check @Kepler.Assembly.the_kepler_conjecture_from_interfaces`
  │   必须 **unknown identifier**。
  └────────────────────────────────────────────────────────────────

  **HOL 对照**：
  · `tame11b_iso`（:86）：`tame_11b H ∧ hyp_iso f (H,H') ⇒ tame_11b H'`
    —— node 轨道基数守恒（W3-W10 `hypIso_node_ncard`）。
  · `tame12o_iso`（:408）：`tame_12o H ∧ hyp_iso f (H,H') ⇒ tame_12o H'`
    —— 例外面/6-节点谓词 + `type_of_node` 迁移；需 meeting-node 三集像等式。
  · `tame13a_iso`（:595）：`tame_13a H ∧ hyp_iso f (H,H') ⇒ tame_13a H'`
    —— 权重取 `w' F = w (f⁻¹''F)`（HOL `w o IMAGE (res_inv f (dart H))`），
    adm1/2/3 + `total_weight` 用 face 轨道像 + `setSum` 像换元。

  **本波新增引擎（W2/W3 可复用）**：
  `weightPreimage`、`hypIso_meetingNode_image`（通用 P）、
  `hypIso_setOf{Triangles,Quadrilaterals,Exceptional,Face}MeetingNode_image`、
  `hypIso_{tri,quad,exc}_ncard`、`hypIso_typeOfNode`、`hypIso_faceSet_image`、
  `hypIso_faceSet_setSum`、`hypIso_{face,triangle}Meeting_setSum`。

  **纪律**：无 `axiom`/`sorry`/`admit`/`native_decide`；不改既有陈述。
-/

import Kepler.Text.TameCorrIso

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameCorrIso2

open Classical
open Kepler.Text (Hypermap setSum dTame tgt)
open Kepler.Text.TameLp (Tame11b Tame12o Tame13a Adm1 Adm2 Adm3 AdmissibleWeight totalWeight
  setOfFaceMeetingNode setOfTrianglesMeetingNode setOfQuadrilateralsMeetingNode
  setOfExceptionalMeetingNode typeOfNode NodeTypeExceptionalFace NodeExceptionalFace
  ExceptionalFace aTame bTame)
open Kepler.Text.TameCorrFloor (finiteSetOfFaceMeetingNode finiteSetOfNMeetingNode)
open Kepler.Text.TameCorrIso (HypIso hypIso_mapsTo hypIso_surjOn hypIso_face_image
  hypIso_face_ncard hypIso_node_image hypIso_node_ncard hypIso_numberOfNodes
  tame9aIso tame10Iso tame11aIso)
open Kepler.Text.TameCorrG4b (cardSetOfNMeetingNodePqr)

/-! ## §1 `setSum` 像换元与 preimage 权重 -/

private theorem setSum_congr {α : Type*} {s : Set α} {f g : α → ℝ}
    (h : ∀ x ∈ s, f x = g x) : setSum s f = setSum s g := by
  by_cases hs : s.Finite
  · rw [setSum, dif_pos hs, setSum, dif_pos hs]
    exact Finset.sum_congr rfl fun x hx => h x (hs.mem_toFinset.1 hx)
  · rw [setSum, dif_neg hs, setSum, dif_neg hs]

/-- `setSum` 沿单射像的换元（HOL `SUM_IMAGE`；TameLp 的对应件是 private，此处自证）。 -/
private theorem setSum_image_injOn {α β : Type*} {s : Set α} (hs : s.Finite)
    {φ : α → β} (hφ : Set.InjOn φ s) (g : β → ℝ) :
    setSum (φ '' s) g = setSum s (fun x => g (φ x)) := by
  have hfin : (φ '' s).Finite := hs.image φ
  rw [setSum, dif_pos hfin, setSum, dif_pos hs]
  refine (Finset.sum_bij (fun x _ => φ x) ?_ ?_ ?_ ?_).symm
  · intro x hx
    exact hfin.mem_toFinset.2 (Set.mem_image_of_mem φ (hs.mem_toFinset.1 hx))
  · intro x1 hx1 x2 hx2 heq
    exact hφ (hs.mem_toFinset.1 hx1) (hs.mem_toFinset.1 hx2) heq
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hfin.mem_toFinset.1 hy
    exact ⟨x, hs.mem_toFinset.2 hx, rfl⟩
  · intro x _
    rfl

section Engine
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- HOL `w o IMAGE (res_inv f (dart H))`：`w' F = w {x ∈ dart H | f x ∈ F}`。 -/
def weightPreimage (f : α → β) (H : Hypermap α) (w : Set α → ℝ) : Set β → ℝ :=
  fun F => w {x : α | x ∈ H.darts ∧ f x ∈ F}

/-- 像映射 `S ↦ f '' S` 在「全为 dart 子集」的族上单射。 -/
theorem image_injOn_of_subset_darts {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (hiso : HypIso f H G) {s : Set (Set α)} (hsub : ∀ S ∈ s, S ⊆ ↑H.darts) :
    Set.InjOn (fun S : Set α => f '' S) s := by
  intro S1 h1 S2 h2 heq
  have heq' : f '' S1 = f '' S2 := heq
  ext z
  constructor
  · intro hz
    have hz1 : f z ∈ f '' S1 := ⟨z, hz, rfl⟩
    rw [heq'] at hz1
    obtain ⟨w, hw, hfw⟩ := hz1
    have hzD : z ∈ H.darts := hsub S1 h1 hz
    have hwD : w ∈ H.darts := hsub S2 h2 hw
    have hwz : w = z := hiso.1.injOn hwD hzD hfw
    exact hwz ▸ hw
  · intro hz
    have hz2 : f z ∈ f '' S2 := ⟨z, hz, rfl⟩
    rw [← heq'] at hz2
    obtain ⟨w, hw, hfw⟩ := hz2
    have hzD : z ∈ H.darts := hsub S2 h2 hz
    have hwD : w ∈ H.darts := hsub S1 h1 hw
    have hwz : w = z := hiso.1.injOn hwD hzD hfw
    exact hwz ▸ hw

/-- `f '' S` 的 preimage（限制在 dart 上）回到 `S`（`S ⊆ dart H`）。 -/
theorem preimage_image {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (hiso : HypIso f H G) {S : Set α} (hS : S ⊆ ↑H.darts) :
    {x : α | x ∈ H.darts ∧ f x ∈ f '' S} = S := by
  ext x
  constructor
  · rintro ⟨hxD, y, hyS, hyx⟩
    have hyD : y ∈ H.darts := hS hyS
    have hyxD : y = x := hiso.1.injOn hyD (by simpa using hxD) hyx
    exact hyxD ▸ hyS
  · intro hxS
    exact ⟨by simpa using hS hxS, ⟨x, hxS, rfl⟩⟩

/-- `weightPreimage` 在 `f '' S` 上回到 `w S`。 -/
theorem weightPreimage_image {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (hiso : HypIso f H G) {S : Set α} (hS : S ⊆ ↑H.darts) (w : Set α → ℝ) :
    weightPreimage f H w (f '' S) = w S := by
  unfold weightPreimage
  rw [preimage_image hiso hS]

/-- `weightPreimage` 在面轨道上回到 `w (H.face x)`。 -/
theorem weightPreimage_face {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (hiso : HypIso f H G) {x : α} (hx : x ∈ H.darts) (w : Set α → ℝ) :
    weightPreimage f H w (G.face (f x)) = w (H.face x) := by
  unfold weightPreimage
  rw [hypIso_face_image hiso hx, preimage_image hiso (Kepler.Text.Hypermap.face_subset_darts H hx)]

/-! ## §2 meeting-node 三集像等式与基数 -/

/-- 通用 meeting-node 集（HOL `set_of_{triangles,quadrilaterals,exceptional}_meeting_node`
的 `P` 参数化形）。 -/
def meetingNodeSet {α : Type*} [DecidableEq α] (H : Hypermap α) (P : ℕ → Prop) (x : α) :
    Set (Set α) :=
  {F | ∃ y ∈ H.darts, F = H.face y ∧ P (H.face y).ncard ∧ y ∈ H.node x}

/-- 通用 meeting-node 像等式：
`G.setOfN P (f x) = (f '' ·) '' H.setOfN P x`。 -/
theorem hypIso_meetingNode_image {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (hiso : HypIso f H G) {x : α} (hx : x ∈ H.darts) (P : ℕ → Prop) :
    meetingNodeSet G P (f x) = (fun F : Set α => f '' F) '' meetingNodeSet H P x := by
  have hx' : x ∈ H.darts := hx
  ext F
  constructor
  · intro hF
    obtain ⟨y, hy, hFy, hPy, hyx⟩ := hF
    obtain ⟨z, hz, hzy⟩ := hypIso_surjOn hiso hy
    have hzD : z ∈ H.darts := by simpa using hz
    have hface : G.face y = f '' H.face z := by
      rw [← hzy]
      exact hypIso_face_image hiso hzD
    have hPy' : P (H.face z).ncard := by
      rw [← hzy, hypIso_face_ncard hiso hzD] at hPy
      exact hPy
    have hnode : y ∈ G.node (f x) := hyx
    have hzx : z ∈ H.node x := by
      rw [← hzy] at hnode
      rw [hypIso_node_image hiso hx'] at hnode
      obtain ⟨w, hw, hwy⟩ := hnode
      have hwD : w ∈ H.darts := Kepler.Text.Hypermap.node_subset_darts H hx' hw
      have hww : w = z := hiso.1.injOn hwD hzD (by rw [hwy, hzy])
      exact hww ▸ hw
    refine ⟨H.face z, ⟨z, hzD, rfl, hPy', hzx⟩, ?_⟩
    change f '' (H.face z) = F
    rw [← hface]
    exact hFy.symm
  · rintro ⟨S, ⟨z, hz, rfl, hPz, hzx⟩, hSF⟩
    have hzD : z ∈ H.darts := hz
    have hSF' : f '' (H.face z) = F := hSF
    refine ⟨f z, hypIso_mapsTo hiso hzD, ?_, ?_, ?_⟩
    · rw [hypIso_face_image hiso hzD]
      exact hSF'.symm
    · rw [hypIso_face_ncard hiso hzD]
      exact hPz
    · rw [hypIso_node_image hiso hx']
      exact ⟨z, hzx, rfl⟩

/-- 三角 meeting-node 集像等式。 -/
theorem hypIso_setOfTrianglesMeetingNode_image {H : Hypermap α} {G : Hypermap β}
    {f : α → β} (hiso : HypIso f H G) {x : α} (hx : x ∈ H.darts) :
    setOfTrianglesMeetingNode G (f x)
      = (fun F : Set α => f '' F) '' setOfTrianglesMeetingNode H x := by
  have h := hypIso_meetingNode_image hiso hx (fun n => n = 3)
  simpa [meetingNodeSet, setOfTrianglesMeetingNode] using h

/-- 四边形 meeting-node 集像等式。 -/
theorem hypIso_setOfQuadrilateralsMeetingNode_image {H : Hypermap α} {G : Hypermap β}
    {f : α → β} (hiso : HypIso f H G) {x : α} (hx : x ∈ H.darts) :
    setOfQuadrilateralsMeetingNode G (f x)
      = (fun F : Set α => f '' F) '' setOfQuadrilateralsMeetingNode H x := by
  have h := hypIso_meetingNode_image hiso hx (fun n => n = 4)
  simpa [meetingNodeSet, setOfQuadrilateralsMeetingNode] using h

/-- 例外 meeting-node 集像等式。 -/
theorem hypIso_setOfExceptionalMeetingNode_image {H : Hypermap α} {G : Hypermap β}
    {f : α → β} (hiso : HypIso f H G) {x : α} (hx : x ∈ H.darts) :
    setOfExceptionalMeetingNode G (f x)
      = (fun F : Set α => f '' F) '' setOfExceptionalMeetingNode H x := by
  have h := hypIso_meetingNode_image hiso hx (fun n => 5 ≤ n)
  simpa [meetingNodeSet, setOfExceptionalMeetingNode] using h

/-- 面 meeting-node 集像等式。 -/
theorem hypIso_setOfFaceMeetingNode_image {H : Hypermap α} {G : Hypermap β}
    {f : α → β} (hiso : HypIso f H G) {x : α} (hx : x ∈ H.darts) :
    setOfFaceMeetingNode G (f x)
      = (fun F : Set α => f '' F) '' setOfFaceMeetingNode H x := by
  have h := hypIso_meetingNode_image hiso hx (fun _ => True)
  simpa [meetingNodeSet, setOfFaceMeetingNode] using h

/-- 三角 meeting-node 集基数守恒。 -/
theorem hypIso_tri_ncard {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (hiso : HypIso f H G) {x : α} (hx : x ∈ H.darts) :
    (setOfTrianglesMeetingNode G (f x)).ncard = (setOfTrianglesMeetingNode H x).ncard := by
  rw [hypIso_setOfTrianglesMeetingNode_image hiso hx]
  exact Set.InjOn.ncard_image (image_injOn_of_subset_darts hiso
    (fun S hS => by
      obtain ⟨z, hz, rfl, _, _⟩ := hS
      exact Kepler.Text.Hypermap.face_subset_darts H hz))

/-- 四边形 meeting-node 集基数守恒。 -/
theorem hypIso_quad_ncard {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (hiso : HypIso f H G) {x : α} (hx : x ∈ H.darts) :
    (setOfQuadrilateralsMeetingNode G (f x)).ncard
      = (setOfQuadrilateralsMeetingNode H x).ncard := by
  rw [hypIso_setOfQuadrilateralsMeetingNode_image hiso hx]
  exact Set.InjOn.ncard_image (image_injOn_of_subset_darts hiso
    (fun S hS => by
      obtain ⟨z, hz, rfl, _, _⟩ := hS
      exact Kepler.Text.Hypermap.face_subset_darts H hz))

/-- 例外 meeting-node 集基数守恒。 -/
theorem hypIso_exc_ncard {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (hiso : HypIso f H G) {x : α} (hx : x ∈ H.darts) :
    (setOfExceptionalMeetingNode G (f x)).ncard
      = (setOfExceptionalMeetingNode H x).ncard := by
  rw [hypIso_setOfExceptionalMeetingNode_image hiso hx]
  exact Set.InjOn.ncard_image (image_injOn_of_subset_darts hiso
    (fun S hS => by
      obtain ⟨z, hz, rfl, _, _⟩ := hS
      exact Kepler.Text.Hypermap.face_subset_darts H hz))

/-- `type_of_node` 守恒。 -/
theorem hypIso_typeOfNode {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (hiso : HypIso f H G) {x : α} (hx : x ∈ H.darts) :
    typeOfNode G (f x) = typeOfNode H x := by
  unfold Kepler.Text.TameLp.typeOfNode
  rw [hypIso_tri_ncard hiso hx, hypIso_quad_ncard hiso hx, hypIso_exc_ncard hiso hx]

/-! ## §3 faceSet 像与 `setSum` 换元 -/

/-- `faceSet` 的成员表示。 -/
private theorem mem_faceSet_iff {H : Hypermap α} {S : Set α} :
    S ∈ H.faceSet ↔ ∃ x ∈ H.darts, S = H.face x := by
  rw [Kepler.Text.Hypermap.faceSet, Kepler.Text.setOfOrbits]
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, e⟩
    exact ⟨x, hx, e.symm⟩
  · rintro ⟨x, hx, e⟩
    exact ⟨x, hx, e.symm⟩

/-- `faceSet` 的轨道像等式：`G.faceSet = (f '' ·) '' H.faceSet`。 -/
theorem hypIso_faceSet_image {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (hiso : HypIso f H G) :
    G.faceSet = (fun S : Set α => f '' S) '' H.faceSet := by
  ext S
  constructor
  · intro hS
    obtain ⟨y, hy, rfl⟩ := mem_faceSet_iff.mp hS
    obtain ⟨x, hx, hxy⟩ := hypIso_surjOn hiso hy
    have hxD : x ∈ H.darts := by simpa using hx
    refine ⟨H.face x, mem_faceSet_iff.mpr ⟨x, hxD, rfl⟩, ?_⟩
    change f '' (H.face x) = G.face y
    rw [← hxy]
    exact (hypIso_face_image hiso hxD).symm
  · rintro ⟨S', hS', rfl⟩
    obtain ⟨x, hx, rfl⟩ := mem_faceSet_iff.mp hS'
    change f '' (H.face x) ∈ G.faceSet
    rw [← hypIso_face_image hiso hx]
    exact mem_faceSet_iff.mpr ⟨f x, hypIso_mapsTo hiso hx, rfl⟩

/-- `total_weight` 换元：`setSum (face_set H') w' = setSum (face_set H) w`。 -/
theorem hypIso_faceSet_setSum {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (hiso : HypIso f H G) (w : Set α → ℝ) :
    setSum G.faceSet (weightPreimage f H w) = setSum H.faceSet w := by
  have hinj : Set.InjOn (fun S : Set α => f '' S) H.faceSet :=
    image_injOn_of_subset_darts hiso
      (fun S hS => by
        obtain ⟨x, hx, rfl⟩ := mem_faceSet_iff.mp hS
        exact Kepler.Text.Hypermap.face_subset_darts H hx)
  rw [hypIso_faceSet_image hiso]
  rw [setSum_image_injOn (Kepler.Text.Hypermap.faceSet_finite H) hinj]
  exact setSum_congr (fun S hS => by
    obtain ⟨x, hx, rfl⟩ := mem_faceSet_iff.mp hS
    simpa using weightPreimage_image hiso (Kepler.Text.Hypermap.face_subset_darts H hx) w)

/-- 面 meeting-node 集上的 `setSum` 换元。 -/
theorem hypIso_faceMeeting_setSum {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (hiso : HypIso f H G) {x : α} (hx : x ∈ H.darts) (w : Set α → ℝ) :
    setSum (setOfFaceMeetingNode G (f x)) (weightPreimage f H w)
      = setSum (setOfFaceMeetingNode H x) w := by
  have hinj : Set.InjOn (fun S : Set α => f '' S) (setOfFaceMeetingNode H x) :=
    image_injOn_of_subset_darts hiso
      (fun S hS => by
        obtain ⟨z, hz, rfl, _⟩ := hS
        exact Kepler.Text.Hypermap.face_subset_darts H hz)
  rw [hypIso_setOfFaceMeetingNode_image hiso hx]
  rw [setSum_image_injOn (finiteSetOfFaceMeetingNode H x) hinj]
  exact setSum_congr (fun S hS => by
    obtain ⟨z, hz, rfl, _⟩ := hS
    simpa using weightPreimage_image hiso (Kepler.Text.Hypermap.face_subset_darts H hz) w)

/-- 三角 meeting-node 集上的 `setSum` 换元。 -/
theorem hypIso_triangleMeeting_setSum {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (hiso : HypIso f H G) {x : α} (hx : x ∈ H.darts) (w : Set α → ℝ) :
    setSum (setOfTrianglesMeetingNode G (f x)) (weightPreimage f H w)
      = setSum (setOfTrianglesMeetingNode H x) w := by
  have hinj : Set.InjOn (fun S : Set α => f '' S) (setOfTrianglesMeetingNode H x) :=
    image_injOn_of_subset_darts hiso
      (fun S hS => by
        obtain ⟨z, hz, rfl, _, _⟩ := hS
        exact Kepler.Text.Hypermap.face_subset_darts H hz)
  rw [hypIso_setOfTrianglesMeetingNode_image hiso hx]
  rw [setSum_image_injOn (finiteSetOfNMeetingNode H x).1 hinj]
  exact setSum_congr (fun S hS => by
    obtain ⟨z, hz, rfl, _, _⟩ := hS
    simpa using weightPreimage_image hiso (Kepler.Text.Hypermap.face_subset_darts H hz) w)

/-! ## §4 S4 余三件 -/

/-- HOL `tame11b_iso`（OXAXUCS.hl:86）：`tame_11b H ∧ hyp_iso f (H,H') ⇒ tame_11b H'`。 -/
theorem tame11bIso {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (h : Tame11b H) (hiso : HypIso f H G) : Tame11b G := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hypIso_surjOn hiso hy
  rw [← hxy, hypIso_node_ncard hiso hx]
  exact h x hx

/-- HOL `tame12o_iso`（OXAXUCS.hl:408）：`tame_12o H ∧ hyp_iso f (H,H') ⇒ tame_12o H'`。 -/
theorem tame12oIso {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (h : Tame12o H) (hiso : HypIso f H G) : Tame12o G := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hypIso_surjOn hiso hy
  rw [← hxy]
  have hx' := h x hx
  refine ⟨?_, ?_⟩
  · -- node_type_exceptional_face
    intro hE
    obtain ⟨hEface, hE6⟩ := hE
    have hE' : ExceptionalFace H x := by
      show 5 ≤ (H.face x).ncard
      rw [← hypIso_face_ncard hiso hx]
      exact hEface
    have h6' : (H.node x).ncard = 6 := by
      rw [← hypIso_node_ncard hiso hx]
      exact hE6
    rw [hypIso_typeOfNode hiso hx]
    exact hx'.1 ⟨hE', h6'⟩
  · -- node_exceptional_face
    intro hE
    have hE' : ExceptionalFace H x := by
      show 5 ≤ (H.face x).ncard
      rw [← hypIso_face_ncard hiso hx]
      exact hE
    rw [hypIso_node_ncard hiso hx]
    exact hx'.2 hE'

/-- HOL `tame13a_iso`（OXAXUCS.hl:595）：`tame_13a H ∧ hyp_iso f (H,H') ⇒ tame_13a H'`。 -/
theorem tame13aIso {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (h : Tame13a H) (hiso : HypIso f H G) : Tame13a G := by
  obtain ⟨w, ⟨h1, h2, h3⟩, htot⟩ := h
  refine ⟨weightPreimage f H w, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- adm_1
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hypIso_surjOn hiso hy
    rw [← hxy, weightPreimage_face hiso hx w, hypIso_face_ncard hiso hx]
    exact h1 x hx
  · -- adm_2
    intro y hy hexc
    obtain ⟨x, hx, hxy⟩ := hypIso_surjOn hiso hy
    rw [← hxy] at hexc
    have hexc' : (setOfExceptionalMeetingNode H x).ncard = 0 := by
      rw [← hypIso_exc_ncard hiso hx]
      exact hexc
    have h2x := h2 x hx hexc'
    rw [← hxy]
    rw [hypIso_tri_ncard hiso hx, hypIso_quad_ncard hiso hx,
      hypIso_faceMeeting_setSum hiso hx w]
    exact h2x
  · -- adm_3
    intro y hy htype
    obtain ⟨x, hx, hxy⟩ := hypIso_surjOn hiso hy
    rw [← hxy] at htype
    have htype' : typeOfNode H x = (5, 0, 1) := by
      rw [← hypIso_typeOfNode hiso hx]
      exact htype
    have h3x := h3 x hx htype'
    rw [← hxy]
    rw [hypIso_triangleMeeting_setSum hiso hx w]
    exact h3x
  · -- total_weight
    show setSum G.faceSet (weightPreimage f H w) < tgt
    rw [hypIso_faceSet_setSum hiso w]
    exact htot

end Engine

end Kepler.Text.TameCorrIso2
