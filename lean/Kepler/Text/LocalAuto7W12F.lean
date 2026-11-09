/-
LocalAuto7W12F: W12(b2b-ii) — straight 支新扇的 `dih2k` 组装（第 1 段：darts 计数）。

本文件交：`FF'`/`FF'rev` 两基数、`selfPairs = ∅`、`ordPairs = FF' ∪ FF'rev`、
`darts = FF' ∪ FF'rev`、**`H.darts.card = 2 * FF'.ncard`**（`dih2k_p3` 第一合取）。
face/node `hasOrders` 与 face∪node 分划、`localFan_p3`/`LocalFan` 收口留下半。

基线 HEAD `f1f78dd1`（W12E 258 行）；LA7 / W12E 均零改动。
-/
import Kepler.Text.LocalAuto7W12E

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-- `FF'rev = {(r w, w) | w ∈ V'}`。 -/
def p12f_FFrev (V : Set V3) (FF : Set (V3 × V3)) (v : V3) : Set (V3 × V3) :=
  {d | ∃ w ∈ p12b_V V v, d = (p12b_R FF v w, w)}

/-- `FF' = {(w, r w) | w ∈ V'}`（图像形）。 -/
theorem p12f_FF_eq_image {V : Set V3} {FF : Set (V3 × V3)} {v : V3} :
    p12b_FF V FF v = (fun w : V3 => (w, p12b_R FF v w)) '' p12b_V V v := by
  ext d
  simp only [p12b_FF, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩

/-- `FF'rev = {(r w, w) | w ∈ V'}`（图像形）。 -/
theorem p12f_FFrev_eq_image {V : Set V3} {FF : Set (V3 × V3)} {v : V3} :
    p12f_FFrev V FF v = (fun w : V3 => (p12b_R FF v w, w)) '' p12b_V V v := by
  ext d
  simp only [p12f_FFrev, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨w, hw, h⟩
    exact ⟨w, hw, h.symm⟩
  · rintro ⟨w, hw, h⟩
    exact ⟨w, hw, h.symm⟩

/-- `FF'.ncard = V'.ncard`（`w ↦ (w, r w)` 单射）。 -/
theorem p12f_FF_card {V : Set V3} {FF : Set (V3 × V3)} {v : V3} :
    (p12b_FF V FF v).ncard = (p12b_V V v).ncard := by
  rw [p12f_FF_eq_image]
  refine Set.InjOn.ncard_image ?_
  intro a ha b hb h
  exact congrArg Prod.fst h

/-- `FF'rev.ncard = V'.ncard`（`w ↦ (r w, w)` 单射）。 -/
theorem p12f_FFrev_card {V : Set V3} {FF : Set (V3 × V3)} {v : V3} :
    (p12f_FFrev V FF v).ncard = (p12b_V V v).ncard := by
  rw [p12f_FFrev_eq_image]
  refine Set.InjOn.ncard_image ?_
  intro a ha b hb h
  exact congrArg Prod.snd h

/-- `selfPairs = ∅`（每点都有邻边 `{w, r w}`，`EE ≠ ∅`）。 -/
theorem p12f_selfPairs_empty {V : Set V3} {FF : Set (V3 × V3)} {v : V3} :
    selfPairs_p3 (p12b_E V FF v) (p12b_V V v) = (∅ : Set (V3 × V3)) := by
  apply Set.not_nonempty_iff_eq_empty.mp
  rintro ⟨d, hd⟩
  obtain ⟨-, hdV, hEE⟩ := hd
  have hmem : p12b_R FF v d.1 ∈ EE_p3 d.1 (p12b_E V FF v) :=
    ⟨d.1, hdV, rfl⟩
  rw [hEE] at hmem
  exact hmem

/-- `ordPairs = FF' ∪ FF'rev`（四点分解；`w = r w` 的单点退化由 `p12b_R_ne` 排除）。 -/
theorem p12f_ordPairs_eq {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) :
    ordPairs_p3 (p12b_E V FF v)
      = p12b_FF V FF v ∪ p12f_FFrev V FF v := by
  ext d
  simp only [ordPairs_p3, Set.mem_setOf_eq, Set.mem_union, p12b_FF, p12f_FFrev]
  constructor
  · intro he
    obtain ⟨w, hw, hwe⟩ := he
    have hne : w ≠ p12b_R FF v w := (p12b_R_ne hcl hedge hv hw).symm
    have h1 : d.1 ∈ ({w, p12b_R FF v w} : Set V3) := by
      rw [← hwe]; exact Set.mem_insert _ _
    have h2 : d.2 ∈ ({w, p12b_R FF v w} : Set V3) := by
      rw [← hwe]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
    -- 单点退化：`d.1 = d.2` 时 `r w ∈ {d.1,d.2}` 给出 `r w = w`，与 `hne` 冲突
    have hsingle : d.1 ≠ d.2 := by
      intro heq
      apply hne
      have hw : w ∈ ({d.1, d.2} : Set V3) := by
        rw [hwe]; exact Set.mem_insert _ _
      have hrw : p12b_R FF v w ∈ ({d.1, d.2} : Set V3) := by
        rw [hwe]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
      rw [heq] at hw hrw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw hrw
      rcases hw with hw | hw <;> rcases hrw with hr | hr <;> exact hw.trans hr.symm
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hsingle
    · exact Or.inl ⟨w, hw, Prod.ext h1 h2⟩
    · exact Or.inr ⟨w, hw, Prod.ext h1 h2⟩
    · exact absurd (h1.trans h2.symm) hsingle
  · rintro (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
    · exact ⟨w, hw, rfl⟩
    · exact ⟨w, hw, by
        show ({p12b_R FF v w, w} : Set V3) = {w, p12b_R FF v w}
        rw [Set.pair_comm]⟩

/-- `darts = FF' ∪ FF'rev`（`darts = ordPairs ∪ selfPairs`，`selfPairs = ∅`）。 -/
theorem p12f_darts_eq {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) :
    dartsOfHyp_p3 (p12b_E V FF v) (p12b_V V v)
      = p12b_FF V FF v ∪ p12f_FFrev V FF v := by
  rw [dartsOfHyp_p3, p12f_ordPairs_eq hcl hedge hv, p12f_selfPairs_empty,
    Set.union_empty]

/-- **`H.darts.card = 2 * FF'.ncard`**（`dih2k_p3` 第一合取）。 -/
theorem p12f_darts_card {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v)
    (hcard3 : 3 ≤ (p12b_V V v).ncard)
    {H : @Hypermap (V3 × V3) dartDecEq3}
    (hdarts : (↑H.darts : Set (V3 × V3))
      = dartsOfHyp_p3 (p12b_E V FF v) (p12b_V V v)) :
    H.darts.card = 2 * (p12b_FF V FF v).ncard := by
  have hfinV : (p12b_V V v).Finite := (p12b_card hcl hv).1
  have hfinFF : (p12b_FF V FF v).Finite := by
    rw [p12f_FF_eq_image]
    exact hfinV.image _
  have hfinR : (p12f_FFrev V FF v).Finite := by
    rw [p12f_FFrev_eq_image]
    exact hfinV.image _
  have hdisj : p12b_FF V FF v ∩ p12f_FFrev V FF v = ∅ := by
    simpa only [p12f_FFrev] using p12e_FFrev_disj hcl hedge hv hw0 hcard3
  have hcard : H.darts.card
      = (p12b_FF V FF v ∪ p12f_FFrev V FF v).ncard := by
    rw [← Set.ncard_coe_finset (s := H.darts), hdarts, p12f_darts_eq hcl hedge hv]
  rw [hcard, Set.ncard_union_eq (Set.disjoint_iff_inter_eq_empty.mpr hdisj)
    hfinFF hfinR, p12f_FF_card, p12f_FFrev_card]
  ring

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p12f_FF_card
#print axioms Kepler.Text.p12f_FFrev_card
#print axioms Kepler.Text.p12f_selfPairs_empty
#print axioms Kepler.Text.p12f_ordPairs_eq
#print axioms Kepler.Text.p12f_darts_eq
#print axioms Kepler.Text.p12f_darts_card

end Kepler.Text
