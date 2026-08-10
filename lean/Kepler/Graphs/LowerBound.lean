/-
Port of the Isabelle AFP "Flyspeck-Tame" theory `LowerBound.thy`.

Source: `reference/afp-flyspeck-tame/LowerBound.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

Contents: the six arithmetic `trans` lemmas and the main theorem
`total_weight_lowerbound` (`squanderLowerBound g ≤ ∑ f ∈ faces g, w f`
for every admissible weight assignment `w` of a final tame graph).

Correspondence notes (conventions as in `Tame.lean` / `ScoreProps.lean`):
- `∑⇘x ∈ xs⇙ f` ↦ `∑ₗ x ∈ xs, f` (`ListSum`); `d |vertices f|` ↦
  `squanderFace f.vertices.length`; `a` ↦ `excessTCount`;
  `b (tri g v) (quad g v)` ↦ `squanderVertex (tri g v) (quad g v)`;
  `d 3`/`d 4` ↦ `d3_const`/`d4_const`.
- Isabelle's list comprehensions `[x ← xs. P x]` are `List.filter` with a
  decidable `Prop` (elaborated to `decide`).
- The Isabelle proof is a single long `calc`-style chain mixing `=` and `≤`
  via the `trans1`–`trans6` lemmas; here the steps are proved as separate
  `have`s and the final inequality is closed by `omega` over the resulting
  linear (in)equalities.
- The hypothesis `∑ f ∈ faces g, w f < squanderTarget` is part of the
  Isabelle statement but is never used in the proof (as in Isabelle).
-/
import Kepler.Graphs.PlaneProps
import Kepler.Graphs.ScoreProps

namespace Kepler.Graphs

/-! ### Arithmetic transitivity helpers (`LowerBound.thy`, lines 10–28) -/

/-- LowerBound.thy: trans1 -/
theorem trans1 {l a1 a2 a3 a4 r : Nat} (h : l = a1 + a2 + (a3 + a4))
    (hr : a1 + a3 = r) : l = r + a2 + a4 := by omega

/-- LowerBound.thy: trans2 -/
theorem trans2 {l a1 a2 a3 r : Nat} (h : l = a1 + a2 + a3) (hr : a1 ≤ r) :
    l ≤ r + a2 + a3 := by omega

/-- LowerBound.thy: trans3 -/
theorem trans3 {l a1 a2 a3 a4 r : Nat} (h : l ≤ a1 + a2 + (a3 + a4))
    (hr : a2 + a3 ≤ r) : l ≤ a1 + r + a4 := by omega

/-- LowerBound.thy: trans4 -/
theorem trans4 {l a1 a2 a3 r : Nat} (h : l ≤ a1 + a2 + a3) (hr : a3 ≤ r) :
    l ≤ a1 + a2 + r := by omega

/-- LowerBound.thy: trans5 -/
theorem trans5 {l a1 a2 a3 r : Nat} (h : l ≤ a1 + a2 + a3) (hr : a2 + a3 = r) :
    l ≤ a1 + r := by omega

/-- LowerBound.thy: trans6 -/
theorem trans6 {a b1 b2 b3 b4 : Nat} (h : a = b1 + (b2 + b3) + b4) (h0 : b3 = 0) :
    a = b1 + b2 + b4 := by omega

/-- Auxiliary: `ListSum_compl2` restated for `Prop`-valued (decidable)
filter predicates, matching the Isabelle `ListSum_compl` splits. -/
private theorem ListSum_filter_compl {β : Type*} (P : β → Prop) [DecidablePred P]
    (f : β → Nat) (xs : List β) :
    ListSum (xs.filter P) f + ListSum (xs.filter fun x => ¬P x) f = ListSum xs f := by
  have h := ListSum_compl2 (fun x => decide (P x)) f xs
  have hnot : (fun x => decide (¬P x)) = (fun x => !decide (P x)) :=
    funext fun x => by rw [decide_not]
  rwa [hnot]

/-- LowerBound.thy: total_weight_lowerbound (lines 35–299). -/
theorem total_weight_lowerbound {g : Graph} {w : Face → Nat} (pl : inv g)
    (fin : g.final = true) (hg : tame g) (adm : admissible w g)
    (_hw : (∑ₗ f ∈ g.faces, w f) < squanderTarget) :
    squanderLowerBound g ≤ ∑ₗ f ∈ g.faces, w f := by
  obtain ⟨adm1, adm2, adm3⟩ := adm
  obtain ⟨V, hENA, pS, Vsub, Vdist⟩ := ExcessNotAt_eq (inv_mgp pl) fin
  -- The vertex partitions V1/V2 and V3/V4, and the face partitions F1/F2, F3/F4.
  set V1 := V.filter (fun v => except g v = 0) with hV1
  set V2 := V.filter (fun v => ¬except g v = 0) with hV2
  set V3 := V2.filter (fun v => vertextype g v = (5, 0, 1)) with hV3
  set V4 := V2.filter (fun v => ¬vertextype g v = (5, 0, 1)) with hV4
  set F1 := g.faces.filter (fun f => ∃ v ∈ V1, f ∈ g.facesAt v) with hF1
  set F2 := g.faces.filter (fun f => ¬∃ v ∈ V1, f ∈ g.facesAt v) with hF2
  set F3 := F2.filter (fun f => ∃ v ∈ V3, f ∈ g.facesAt v) with hF3
  set F4 := F2.filter (fun f => ¬∃ v ∈ V3, f ∈ g.facesAt v) with hF4
  -- Facts about V1.
  have pSV1 : separated g (· ∈ V1) :=
    separated_subset (fun v hv => (List.mem_filter.mp hv).1) pS
  have V1dist : V1.Nodup := Vdist.filter _
  have noExV1 : noExceptionals g (· ∈ V1) := by
    intro v hv
    have hex : except g v = 0 := of_decide_eq_true (List.mem_filter.mp hv).2
    simp [exceptionalVertex, hex]
  have V1sub : ∀ v ∈ V1, v ∈ g.vertices := fun v hv => Vsub v (List.mem_filter.mp hv).1
  -- Facts about V3.
  have V3sep : separated g (· ∈ V3) :=
    separated_subset (fun v hv => (List.mem_filter.mp (List.mem_filter.mp hv).1).1) pS
  have V3dist : V3.Nodup := (Vdist.filter _).filter _
  have V3sub : ∀ v ∈ V3, v ∈ g.vertices :=
    fun v hv => Vsub v (List.mem_filter.mp (List.mem_filter.mp hv).1).1
  -- `faceSquanderLowerBound g = ∑ f ∈ faces g, d |vertices f|` (final graph).
  have hFSL : faceSquanderLowerBound g =
      ∑ₗ f ∈ g.faces, squanderFace f.vertices.length := by
    rw [faceSquanderLowerBound_eq_ListSum]
    congr 1
    show g.faces.filter Face.final = g.faces
    rw [List.filter_eq_self]
    intro f hf
    exact finalGraph_face fin hf
  -- The partition sum equations.
  have hsplitV : (∑ₗ v ∈ V1, ExcessAt g v) + (∑ₗ v ∈ V2, ExcessAt g v) =
      ∑ₗ v ∈ V, ExcessAt g v := by
    have h := ListSum_filter_compl (fun v => except g v = 0) (fun v => ExcessAt g v) V
    rwa [← hV1, ← hV2] at h
  have hsplitV2 : (∑ₗ v ∈ V3, ExcessAt g v) + (∑ₗ v ∈ V4, ExcessAt g v) =
      ∑ₗ v ∈ V2, ExcessAt g v := by
    have h := ListSum_filter_compl (fun v => vertextype g v = (5, 0, 1))
      (fun v => ExcessAt g v) V2
    rwa [← hV3, ← hV4] at h
  have hsplitF : (∑ₗ f ∈ F1, squanderFace f.vertices.length) +
      (∑ₗ f ∈ F2, squanderFace f.vertices.length) =
      ∑ₗ f ∈ g.faces, squanderFace f.vertices.length := by
    have h := ListSum_filter_compl (fun f => ∃ v ∈ V1, f ∈ g.facesAt v)
      (fun f => squanderFace f.vertices.length) g.faces
    rwa [← hF1, ← hF2] at h
  have hsplitF2 : (∑ₗ f ∈ F3, squanderFace f.vertices.length) +
      (∑ₗ f ∈ F4, squanderFace f.vertices.length) =
      ∑ₗ f ∈ F2, squanderFace f.vertices.length := by
    have h := ListSum_filter_compl (fun f => ∃ v ∈ V3, f ∈ g.facesAt v)
      (fun f => squanderFace f.vertices.length) F2
    rwa [← hF3, ← hF4] at h
  -- Reunion equations for the weight sums.
  have hreunF2 : (∑ₗ f ∈ F3, w f) + (∑ₗ f ∈ F4, w f) = ∑ₗ f ∈ F2, w f := by
    have h := ListSum_filter_compl (fun f => ∃ v ∈ V3, f ∈ g.facesAt v) (fun f => w f) F2
    rwa [← hF3, ← hF4] at h
  have hreunF : (∑ₗ f ∈ F1, w f) + (∑ₗ f ∈ F2, w f) = ∑ₗ f ∈ g.faces, w f := by
    have h := ListSum_filter_compl (fun f => ∃ v ∈ V1, f ∈ g.facesAt v) (fun f => w f)
      g.faces
    rwa [← hF1, ← hF2] at h
  -- Isabelle lines 134–161: the F2-condition is automatic for faces at V3.
  have hF3char : F3 = g.faces.filter (fun f => ∃ v ∈ V3, f ∈ g.facesAt v) := by
    rw [hF3, hF2, List.filter_filter]
    apply List.filter_congr
    intro f _hf
    show (decide (∃ v ∈ V3, f ∈ g.facesAt v) &&
        decide (¬∃ v ∈ V1, f ∈ g.facesAt v)) = decide (∃ v ∈ V3, f ∈ g.facesAt v)
    by_cases h3 : decide (∃ v ∈ V3, f ∈ g.facesAt v) = true
    · rw [h3, Bool.true_and, decide_eq_true]
      obtain ⟨v3, hv3, hfat3⟩ := of_decide_eq_true h3
      rintro ⟨v1, hv1, hfat1⟩
      have hv1V : v1 ∈ V := (List.mem_filter.mp hv1).1
      have hex1 : except g v1 = 0 := of_decide_eq_true (List.mem_filter.mp hv1).2
      have hv3V2 : v3 ∈ V2 := (List.mem_filter.mp hv3).1
      have hv3V : v3 ∈ V := (List.mem_filter.mp hv3V2).1
      have hex3 : ¬except g v3 = 0 := of_decide_eq_true (List.mem_filter.mp hv3V2).2
      have hne13 : v1 ≠ v3 := fun e => hex3 (e ▸ hex1)
      have hv1g : v1 ∈ g.vertices := Vsub v1 hv1V
      have hnoex1 : exceptionalVertex g v1 = false := by simp [exceptionalVertex, hex1]
      have hc : f.vertices.length ≤ 4 := not_exceptional pl fin hv1g hfat1 hnoex1
      have h3mem : v3 ∈ f.vertices := ((pS.2 v3 hv3V f hfat3 hc v3).mpr rfl).1
      have hcontra : v3 = v1 := (pS.2 v1 hv1V f hfat1 hc v3).mp ⟨h3mem, hv3V⟩
      exact hne13 hcontra.symm
    · have h3f : decide (∃ v ∈ V3, f ∈ g.facesAt v) = false := (Bool.not_eq_true _).mp h3
      rw [h3f, Bool.false_and]
  -- (E1), Isabelle lines 170–195.
  have sF1 : (∑ₗ f ∈ F1, squanderFace f.vertices.length) =
      ∑ₗ v ∈ V1, (tri g v * d3_const + quad g v * d4_const) := by
    have h := squanderFace_distr2 pl fin noExV1 pSV1 V1dist V1sub
    rwa [← hF1] at h
  have hE1 : (∑ₗ v ∈ V1, ExcessAt g v) + (∑ₗ f ∈ F1, squanderFace f.vertices.length) =
      ∑ₗ v ∈ V1, squanderVertex (tri g v) (quad g v) := by
    rw [sF1, ListSum_add]
    apply ListSum_eq
    intro v hv
    have hvV : v ∈ V := (List.mem_filter.mp hv).1
    have hex : except g v = 0 := of_decide_eq_true (List.mem_filter.mp hv).2
    show ExcessAt g v + (tri g v * d3_const + quad g v * d4_const) =
      squanderVertex (tri g v) (quad g v)
    rw [← Nat.add_assoc]
    exact excess_eq1 pl fin hg hex (Vsub v hvV)
  -- (E2), Isabelle lines 200–206: exceptional vertices of degree 5 contribute `a`.
  have hE2 : (∑ₗ v ∈ V3, ExcessAt g v) = ∑ₗ v ∈ V3, excessTCount := by
    apply ListSum_eq
    intro v hv
    have hvt : vertextype g v = (5, 0, 1) := of_decide_eq_true (List.mem_filter.mp hv).2
    have hv2 : v ∈ V2 := (List.mem_filter.mp hv).1
    have hvV : v ∈ V := (List.mem_filter.mp hv2).1
    have hfv : finalVertex g v = true := finalVertexI pl fin (Vsub v hvV)
    have hnot : ¬ (!finalVertex g v) = true := by simp [hfv]
    have htri : tri g v = 5 := congrArg Prod.fst hvt
    have hquad : quad g v = 0 := congrArg (fun p => p.2.1) hvt
    have hex : except g v = 1 := congrArg (fun p => p.2.2) hvt
    show ExcessAt g v = excessTCount
    unfold ExcessAt
    rw [if_neg hnot, htri, hquad, hex]
    rfl
  -- (E3), Isabelle lines 211–215: exceptional vertices of degree ≠ 5 contribute 0.
  have hE3 : (∑ₗ v ∈ V4, ExcessAt g v) = 0 := by
    have h0 : ∀ v ∈ V4, ExcessAt g v = 0 := by
      intro v hv
      have hv2 : v ∈ V2 := (List.mem_filter.mp hv).1
      have hvt : ¬vertextype g v = (5, 0, 1) :=
        of_decide_eq_true (List.mem_filter.mp hv).2
      have hvV : v ∈ V := (List.mem_filter.mp hv2).1
      have hexne : ¬except g v = 0 := of_decide_eq_true (List.mem_filter.mp hv2).2
      have hvg : v ∈ g.vertices := Vsub v hvV
      have hfv : finalVertex g v = true := finalVertexI pl fin hvg
      have hnot : ¬ (!finalVertex g v) = true := by simp [hfv]
      have hdeg : degree g v = tri g v + quad g v + except g v := degree_eq pl fin hvg
      have hd6 : degree g v ≠ 6 := by
        intro hd
        apply hvt
        have hmem : (if except g v ≠ 0 ∧ degree g v = 6 then
            decide (vertextype g v = (5, 0, 1)) else true) = true :=
          List.all_eq_true.mp hg.2.2.2.2.1 v hvg
        rw [if_pos ⟨hexne, hd⟩] at hmem
        exact of_decide_eq_true hmem
      have hne6 : tri g v + quad g v + except g v ≠ 6 := fun h => hd6 (hdeg.trans h)
      unfold ExcessAt
      rw [if_neg hnot]
      unfold excessAtType
      rw [if_neg hexne, if_pos hne6]
    have hsum := ListSum_eq h0
    rw [ListSum_zero] at hsum
    exact hsum
  -- (A1), Isabelle lines 219–239: `admissible₂` + `separated_disj_Union2`.
  have hA1 : (∑ₗ v ∈ V1, squanderVertex (tri g v) (quad g v)) ≤ ∑ₗ f ∈ F1, w f := by
    have hle : (∑ₗ v ∈ V1, squanderVertex (tri g v) (quad g v)) ≤
        ∑ₗ v ∈ V1, ∑ₗ f ∈ g.facesAt v, w f := by
      apply ListSum_le
      intro v hv
      have hvV : v ∈ V := (List.mem_filter.mp hv).1
      have hex : except g v = 0 := of_decide_eq_true (List.mem_filter.mp hv).2
      have h := adm2 v (Vsub v hvV) hex
      rw [← ListSum_eq_sum_map] at h
      exact h
    have heq : (∑ₗ v ∈ V1, ∑ₗ f ∈ g.facesAt v, w f) = ∑ₗ f ∈ F1, w f := by
      have h := separated_disj_Union2 w pl fin noExV1 pSV1 V1dist V1sub
      rwa [← hF1] at h
    calc (∑ₗ v ∈ V1, squanderVertex (tri g v) (quad g v))
        ≤ ∑ₗ v ∈ V1, ∑ₗ f ∈ g.facesAt v, w f := hle
      _ = ∑ₗ f ∈ F1, w f := heq
  -- (A2), Isabelle lines 243–276: the triangle/non-triangle split of F3.
  have hA2 : (∑ₗ v ∈ V3, excessTCount) + (∑ₗ f ∈ F3, squanderFace f.vertices.length) ≤
      ∑ₗ f ∈ F3, w f := by
    have hsplitD : (∑ₗ f ∈ F3, squanderFace f.vertices.length) =
        (∑ₗ f ∈ F3.filter triangle, squanderFace f.vertices.length) +
        (∑ₗ f ∈ F3.filter (fun f => !triangle f), squanderFace f.vertices.length) :=
      (ListSum_compl2 triangle (fun f => squanderFace f.vertices.length) F3).symm
    have hTD : (∑ₗ f ∈ F3.filter triangle, squanderFace f.vertices.length) = 0 := by
      have h0 : ∀ f ∈ F3.filter triangle, squanderFace f.vertices.length = 0 := by
        intro f hf
        have ht : triangle f = true := (List.mem_filter.mp hf).2
        have h3 : f.vertices.length = 3 := beq_iff_eq.mp ht
        calc squanderFace f.vertices.length = squanderFace 3 := by rw [h3]
          _ = 0 := rfl
      have hsum := ListSum_eq h0
      rw [ListSum_zero] at hsum
      exact hsum
    have hEle : (∑ₗ f ∈ F3.filter (fun f => !triangle f), squanderFace f.vertices.length) ≤
        ∑ₗ f ∈ F3.filter (fun f => !triangle f), w f := by
      apply ListSum_le
      intro f hf
      have hfg : f ∈ g.faces :=
        (List.mem_filter.mp (List.mem_filter.mp (List.mem_filter.mp hf).1).1).1
      exact adm1 f hfg
    have hAle : (∑ₗ v ∈ V3, excessTCount) ≤
        ∑ₗ v ∈ V3, ∑ₗ f ∈ (g.facesAt v).filter triangle, w f := by
      apply ListSum_le
      intro v hv
      have hv2 : v ∈ V2 := (List.mem_filter.mp hv).1
      have hvt : vertextype g v = (5, 0, 1) := of_decide_eq_true (List.mem_filter.mp hv).2
      have hvg : v ∈ g.vertices := Vsub v (List.mem_filter.mp hv2).1
      have h := adm3 v hvg hvt
      rw [← ListSum_eq_sum_map] at h
      exact h
    have hnoex : ∀ f, triangle f = true → f.vertices.length ≤ 4 := by
      intro f ht
      have h3 : f.vertices.length = 3 := beq_iff_eq.mp ht
      omega
    have hbool : ∀ l : List Face,
        l.filter (fun f => triangle f = true) = l.filter triangle :=
      fun l => List.filter_congr fun f _ => by
        show decide (triangle f = true) = triangle f
        cases triangle f <;> rfl
    have hW : (∑ₗ v ∈ V3, ∑ₗ f ∈ (g.facesAt v).filter triangle, w f) =
        ∑ₗ f ∈ F3.filter triangle, w f := by
      have h := ListSum_V_F_eq_ListSum_F (fun f => triangle f = true) pl V3sep V3dist
        V3sub hnoex w
      have h1 : (∑ₗ v ∈ V3, ∑ₗ f ∈ (g.facesAt v).filter (fun f => triangle f = true),
          w f) = ∑ₗ v ∈ V3, ∑ₗ f ∈ (g.facesAt v).filter triangle, w f := by
        apply ListSum_eq
        intro v _
        show ListSum ((g.facesAt v).filter (fun f => triangle f = true)) (fun f => w f) =
          ListSum ((g.facesAt v).filter triangle) (fun f => w f)
        congr 1
        exact hbool (g.facesAt v)
      have hT : F3.filter triangle =
          g.faces.filter (fun f => ∃ v ∈ V3, f ∈ g.facesAt v ∧ triangle f = true) := by
        rw [hF3char, List.filter_filter]
        apply List.filter_congr
        intro f _
        show (triangle f && decide (∃ v ∈ V3, f ∈ g.facesAt v)) =
          decide (∃ v ∈ V3, f ∈ g.facesAt v ∧ triangle f = true)
        by_cases hb1 : decide (∃ v ∈ V3, f ∈ g.facesAt v) = true <;>
          cases hb2 : triangle f <;> simp [hb1, hb2]
      rw [h1, ← hT] at h
      exact h
    have hTE : (∑ₗ f ∈ F3.filter triangle, w f) +
        (∑ₗ f ∈ F3.filter (fun f => !triangle f), w f) = ∑ₗ f ∈ F3, w f :=
      ListSum_compl2 triangle (fun f => w f) F3
    omega
  -- (A3), Isabelle lines 281–286: `admissible₁` on F4.
  have hA3 : (∑ₗ f ∈ F4, squanderFace f.vertices.length) ≤ ∑ₗ f ∈ F4, w f := by
    apply ListSum_le
    intro f hf
    have hfg : f ∈ g.faces := (List.mem_filter.mp (List.mem_filter.mp hf).1).1
    exact adm1 f hfg
  -- Final reunion (Isabelle lines 290–298).
  have hSLB : squanderLowerBound g = faceSquanderLowerBound g + ExcessNotAt g none := rfl
  omega

end Kepler.Graphs
