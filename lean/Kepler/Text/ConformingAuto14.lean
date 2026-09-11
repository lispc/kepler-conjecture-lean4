/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level theorems, batch 14
(Conforming.hl:4848-6177).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage (batch 14, Conforming.hl:4848-6177):
- `unique_tranf_fan` (4848)
- `tran_in_dart_newfan` (4969)
- `INJ_TRAN_D1_FAN` (4990)
- `INJ_TRANF_FACE_DELETE_DS` (5009)
- `ds1_in_face_set_fanadd` (5117)
- `ds2_in_face_set_fanadd` (5155)
- `condition_f1_fan_power_in_face_set` (5195)
- `SUR_TRANF_FACE_DELETE_DS` (5220)
- `DOMAIN_TRANF_FACE_DELETE_DS` (5773)  [listed only as ":5773" in the task]
- `EQ_CARD_FACE_FAN_AND_FANADD` (6121)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `FAN(x,V,E)` ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); HOL
  `set_of_edge v V E` ↔ `setOfEdge v V E` (Kepler/Text/Fan.lean:62); HOL
  `sigma_fan` ↔ `sigmaFan` (Kepler/Text/Fan.lean:67); HOL `fan80` ↔
  `fan80` (Kepler/Text/Fan.lean:227); HOL `CARD (set_of_edge v V E) > 1` ↔
  `1 < (setOfEdge v V E).ncard`; HOL `CARD ds > 3` ↔ `3 < ds.ncard`; HOL
  `CARD s` ↔ `s.ncard`.
- HOL `hypermap1_of_fanx (x,V,E)` is NOT ported; as in
  Kepler/Text/PlanarityComponent.lean:37-48 and the earlier conforming
  batches, `face_set (hypermap1_of_fanx (x,V,E))` is encoded as
  `(hypermapOfFan x V E hfan).faceSet`, `face (hypermap1_of_fanx (x,V,E)) f`
  as `(hypermapOfFan x V E hfan).face f`, and `face_set (...) DELETE ds` as
  `(hypermapOfFan x V E hfan).faceSet \ {ds}`. Since `hypermapOfFan`
  (Kepler/Text/Fan.lean:1169) needs an explicit `hfan : FAN x V E`, every
  theorem that mentions it carries an extra explicit `(hfan : FAN x V E)`
  argument; theorems that also mention `face (hypermap1_of_fanx (x,V,E1))`
  carry a second extra explicit argument `(hfan1 : FAN x V E1)`. These are
  the only deviations from the HOL signatures (HOL's `hypermap_of_fan` is
  total). Theorems `tran_in_dart_newfan`, `INJ_TRAN_D1_FAN` and
  `condition_f1_fan_power_in_face_set` mention only `d1_fan`/`d_fan`, so they
  need no `hypermapOfFan` witness; `condition_f1_fan_power_in_face_set` still
  needs `hfan` for its `face_set` hypothesis.
- HOL quadruple darts `real^3#real^3#real^3#real^3` are encoded as pair darts
  `V3 × V3` (Kepler/Text/PlanarityComponent.lean:37-48); `pr2 y`/`pr3 y` ↦
  `y.1`/`y.2`. Consequently the HOL quadruples `(x,w,v,u)`, `(x,v,u,w)`,
  `(x,u,w,v)` contract to the pairs `(w,v)`, `(v,u)`, `(u,w)`, and
  `(x,v,w,sigma_fan x V E1 v w)` / `(x,w,v,sigma_fan x V E1 w v)` to the
  pairs `(v,w)` / `(w,v)`.
- HOL `f1_fan x V E` ↔ `f1Fan x V E` (Kepler/Text/ConformingDefs.lean:87);
  HOL `(f1_fan x V E POWER n) y` ↔ `(f1Fan x V E)^[n] y` (Function.iterate).
- HOL `d1_fan (x,V,E)` ↔ `dart1OfFan V E` (Kepler/Text/Fan.lean:86); HOL
  `d_fan (x,V,E)` ↔ `dartOfFan V E` (Kepler/Text/Fan.lean:90).
- HOL `tran` (Conforming.hl:4097) is NOT ported. It is
  `(\(x,y,z,w). (x,y,z,sigma_fan x V E1 y z))`: it only rewrites the 4th
  component of a dart. Since the repo's pair-dart encoding keeps
  `(pr2,pr3)` and drops the 4th component, `tran x V E1` is the IDENTITY on
  pair darts (same convention as Kepler/Text/ConformingAuto13.lean:55-68).
  Hence `tran x V E1 y` is inlined as `y`; the statements
  `tran_in_dart_newfan` / `INJ_TRAN_D1_FAN` therefore read `y ∈ dart1OfFan
  V E → y ∈ dart1OfFan V E1` and `y = y1 → y = y1`. This is the only
  deviation in those two statements, and it is forced by the pair encoding
  (the 4th component is a function of the other three on `d1_fan`). NOTE:
  the already-ported `exists_tranf_fan` (Kepler/Text/ConformingAuto12.lean:935)
  instead inlines `tran x V E1 y` as `(y.1, sigmaFan x V E1 y.1 y.2)`, i.e.
  it uses the `n_fan` map; that encoding changes the `(pr2,pr3)` dart and is
  NOT used here.
- HOL `tranf x V E E1 ds = @f. ?y. f = face (hypermap1_of_fanx (x,V,E1))
  (tran x V E1 y) /\ y IN ds` (Conforming.hl:4101) is NOT ported. Its
  closest existing encoding is the Hilbert choice of the same existence
  predicate (with `tran` read as the identity, i.e. `f = face y /\ y ∈ ds`);
  since the existence is only available under the theorem's hypotheses,
  `tranf` is inlined in each statement as the totalized function
  `fun s => if h : (∃ f, ∃ y, f = face y ∧ y ∈ s) then Classical.choose h else ∅`
  bound by a local `let` (the `else` branch is unreachable under the
  hypotheses). No new definition is introduced.
- HOL `trans` (4094) is not needed by any of the ten theorems.
- HOL `CARD_IMAGE_INJ_EQ` (used by `EQ_CARD_FACE_FAN_AND_FANADD`) is NOT
  ported; Mathlib's `Set.ncard_image_of_injOn` / `Set.ncard_congr` are the
  closest analogues.
- Proof dependencies living in earlier conforming batches are NOT imported
  here (per the porting convention this batch imports only
  `PlanarityAuto16` and `ConformingDefs`); the proof sketches name them as
  candidates to be restated or imported by the worker pool.
- None of the ten statements is Mathlib-general: every one mentions the
  repo-specific `FAN`/`sigmaFan`/`f1Fan`/`dart1OfFan`/`hypermapOfFan`
  vocabulary, so nothing is skipped.
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs
import Kepler.Text.ConformingAuto10
import Kepler.Text.ConformingAuto13

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Classical

/-! ## `tranf` 的唯一性与 `tran` 的像/单射（Conforming.hl:4848-5116） -/

/-- `hypermapOfFan` 的 `faceMap` 在 `dart1OfFan` 上等于 `f1Fan`。 -/
private theorem hypermapOfFan_faceMap_eq_f1Fan {x : V3} {V : Set V3}
    {E : Set (Set V3)} (hfan : FAN x V E) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) :
    (hypermapOfFan x V E hfan).faceMap d = f1Fan x V E d := by
  have hba : ({d.2, d.1} : Set V3) ∈ E := by
    have h : ({d.1, d.2} : Set V3) ∈ E := hd
    rwa [Set.pair_comm] at h
  have hface : (hypermapOfFan x V E hfan).faceMap d = fFanPair x V E d := by
    unfold hypermapOfFan extendPerm
    simp only [Equiv.ofBijective_apply]
    unfold Kepler.Text.Fan.res
    rw [if_pos (by simpa [(finite_dart1_fan hfan).coe_toFinset] using hd)]
  have hpair : fFanPair x V E d = f1Fan x V E d := by
    simp only [fFanPair, f1Fan]
    rw [inverse_sigma_fan_eq_inverse1 hfan hba]
  rw [hface, hpair]

/-- HOL Conforming.hl :4848-4967 `unique_tranf_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 ds0 f y.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ ds1 = face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)
/\ ds2 = face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
/\ f= face (hypermap1_of_fanx (x,V,E1)) (tran x V E1 y)/\ y IN ds0
/\ ds0 IN face_set (hypermap1_of_fanx (x,V,E)) DELETE ds
==> tranf x V E E1 ds0 = f
```

编码说明：`pr2 f1 =v`/`pr2 f2 =u`/`pr2 f3=w` ↦ `f1.1 = v`/`f2.1 = u`/
`f3.1 = w`；`pr3 f1= u`/`pr3 f2= w` ↦ `f1.2 = u`/`f2.2 = w`；`CARD ds >3`
↦ `3 < ds.ncard`；`{f1,f2,f3} SUBSET ds` ↦ `({f1,f2,f3} : Set (V3×V3)) ⊆ ds`；
`face_set (...) DELETE ds` ↦ `faceSet \ {ds}`；`tran` 在点对编码下为恒等，
`face(...)(tran x V E1 y)` 编码为 `face y`；`tranf` 内联为局部 `let`
（见文件头）。额外携带 `hfan`、`hfan1`。

证明思路：由 `ds0 ∈ faceSet(E) \ {ds}` 及 `y ∈ ds0` 知 `ds0` 是 `E` 的一个
面；对 `E1 = E ∪ {{v,w}}` 用 `STEP3_REDUCE_FAN`/`TRANF` 得 `ds0` 中任一元素
在 `face_{E1}` 下的像与 `face_{E1} y = f` 相同（`unique`），从而
`Classical.choose` 取到的面等于 `f`，`dif_pos`/`Classical.choose_spec` 收口。

候选已有引理：
- `TRANF`（Kepler/Text/ConformingAuto13.lean:145）
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `identity_face_in_face_set`（Kepler/Text/ConformingAuto8.lean:380）
- `Hypermap.face_representation`（Kepler/Text/Hypermap.lean:2794）
- 缺口：HOL `tran`/`tranf`（Conforming.hl:4097-4101）、`hypermap_of_fan_rep`
  （fan.hl:2780）、`dartset_fully_surrounded_is_non_isolated_fan` 未移植 -/
theorem unique_tranf_fan (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3) (ds0 : Set (V3 × V3))
    (f : Set (V3 × V3)) (y : V3 × V3)
    (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    let tranf : Set (V3 × V3) → Set (V3 × V3) := fun s =>
      if h : (∃ g : Set (V3 × V3), ∃ z : V3 × V3,
          g = (hypermapOfFan x V E1 hfan1).face z ∧ z ∈ s)
      then Classical.choose h else ∅;
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    ds1 = (hypermapOfFan x V E1 hfan1).face (v, w) ∧
    ds2 = (hypermapOfFan x V E1 hfan1).face (w, v) ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 ∧
    f = (hypermapOfFan x V E1 hfan1).face y ∧ y ∈ ds0 ∧
    ds0 ∈ (hypermapOfFan x V E hfan).faceSet \ {ds} →
      tranf ds0 = f := by
  dsimp only
  rintro ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
    hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2,
    hf10, hf20, hf30, hE1, hfy, hyds0, hds0mem⟩
  have hEsub : E ⊆ E1 := by rw [← hE1]; exact Set.subset_union_left
  obtain ⟨hds0_faceSet, hds0_ne⟩ := hds0mem
  have hP : ∃ g : Set (V3 × V3), ∃ z : V3 × V3,
      g = (hypermapOfFan x V E1 hfan1).face z ∧ z ∈ ds0 :=
    ⟨f, y, hfy, hyds0⟩
  rw [dif_pos hP]
  obtain ⟨z, hz, hzds0⟩ := Classical.choose_spec hP
  rw [hz, hfy]
  set HE : Hypermap (V3 × V3) := hypermapOfFan x V E hfanC with hHE
  set H1 : Hypermap (V3 × V3) := hypermapOfFan x V E1 hfan1 with hH1
  have hdarts_eq : (↑HE.darts : Set (V3 × V3)) = dart1OfFan V E := by
    rw [hHE]
    change (↑(finite_dart1_fan hfanC).toFinset : Set (V3 × V3)) = dart1OfFan V E
    exact (finite_dart1_fan hfanC).coe_toFinset
  obtain ⟨a, ha_darts, ha_face⟩ := HE.face_representation hds0_faceSet
  have hds0_subset : ds0 ⊆ (↑HE.darts : Set (V3 × V3)) := by
    rw [ha_face]; exact HE.face_subset_darts ha_darts
  have hy_face : y ∈ HE.face a := by rw [← ha_face]; exact hyds0
  have hface_y : HE.face y = ds0 :=
    (HE.face_eq_of_mem hy_face).symm.trans ha_face.symm
  have hz_in_face_y : z ∈ HE.face y := by rw [hface_y]; exact hzds0
  obtain ⟨n, hn⟩ := hz_in_face_y
  have hpoint : ∀ p : V3 × V3, p ∈ ds0 → HE.faceMap p = H1.faceMap p := by
    intro p hp
    have hp_dart1_E : p ∈ dart1OfFan V E := by
      rw [← hdarts_eq]; exact hds0_subset hp
    have hp_dart1_E1 : p ∈ dart1OfFan V E1 := hEsub hp_dart1_E
    have hp_not_ds : ¬ p ∈ ds := by
      intro hpds
      have h1 : HE.face p = ds0 := by
        have hpfa : p ∈ HE.face a := by rw [← ha_face]; exact hp
        exact (HE.face_eq_of_mem hpfa).symm.trans ha_face.symm
      obtain ⟨b, _hb, hb_face⟩ := HE.face_representation hds
      have hpfb : p ∈ HE.face b := by rw [← hb_face]; exact hpds
      have h2 : HE.face p = ds := (HE.face_eq_of_mem hpfb).symm.trans hb_face.symm
      exact hds0_ne (h1.symm.trans h2)
    have hmapE : HE.faceMap p = f1Fan x V E p := by
      rw [hHE]; exact hypermapOfFan_faceMap_eq_f1Fan hfanC hp_dart1_E
    have hmapE1 : H1.faceMap p = f1Fan x V E1 p := by
      rw [hH1]; exact hypermapOfFan_faceMap_eq_f1Fan hfan1 hp_dart1_E1
    rw [hmapE, hmapE1]
    exact TRAN_COMMUTATIVE_F1_FAN x V E E1 ds f1 f2 f3 v u w ds1 ds2
      f10 f20 f30 p hfanC hfan1
      ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
       hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2,
       hf10, hf20, hf30, hE1, hp_not_ds, Or.inr hp_dart1_E⟩
  have hiter : ∀ k : ℕ, (HE.faceMap ^ k) y = (H1.faceMap ^ k) y := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        have hp_mem : (HE.faceMap ^ k) y ∈ ds0 := by
          have hmem := pow_apply_mem_orbitMap HE.faceMap k y
          rw [← hface_y]
          exact hmem
        rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
        rw [← ih]
        exact hpoint ((HE.faceMap ^ k) y) hp_mem
  have hz_in_H1 : z ∈ H1.face y := ⟨n, by rw [← hiter n]; exact hn⟩
  exact (H1.face_eq_of_mem hz_in_H1).symm

/-- HOL Conforming.hl :4969-4989 `tran_in_dart_newfan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 y .
FAN(x,V,E)/\ FAN(x,V,E1)
/\ E SUBSET E1
/\ y IN d1_fan(x,V,E)
==> tran x V E1 y IN d1_fan(x,V,E1)
```

编码说明：`E SUBSET E1` ↦ `E ⊆ E1`；`d1_fan` ↦ `dart1OfFan`；`tran` 在点对
编码下为恒等（见文件头），故 `tran x V E1 y` 内联为 `y`。本定理不涉及
`hypermapOfFan`，故无需 `hfan` 见证。

证明思路：由 `y ∈ dart1OfFan V E` 得 `{y.1, y.2} ∈ E`，配合 `E ⊆ E1` 得
`{y.1, y.2} ∈ E1`，即 `y ∈ dart1OfFan V E1`（`dart1OfFan` 展开即得）。

候选已有引理：
- `dart1OfFan`（Kepler/Text/Fan.lean:86）
- `Set.mem_of_subset_of_mem`（Mathlib）
- 缺口：HOL `tran`（Conforming.hl:4097）未移植 -/
theorem tran_in_dart_newfan (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (y : V3 × V3) :
    FAN x V E ∧ FAN x V E1 ∧ E ⊆ E1 ∧ y ∈ dart1OfFan V E →
      y ∈ dart1OfFan V E1 := by
  rintro ⟨_, _, hsub, hy⟩
  exact hsub hy

/-- HOL Conforming.hl :4990-5008 `INJ_TRAN_D1_FAN`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 y y1.
FAN(x,V,E)/\ FAN(x,V,E1)
/\ E SUBSET E1
/\ y IN d1_fan(x,V,E)
/\ y1 IN d1_fan(x,V,E)
/\
tran x V E1 y = tran x V E1 y1
==> y =y1
```

编码说明：`d1_fan` ↦ `dart1OfFan`；`tran` 在点对编码下为恒等（见文件头），
故假设 `tran x V E1 y = tran x V E1 y1` 内联为 `y = y1`。本定理不涉及
`hypermapOfFan`，故无需 `hfan` 见证。

证明思路：在点对编码下 `tran` 是恒等，结论与（内联后的）假设相同，直接
`exact`/`assumption` 收口。

候选已有引理：
- `dart1OfFan`（Kepler/Text/Fan.lean:86）
- 缺口：HOL `tran`（Conforming.hl:4097）未移植 -/
theorem INJ_TRAN_D1_FAN (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (y y1 : V3 × V3) :
    FAN x V E ∧ FAN x V E1 ∧ E ⊆ E1 ∧
    y ∈ dart1OfFan V E ∧ y1 ∈ dart1OfFan V E ∧
    y = y1 →
      y = y1 := by
  rintro ⟨-, -, -, -, -, hy⟩
  exact hy

/-- `f1Fan` 把 `dart1OfFan` 中的元素仍送到 `dart1OfFan`。 -/
private theorem f1Fan_iterate_mem_dart1OfFan {x : V3} {V : Set V3}
    {E : Set (Set V3)} (hfan : FAN x V E) {z : V3 × V3}
    (hz : z ∈ dart1OfFan V E) :
    ∀ m : ℕ, (f1Fan x V E)^[m] z ∈ dart1OfFan V E := by
  intro m
  induction m with
  | zero => simpa using hz
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      have hpair : f1Fan x V E ((f1Fan x V E)^[m] z) =
          fFanPair x V E ((f1Fan x V E)^[m] z) := by
        have hba : {((f1Fan x V E)^[m] z).2, ((f1Fan x V E)^[m] z).1} ∈ E := by
          have h : {((f1Fan x V E)^[m] z).1, ((f1Fan x V E)^[m] z).2} ∈ E := ih
          rwa [Set.pair_comm] at h
        simp only [f1Fan, fFanPair]
        rw [inverse_sigma_fan_eq_inverse1 hfan hba]
      rw [hpair]
      exact fFanPair_mem_dart1 hfan ih

/-- `hypermapOfFan` 的 `faceMap` 的幂在 `dart1OfFan` 上等于 `f1Fan` 的迭代。 -/
private theorem hypermapOfFan_faceMap_pow_eq_iterate {x : V3} {V : Set V3}
    {E : Set (Set V3)} (hfan : FAN x V E) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) (k : ℕ) :
    ((hypermapOfFan x V E hfan).faceMap ^ k) d = (f1Fan x V E)^[k] d := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih, Function.iterate_succ_apply']
      exact hypermapOfFan_faceMap_eq_f1Fan hfan
        (f1Fan_iterate_mem_dart1OfFan hfan hd k)

/-- 若 `f1 ∈ ds` 且 `ds` 是 `faceSet` 中的面，则 `ds` 就是 `f1` 所在的面。 -/
private theorem identity_face_in_face_set {x : V3} {V : Set V3} {E : Set (Set V3)}
    {ds : Set (V3 × V3)} {f1 : V3 × V3}
    (hfan : FAN x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hf1 : f1 ∈ ds) :
    ds = (hypermapOfFan x V E hfan).face f1 := by
  obtain ⟨d, _hd, rfl⟩ := (hypermapOfFan x V E hfan).face_representation hds
  exact (hypermapOfFan x V E hfan).face_eq_of_mem hf1

/-- HOL Conforming.hl :5009-5116 `INJ_TRANF_FACE_DELETE_DS`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 ds0 ds0'.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ ds1 = face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)
/\ ds2 = face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
/\ ds0 IN face_set (hypermap1_of_fanx (x,V,E)) DELETE ds
/\ ds0' IN face_set (hypermap1_of_fanx (x,V,E)) DELETE ds
/\ tranf x V E E1 ds0=tranf x V E E1 ds0'
==>
 ds0 = ds0'
```

编码说明：`pr3 f1= u`/`pr3 f2= w` ↦ `f1.2 = u`/`f2.2 = w`；`tranf` 内联为
局部 `let`（见文件头）；`face_set (...) DELETE ds` ↦ `faceSet \ {ds}`。
额外携带 `hfan`、`hfan1`。

证明思路：`tranf` 取 `ds0`（分别为 `E` 的面）中元素在 `face_{E1}` 下的像；
由 `TRANF` 及 `unique_tranf_fan` 可知 `tranf ds0 = face_{E1} y`（`y ∈ ds0`）
且 `tranf ds0' = face_{E1} y'`（`y' ∈ ds0'`）；两者相等结合
`INJ_TRAN_D1_FAN` 与 `identity_face_in_face_set` 得 `ds0 = ds0'`。

候选已有引理：
- `TRANF`（Kepler/Text/ConformingAuto13.lean:145）
- `unique_tranf_fan`（本文件）
- `INJ_TRAN_D1_FAN`（本文件）
- `identity_face_in_face_set`（Kepler/Text/ConformingAuto8.lean:380）
- 缺口：HOL `tran`/`tranf`（Conforming.hl:4097-4101）、`hypermap_of_fan_rep`
  （fan.hl:2780）、`face_subset_dart_fan` 未移植 -/
theorem INJ_TRANF_FACE_DELETE_DS (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (ds0 ds0' : Set (V3 × V3))
    (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    let tranf : Set (V3 × V3) → Set (V3 × V3) := fun s =>
      if h : (∃ g : Set (V3 × V3), ∃ z : V3 × V3,
          g = (hypermapOfFan x V E1 hfan1).face z ∧ z ∈ s)
      then Classical.choose h else ∅;
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    ds1 = (hypermapOfFan x V E1 hfan1).face (v, w) ∧
    ds2 = (hypermapOfFan x V E1 hfan1).face (w, v) ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 ∧
    ds0 ∈ (hypermapOfFan x V E hfan).faceSet \ {ds} ∧
    ds0' ∈ (hypermapOfFan x V E hfan).faceSet \ {ds} ∧
    tranf ds0 = tranf ds0' →
      ds0 = ds0' := by
  dsimp only
  rintro ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
    hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2,
    hf10, hf20, hf30, hE1, hds0mem, hds0'mem, htranf⟩
  obtain ⟨hds0_faceSet, hds0_ne⟩ := hds0mem
  obtain ⟨hds0'_faceSet, hds0'_ne⟩ := hds0'mem
  have hEsub : E ⊆ E1 := by rw [← hE1]; exact Set.subset_union_left
  have hdarts_E : (↑(hypermapOfFan x V E hfanC).darts : Set (V3 × V3)) =
      dart1OfFan V E := by
    change (↑(finite_dart1_fan hfanC).toFinset : Set (V3 × V3)) = dart1OfFan V E
    exact (finite_dart1_fan hfanC).coe_toFinset
  -- `TRANF` 给出两个 E-面各自在 `face_{E1}` 下的像与代表元。
  have hT0raw := TRANF x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 ds0
    hfanC hfan1
    ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
     hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hds1, hds2,
     hf10, hf20, hf30, hE1, ⟨hds0_faceSet, hds0_ne⟩⟩
  dsimp only at hT0raw
  obtain ⟨y, hy_eq, hy_mem⟩ := hT0raw
  have hT0'raw := TRANF x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 ds0'
    hfanC hfan1
    ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
     hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hds1, hds2,
     hf10, hf20, hf30, hE1, ⟨hds0'_faceSet, hds0'_ne⟩⟩
  dsimp only at hT0'raw
  obtain ⟨y', hy'_eq, hy'_mem⟩ := hT0'raw
  have hyface : (hypermapOfFan x V E1 hfan1).face y =
      (hypermapOfFan x V E1 hfan1).face y' :=
    hy_eq.symm.trans (htranf.trans hy'_eq)
  have hds0_eq : ds0 = (hypermapOfFan x V E hfanC).face y :=
    identity_face_in_face_set hfanC hds0_faceSet hy_mem
  have hds0'_eq : ds0' = (hypermapOfFan x V E hfanC).face y' :=
    identity_face_in_face_set hfanC hds0'_faceSet hy'_mem
  -- `y`、`y'` 都不在特殊面 `ds` 中。
  have hy_not_ds : y ∉ ds := by
    intro hyds
    have hds_eq : ds = (hypermapOfFan x V E hfanC).face y :=
      identity_face_in_face_set hfanC hds hyds
    exact hds0_ne (hds0_eq.trans hds_eq.symm)
  have hy'_not_ds : y' ∉ ds := by
    intro hy'ds
    have hds_eq : ds = (hypermapOfFan x V E hfanC).face y' :=
      identity_face_in_face_set hfanC hds hy'ds
    exact hds0'_ne (hds0'_eq.trans hds_eq.symm)
  -- 两个代表元都在 `dart1OfFan V E`（从而也在 `dartOfFan V E`）。
  obtain ⟨a, ha_darts, ha_face⟩ :=
    (hypermapOfFan x V E hfanC).face_representation hds0_faceSet
  have hds0_subset : ds0 ⊆ (↑(hypermapOfFan x V E hfanC).darts : Set (V3 × V3)) := by
    rw [ha_face]; exact (hypermapOfFan x V E hfanC).face_subset_darts ha_darts
  have hy_dart1_E : y ∈ dart1OfFan V E := by
    rw [← hdarts_E]; exact hds0_subset hy_mem
  obtain ⟨a', ha'_darts, ha'_face⟩ :=
    (hypermapOfFan x V E hfanC).face_representation hds0'_faceSet
  have hds0'_subset : ds0' ⊆ (↑(hypermapOfFan x V E hfanC).darts : Set (V3 × V3)) := by
    rw [ha'_face]; exact (hypermapOfFan x V E hfanC).face_subset_darts ha'_darts
  have hy'_dart1_E : y' ∈ dart1OfFan V E := by
    rw [← hdarts_E]; exact hds0'_subset hy'_mem
  have hy'_dartOfFan : y' ∈ dartOfFan V E := Or.inr hy'_dart1_E
  -- `y` 与 `y'` 在同一个 `face_{E1}` 轨道，取幂次 `n`。
  have hy_in_H1face : y ∈ (hypermapOfFan x V E1 hfan1).face y' :=
    hyface ▸ (hypermapOfFan x V E1 hfan1).mem_face_self y
  simp only [Hypermap.face, orbitMap] at hy_in_H1face
  obtain ⟨n, hn⟩ := hy_in_H1face
  have hy'_dart1_E1 : y' ∈ dart1OfFan V E1 := hEsub hy'_dart1_E
  have hn' : (f1Fan x V E1)^[n] y' = y :=
    (hypermapOfFan_faceMap_pow_eq_iterate hfan1 hy'_dart1_E1 n).symm.trans hn
  -- `TRAN_COMMUTATIVE_F1_FAN_POWER` 把 `f1Fan` 幂从 `E1` 换回 `E`。
  have hT := TRAN_COMMUTATIVE_F1_FAN_POWER x V E E1 ds f1 f2 f3 v u w ds1 ds2
    f10 f20 f30 y' n hfanC hfan1
    ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
     hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2,
     hf10, hf20, hf30, hE1, hy'_not_ds, hy'_dartOfFan⟩
  have hpow_eq : (f1Fan x V E)^[n] y' = y := hT.trans hn'
  -- 于是 `y` 落在 `ds0'` 中；结合 `y ∈ ds0` 得两个面相等。
  have hy_ds0' : y ∈ ds0' := by
    rw [hds0'_eq]
    have hmem : ((hypermapOfFan x V E hfanC).faceMap ^ n) y' ∈
        (hypermapOfFan x V E hfanC).face y' :=
      pow_apply_mem_orbitMap _ n y'
    rw [hypermapOfFan_faceMap_pow_eq_iterate hfanC hy'_dart1_E n, hpow_eq] at hmem
    exact hmem
  exact hds0_eq.trans (identity_face_in_face_set hfanC hds0'_faceSet hy_ds0').symm

/-! ## 新面集的成员性与 `f1_fan` 幂的不变性（Conforming.hl:5117-5219） -/

/-- HOL Conforming.hl :5117-5154 `ds1_in_face_set_fanadd`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ ds1=face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)
/\ ds2=face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
==> ds1 IN face_set (hypermap1_of_fanx (x,V,E1))
```

编码说明：`pr3 f1= u`/`pr3 f2= w` ↦ `f1.2 = u`/`f2.2 = w`；
`ds1=face ... (x,v,w,sigma_fan x V E1 v w)` ↦ `ds1 = face (v, w)`。
额外携带 `hfan`、`hfan1`。

证明思路：`faceSet = setOfOrbits darts faceMap`；取代表元 `(v,w) ∈
dart1OfFan V E1`（由 `E ⊆ E1`），则 `face (v,w) ∈ faceSet`，再由假设
`ds1 = face (v,w)` 得 `ds1 ∈ faceSet`。可用 `Hypermap.face_representation`
的逆或直接 `⟨(v,w), _, rfl⟩` 构造。

候选已有引理：
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `add_edge_imp_card_set_edge_ge1_fan`（Kepler/Text/ConformingAuto9.lean:376）
- `Hypermap.faceSet`（Kepler/Text/Hypermap.lean:1008）、
  `Hypermap.face`（同:846）
- 缺口：`hypermap_of_fan_rep`（fan.hl:2780）未移植 -/
theorem ds1_in_face_set_fanadd (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    ds1 = (hypermapOfFan x V E1 hfan1).face (v, w) ∧
    ds2 = (hypermapOfFan x V E1 hfan1).face (w, v) ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 →
      ds1 ∈ (hypermapOfFan x V E1 hfan1).faceSet := by
  rintro ⟨_hfanC, _hcard, _hfan80, _hds, _hds3, _hsub, _hf1f2, _hf2f3, _hf3ne,
    _hf1v, _hf2u, _hf3w, _hvu, _huw, _hwv, _hsigma, _hf1u, _hf2w, hds1, _hds2,
    _hf10, _hf20, _hf30, hE1⟩
  have hvwE1 : ({v, w} : Set V3) ∈ E1 := by
    rw [← hE1]
    exact Or.inr rfl
  have hdart1 : (v, w) ∈ dart1OfFan V E1 := hvwE1
  have hmem : (v, w) ∈ (hypermapOfFan x V E1 hfan1).darts := by
    show (v, w) ∈ (finite_dart1_fan hfan1).toFinset
    exact (finite_dart1_fan hfan1).mem_toFinset.mpr hdart1
  have hface : (hypermapOfFan x V E1 hfan1).face (v, w) ∈
      (hypermapOfFan x V E1 hfan1).faceSet :=
    (Hypermap.mem_darts_iff_face_mem _ _).mp hmem
  rw [hds1]
  exact hface

/-- HOL Conforming.hl :5155-5194 `ds2_in_face_set_fanadd`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)= ds1
/\ ds2=face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
==> ds2 IN face_set (hypermap1_of_fanx (x,V,E1))
```

编码说明：与 `ds1_in_face_set_fanadd` 平行，但 `ds1` 的假设方向相反
（`face (v,w) = ds1`），结论为 `ds2 = face (w,v)`。额外携带 `hfan`、
`hfan1`。

证明思路：取代表元 `(w,v) ∈ dart1OfFan V E1`，则 `face (w,v) ∈ faceSet`，
再由 `ds2 = face (w,v)` 得 `ds2 ∈ faceSet`。

候选已有引理：
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `Hypermap.faceSet`（Kepler/Text/Hypermap.lean:1008）、
  `Hypermap.face`（同:846）
- 缺口：`hypermap_of_fan_rep`（fan.hl:2780）未移植 -/
theorem ds2_in_face_set_fanadd (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    (hypermapOfFan x V E1 hfan1).face (v, w) = ds1 ∧
    ds2 = (hypermapOfFan x V E1 hfan1).face (w, v) ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 →
      ds2 ∈ (hypermapOfFan x V E1 hfan1).faceSet := by
  rintro ⟨_hfanC, _hcard, _hfan80, _hds, _hds3, _hsub, _hf1f2, _hf2f3, _hf3ne,
    _hf1v, _hf2u, _hf3w, _hvu, _huw, _hwv, _hsigma, _hf1u, _hf2w, _hds1, hds2,
    _hf10, _hf20, _hf30, hE1⟩
  have hvwE1 : ({v, w} : Set V3) ∈ E1 := by
    rw [← hE1]
    exact Or.inr rfl
  have hwvE1 : ({w, v} : Set V3) ∈ E1 := by
    rwa [Set.pair_comm]
  have hdart1 : (w, v) ∈ dart1OfFan V E1 := hwvE1
  have hmem : (w, v) ∈ (hypermapOfFan x V E1 hfan1).darts := by
    show (w, v) ∈ (finite_dart1_fan hfan1).toFinset
    exact (finite_dart1_fan hfan1).mem_toFinset.mpr hdart1
  have hface : (hypermapOfFan x V E1 hfan1).face (w, v) ∈
      (hypermapOfFan x V E1 hfan1).faceSet :=
    (Hypermap.mem_darts_iff_face_mem _ _).mp hmem
  rw [hds2]
  exact hface

/-- HOL Conforming.hl :5195-5219 `condition_f1_fan_power_in_face_set`

HOL 原文：
```
!n:num x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) y y1 ds.
FAN(x,V,E)
/\ y = (f1_fan x V E POWER n) y1
/\ ds IN face_set (hypermap1_of_fanx (x,V,E))
/\ d_fan (x,V,E) =d1_fan (x,V,E)
/\ y1 IN ds
==> y IN ds
```

编码说明：`n:num` ↦ `n : ℕ`；`(f1_fan x V E POWER n) y1` ↦
`(f1Fan x V E)^[n] y1`；`d_fan`/`d1_fan` ↦ `dartOfFan`/`dart1OfFan`；
`face_set (...)` ↦ `(hypermapOfFan x V E hfan).faceSet`。仅需 `hfan`。

证明思路：对 `n` 归纳。`n = 0` 时 `y = y1`，直接由 `y1 ∈ ds` 得。归纳步
用 `condition_f1_fan_in_face_set`（`PlanarityAuto14.lean:741`）把
`f1Fan x V E ((f1Fan x V E)^[n] y1) ∈ ds` 转成
`(f1Fan x V E)^[n+1] y1 ∈ ds`，注意 `f1Fan` 是 `faceMap` 在 `dart1OfFan`
上的限制（需 `d_fan = d1_fan` 把面内元素拉回 `dart1OfFan`）。

候选已有引理：
- `condition_f1_fan_in_face_set`（Kepler/Text/PlanarityAuto14.lean:741）
- `f1_fan_power_in_face_imp_in_face`（Kepler/Text/ConformingAuto13.lean:746）
- `IMAGE_F1_IN_FACE_IMP_IN_FACE`（Kepler/Text/ConformingAuto1.lean:271）
- `Function.iterate_succ_apply'`（Mathlib）
- 缺口：HOL `d_fan`/`d1_fan` 的等价（`dartset_fully_surrounded_is_non_isolated_fan`）
  未移植 -/
theorem condition_f1_fan_power_in_face_set (n : ℕ) (x : V3) (V : Set V3)
    (E : Set (Set V3)) (y y1 : V3 × V3) (ds : Set (V3 × V3))
    (hfan : FAN x V E) :
    FAN x V E ∧
    y = (f1Fan x V E)^[n] y1 ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧
    dartOfFan V E = dart1OfFan V E ∧
    y1 ∈ ds →
      y ∈ ds := by
  rintro ⟨_, hy, hds, _hdf, hy1⟩
  obtain ⟨d, hd, hface⟩ := Hypermap.face_representation (hypermapOfFan x V E hfan) hds
  have hy1face : y1 ∈ (hypermapOfFan x V E hfan).face d := by simpa [hface] using hy1
  have hy1mem : y1 ∈ (hypermapOfFan x V E hfan).darts :=
    (hypermapOfFan x V E hfan).face_subset_darts hd hy1face
  have hdarts : (↑(hypermapOfFan x V E hfan).darts : Set (V3 × V3)) =
      dart1OfFan V E := by
    change (↑(finite_dart1_fan hfan).toFinset : Set (V3 × V3)) = dart1OfFan V E
    exact (finite_dart1_fan hfan).coe_toFinset
  have hy1d : y1 ∈ dart1OfFan V E := by
    change y1 ∈ (↑(hypermapOfFan x V E hfan).darts : Set (V3 × V3)) at hy1mem
    simpa [hdarts] using hy1mem
  have hface_eq : (hypermapOfFan x V E hfan).face y1 = ds :=
    ((hypermapOfFan x V E hfan).face_eq_of_mem hy1face).symm.trans hface.symm
  have hpow : ((hypermapOfFan x V E hfan).faceMap ^ n) y1 = (f1Fan x V E)^[n] y1 :=
    hypermapOfFan_faceMap_pow_eq_iterate hfan hy1d n
  have hmem : ((hypermapOfFan x V E hfan).faceMap ^ n) y1 ∈
      (hypermapOfFan x V E hfan).face y1 :=
    pow_apply_mem_orbitMap _ n y1
  rw [hy, ← hpow, ← hface_eq]
  exact hmem

/-! ## `tranf` 在删面集上的满射与像（Conforming.hl:5220-6120） -/

/-- HOL Conforming.hl :5220-5772 `SUR_TRANF_FACE_DELETE_DS`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 f.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)= ds1
/\ face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)=ds2
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
/\  f IN (face_set (hypermap1_of_fanx (x,V,E1)) DELETE ds1 ) DELETE ds2
==> ?ds0. ds0 IN face_set (hypermap1_of_fanx (x,V,E)) DELETE ds
/\ tranf x V E E1 ds0=f
```

编码说明：`pr3 f1= u`/`pr3 f2= w` ↦ `f1.2 = u`/`f2.2 = w`；
`(face_set (...) DELETE ds1) DELETE ds2` ↦
`(faceSet \ {ds1}) \ {ds2}`；`tranf` 内联为局部 `let`（见文件头）。
额外携带 `hfan`、`hfan1`。

证明思路：`f` 是 `E1` 的面且 `f ≠ ds1, ds2`。取 `f` 的代表元
`x' = (v',w') ∈ dart1OfFan V E1`。若 `{v',w'} ≠ {v,w}`，则
`{v',w'} ∈ E`，故 `y = (x,v',w',sigma_fan x V E v' w') ∈ d1_fan(x,V,E)`
且其所在 `E` 面 `ds0 = face_E y ∈ faceSet(E) \ {ds}` 满足
`tranf ds0 = f`（由 `tran` 恒等、`face` 的循环性）。若 `{v',w'} = {v,w}`，
则 `f ∈ {ds1, ds2}`，与假设矛盾。HOL 证明按 `f1_fan` 幂的循环分类处理
（`k=0,1,≥2` 分支），对应 `ds1`/`ds2`/其余面的排除。

候选已有引理：
- `TRANF`（Kepler/Text/ConformingAuto13.lean:145）
- `reperentation_of_ds2`（Kepler/Text/ConformingAuto12.lean:596）
- `ds1_in_face_set_fanadd`、`ds2_in_face_set_fanadd`（本文件）
- `SIGMA_FAN_OF_FANADD1`（Kepler/Text/ConformingAuto10.lean:197）
- `SIGMA_FAN_OF_FANADD_AT_POINT1/2`（Kepler/Text/ConformingAuto10.lean:399/510）
- `identity_face_in_face_set`（Kepler/Text/ConformingAuto8.lean:380）
- 缺口：HOL `tran`/`tranf`（Conforming.hl:4097-4101）、`hypermap_of_fan_rep`
  （fan.hl:2780）、`face_subset_dart_fan`、`into_domain_power_efn_fan`
  （fan.hl:2694）、`lemma_face_cycle`/`orbit_cyclic` 未移植 -/
theorem SUR_TRANF_FACE_DELETE_DS (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3) (f : Set (V3 × V3))
    (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    let tranf : Set (V3 × V3) → Set (V3 × V3) := fun s =>
      if h : (∃ g : Set (V3 × V3), ∃ z : V3 × V3,
          g = (hypermapOfFan x V E1 hfan1).face z ∧ z ∈ s)
      then Classical.choose h else ∅;
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    (hypermapOfFan x V E1 hfan1).face (v, w) = ds1 ∧
    (hypermapOfFan x V E1 hfan1).face (w, v) = ds2 ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 ∧
    f ∈ ((hypermapOfFan x V E1 hfan1).faceSet \ {ds1}) \ {ds2} →
      ∃ ds0, ds0 ∈ (hypermapOfFan x V E hfan).faceSet \ {ds} ∧ tranf ds0 = f := by
  dsimp only
  rintro ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
    hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2,
    hf10, hf20, hf30, hE1, hfmem⟩
  obtain ⟨hfmem', hf_ne_ds2⟩ := hfmem
  obtain ⟨hf_faceSet1, hf_ne_ds1⟩ := hfmem'
  have hf_ne_ds1' : f ≠ ds1 := by simpa using hf_ne_ds1
  have hf_ne_ds2' : f ≠ ds2 := by simpa using hf_ne_ds2
  let H : Hypermap (V3 × V3) := hypermapOfFan x V E hfanC
  let H1 : Hypermap (V3 × V3) := hypermapOfFan x V E1 hfan1
  have hdarts_E : (↑H.darts : Set (V3 × V3)) = dart1OfFan V E := by
    change (↑(finite_dart1_fan hfanC).toFinset : Set (V3 × V3)) = dart1OfFan V E
    exact (finite_dart1_fan hfanC).coe_toFinset
  have hdarts_E1 : (↑H1.darts : Set (V3 × V3)) = dart1OfFan V E1 := by
    change (↑(finite_dart1_fan hfan1).toFinset : Set (V3 × V3)) = dart1OfFan V E1
    exact (finite_dart1_fan hfan1).coe_toFinset
  have hds_dart1 : ds ⊆ dart1OfFan V E := by
    obtain ⟨a, ha_darts, ha_face⟩ := H.face_representation hds
    intro y hy
    rw [ha_face] at hy
    rw [← hdarts_E]
    exact H.face_subset_darts ha_darts hy
  obtain ⟨p, hp_darts, hp_face⟩ := H1.face_representation hf_faceSet1
  have hface_of_mem : ∀ y ∈ f, H1.face y = f := by
    intro y hy
    have hy' : y ∈ H1.face p := by rw [← hp_face]; exact hy
    exact (H1.face_eq_of_mem hy').symm.trans hp_face.symm
  have hf2_eq : f2 = (u, w) := Prod.ext hf2u hf2w
  have hwv_E1 : ({w, v} : Set V3) ∈ E1 := by
    rw [← hE1]; exact Set.mem_union_right E (by simp [Set.pair_comm])
  have hsig3 : sigmaFan x V E1 w v = u :=
    SIGMA_FAN_OF_FANADD_AT_POINT3 x V E E1 v u w
      ⟨hfanC, hfan1, hvu, huw, hwv, hsigma, hfan80, hcard, hE1⟩
  have hinv_wu : inverse1SigmaFan x V E1 w u = v := by
    have h := (INVERSE1_SIGMA_FAN (x := x) (V := V) (E := E1) (v := w) hfan1).2.2 v hwv_E1
    rw [hsig3] at h
    exact h
  have hfm_f2 : H1.faceMap f2 = (w, v) := by
    have hd1 : f2 ∈ dart1OfFan V E1 := by
      rw [hf2_eq]
      change ({u, w} : Set V3) ∈ E1
      rw [← hE1]
      exact Set.mem_union_left _ huw
    have h := hypermapOfFan_faceMap_eq_f1Fan hfan1 hd1
    rw [h]
    simp only [f1Fan, hf2_eq, hinv_wu]
  have hface_f2_ds2 : H1.face f2 = ds2 := by
    have hmem : (w, v) ∈ H1.face f2 := by
      change (w, v) ∈ orbitMap H1.faceMap f2
      exact ⟨1, by rw [pow_one]; exact hfm_f2⟩
    exact (H1.face_eq_of_mem hmem).trans hds2
  have hvw_E1 : ({v, w} : Set V3) ∈ E1 := by
    rw [← hE1]; exact Set.mem_union_right E (by simp)
  have hsig1 : sigmaFan x V E1 v w = sigmaFan x V E v u :=
    SIGMA_FAN_OF_FANADD_AT_POINT1 x V E E1 v u w
      ⟨hfanC, hfan1, hvu, huw, hwv, hsigma, hfan80, hcard, hE1⟩
  have hinv_v : inverse1SigmaFan x V E1 v (sigmaFan x V E v u) = w := by
    have h := (INVERSE1_SIGMA_FAN (x := x) (V := V) (E := E1) (v := v) hfan1).2.2 w hvw_E1
    rw [hsig1] at h
    exact h
  have hfm_h : H1.faceMap (sigmaFan x V E v u, v) = (v, w) := by
    have hd1 : (sigmaFan x V E v u, v) ∈ dart1OfFan V E1 := by
      have hu_mem : u ∈ setOfEdge v V E :=
        (properties_of_setOfEdge_fan x V E v u hfanC).mp hvu
      have hσ_mem : sigmaFan x V E v u ∈ setOfEdge v V E :=
        sigma_fan_in_setOfEdge hfanC hu_mem
      have hedge : ({v, sigmaFan x V E v u} : Set V3) ∈ E :=
        (properties_of_setOfEdge_fan x V E v (sigmaFan x V E v u) hfanC).mpr hσ_mem
      have hedge' : ({sigmaFan x V E v u, v} : Set V3) ∈ E := by
        rwa [Set.pair_comm] at hedge
      change ({sigmaFan x V E v u, v} : Set V3) ∈ E1
      rw [← hE1]
      exact Set.mem_union_left _ hedge'
    have h := hypermapOfFan_faceMap_eq_f1Fan hfan1 hd1
    rw [h]
    simp only [f1Fan, hinv_v]
  have hface_h_ds1 : H1.face (sigmaFan x V E v u, v) = ds1 := by
    have hmem : (v, w) ∈ H1.face (sigmaFan x V E v u, v) := by
      change (v, w) ∈ orbitMap H1.faceMap (sigmaFan x V E v u, v)
      exact ⟨1, by rw [pow_one]; exact hfm_h⟩
    exact (H1.face_eq_of_mem hmem).trans hds1
  have h_agree : ∀ y ∈ ds, y ≠ (u, w) → y ≠ (sigmaFan x V E v u, v) →
      f1Fan x V E y = f1Fan x V E1 y := by
    intro y hy_ds hy_f2 hy_h
    have hy_dart1 : y ∈ dart1OfFan V E := hds_dart1 hy_ds
    have hy_dart : y ∈ dartOfFan V E := Set.mem_union_right _ hy_dart1
    by_cases hy2 : y.2 ∈ ({v, w} : Set V3)
    · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy2
      rcases hy2 with hy2 | hy2
      · by_cases hy1 : y.1 = sigmaFan x V E v u
        · exact absurd (Prod.ext hy1 hy2) hy_h
        · exact TRAN_COMMUTATIVE_F1_FAN3 x V E E1 ds f1 f2 f3 v u w ds1 ds2
            f10 f20 f30 y hfanC hfan1
            ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
             hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hds1.symm, hds2.symm,
             hf10, hf20, hf30, hE1, hy1, hy2, hy_dart⟩
      · by_cases hy1 : y.1 = u
        · exact absurd (Prod.ext hy1 hy2) hy_f2
        · exact TRAN_COMMUTATIVE_F1_FAN2 x V E E1 ds f1 f2 f3 v u w ds1 ds2
            f10 f20 f30 y hfanC hfan1
            ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
             hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hds1.symm, hds2.symm,
             hf10, hf20, hf30, hE1, hy1, hy2, hy_dart⟩
    · exact TRAN_COMMUTATIVE_F1_FAN1 x V E E1 ds f1 f2 f3 v u w ds1 ds2
        f10 f20 f30 y hfanC hfan1
        ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
         hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hds1.symm, hds2.symm,
         hf10, hf20, hf30, hE1, hy2, hy_dart⟩
  have hf2_ds : f2 ∈ ds := hsub (by simp)
  have hnot_sub : ¬ f ⊆ ds := by
    intro hfsub
    have hf2_not : f2 ∉ f := by
      intro hf2f
      have hface_f2_eq : H1.face f2 = f := hface_of_mem f2 hf2f
      exact hf_ne_ds2' (hface_f2_eq.symm.trans hface_f2_ds2)
    have h_not : (sigmaFan x V E v u, v) ∉ f := by
      intro hf_h
      have hface_h_eq : H1.face (sigmaFan x V E v u, v) = f :=
        hface_of_mem _ hf_h
      exact hf_ne_ds1' (hface_h_eq.symm.trans hface_h_ds1)
    have hH_inv : ∀ y ∈ f, H.faceMap y ∈ f := by
      intro y hy
      have hy_ds : y ∈ ds := hfsub hy
      have hy_dart1 : y ∈ dart1OfFan V E := hds_dart1 hy_ds
      have hy_dart1_E1 : y ∈ dart1OfFan V E1 := by
        change ({y.1, y.2} : Set V3) ∈ E1
        rw [← hE1]
        exact Set.mem_union_left _ hy_dart1
      have hmapE : H.faceMap y = f1Fan x V E y :=
        hypermapOfFan_faceMap_eq_f1Fan hfanC hy_dart1
      have hmapE1 : H1.faceMap y = f1Fan x V E1 y :=
        hypermapOfFan_faceMap_eq_f1Fan hfan1 hy_dart1_E1
      have hagree : f1Fan x V E y = f1Fan x V E1 y :=
        h_agree y hy_ds (fun hh => hf2_not (by rw [hf2_eq]; exact hh ▸ hy))
          (fun hh => h_not (hh ▸ hy))
      rw [hmapE, hagree, ← hmapE1]
      have : H1.faceMap y ∈ H1.face y := by
        simpa [Hypermap.face, pow_one] using pow_apply_mem_orbitMap H1.faceMap 1 y
      rw [← hface_of_mem y hy]
      exact this
    have hds_subset_f : ds ⊆ f := by
      have hp_f : p ∈ f := by rw [hp_face]; exact H1.mem_face_self p
      have hp_ds : p ∈ ds := hfsub hp_f
      obtain ⟨q, _, hq_face⟩ := H.face_representation hds
      have hp_in_Hq : p ∈ H.face q := by rw [← hq_face]; exact hp_ds
      have hface_p_ds : H.face p = ds :=
        (H.face_eq_of_mem hp_in_Hq).symm.trans hq_face.symm
      intro y hy
      have hy_orbit : y ∈ H.face p := by rw [hface_p_ds]; exact hy
      rw [Hypermap.face] at hy_orbit
      obtain ⟨n, hn⟩ := hy_orbit
      rw [← hn]
      clear hn hy
      induction n with
      | zero => simpa using hp_f
      | succ k ih =>
          rw [pow_succ', Equiv.Perm.mul_apply]
          exact hH_inv _ ih
    exact hf2_not (hds_subset_f hf2_ds)
  obtain ⟨z, hz_f, hz_not_ds⟩ := Set.not_subset.mp hnot_sub
  have hz_in_p : z ∈ H1.face p := by rw [← hp_face]; exact hz_f
  have hz_darts1 : z ∈ H1.darts := H1.face_subset_darts hp_darts hz_in_p
  have hz_dart1_E1 : z ∈ dart1OfFan V E1 := by
    rw [← hdarts_E1]; exact hz_darts1
  have hfz : f = H1.face z := hp_face.trans (H1.face_eq_of_mem hz_in_p)
  have hz_dart1_E : z ∈ dart1OfFan V E := by
    by_contra hz
    have hpair_E1 : ({z.1, z.2} : Set V3) ∈ E1 := hz_dart1_E1
    rw [← hE1] at hpair_E1
    rcases hpair_E1 with hpair | hpair
    · exact hz hpair
    · rcases (Set.pair_eq_pair_iff.mp hpair) with ⟨hz1, hz2⟩ | ⟨hz1, hz2⟩
      · have hz_eq : z = (v, w) := Prod.ext hz1 hz2
        exact hf_ne_ds1' (by rw [hfz, hz_eq, hds1])
      · have hz_eq : z = (w, v) := Prod.ext hz1 hz2
        exact hf_ne_ds2' (by rw [hfz, hz_eq, hds2])
  let ds0 : Set (V3 × V3) := (hypermapOfFan x V E hfanC).face z
  have hz_darts_E : z ∈ H.darts := by
    change z ∈ (↑H.darts : Set (V3 × V3))
    rw [hdarts_E]
    exact hz_dart1_E
  have hds0_faceSet : ds0 ∈ (hypermapOfFan x V E hfanC).faceSet :=
    (Hypermap.mem_darts_iff_face_mem _ z).mp hz_darts_E
  have hz_ds0 : z ∈ ds0 := by
    change z ∈ (hypermapOfFan x V E hfanC).face z
    exact Hypermap.mem_face_self _ z
  have hds0_ne : ds0 ≠ ds := by
    intro h
    exact hz_not_ds (by rw [← h]; exact hz_ds0)
  refine ⟨ds0, ⟨hds0_faceSet, hds0_ne⟩, ?_⟩
  exact unique_tranf_fan x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30
    ds0 f z hfanC hfan1
    ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
     hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1.symm, hds2.symm,
     hf10, hf20, hf30, hE1, hfz, hz_ds0, hds0_faceSet, hds0_ne⟩

/-- HOL Conforming.hl :5773-6120 `DOMAIN_TRANF_FACE_DELETE_DS`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 ds0.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)= ds1
/\ face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)=ds2
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
/\ ds0 IN face_set (hypermap1_of_fanx (x,V,E)) DELETE ds
      ==> tranf x V E E1 ds0 IN
          face_set (hypermap1_of_fanx (x,V,E1)) DELETE ds1 DELETE ds2
```

编码说明：`pr3 f1= u`/`pr3 f2= w` ↦ `f1.2 = u`/`f2.2 = w`；
`(face_set (...) DELETE ds1) DELETE ds2` ↦
`(faceSet \ {ds1}) \ {ds2}`；`tranf` 内联为局部 `let`（见文件头）。
额外携带 `hfan`、`hfan1`。

证明思路：`ds0 ∈ faceSet(E) \ {ds}`，取代表元 `y ∈ ds0`。由 `TRANF`
（或 `unique_tranf_fan`）`tranf ds0 = face_{E1} y`；再证该面不属于 `ds1`、
`ds2`：若等于 `ds1`（对应 `f1_fan` 幂为 0 或 1 的分支）或 `ds2`
（对应 `f1_fan` 幂 ≥2 的分支），用 `SIGMA_FAN_OF_FANADD_AT_POINT1/2`、
`reperentation_of_ds2` 及 `{w,v} ∉ E` 导出矛盾。

候选已有引理：
- `TRANF`（Kepler/Text/ConformingAuto13.lean:145）
- `reperentation_of_ds2`（Kepler/Text/ConformingAuto12.lean:596）
- `SIGMA_FAN_OF_FANADD_AT_POINT1`（Kepler/Text/ConformingAuto10.lean:399）
- `SIGMA_FAN_OF_FANADD_AT_POINT2`（Kepler/Text/ConformingAuto10.lean:510）
- `INJ_TRAN_D1_FAN`（本文件）
- `identity_face_in_face_set`（Kepler/Text/ConformingAuto8.lean:380）
- 缺口：HOL `tran`/`tranf`（Conforming.hl:4097-4101）、`hypermap_of_fan_rep`
  （fan.hl:2780）、`face_subset_dart_fan`、`into_domain_power_efn_fan`
  （fan.hl:2694）未移植 -/
theorem DOMAIN_TRANF_FACE_DELETE_DS (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3) (ds0 : Set (V3 × V3))
    (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    let tranf : Set (V3 × V3) → Set (V3 × V3) := fun s =>
      if h : (∃ g : Set (V3 × V3), ∃ z : V3 × V3,
          g = (hypermapOfFan x V E1 hfan1).face z ∧ z ∈ s)
      then Classical.choose h else ∅;
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    (hypermapOfFan x V E1 hfan1).face (v, w) = ds1 ∧
    (hypermapOfFan x V E1 hfan1).face (w, v) = ds2 ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 ∧
    ds0 ∈ (hypermapOfFan x V E hfan).faceSet \ {ds} →
      tranf ds0 ∈ ((hypermapOfFan x V E1 hfan1).faceSet \ {ds1}) \ {ds2} := by
  dsimp only
  rintro ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
    hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2,
    hf10, hf20, hf30, hE1, hds0mem⟩
  obtain ⟨hds0_faceSet, hds0_ne⟩ := hds0mem
  have hEsub : E ⊆ E1 := by rw [← hE1]; exact Set.subset_union_left
  have hT := TRANF x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 ds0
    hfanC hfan1
    ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
     hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hds1.symm, hds2.symm,
     hf10, hf20, hf30, hE1, ⟨hds0_faceSet, hds0_ne⟩⟩
  dsimp only at hT
  obtain ⟨y, hy_eq, hy_mem⟩ := hT
  have hdarts_E : (↑(hypermapOfFan x V E hfanC).darts : Set (V3 × V3)) =
      dart1OfFan V E := by
    change (↑(finite_dart1_fan hfanC).toFinset : Set (V3 × V3)) = dart1OfFan V E
    exact (finite_dart1_fan hfanC).coe_toFinset
  obtain ⟨a, ha_darts, ha_face⟩ :=
    (hypermapOfFan x V E hfanC).face_representation hds0_faceSet
  have hds0_subset : ds0 ⊆ (↑(hypermapOfFan x V E hfanC).darts : Set (V3 × V3)) := by
    rw [ha_face]; exact (hypermapOfFan x V E hfanC).face_subset_darts ha_darts
  have hy_dart1_E : y ∈ dart1OfFan V E := by
    rw [← hdarts_E]; exact hds0_subset hy_mem
  have hy_dartOfFan : y ∈ dartOfFan V E := Or.inr hy_dart1_E
  have hface_y_ds0 : (hypermapOfFan x V E hfanC).face y = ds0 := by
    have hy_in : y ∈ (hypermapOfFan x V E hfanC).face a := by
      rw [← ha_face]; exact hy_mem
    exact ((hypermapOfFan x V E hfanC).face_eq_of_mem hy_in).symm.trans ha_face.symm
  have hy_not_ds : y ∉ ds := by
    intro hyds
    have hface_ds : ds = (hypermapOfFan x V E hfanC).face y :=
      identity_face_in_face_set hfanC hds hyds
    exact hds0_ne (hface_ds.trans hface_y_ds0).symm
  have hdarts_E1 : (↑(hypermapOfFan x V E1 hfan1).darts : Set (V3 × V3)) =
      dart1OfFan V E1 := by
    change (↑(finite_dart1_fan hfan1).toFinset : Set (V3 × V3)) = dart1OfFan V E1
    exact (finite_dart1_fan hfan1).coe_toFinset
  have hy_dart1_E1 : y ∈ dart1OfFan V E1 := hEsub hy_dart1_E
  have hpow : ∀ n : ℕ,
      ((hypermapOfFan x V E hfanC).faceMap ^ n) y =
      ((hypermapOfFan x V E1 hfan1).faceMap ^ n) y := by
    intro n
    rw [hypermapOfFan_faceMap_pow_eq_iterate hfanC hy_dart1_E n,
        hypermapOfFan_faceMap_pow_eq_iterate hfan1 hy_dart1_E1 n]
    exact TRAN_COMMUTATIVE_F1_FAN_POWER x V E E1 ds f1 f2 f3 v u w ds1 ds2
      f10 f20 f30 y n hfanC hfan1
      ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
       hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w,
       hds1.symm, hds2.symm, hf10, hf20, hf30, hE1, hy_not_ds, hy_dartOfFan⟩
  have hface_eq : (hypermapOfFan x V E1 hfan1).face y =
      (hypermapOfFan x V E hfanC).face y := by
    ext z
    simp only [Hypermap.face, orbitMap, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, (hpow n).trans hn⟩
    · rintro ⟨n, hn⟩; exact ⟨n, (hpow n).symm.trans hn⟩
  have hds0_eq_face1 : ds0 = (hypermapOfFan x V E1 hfan1).face y := by
    rw [← hface_y_ds0, hface_eq]
  have hy_darts1 : y ∈ (hypermapOfFan x V E1 hfan1).darts := by
    change y ∈ (↑(hypermapOfFan x V E1 hfan1).darts : Set (V3 × V3))
    rw [hdarts_E1]
    exact hy_dart1_E1
  have hds0_faceSet1 : ds0 ∈ (hypermapOfFan x V E1 hfan1).faceSet := by
    rw [hds0_eq_face1]
    exact (Hypermap.mem_darts_iff_face_mem _ y).mp hy_darts1
  have hvw_ds1 : (v, w) ∈ ds1 := by
    rw [← hds1]
    exact (hypermapOfFan x V E1 hfan1).mem_face_self (v, w)
  have hwv_ds2 : (w, v) ∈ ds2 := by
    rw [← hds2]
    exact (hypermapOfFan x V E1 hfan1).mem_face_self (w, v)
  have hds0_ne_ds1 : ds0 ≠ ds1 := by
    intro h
    have hvw_ds0 : (v, w) ∈ ds0 := by rw [h]; exact hvw_ds1
    have hvw_dart : (v, w) ∈ dart1OfFan V E := by
      rw [← hdarts_E]; exact hds0_subset hvw_ds0
    have hpair : ({v, w} : Set V3) ∈ E := hvw_dart
    exact hwv (by rwa [Set.pair_comm] at hpair)
  have hds0_ne_ds2 : ds0 ≠ ds2 := by
    intro h
    have hwv_ds0 : (w, v) ∈ ds0 := by rw [h]; exact hwv_ds2
    have hwv_dart : (w, v) ∈ dart1OfFan V E := by
      rw [← hdarts_E]; exact hds0_subset hwv_ds0
    exact hwv hwv_dart
  rw [hy_eq, hface_eq, hface_y_ds0]
  simp only [Set.mem_sdiff, Set.mem_singleton_iff]
  exact ⟨⟨hds0_faceSet1, hds0_ne_ds1⟩, hds0_ne_ds2⟩

/-- HOL Conforming.hl :6121-6177 `EQ_CARD_FACE_FAN_AND_FANADD`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)= ds1
/\ face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)=ds2
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
==> CARD ((face_set (hypermap1_of_fanx (x,V,E1)) DELETE ds1 ) DELETE ds2 )= CARD (face_set (hypermap1_of_fanx (x,V,E)) DELETE ds)
```

编码说明：`CARD s` ↦ `s.ncard`；`(face_set (...) DELETE ds1) DELETE ds2` ↦
`(faceSet \ {ds1}) \ {ds2}`；`face (v,w) = ds1`/`face (w,v) = ds2`。额外携带
`hfan`、`hfan1`。本定理的结论不含 `tranf`，但 HOL 证明用 `tranf` 作为
双射（`DOMAIN`/`SUR`/`INJ_TRANF_FACE_DELETE_DS`）。

证明思路：用 `CARD_IMAGE_INJ_EQ`（HOL）即 Mathlib 的
`Set.ncard_image_of_injOn`：以 `tranf` 为映射，
`DOMAIN_TRANF_FACE_DELETE_DS` 给出像集包含于
`(faceSet1 \ {ds1}) \ {ds2}`，`SUR_TRANF_FACE_DELETE_DS` 给出满射，
`INJ_TRANF_FACE_DELETE_DS` 给出单射；两侧 `ncard` 相等。需
`FINITE_HYPERMAP_ORBITS`（即 `Hypermap.faceSet_finite`）保证有限性。

候选已有引理：
- `DOMAIN_TRANF_FACE_DELETE_DS`、`SUR_TRANF_FACE_DELETE_DS`、
  `INJ_TRANF_FACE_DELETE_DS`（本文件）
- `Hypermap.faceSet_finite`（Kepler/Text/Hypermap.lean:1016）
- `Set.ncard_image_of_injOn`、`Set.ncard_congr`（Mathlib）
- 缺口：HOL `CARD_IMAGE_INJ_EQ`（Mathlib 有等价形式）、`tranf`
  （Conforming.hl:4101）未移植 -/
theorem EQ_CARD_FACE_FAN_AND_FANADD (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    (hypermapOfFan x V E1 hfan1).face (v, w) = ds1 ∧
    (hypermapOfFan x V E1 hfan1).face (w, v) = ds2 ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 →
      (((hypermapOfFan x V E1 hfan1).faceSet \ {ds1}) \ {ds2}).ncard =
        ((hypermapOfFan x V E hfan).faceSet \ {ds}).ncard := by
  intro ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
    hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2,
    hf10, hf20, hf30, hE1⟩
  let tranf : Set (V3 × V3) → Set (V3 × V3) := fun s =>
    if h : (∃ g : Set (V3 × V3), ∃ z : V3 × V3,
        g = (hypermapOfFan x V E1 hfan1).face z ∧ z ∈ s)
    then Classical.choose h else ∅
  refine (Set.ncard_congr
    (s := (hypermapOfFan x V E hfan).faceSet \ {ds})
    (t := ((hypermapOfFan x V E1 hfan1).faceSet \ {ds1}) \ {ds2})
    (fun a _ => tranf a) ?_ ?_ ?_).symm
  · intro a ha
    exact DOMAIN_TRANF_FACE_DELETE_DS x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 a
      hfan hfan1
      ⟨hfan, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
       hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2,
       hf10, hf20, hf30, hE1, ha⟩
  · intro a b ha hb hab
    exact INJ_TRANF_FACE_DELETE_DS x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 a b
      hfan hfan1
      ⟨hfan, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
       hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w,
       hds1.symm, hds2.symm,
       hf10, hf20, hf30, hE1, ha, hb, hab⟩
  · intro b hb
    obtain ⟨ds0, hds0mem, heq⟩ :=
      SUR_TRANF_FACE_DELETE_DS x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 b
        hfan hfan1
        ⟨hfan, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
         hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2,
         hf10, hf20, hf30, hE1, hb⟩
    exact ⟨ds0, hds0mem, by simpa only [tranf] using heq⟩

end Kepler.Text
