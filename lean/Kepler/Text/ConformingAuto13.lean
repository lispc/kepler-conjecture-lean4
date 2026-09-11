/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level theorems, batch 13
(Conforming.hl:4156-4847).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage (batch 13, Conforming.hl:4156-4847):
- `TRANF` (4156)
- `TRAN_COMMUTATIVE_F1_FAN1` (4185)
- `TRAN_COMMUTATIVE_F1_FAN2` (4253)
- `TRAN_COMMUTATIVE_F1_FAN3` (4340)
- `TRAN_COMMUTATIVE_F1_FAN` (4427)
- `f1_fan_power_in_face` (4606)
- `f1_fan_power_in_face_imp_in_face` (4639)
- `TRAN_COMMUTATIVE_F1_FAN0` (4671)
- `TRAN_COMMUTATIVE_F1_FAN_POWER` (4718)
- `TRAN_COMMUTATIVE_F1_FAN_POWER3` (4769)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `FAN(x,V,E)` ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); HOL
  `set_of_edge v V E` ↔ `setOfEdge v V E` (Kepler/Text/Fan.lean:62); HOL
  `sigma_fan` ↔ `sigmaFan` (Kepler/Text/Fan.lean:67); HOL `fan80` ↔
  `fan80` (Kepler/Text/Fan.lean:227); HOL
  `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`; HOL
  `CARD ds > 3` ↔ `3 < ds.ncard`.
- HOL `hypermap1_of_fanx (x,V,E)` is NOT ported; as in
  Kepler/Text/PlanarityComponent.lean:37-48 and the earlier conforming
  batches, `face_set (hypermap1_of_fanx (x,V,E))` is encoded as
  `(hypermapOfFan x V E hfan).faceSet`, `face (hypermap1_of_fanx (x,V,E)) f`
  as `(hypermapOfFan x V E hfan).face f`, and
  `face_set (...) DELETE ds` as `(hypermapOfFan x V E hfan).faceSet \ {ds}`.
  Since `hypermapOfFan` (Kepler/Text/Fan.lean:1169) needs an explicit
  `hfan : FAN x V E`, every theorem that mentions it carries an extra
  explicit `(hfan : FAN x V E)` argument; theorems that also mention
  `face (hypermap1_of_fanx (x,V,E1))` carry a second extra explicit
  argument `(hfan1 : FAN x V E1)`. These are the only deviations from the
  HOL signatures (HOL's `hypermap_of_fan` is total).
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
  pair darts. Hence the commutativity conclusions collapse to
  `f1Fan x V E y = f1Fan x V E1 y` (resp. the `POWER` form
  `(f1Fan x V E)^[n] y = (f1Fan x V E1)^[n] y`). Caveat: the already-ported
  `exists_tranf_fan` (Kepler/Text/ConformingAuto12.lean:953) instead inlines
  `tran x V E1 y` as `nFanPair x V E1 y`; that encoding is NOT used here
  because it changes the `(pr2,pr3)` dart and would make the commutativity
  statements false (e.g. it would force `y.2 = sigmaFan x V E1 y.1 y.2`).
- HOL `tranf x V E E1 ds0 = @f. ?y. f = face (hypermap1_of_fanx (x,V,E1))
  (tran x V E1 y) /\ y IN ds0` (Conforming.hl:4101) is NOT ported. Its
  closest existing encoding is the Hilbert choice `Classical.choose` of the
  same existence predicate (with `tran` read as the identity, i.e.
  `f = face y /\ y IN ds0`); since the existence is only available under the
  theorem's hypotheses, `tranf` is inlined in `TRANF` as the totalized
  `if h : (∃ f, ∃ y, ...) then Classical.choose h else ∅` (the `else` branch
  is unreachable under the hypotheses). No new definition is introduced.
- HOL `trans` (4094) is not needed by any of the ten theorems.
- HOL `IMAGE_F1_IN_FACE_IMP_IN_FACE` ↔ `IMAGE_F1_IN_FACE_IMP_IN_FACE`
  (Kepler/Text/ConformingAuto1.lean:271); `STEP3_REDUCE_FAN`
  (Kepler/Text/ConformingAuto9.lean:298); `exists_tranf_fan`
  (Kepler/Text/ConformingAuto12.lean:935). These live in earlier conforming
  batches which are NOT imported here (per the porting convention the batch
  imports only `PlanarityAuto16` and `ConformingDefs`); the proof sketches
  note them as candidates to be restated or imported by the worker pool.
- None of the ten statements is Mathlib-general: every one mentions the
  repo-specific `FAN`/`sigmaFan`/`f1Fan`/`hypermapOfFan` vocabulary, so
  nothing is skipped.
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs
import Kepler.Text.ConformingAuto11

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Classical

/-! ## `tranf` 的存在性与 `tran` 与 `f1_fan` 的交换（Conforming.hl:4156-4599） -/

/-- HOL Conforming.hl :4156-4184 `TRANF`

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
/\ sigma_fan x V E u w = v
/\ ds1 = face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)
/\ ds2 = face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
/\ ds0 IN face_set (hypermap1_of_fanx (x,V,E)) DELETE ds
==>
?y. tranf x V E E1 ds0 = face (hypermap1_of_fanx (x,V,E1)) (tran x V E1 y)/\ y IN ds0
```

编码说明：`face_set (...) DELETE ds` ↦
`(hypermapOfFan x V E hfan).faceSet \ {ds}`；`tran` 未移植，在点对编码下
为恒等（见文件头），故 `face(...)(tran x V E1 y)` 编码为 `face y`；
`tranf` 未移植，内联为
`if h : (∃ f, ∃ y, f = face y ∧ y ∈ ds0) then Classical.choose h else ∅`
（见文件头）。额外携带 `hfan`、`hfan1`。

证明思路：`tranf` 是 `@f. ?y. f = face(...)(tran...y) /\ y IN ds0` 的选择
函数，其 spec 恰是本结论。由 `ds0 ∈ faceSet \ {ds}` 得某 `x' ∈ ds0` 且
`ds0 = face x'`；`tranf` 满足其定义谓词，取 `y` 为该谓词给出的点即可，
`Classical.choose_spec`/`dif_pos` 收口（无需 `exists_tranf_fan`）。

候选已有引理：
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `Classical.choose_spec`、`dif_pos`（Mathlib/Lean core）
- `exists_tranf_fan`（Kepler/Text/ConformingAuto12.lean:935）——注意该
  port 把 `tran` 写成 `nFanPair`，与本文件对 `tran` 的忠实编码不一致，
  故不采用
- 缺口：HOL `tranf`/`tran`（Conforming.hl:4094-4101）未移植 -/
theorem TRANF (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3) (ds0 : Set (V3 × V3))
    (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧
    ds1 = (hypermapOfFan x V E1 hfan1).face (v, w) ∧
    ds2 = (hypermapOfFan x V E1 hfan1).face (w, v) ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 ∧
    ds0 ∈ (hypermapOfFan x V E hfan).faceSet \ {ds} →
      (let tranf : Set (V3 × V3) :=
         if h : ∃ f : Set (V3 × V3), ∃ y : V3 × V3,
             f = (hypermapOfFan x V E1 hfan1).face y ∧ y ∈ ds0
         then Classical.choose h else ∅;
       ∃ y : V3 × V3,
         tranf = (hypermapOfFan x V E1 hfan1).face y ∧ y ∈ ds0) := by
  rintro ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hds0⟩
  have hface : ds0 ∈ (hypermapOfFan x V E hfan).faceSet := hds0.1
  obtain ⟨y0, _, hy0⟩ := (hypermapOfFan x V E hfan).face_representation hface
  have hy0mem : y0 ∈ ds0 := by
    rw [hy0]
    exact (hypermapOfFan x V E hfan).mem_face_self y0
  have hP : ∃ f : Set (V3 × V3), ∃ y : V3 × V3,
      f = (hypermapOfFan x V E1 hfan1).face y ∧ y ∈ ds0 :=
    ⟨(hypermapOfFan x V E1 hfan1).face y0, y0, rfl, hy0mem⟩
  dsimp only
  rw [dif_pos hP]
  exact Classical.choose_spec hP

/-- HOL Conforming.hl :4185-4252 `TRAN_COMMUTATIVE_F1_FAN1`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 y.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v
/\ ds1 = face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)
/\ ds2 = face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
/\ ~(pr3 y IN {v,w})
/\ y IN d_fan(x,V,E)
==>
tran x V E1 ((f1_fan x V E ) y)=(f1_fan x V E1 ) (tran x V E1 y)
```

编码说明：`~(pr3 y IN {v,w})` ↦ `¬ (y.2 ∈ ({v, w} : Set V3))`；
`d_fan` ↦ `dartOfFan`；`tran` 在点对编码下为恒等（见文件头），故结论化为
`f1Fan x V E y = f1Fan x V E1 y`。额外携带 `hfan`、`hfan1`。

证明思路：展开 `f1Fan`/`sigmaFan`，把目标化为
`inverse1SigmaFan` 在 `E` 与 `E1` 下相等。由 `STEP3_REDUCE_FAN` 与
`SIGMA_FAN_OF_FANADD1`（E1 = E ∪ {{v,w}}）在 `pr3 y ∉ {v,w}` 的情形下
给出 σ 相同；`INVERSE1_SIGMA_FAN` 连接 σ 与 `inverse1SigmaFan`。

候选已有引理：
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `SIGMA_FAN_OF_FANADD1`（Kepler/Text/ConformingAuto10.lean:197）
- `INVERSE1_SIGMA_FAN`（Kepler/Text/Fan.lean:822）
- `dartOfFan_eq_dart1_of_surrounded`（Kepler/Text/Fan.lean:1084）
- 缺口：HOL `tran`/`tranf`、`hypermap_of_fan_rep`（fan.hl:2780）、
  `dartset_fully_surrounded_is_non_isolated_fan` 未移植 -/
private lemma setOfEdge_eq_of_add_edge_not_mem (V : Set V3) (E E1 : Set (Set V3))
    (v w a : V3) (hE1 : E ∪ {({v, w} : Set V3)} = E1)
    (ha : a ∉ ({v, w} : Set V3)) :
    setOfEdge a V E = setOfEdge a V E1 := by
  ext u
  simp only [setOfEdge, Set.mem_setOf_eq]
  constructor
  · rintro ⟨he, hu⟩
    exact ⟨by rw [← hE1]; exact Or.inl he, hu⟩
  · rintro ⟨he, hu⟩
    rw [← hE1] at he
    rcases he with he | he
    · exact ⟨he, hu⟩
    · simp only [Set.mem_singleton_iff] at he
      exact absurd (he ▸ (by simp : a ∈ ({a, u} : Set V3))) ha

private lemma sigmaFan_eq_of_add_edge_not_mem (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (v w a : V3)
    (hE1 : E ∪ {({v, w} : Set V3)} = E1)
    (ha : a ∉ ({v, w} : Set V3)) (u : V3) :
    sigmaFan x V E a u = sigmaFan x V E1 a u := by
  have hS := setOfEdge_eq_of_add_edge_not_mem V E E1 v w a hE1 ha
  unfold sigmaFan
  rw [hS]

private lemma inverse1SigmaFan_eq_of_add_edge_not_mem (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (v w a : V3)
    (hE1 : E ∪ {({v, w} : Set V3)} = E1)
    (ha : a ∉ ({v, w} : Set V3)) :
    inverse1SigmaFan x V E a = inverse1SigmaFan x V E1 a := by
  have hmem : ∀ u : V3, ({a, u} : Set V3) ∈ E ↔ ({a, u} : Set V3) ∈ E1 := by
    intro u
    constructor
    · intro he; rw [← hE1]; exact Or.inl he
    · intro he
      rw [← hE1] at he
      rcases he with he | he
      · exact he
      · simp only [Set.mem_singleton_iff] at he
        exact absurd (he ▸ (by simp : a ∈ ({a, u} : Set V3))) ha
  have hsig : ∀ u : V3, sigmaFan x V E a u = sigmaFan x V E1 a u :=
    fun u => sigmaFan_eq_of_add_edge_not_mem x V E E1 v w a hE1 ha u
  unfold inverse1SigmaFan
  apply congrArg
  funext g
  simp only [hmem, hsig]

theorem TRAN_COMMUTATIVE_F1_FAN1 (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3) (y : V3 × V3)
    (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧
    ds1 = (hypermapOfFan x V E1 hfan1).face (v, w) ∧
    ds2 = (hypermapOfFan x V E1 hfan1).face (w, v) ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 ∧
    ¬ (y.2 ∈ ({v, w} : Set V3)) ∧
    y ∈ dartOfFan V E →
      f1Fan x V E y = f1Fan x V E1 y := by
  rintro ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hE1, hy2, _⟩
  simp only [f1Fan]
  rw [inverse1SigmaFan_eq_of_add_edge_not_mem x V E E1 v w y.2 hE1 hy2]

/-- HOL Conforming.hl :4253-4339 `TRAN_COMMUTATIVE_F1_FAN2`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 y.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v
/\ ds1 = face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)
/\ ds2 = face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
/\ ~(pr2 y= u)
/\ pr3 y = w
/\ y IN d_fan(x,V,E)
==>
tran x V E1 ((f1_fan x V E ) y)=(f1_fan x V E1 ) (tran x V E1 y)
```

编码说明：`~(pr2 y = u)`/`pr3 y = w` ↦ `¬ (y.1 = u)`/`y.2 = w`；
`d_fan` ↦ `dartOfFan`；`tran` 在点对编码下为恒等，故结论化为
`f1Fan x V E y = f1Fan x V E1 y`。额外携带 `hfan`、`hfan1`。

证明思路：与 FAN1 平行，只是 `y` 落在 `pr3 y = w`、`pr2 y ≠ u` 的分支。
由 `SIGMA_FAN_OF_FANADD_AT_POINT5`（ConformingAuto11.lean）处理该点的 σ
不变性，再用 `INVERSE1_SIGMA_FAN` 转为 `inverse1SigmaFan` 的等式。

候选已有引理：
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `SIGMA_FAN_OF_FANADD_AT_POINT5`（Kepler/Text/ConformingAuto11.lean）
- `INVERSE1_SIGMA_FAN`（Kepler/Text/Fan.lean:822）
- 缺口：HOL `tran`、`hypermap_of_fan_rep` 未移植 -/
theorem TRAN_COMMUTATIVE_F1_FAN2 (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3) (y : V3 × V3)
    (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧
    ds1 = (hypermapOfFan x V E1 hfan1).face (v, w) ∧
    ds2 = (hypermapOfFan x V E1 hfan1).face (w, v) ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 ∧
    ¬ (y.1 = u) ∧
    y.2 = w ∧
    y ∈ dartOfFan V E →
      f1Fan x V E y = f1Fan x V E1 y := by
  rintro ⟨hfan, hcard, hfan80, _, _, _, _, _, _, _, _, _,
    hvu, huw, hwv, hsigma, _, _, _, _, _, hE1, hy1, hy2, hydart⟩
  have hdart1 : y ∈ dart1OfFan V E := by
    rw [← dartOfFan_eq_dart1_of_surrounded hfan hcard]
    exact hydart
  have hyedge : ({y.1, y.2} : Set V3) ∈ E := hdart1
  have hwu : ({w, u} : Set V3) ∈ E := by rw [Set.pair_comm]; exact huw
  have hwa : ({w, y.1} : Set V3) ∈ E := by
    rw [Set.pair_comm, ← hy2]
    exact hyedge
  have hsigE := INVERSE1_SIGMA_FAN (x := x) (V := V) (E := E) (v := w) hfan
  have hsigE1 := INVERSE1_SIGMA_FAN (x := x) (V := V) (E := E1) (v := w) hfan1
  set p : V3 := inverse1SigmaFan x V E w y.1 with hp
  have hp_sigma : sigmaFan x V E w p = y.1 := by
    rw [hp]
    exact hsigE.2.1 y.1 hwa
  have hq_sigma : sigmaFan x V E w (inverse1SigmaFan x V E w u) = u :=
    hsigE.2.1 u hwu
  have hp_ne_q : p ≠ inverse1SigmaFan x V E w u := by
    intro hpq
    have : y.1 = u := by
      rw [← hp_sigma, hpq, hq_sigma]
    exact hy1 this
  have hp_edge : ({w, p} : Set V3) ∈ E := by
    rw [hp]
    exact hsigE.1 y.1 hwa
  have hsigma5 : sigmaFan x V E1 w p = sigmaFan x V E w p :=
    SIGMA_FAN_OF_FANADD_AT_POINT5 x V E E1 v u w p
      ⟨hfan, hfan1, hfan80, hvu, huw, hwv, hp_ne_q, hp_edge, hsigma, hcard, hE1⟩
  have hEsub : E ⊆ E1 := by rw [← hE1]; exact Set.subset_union_left
  have hp_edge_E1 : ({w, p} : Set V3) ∈ E1 := hEsub hp_edge
  have hp_sigma_E1 : sigmaFan x V E1 w p = y.1 := by
    rw [hsigma5]; exact hp_sigma
  have hfinal : inverse1SigmaFan x V E1 w y.1 = p := by
    have h := hsigE1.2.2 p hp_edge_E1
    rwa [hp_sigma_E1] at h
  simp only [f1Fan]
  rw [hy2, ← hp, hfinal]

/-- HOL Conforming.hl :4340-4426 `TRAN_COMMUTATIVE_F1_FAN3`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 y.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v
/\ ds1 = face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)
/\ ds2 = face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
/\ ~(pr2 y= sigma_fan x V E v u)
/\ pr3 y = v
/\ y IN d_fan(x,V,E)
==>
tran x V E1 ((f1_fan x V E ) y)=(f1_fan x V E1 ) (tran x V E1 y)
```

编码说明：`~(pr2 y = sigma_fan x V E v u)`/`pr3 y = v` ↦
`¬ (y.1 = sigmaFan x V E v u)`/`y.2 = v`；`tran` 在点对编码下为恒等，故
结论化为 `f1Fan x V E y = f1Fan x V E1 y`。额外携带 `hfan`、`hfan1`。

证明思路：与 FAN1/FAN2 平行，落在 `pr3 y = v`、`pr2 y ≠ sigma_fan x V E v u`
的分支。由 `SIGMA_FAN_OF_FANADD_AT_POINT4`（ConformingAuto11.lean）给出该点
的 σ 不变性，再用 `INVERSE1_SIGMA_FAN` 收口。

候选已有引理：
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `SIGMA_FAN_OF_FANADD_AT_POINT4`（Kepler/Text/ConformingAuto11.lean）
- `INVERSE1_SIGMA_FAN`（Kepler/Text/Fan.lean:822）
- 缺口：HOL `tran`、`hypermap_of_fan_rep` 未移植 -/
theorem TRAN_COMMUTATIVE_F1_FAN3 (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3) (y : V3 × V3)
    (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧
    ds1 = (hypermapOfFan x V E1 hfan1).face (v, w) ∧
    ds2 = (hypermapOfFan x V E1 hfan1).face (w, v) ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 ∧
    ¬ (y.1 = sigmaFan x V E v u) ∧
    y.2 = v ∧
    y ∈ dartOfFan V E →
      f1Fan x V E y = f1Fan x V E1 y := by
  sorry

/-- HOL Conforming.hl :4427-4605 `TRAN_COMMUTATIVE_F1_FAN`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 y.
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
/\ ~(y IN ds)
/\ y IN d_fan(x,V,E)
==>
tran x V E1 ((f1_fan x V E ) y)=(f1_fan x V E1 ) (tran x V E1 y)
```

编码说明：`pr3 f1 = u`/`pr3 f2 = w` 附加在 `sigma_fan ... = v` 行上，编码为
`f1.2 = u ∧ f2.2 = w`；`~(y IN ds)` ↦ `¬ (y ∈ ds)`；`tran` 在点对编码下
为恒等，故结论化为 `f1Fan x V E y = f1Fan x V E1 y`。额外携带 `hfan`、
`hfan1`。

证明思路：HOL 对 `pr3 y` 是否在 `{v,w}` 及 `y` 的其余位置作五种情形的
分划，分别调用 FAN1/FAN2/FAN3；`y ∉ ds` 与 `{f1,f2,f3} ⊆ ds` 把剩余情形
归约到 `y = f1` 或 `y = f2` 的置换计算。

候选已有引理：
- `TRAN_COMMUTATIVE_F1_FAN1`/`FAN2`/`FAN3`（本文件上文）
- `IMAGE_F1_IN_FACE_IMP_IN_FACE`（Kepler/Text/ConformingAuto1.lean:271）
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- 缺口：HOL `tran`、`hypermap_of_fan_rep` 未移植 -/
theorem TRAN_COMMUTATIVE_F1_FAN (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3) (y : V3 × V3)
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
    E ∪ {({v, w} : Set V3)} = E1 ∧
    ¬ (y ∈ ds) ∧
    y ∈ dartOfFan V E →
      f1Fan x V E y = f1Fan x V E1 y := by
  sorry

/-! ## `f1_fan` 幂在面内的保持与反映（Conforming.hl:4606-4670） -/

/-- HOL Conforming.hl :4606-4638 `f1_fan_power_in_face`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds y n.
FAN(x,V,E)/\
(!v. v IN V ==> CARD (set_of_edge v V E) > 1) /\
      ds IN face_set (hypermap1_of_fanx (x,V,E))/\
y IN d1_fan (x,V,E)
/\ ~(y IN ds)
==> ~((f1_fan x V E POWER n) y IN ds)
```

编码说明：`d1_fan` ↦ `dart1OfFan`；
`(f1_fan x V E POWER n) y` ↦ `(f1Fan x V E)^[n] y`。额外携带 `hfan`。

证明思路：对 `n` 归纳。`n=0` 时假设即 `y ∉ ds`；`n+1` 时用
`into_domain1_power_efn_fan` 把 `(f1Fan)^[n] y` 留在 `d1_fan`，再对
`IMAGE_F1_IN_FACE_IMP_IN_FACE` 取逆否。

候选已有引理：
- `IMAGE_F1_IN_FACE_IMP_IN_FACE`（Kepler/Text/ConformingAuto1.lean:271）
- `IMAGE_F1_POWER_IN_FACE_IMP_IN_FACE`（Kepler/Text/ConformingAuto1.lean:362）
- `dartOfFan_eq_dart1_of_surrounded`（Kepler/Text/Fan.lean:1084）
- `Function.iterate_succ_apply'`（Mathlib/Logic/Function/Iterate.lean）
- 缺口：HOL `into_domain1_power_efn_fan`（fan.hl:2694）未以该名移植 -/
theorem f1_fan_power_in_face (x : V3) (V : Set V3) (E : Set (Set V3))
    (ds : Set (V3 × V3)) (y : V3 × V3) (n : ℕ)
    (hfan : FAN x V E) :
    FAN x V E ∧
    (∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard) ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧
    y ∈ dart1OfFan V E ∧
    ¬ (y ∈ ds) →
      ¬ ((f1Fan x V E)^[n] y ∈ ds) := by
  sorry

/-- HOL Conforming.hl :4639-4670 `f1_fan_power_in_face_imp_in_face`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds y n.
FAN(x,V,E)/\
(!v. v IN V ==> CARD (set_of_edge v V E) > 1) /\
      ds IN face_set (hypermap1_of_fanx (x,V,E))/\
y IN d1_fan (x,V,E)
/\ ((f1_fan x V E POWER n) y IN ds)
==>
(y IN ds)
```

编码说明：`d1_fan` ↦ `dart1OfFan`；
`(f1_fan x V E POWER n) y` ↦ `(f1Fan x V E)^[n] y`。额外携带 `hfan`。

证明思路：对 `n` 归纳。`n=0` 时结论即假设；`n+1` 时把
`(f1Fan)^[n] y` 归入 `d1_fan`，用归纳假设把 `y` 的像拉回 `ds`，再用
`IMAGE_F1_IN_FACE_IMP_IN_FACE`。

候选已有引理：
- `IMAGE_F1_IN_FACE_IMP_IN_FACE`（Kepler/Text/ConformingAuto1.lean:271）
- `IMAGE_F1_POWER_IN_FACE_IMP_IN_FACE`（Kepler/Text/ConformingAuto1.lean:362）
- `dartOfFan_eq_dart1_of_surrounded`（Kepler/Text/Fan.lean:1084）
- 缺口：HOL `into_domain1_power_efn_fan`（fan.hl:2694）未以该名移植 -/
theorem f1_fan_power_in_face_imp_in_face (x : V3) (V : Set V3) (E : Set (Set V3))
    (ds : Set (V3 × V3)) (y : V3 × V3) (n : ℕ)
    (hfan : FAN x V E) :
    FAN x V E ∧
    (∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard) ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧
    y ∈ dart1OfFan V E ∧
    ((f1Fan x V E)^[n] y ∈ ds) →
      y ∈ ds := by
  sorry

/-! ## `TRAN_COMMUTATIVE_F1_FAN` 的合并形式与幂形式（Conforming.hl:4671-4847） -/

/-- HOL Conforming.hl :4671-4717 `TRAN_COMMUTATIVE_F1_FAN0`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 y.
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
 /\ ((~(pr2 y= sigma_fan x V E v u)/\ pr3 y = v)\/
(~(pr2 y= u)/\ pr3 y = w) \/  ~(pr3 y IN {v,w}))
/\ y IN d_fan(x,V,E)
==>
tran x V E1 ((f1_fan x V E ) y)=(f1_fan x V E1 ) (tran x V E1 y)
```

编码说明：额外条件编码为析取
`(¬ (y.1 = sigmaFan x V E v u) ∧ y.2 = v) ∨ (¬ (y.1 = u) ∧ y.2 = w) ∨
 ¬ (y.2 ∈ ({v, w} : Set V3))`；`tran` 在点对编码下为恒等，故结论化为
`f1Fan x V E y = f1Fan x V E1 y`。额外携带 `hfan`、`hfan1`。

证明思路：直接对三个析取支分别调用 FAN3、FAN2、FAN1。

候选已有引理：
- `TRAN_COMMUTATIVE_F1_FAN1`/`FAN2`/`FAN3`（本文件上文）
- 缺口：HOL `tran` 未移植 -/
theorem TRAN_COMMUTATIVE_F1_FAN0 (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3) (y : V3 × V3)
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
    E ∪ {({v, w} : Set V3)} = E1 ∧
    ((¬ (y.1 = sigmaFan x V E v u) ∧ y.2 = v) ∨
      (¬ (y.1 = u) ∧ y.2 = w) ∨
      ¬ (y.2 ∈ ({v, w} : Set V3))) ∧
    y ∈ dartOfFan V E →
      f1Fan x V E y = f1Fan x V E1 y := by
  sorry

/-- HOL Conforming.hl :4718-4768 `TRAN_COMMUTATIVE_F1_FAN_POWER`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 y n.
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
/\ ~(y IN ds)
/\ y IN d_fan(x,V,E)
==>
tran x V E1 ((f1_fan x V E POWER n) y)=(f1_fan x V E1 POWER n) (tran x V E1 y)
```

编码说明：`(f1_fan x V E POWER n) y` ↦ `(f1Fan x V E)^[n] y`；`tran` 在点对
编码下为恒等，故结论化为 `(f1Fan x V E)^[n] y = (f1Fan x V E1)^[n] y`。
额外携带 `hfan`、`hfan1`。

证明思路：对 `n` 归纳。`n=0` 时两边都是 `y`；`n+1` 时用
归纳假设把 `(f1Fan)^[n] y` 换到 `E1`，再用 `TRAN_COMMUTATIVE_F1_FAN`，
并需 `f1_fan_power_in_face` 保证 `(f1Fan)^[n] y ∉ ds`。

候选已有引理：
- `TRAN_COMMUTATIVE_F1_FAN`（本文件上文）
- `f1_fan_power_in_face`（本文件上文）
- `Function.iterate_succ_apply'`（Mathlib/Logic/Function/Iterate.lean）
- 缺口：HOL `tran`、`into_domain1_power_efn_fan`（fan.hl:2694）未移植 -/
theorem TRAN_COMMUTATIVE_F1_FAN_POWER (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3) (y : V3 × V3) (n : ℕ)
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
    E ∪ {({v, w} : Set V3)} = E1 ∧
    ¬ (y ∈ ds) ∧
    y ∈ dartOfFan V E →
      (f1Fan x V E)^[n] y = (f1Fan x V E1)^[n] y := by
  sorry

/-- HOL Conforming.hl :4769-4847 `TRAN_COMMUTATIVE_F1_FAN_POWER3`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 y n.
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
/\ y IN d_fan(x,V,E)
/\ (!m.  m < n ==> (~(pr2 ((f1_fan x V E POWER m) y) = sigma_fan x V E v u) /\
               pr3 ((f1_fan x V E POWER m) y) = v) \/
               (~(pr2 ((f1_fan x V E POWER m) y) = u) /\
               pr3 ((f1_fan x V E POWER m) y) = w) \/
               ~(pr3 ((f1_fan x V E POWER m) y) IN {v, w}))
==>
tran x V E1 ((f1_fan x V E POWER n) y)=(f1_fan x V E1 POWER n) (tran x V E1 y)
```

编码说明：额外条件编码为
`∀ m : ℕ, m < n → (¬ (((f1Fan x V E)^[m] y).1 = sigmaFan x V E v u) ∧
 ((f1Fan x V E)^[m] y).2 = v) ∨ (¬ (((f1Fan x V E)^[m] y).1 = u) ∧
 ((f1Fan x V E)^[m] y).2 = w) ∨
 ¬ (((f1Fan x V E)^[m] y).2 ∈ ({v, w} : Set V3))`；`tran` 在点对编码下为
恒等，故结论化为 `(f1Fan x V E)^[n] y = (f1Fan x V E1)^[n] y`。额外携带
`hfan`、`hfan1`。

证明思路：对 `n` 归纳。`n=0` 平凡；`n+1` 时对 `m ≤ n` 的逐点条件截断，
用归纳假设把 `(f1Fan)^[n] y` 换到 `E1`，再用 `TRAN_COMMUTATIVE_F1_FAN0`
（三个析取支恰好对应 `m = n` 的条件），最后用 `f1_fan_power_in_face`
维持 `(f1Fan)^[n] y ∉ ds`。

候选已有引理：
- `TRAN_COMMUTATIVE_F1_FAN0`（本文件上文）
- `f1_fan_power_in_face`（本文件上文）
- `Function.iterate_succ_apply'`（Mathlib/Logic/Function/Iterate.lean）
- 缺口：HOL `tran`、`into_domain1_power_efn_fan`（fan.hl:2694）未移植 -/
theorem TRAN_COMMUTATIVE_F1_FAN_POWER3 (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3) (y : V3 × V3) (n : ℕ)
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
    E ∪ {({v, w} : Set V3)} = E1 ∧
    y ∈ dartOfFan V E ∧
    (∀ m : ℕ, m < n →
      (¬ (((f1Fan x V E)^[m] y).1 = sigmaFan x V E v u) ∧
        ((f1Fan x V E)^[m] y).2 = v) ∨
      (¬ (((f1Fan x V E)^[m] y).1 = u) ∧
        ((f1Fan x V E)^[m] y).2 = w) ∨
      ¬ (((f1Fan x V E)^[m] y).2 ∈ ({v, w} : Set V3))) →
      (f1Fan x V E)^[n] y = (f1Fan x V E1)^[n] y := by
  sorry

end Kepler.Text
