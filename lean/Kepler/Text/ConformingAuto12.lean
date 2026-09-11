/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level theorems, batch 12
(Conforming.hl:3690-4155).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage (batch 12, Conforming.hl:3690-4155):
- `f1_fan_of_f30_eq_f10` (3690)
- `f10_in_d1_fanadd` (3731)
- `pair_disjoint_f10_f20_f30` (3777)
- `f1_fan_permutes_prime` (3800)
- `card_ds2_fanadd_eq3` (3832)
- `reperentation_of_ds2` (3914)
- `edge_not_in_ds2` (3992)
- `disjoint_ds1_and_ds2` (4036)
- `card_eq_image_in_d_fan` (4065)
- `exists_tranf_fan` (4106)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `FAN(x,V,E)` ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); HOL
  `set_of_edge v V E` ↔ `setOfEdge v V E` (Kepler/Text/Fan.lean:62); HOL
  `sigma_fan` ↔ `sigmaFan` (Kepler/Text/Fan.lean:67); HOL `fan80` ↔
  `fan80` (Kepler/Text/Fan.lean:227); HOL `res` (Set 版) ↔
  `Kepler.Text.Fan.res` (Kepler/Text/Fan.lean:123) — 注意 `Kepler.Text.res`
  (Finset 版, Kepler/Text/Hypermap.lean:662) 在同一命名空间内遮蔽它，故本
  文件显式限定为 `Kepler.Text.Fan.res`。
- HOL `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`
  (repo convention, cf. Kepler/Text/PlanarityDarts.lean:94); HOL
  `CARD ds > 3` ↔ `3 < ds.ncard`; HOL `CARD ds2 = 3` ↔ `ds2.ncard = 3`.
- HOL `hypermap1_of_fanx (x,V,E)` is NOT ported; as in
  Kepler/Text/PlanarityComponent.lean:37-48 and ConformingAuto8/9/11, the
  face-set hypothesis `ds IN face_set(hypermap1_of_fanx (x,V,E))` is encoded
  as `ds ∈ (hypermapOfFan x V E hfan).faceSet`, `face (hypermap1_of_fanx
  (x,V,E)) f` as `(hypermapOfFan x V E hfan).face f`, and
  `face_set (...) DELETE ds` as `(hypermapOfFan x V E hfan).faceSet \ {ds}`.
  Because `hypermapOfFan` (Kepler/Text/Fan.lean:1169) needs an explicit
  `hfan : FAN x V E`, every theorem that mentions it carries an extra
  explicit `(hfan : FAN x V E)` argument. The theorems that additionally
  mention `face (hypermap1_of_fanx (x,V,E1))` carry a second extra explicit
  argument `(hfan1 : FAN x V E1)` (HOL derives `FAN(x,V,E1)` from
  `STEP3_REDUCE_FAN`; the Lean witness must be supplied). These are the only
  deviations from the HOL signatures (HOL's `hypermap_of_fan` is total).
- HOL quadruple darts `real^3#real^3#real^3#real^3` are encoded as pair darts
  `V3 × V3` (Kepler/Text/PlanarityComponent.lean:37-48); `pr2 y`/`pr3 y` ↦
  `y.1`/`y.2`. Consequently the HOL quadruples `(x,w,v,u)`, `(x,v,u,w)`,
  `(x,u,w,v)` contract to the pairs `(w,v)`, `(v,u)`, `(u,w)`, and
  `(x,v,w,sigma_fan x V E1 v w)` to `(v,w)`; HOL `f1_fan` ↔ `f1Fan`
  (Kepler/Text/ConformingDefs.lean:87).
- HOL `d1_fan (x,V,E)` ↔ `dart1OfFan V E` (Kepler/Text/Fan.lean:86); HOL
  `d_fan (x,V,E)` ↔ `dartOfFan V E` (Kepler/Text/Fan.lean:90).
- HOL `pr23 = (\(x,y,z,t). (y,z))` (Conforming.hl:2249) is NOT ported. Under
  the pair-dart encoding the contracted dart already IS the pair `(pr2,pr3)`,
  so `pr23` collapses to the identity
  `(fun p : V3 × V3 => (p.1, p.2))`; `IMAGE pr23 ds` is encoded as
  `Set.image (fun p : V3 × V3 => (p.1, p.2)) ds` (same convention as
  `PR23_OF_D1_FAN`, ConformingAuto9.lean:398-425).
- HOL `p permutes s` (HOL Light's "is a bijection of `s`") is NOT ported as a
  named predicate; the closest existing encoding is `Set.BijOn p s s`, the
  set-level bijection used to build `hypermapOfFan` (Kepler/Text/Fan.lean:1174
  ff.). `PERMUTES_FINITE_SURJECTIVE` (used by the HOL proof) is not ported;
  Mathlib's `Set.BijOn` API and `Equiv.permOfUniquePreimage`
  (Kepler/Text/Hypermap.lean:6221) cover it.
- HOL `tran` (Conforming.hl:4097) is NOT ported. It is `(\(x,y,z,w). (x,y,z,
  sigma_fan x V E1 y z))`; on pair darts this is
  `fun y => (y.1, sigmaFan x V E1 y.1 y.2)`. In `exists_tranf_fan` it is
  inlined (no new definition is introduced). `trans` (4094) and `tranf`
  (4101) are not needed by the ten theorems and are likewise not ported.
- None of the ten statements is Mathlib-general: every one mentions the
  repo-specific `FAN`/`sigmaFan`/`f1Fan`/`hypermapOfFan`/`dartOfFan`
  vocabulary, so nothing is skipped.
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs
import Kepler.Text.ConformingAuto11

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Classical

/-! ## `f30` 的 `f1_fan` 像与 `f10` 的三种互异性（Conforming.hl:3690-3798） -/

/-- HOL Conforming.hl :3690-3729 `f1_fan_of_f30_eq_f10`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f30.
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
/\ f10=(x,w,v,u)
/\ f30=(x,u,w,v)
/\ E UNION {{v,w}}= E1
==> f10=f1_fan x V E1 f30
```

编码说明：HOL 变量表 `... ds1 ds2 f10 f30`（无 `f20`）；四元组
`(x,w,v,u)`↦`(w,v)`、`(x,u,w,v)`↦`(u,w)`；`f1_fan`↦`f1Fan`（第二参数
是 `E1`）。因 `ds1`/`ds2` 用到 `hypermap1_of_fanx (x,V,E1)`，额外携带
`(hfan : FAN x V E)`、`(hfan1 : FAN x V E1)`（见文件头编码说明）。

证明思路：由 `STEP3_REDUCE_FAN` 得 `FAN x V E1`；`hypermap_of_fan_rep`
（未移植）把两幅 hypermap 的 face 映射化为 `f1Fan`；
`SIGMA_FAN_OF_FANADD_AT_POINT3` 给出 `sigmaFan x V E1 v w`，再用
`INVERSE1_SIGMA_FAN` 对齐 `f1Fan` 的第二分量，最后展开 `f1Fan` 并用
`Prod.ext` 对齐两分量。

候选已有引理：
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `SIGMA_FAN_OF_FANADD_AT_POINT3`（Kepler/Text/ConformingAuto11.lean:554）
- `INVERSE1_SIGMA_FAN`（Kepler/Text/Fan.lean:821）
- `f1Fan`（Kepler/Text/ConformingDefs.lean:87）
- `hypermapOfFan`（Kepler/Text/Fan.lean:1169）
- `add_edge_imp_card_set_edge_ge1_fan`（Kepler/Text/ConformingAuto9.lean:376）
- 缺口：HOL `hypermap_of_fan_rep`（fan.hl:2780）、
  `dartset_fully_surrounded_is_non_isolated_fan` 未以该名移植 -/
theorem f1_fan_of_f30_eq_f10 (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f30 : V3 × V3)
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
    f10 = (w, v) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 →
      f10 = f1Fan x V E1 f30 := by
  rintro ⟨-, hcard, hfan80, -, -, -, -, -, -, -, -, -, hvu, huw, hwv, hsigma,
    -, -, hf10, hf30, hE1⟩
  have hsig3 : sigmaFan x V E1 w v = u :=
    SIGMA_FAN_OF_FANADD_AT_POINT3 x V E E1 v u w
      ⟨hfan, hfan1, hvu, huw, hwv, hsigma, hfan80, hcard, hE1⟩
  have hwv_E1 : ({w, v} : Set V3) ∈ E1 := by
    rw [← hE1]
    exact Set.mem_union_right E (by simp [Set.pair_comm])
  have hinv : inverse1SigmaFan x V E1 w u = v := by
    rw [← hsig3]
    exact (INVERSE1_SIGMA_FAN (v := w) hfan1).2.2 v hwv_E1
  rw [hf10, hf30]
  simp only [f1Fan, hinv]

/-- HOL Conforming.hl :3731-3775 `f10_in_d1_fanadd`

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
/\ sigma_fan x V E u w = v
/\ ds1 = face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)
/\ ds2 = face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)
/\ f10=(x,w,v,u)
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
==> f10 IN d1_fan (x,V,E1)
```

编码说明：`d1_fan (x,V,E1)`↦`dart1OfFan V E1`；`(x,w,v,u)`↦`(w,v)`，
`(x,v,u,w)`↦`(v,u)`，`(x,u,w,v)`↦`(u,w)`。额外携带 `hfan`、`hfan1`。

证明思路：由 `f1_fan_of_f10_eq_f20`、`f1_fan_of_f20_eq_f30`、
`f1_fan_of_f30_eq_f10` 得 `f1Fan x V E1` 的三循环
`f10 ↦ f20 ↦ f30 ↦ f10`；`SIGMA_FAN_OF_FANADD_AT_POINT3` 给
`sigmaFan x V E1 w v = u`，故 `f10 = (w,v)` 的第四分量正是
`sigmaFan x V E1 w v`，从而 `f10 ∈ dart1OfFan V E1`（定义展开）。

候选已有引理：
- `f1_fan_of_f10_eq_f20`（Kepler/Text/ConformingAuto11.lean:1153）
- `f1_fan_of_f20_eq_f30`（Kepler/Text/ConformingAuto11.lean:1227）
- `f1_fan_of_f30_eq_f10`（本文件上文）
- `SIGMA_FAN_OF_FANADD_AT_POINT3`（Kepler/Text/ConformingAuto11.lean:554）
- `dart1OfFan`（Kepler/Text/Fan.lean:86）
- 缺口：HOL `hypermap_of_fan_rep`（fan.hl:2780）、
  `dartset_fully_surrounded_is_non_isolated_fan` 未以该名移植 -/
theorem f10_in_d1_fanadd (x : V3) (V : Set V3) (E E1 : Set (Set V3))
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
    sigmaFan x V E u w = v ∧
    ds1 = (hypermapOfFan x V E1 hfan1).face (v, w) ∧
    ds2 = (hypermapOfFan x V E1 hfan1).face (w, v) ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 →
      f10 ∈ dart1OfFan V E1 := by
  intro h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hf10, _, _, hE1⟩ := h
  rw [hf10]
  change ({w, v} : Set V3) ∈ E1
  rw [← hE1]
  exact Set.mem_union_right E (by simp [Set.pair_comm])

/-- HOL Conforming.hl :3777-3798 `pair_disjoint_f10_f20_f30`

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
/\ sigma_fan x V E u w = v
/\ ds1 = face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)
/\ ds2 = face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)
/\ f10=(x,w,v,u)
/\ f20=(x,v,u,w)
/\ f30=(x,u,w,v)
/\ E UNION {{v,w}}= E1
==> ~(f10= f20)/\ ~(f20= f30)/\ ~(f30=f10)
```

编码说明：结论的三个不等式对应三对收缩 dart 的互异；`remark1_fan`
（未移植）在 HOL 中给出 `{v,u},{u,w} ∈ E` 蕴含 `u≠v`、`w≠u`。额外携带
`hfan`、`hfan1`。

证明思路：把 `f10,f20,f30` 分别改写为 `(w,v),(v,u),(u,w)`，逐对用
`Prod.ext` 展开成点等式；`remark1_fan` 提供 `u≠v`、`w≠u`（以及
`v≠w`）排除各分量相等，从而三个不等式成立。

候选已有引理：
- `edge_ne_of_fan`（Kepler/Text/Fan.lean:1039）
- `dartOfFan_eq_dart1_of_surrounded`（Kepler/Text/Fan.lean:1084）
- `Prod.ext`/`Prod.ext_iff`（Mathlib）
- 缺口：HOL `remark1_fan`（fan.hl:423）未以该名移植 -/
theorem pair_disjoint_f10_f20_f30 (x : V3) (V : Set V3) (E E1 : Set (Set V3))
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
    sigmaFan x V E u w = v ∧
    ds1 = (hypermapOfFan x V E1 hfan1).face (v, w) ∧
    ds2 = (hypermapOfFan x V E1 hfan1).face (w, v) ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 →
      ¬ (f10 = f20) ∧ ¬ (f20 = f30) ∧ ¬ (f30 = f10) := by
  rintro ⟨hfan, -, -, -, -, -, -, -, -, -, -, -, hvu, huw, -, -, -, -,
    hf10, hf20, hf30, -⟩
  have hne_vu : v ≠ u := edge_ne_of_fan hfan hvu
  have hne_uw : u ≠ w := edge_ne_of_fan hfan huw
  rw [hf10, hf20, hf30]
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact hne_vu (Prod.ext_iff.mp h).2
  · intro h
    exact hne_vu (Prod.ext_iff.mp h).1
  · intro h
    exact hne_uw (Prod.ext_iff.mp h).1

/-! ## `f1_fan` 在 `d_fan` 上的置换性与 `ds2` 的三元表示
    （Conforming.hl:3800-3990） -/

/-- HOL Conforming.hl :3800-3830 `f1_fan_permutes_prime`

HOL 原文：
```
!x:real^3 V:real^3->bool (E:(real^3->bool)->bool) p.
FAN(x,V,E) /\ p = ( \ t. res (t x V E ) (d1_fan (x,V,E)))
==> (p f1_fan) permutes (d_fan (x,V,E))
```

编码说明：`p` 是 HOL 的高阶函数，取 `t : real^3 -> (real^3->bool) ->
((real^3->bool)->bool) -> dart -> dart` 并返回
`res (t x V E) (d1_fan (x,V,E))`；Lean 中
`p : (V3 → Set V3 → Set (Set V3) → V3 × V3 → V3 × V3) → (V3 × V3 → V3 × V3)`，
`f1_fan`↦`f1Fan`，`d1_fan`↦`dart1OfFan`，`d_fan`↦`dartOfFan`，`res` 取
Set 版 `Kepler.Text.Fan.res`（Finset 版 `Kepler.Text.res` 遮蔽之）。
HOL `permutes` 未以该名移植，最接近的编码是集合层双射 `Set.BijOn`
（与 `hypermapOfFan` 的构造一致，Kepler/Text/Fan.lean:1174）。本定理不
使用 `hypermapOfFan`，故无需额外 `hfan` 参数。

证明思路：由 `finite_d_fan`（`finite_dart_fan`）与
`PERMUTES_FINITE_SURJECTIVE`（未移植；`Set.BijOn` 三分量）把结论化为
"映到 `d_fan` 内 + 单射 + 满射"；`into_domain_f1_fan`（未移植）给
映射入 `d_fan`；`permuters_of_enf_fan`（未移植）给 `f1_fan` 在
`d1_fan` 上的单射与满射，配合 `subset_d_fan`（`d1_fan ⊆ d_fan`）收口。

候选已有引理：
- `Kepler.Text.Fan.res`（Kepler/Text/Fan.lean:123，HOL `res`）
- `dart1OfFan`（Kepler/Text/Fan.lean:86）、`dartOfFan`（同:90）
- `f1Fan`（Kepler/Text/ConformingDefs.lean:87）
- `finite_dart_fan`（Kepler/Text/Fan.lean:872）
- `Equiv.permOfUniquePreimage`（Kepler/Text/Hypermap.lean:6221）
- 缺口：HOL `into_domain_f1_fan`（fan.hl:2469）、
  `permuters_of_enf_fan`（fan.hl:2174）、`subset_d_fan`、
  `PERMUTES_FINITE_SURJECTIVE` 未以该名移植；`permutes` 用 `Set.BijOn`
  代替 -/
theorem f1_fan_permutes_prime (x : V3) (V : Set V3) (E : Set (Set V3))
    (p : (V3 → Set V3 → Set (Set V3) → V3 × V3 → V3 × V3) →
      (V3 × V3 → V3 × V3)) :
    FAN x V E ∧
      p = (fun t => Kepler.Text.Fan.res (t x V E) (dart1OfFan V E)) →
      Set.BijOn (p f1Fan) (dartOfFan V E) (dartOfFan V E) := by
  sorry

/-- HOL Conforming.hl :3832-3912 `card_ds2_fanadd_eq3`

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
/\ sigma_fan x V E u w = v
/\ ds1 = face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)
/\ ds2 = face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
==> CARD ds2=3
```

编码说明：结论 `CARD ds2=3`↦`ds2.ncard = 3`。额外携带 `hfan`、`hfan1`。

证明思路：由 `SIGMA_FAN_OF_FANADD_AT_POINT3` 得 `f1Fan x V E1` 在
`ds2` 上把 `f10` 循环到 `f20`、`f30` 再回到 `f10`
（`in_orbit_lemma` 的各幂次特例）；`f10_in_d1_fanadd` 给
`f10 ∈ dart1OfFan V E1`；`f1_fan_permutes_prime` 与 `card_orbit_le`
给出轨道大小上界 3，`pair_disjoint_f10_f20_f30` 给
`{f10,f20,f30}` 基数 3，再用 `CARD_SUBSET_LE`（`Set.ncard_le_ncard`）
夹出 `ds2.ncard = 3`。

候选已有引理：
- `SIGMA_FAN_OF_FANADD_AT_POINT3`（Kepler/Text/ConformingAuto11.lean:554）
- `f10_in_d1_fanadd`（本文件上文）
- `pair_disjoint_f10_f20_f30`（本文件上文）
- `f1_fan_permutes_prime`（本文件上文）
- `card_orbit_le`（Kepler/Text/Hypermap.lean:1115）
- `Set.ncard_le_ncard`（Mathlib/Data/Set/Card.lean:657）
- 缺口：HOL `into_domain_power_efn_fan`（fan.hl:2694）、
  `in_orbit_lemma`（hypermap.hl:274/279）、`CARD_SUBSET_LE` 未以该名
  移植 -/
theorem card_ds2_fanadd_eq3 (x : V3) (V : Set V3) (E E1 : Set (Set V3))
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
    sigmaFan x V E u w = v ∧
    ds1 = (hypermapOfFan x V E1 hfan1).face (v, w) ∧
    ds2 = (hypermapOfFan x V E1 hfan1).face (w, v) ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 →
      ds2.ncard = 3 := by
  sorry

/-- HOL Conforming.hl :3914-3990 `reperentation_of_ds2`

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
/\ sigma_fan x V E u w = v
/\ ds1 = face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)
/\ ds2 = face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
==> ds2={f10,f20,f30}
```

编码说明：结论 `ds2={f10,f20,f30}`↦
`ds2 = ({f10, f20, f30} : Set (V3 × V3))`。额外携带 `hfan`、`hfan1`。
（HOL 定理名拼写 `reperentation` 为原文笔误，按"名字 = HOL 名"保留。）

证明思路：与 `card_ds2_fanadd_eq3` 同：`SIGMA_FAN_OF_FANADD_AT_POINT3`
与 `in_orbit_lemma` 给 `{f10,f20,f30} ⊆ ds2`；`f1_fan_permutes_prime`
与 `card_orbit_le` 给 `ds2.ncard ≤ 3`；`pair_disjoint_f10_f20_f30` 给
`{f10,f20,f30}` 基数 3，故两边都是基数 3 且一边含于另一边，用
`Set.eq_of_subset_of_ncard_le` 收口。

候选已有引理：
- `SIGMA_FAN_OF_FANADD_AT_POINT3`（Kepler/Text/ConformingAuto11.lean:554）
- `f10_in_d1_fanadd`（本文件上文）
- `pair_disjoint_f10_f20_f30`（本文件上文）
- `f1_fan_permutes_prime`（本文件上文）
- `card_orbit_le`（Kepler/Text/Hypermap.lean:1115）
- `Set.eq_of_subset_of_ncard_le`、`Set.ncard_le_ncard`
  （Mathlib/Data/Set/Card.lean:862 / :657）
- 缺口：HOL `into_domain_power_efn_fan`（fan.hl:2694）、
  `in_orbit_lemma`（hypermap.hl:274/279）、`CARD_SUBSET_LE` 未以该名
  移植 -/
theorem reperentation_of_ds2 (x : V3) (V : Set V3) (E E1 : Set (Set V3))
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
    sigmaFan x V E u w = v ∧
    ds1 = (hypermapOfFan x V E1 hfan1).face (v, w) ∧
    ds2 = (hypermapOfFan x V E1 hfan1).face (w, v) ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 →
      ds2 = ({f10, f20, f30} : Set (V3 × V3)) := by
  sorry

/-! ## `ds1` 与 `ds2` 不相交、`pr23` 的基数与 `tran` 的存在性
    （Conforming.hl:3992-4155） -/

/-- HOL Conforming.hl :3992-4034 `edge_not_in_ds2`

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
/\ sigma_fan x V E u w = v
/\ ds1 = face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)
/\ ds2 = face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)
/\ f10=(x,w,v,u)
/\ f20=(x,v,u,w)
/\ f30=(x,u,w,v)
/\ E UNION {{v,w}}=E1
==> ~((x,v,w,sigma_fan x V E1 v w) IN ds2)
```

编码说明：`(x,v,w,sigma_fan x V E1 v w)`↦`(v,w)`（即 `ds1` 的生成 dart）。
额外携带 `hfan`、`hfan1`。

证明思路：由 `reperentation_of_ds2` 把 `ds2` 写成 `{f10,f20,f30}`，再
逐项用 `Prod.ext` 排除 `(v,w)=(w,v)`、`(v,w)=(v,u)`、`(v,w)=(u,w)`；
`remark1_fan`（未移植）提供 `v≠w`、`v≠u`、`w≠u`，并用
`SIGMA_FAN` 排除 `sigma_fan x V E1 v w = w` 等退化情形。

候选已有引理：
- `reperentation_of_ds2`（本文件上文）
- `SIGMA_FAN`（Kepler/Text/Fan.lean:317）
- `edge_ne_of_fan`（Kepler/Text/Fan.lean:1039）
- `Set.mem_insert_iff`、`Prod.ext`（Mathlib）
- 缺口：HOL `remark1_fan`（fan.hl:423）未以该名移植 -/
theorem edge_not_in_ds2 (x : V3) (V : Set V3) (E E1 : Set (Set V3))
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
    sigmaFan x V E u w = v ∧
    ds1 = (hypermapOfFan x V E1 hfan1).face (v, w) ∧
    ds2 = (hypermapOfFan x V E1 hfan1).face (w, v) ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 →
      (v, w) ∉ ds2 := by
  sorry

/-- HOL Conforming.hl :4036-4063 `disjoint_ds1_and_ds2`

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
/\ sigma_fan x V E u w = v
/\ ds1 = face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)
/\ ds2 = face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
==> ~(ds1=ds2)
```

编码说明：`ds1 = face (...) (v,w)`，故 `ds1` 含 `(v,w)`（`orbitMap` 的
0 次幂即自身）；`edge_not_in_ds2` 给 `(v,w) ∉ ds2`，故 `ds1 ≠ ds2`。
额外携带 `hfan`、`hfan1`。

证明思路：`MONO_NOT` + 假设 `ds1 = ds2`，把 `ds1` 展开为
`orbitMap faceMap (v,w)` 并取 `0` 次幂（`POWER;I_DEF`）得
`(v,w) ∈ ds2`，与 `edge_not_in_ds2` 矛盾。

候选已有引理：
- `edge_not_in_ds2`（本文件上文）
- `Hypermap.face`（Kepler/Text/Hypermap.lean:846）
- `pow_apply_mem_orbitMap`（Kepler/Text/Hypermap.lean:717）
- `Set.eq_of_subset_of_ncard_le`（Mathlib/Data/Set/Card.lean:862）
- 缺口：HOL `face`/`orbit_map` 的直接展开在移植中以 `Hypermap.face`
  的 `orbitMap` 定义呈现 -/
theorem disjoint_ds1_and_ds2 (x : V3) (V : Set V3) (E E1 : Set (Set V3))
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
    sigmaFan x V E u w = v ∧
    ds1 = (hypermapOfFan x V E1 hfan1).face (v, w) ∧
    ds2 = (hypermapOfFan x V E1 hfan1).face (w, v) ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 →
      ds1 ≠ ds2 := by
  sorry

/-- HOL Conforming.hl :4065-4092 `card_eq_image_in_d_fan`

HOL 原文：
```
!x V E ds.
FAN(x,V,E) /\
(!v. v IN V==>CARD (set_of_edge v V E) >1)/\
ds SUBSET d_fan(x,V,E)
==>
CARD(IMAGE pr23 ds)= CARD ds
```

编码说明：`pr23` 未移植，在点对编码下退化为恒等
`(fun p : V3 × V3 => (p.1, p.2))`（见文件头）；`d_fan`↦`dartOfFan`；
`CARD`↦`Set.ncard`。本定理不使用 `hypermapOfFan`，故无需额外 `hfan`。

证明思路：HOL 用 `CARD_IMAGE_INJ`：只需证 `pr23` 在 `ds` 上单射。
`finite_d_fan`（`finite_dart_fan`）给 `d_fan` 有限，`FINITE_SUBSET`
给 `ds` 有限；对 `x',y ∈ ds ⊆ d_fan`，`dartset_fully_surrounded_...`
把 `d_fan` 化为 `d1_fan`，由 `pr23 x' = pr23 y`（即点对相等）
直接得 `x' = y`。移植中 `pr23` 是恒等，结论等价于
`(Set.image (fun p => (p.1,p.2)) ds).ncard = ds.ncard`，可用
`Set.ncard_image_of_injective` 或 `Set.image_id` 收口。

候选已有引理：
- `finite_dart_fan`（Kepler/Text/Fan.lean:872，HOL `finite_d_fan`）
- `dartOfFan_eq_dart1_of_surrounded`（Kepler/Text/Fan.lean:1084）
- `Set.ncard_image_of_injective`（Mathlib/Data/Set/Card.lean:830）
- `Set.image_id`（Mathlib）
- 缺口：HOL `pr23`、`d1_fan`、`d_fan` 未以该名移植（见文件头）；
  `CARD_IMAGE_INJ`、`FINITE_SUBSET` 由 Mathlib `Set.ncard_image_*` 覆盖 -/
theorem card_eq_image_in_d_fan (x : V3) (V : Set V3) (E : Set (Set V3))
    (ds : Set (V3 × V3)) :
    FAN x V E ∧
    (∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard) ∧
    ds ⊆ dartOfFan V E →
      (Set.image (fun p : V3 × V3 => (p.1, p.2)) ds).ncard = ds.ncard := by
  sorry

/-- HOL Conforming.hl :4106-4155 `exists_tranf_fan`

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
==> ?f. ?y. f = face (hypermap1_of_fanx (x,V,E1)) (tran x V E1 y)/\ y IN ds0
```

编码说明：`face_set (...) DELETE ds`↦
`(hypermapOfFan x V E hfan).faceSet \ {ds}`；`tran` 未移植
（Conforming.hl:4097），在点对编码下为
`fun y => (y.1, sigmaFan x V E1 y.1 y.2)`，此处内联（不引入新定义）。
额外携带 `hfan`、`hfan1`。

证明思路：由 `STEP3_REDUCE_FAN` 得 `FAN x V E1`；把
`ds0 ∈ faceSet \ {ds}` 拆出 `ds0 ∈ faceSet`，展开 `faceSet`/`setOfOrbits`
得某个 `x' ∈ ds0`；取 `f = face (hypermap1_of_fanx (x,V,E1)) (tran x V E1 x')`、
`y = x'`，`tran` 展开后 `y` 自身（`orbitMap` 0 次幂）即满足。

候选已有引理：
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `Hypermap.faceSet`（Kepler/Text/Hypermap.lean:1008）、
  `Hypermap.face`（同:846）、`pow_apply_mem_orbitMap`（同:717）
- `SIGMA_FAN_OF_FANADD_AT_POINT3`（Kepler/Text/ConformingAuto11.lean:554）
- `add_edge_imp_card_set_edge_ge1_fan`（Kepler/Text/ConformingAuto9.lean:376）
- 缺口：HOL `tran`/`trans`/`tranf`（Conforming.hl:4094-4101）、
  `hypermap_of_fan_rep`（fan.hl:2780）、
  `dartset_fully_surrounded_is_non_isolated_fan` 未移植 -/
theorem exists_tranf_fan (x : V3) (V : Set V3) (E E1 : Set (Set V3))
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
      ∃ f, ∃ y, f = (hypermapOfFan x V E1 hfan1).face
          (y.1, sigmaFan x V E1 y.1 y.2) ∧ y ∈ ds0 := by
  sorry

end Kepler.Text
