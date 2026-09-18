/-
Kepler.Text.LocalAuto8 — Local Fan chapter: the `stable_sy` covering kit.

HOL source (persistent copy under `lean/scripts/local/`): `MTUWLUN.hl`
(4562 ln, module `Mtuwlun`, 14 defs + 24 theorems): the diagonal-slice
("cover") machinery for stable systems — `IS_SY`/`kl_sy`/`fl_sy`, the
`COVER1_SY`..`COVER6_SY`/`COVER_SY` bundle, the two row-slicing matrices
`pmat1`/`pmat2`, the diagonal predicate `DIA_SY`, the re-indexing
`SCHANGE`, and the 24 covering theorems from `CARD_I_SY_LT_3` through
`IN_B_SY2_COVER`.

Encoding notes.
- HOL `stable_sy` (HDPLYGY.hl:204, `new_type_definition` over the 7-tuple
  `(k,d,I,a,b,J,f)` constrained by `stable_system`) is ported as the
  structure `StableSy`; the HDPLYGY accessors `k_sy`/`d_sy`/`I_SY`/`a_sy`/
  `b_sy`/`J_SY`/`f_sy` collapse to fields (`s.k`/`s.d`/`s.I`/`s.a`/`s.b`/
  `s.J`/`s.f`), and `stable_sy_lemma` is the `stable` field (a hypothesis,
  not a theorem to prove).  `stable_system`/`constraint_system`/`torsor`
  (dih2k.hl:48-70) get `_p8` copies over `Set`/`Nat.card` (HOL `num->bool`
  ↦ `Set ℕ`, `CARD` ↦ `Nat.card`, `s HAS_SIZE k` ↦ `Nat.card s = k`).
- Dimensions: HOL `dimindex(:M) = k`, `dimindex(:P) = p`,
  `dimindex(:N) = k-p+2` are absorbed into the type parameters
  `l : FinVec k 3`, `l1 : FinVec p 3`, `l2 : FinVec (k-p+2) 3`
  (LocalAuto4's `FinVec`/`matvec_p4`/`vecmats_p4` kit); the `DIMINDEX_GE_1`
  hypotheses become explicit `1 ≤ k` / `1 ≤ p` / `1 ≤ k - p`.
- Rows: HOL `row i (vecmats l)` is 1-based; `rowSy l j` takes the 0-based
  row `j+1` (junk `0` row out of range, as in HOL's total indexing).  So
  `row k (vecmats l)` ↦ `rowSy l (k-1)`, `row (p-1) (vecmats l)` ↦
  `rowSy l (p-2)`, `row (SUC (i MOD k))` ↦ `rowSy l (i % k)`.
- `pmat1`/`pmat2` carry the output dimension `q` explicitly (HOL reads it
  off the result type `real^3^P`/`real^3^N`); the 1-based `i < dimindex(:P)`
  branch becomes `(i:ℕ)+1 < q`, and `A$dimindex(:M)$j` (last row) becomes
  `A ⟨m-1⟩ j`.
- HOL `ITER` ↦ `f^[i]`; `POWER` ↦ `Function.iterate`; `sum S g` over a set
  ↦ `Kepler.Text.setSum` (junk 0 on infinite sets); `order` ↦ `order_p8`
  (HOL choice via `Classical.epsilon`, cf. `order_p2`).
- External Flyspeck defs used by MTUWLUN but owned elsewhere get `_p8`
  copies with NEEDS markers: `stableSystem_p8`/`torsor_p8`/
  `constraintSystem_p8` (dih2k.hl), `aEar0_p8`/`bEar0_p8`/`earSy_p8`/
  `sigmaSy_p8`/`J1_SY_p8`/`dFun_p8`/`tauStar_p8` (HDPLYGY.hl),
  `order_p8`/`slicev_p8`/`slicee_p8`/`slicef_p8`/`wedgeInFanGt_p8`/
  `EJRCFJD_p8` (localization.hl/NKEZBFC.hl), `rowSy`/`B_SY1_p8` (dih2k.hl),
  `DETER_RHO_NODE_p8` (Local_lemmas.hl, sorry: giant).
  LocalAuto4's `V_SY_p4`/`E_SY_p4`/`F_SY_p4`/`convexLocalFan_p4` and
  LocalAuto1's `rhoNode1`/`tauFun`/`solLocal`/`cstab`/`ee` are imported
  (unsuffixed homes pending; merge note as usual).
- `d_sy` is a dummy argument of `constraint_system` (unused, verbatim);
  `#0.11` ↦ `(11:ℝ)/100`, `#0.1` ↦ `(1:ℝ)/10`; `J1_SY` pairs are 1-based, so
  `dFun_p8` indexes rows `x.1 - 1` / `x.2 - 1`.
- The 12 mechanical theorems are PROVED; the 12 remaining statements are
  the faithful skeleton with `sorry` bodies (giants): `D_FUN_COVER_SY`,
  `ORDER_COVER1_SY`, `ORDER_COVER2_SY`, the `SLICE*_EQ_*` quartet and the
  `_2` pair, `TAU_STAR_COVER`, `IN_B_SY_COVER`, `IN_B_SY2_COVER`.

DISCHARGES: nothing yet (statements are the MTUWLUN contract registry).
-/

import Kepler.Text.Polytope
import Kepler.Text.Fan
import Kepler.Text.PackingAuto2
import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto4
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-! ## `_p8` substrate: torsor / constraint / stable systems (dih2k.hl:48-70) -/

/-- HOL `torsor` (dih2k.hl:48); `s HAS_SIZE k` ↦ `Nat.card s = k`. -/
def torsor_p8 {α : Type*} (s : Set α) (k : ℕ) (f : α → α) : Prop :=
  (∀ x ∈ s, f x ∈ s) ∧ (∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂) ∧
    (∀ i x, 0 < i → i < k → x ∈ s → f^[i] x ≠ x) ∧
    (∀ x ∈ s, f^[k] x = x) ∧ Nat.card s = k

/-- HOL `constraint_system` (dih2k.hl:52); `d` is the (unused) HOL dummy. -/
def constraintSystem_p8 (k d : ℕ) (s : Set ℕ) (a b : ℕ → ℕ → ℝ)
    (J : Set (Set ℕ)) (f : ℕ → ℕ) : Prop :=
  3 ≤ k ∧ k ≤ 6 ∧ torsor_p8 s k f ∧
    (∀ i j, a i j = a j i ∧ b i j = b j i ∧ a i j ≤ b i j) ∧
    (∀ i j, a i j = a i (f^[k] j) ∧ b i j = b i (f^[k] j)) ∧
    J ⊆ {e | ∃ i ∈ s, e = {i, f i}} ∧ Nat.card J + k ≤ 6

/-- HOL `stable_system` (dih2k.hl:61). -/
def stableSystem_p8 (k d : ℕ) (s : Set ℕ) (a b : ℕ → ℕ → ℝ)
    (J : Set (Set ℕ)) (f : ℕ → ℕ) : Prop :=
  constraintSystem_p8 k d s a b J f ∧
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → 2 ≤ a i j) ∧
    (∀ i ∈ s, a i i = 0 ∧ b i (f i) ≤ cstab) ∧
    (∀ i j, {i, j} ∈ J → a i j = Real.sqrt 8 ∧ b i j = cstab)

/-- HOL `stable_sy` (HDPLYGY.hl:204): the subtype of 7-tuples satisfying
`stable_system`; projections are the fields (`stable_sy_lemma` = `stable`). -/
structure StableSy where
  k : ℕ
  d : ℕ
  I : Set ℕ
  a : ℕ → ℕ → ℝ
  b : ℕ → ℕ → ℝ
  J : Set (Set ℕ)
  f : ℕ → ℕ
  stable : stableSystem_p8 k d I a b J f

/-! ## `_p8` substrate: the ear kit (HDPLYGY.hl:35-238) -/

/-- HOL `a_ear0` (HDPLYGY.hl:35 = localization.hl:135). -/
noncomputable def aEar0_p8 (J : Set (Set ℕ)) (i j : ℕ) : ℝ :=
  if i % 3 = j % 3 then 0 else if ({i % 3, j % 3} : Set ℕ) ∈ J then Real.sqrt 8 else 2

/-- HOL `b_ear0` (HDPLYGY.hl:39 = localization.hl:138). -/
noncomputable def bEar0_p8 (J : Set (Set ℕ)) (i j : ℕ) : ℝ :=
  if i % 3 = j % 3 then 0 else if ({i % 3, j % 3} : Set ℕ) ∈ J then cstab else 2 * h0

/-- HOL `ear_sy` (HDPLYGY.hl:228); `CARD` ↦ `Nat.card`. -/
def earSy_p8 (s : StableSy) : Prop :=
  Nat.card s.I = 3 ∧ s.d = (11 : ℝ) / 100 ∧ Nat.card s.J = 1 ∧
    s.a = aEar0_p8 s.J ∧ s.b = bEar0_p8 s.J

/-- HOL `sigma_sy` (HDPLYGY.hl:232). -/
noncomputable def sigmaSy_p8 (s : StableSy) : ℝ :=
  if earSy_p8 s then 1 else -1

/-- HOL `row i (vecmats l)` (1-based) ↦ `rowSy l (i-1)`: the 0-based row of
the flattened `l`, junk `0` when out of range (HOL's `$` is total). -/
def rowSy {m : ℕ} (l : FinVec m 3) (i : ℕ) : V3 :=
  if h : i < m then vecmatsV3_p4 l ⟨i, h⟩ else 0

/-- HOL `J1_SY` (HDPLYGY.hl:234); `x = i, SUC (i MOD k)` ↦ the pair
`(i, i % k + 1)`, `i IN 1..k` ↦ `i ∈ Set.Icc 1 s.k`. -/
def J1_SY_p8 (s : StableSy) : Set (ℕ × ℕ) :=
  {x | ∃ i : ℕ, {i % s.k, s.f (i % s.k)} ∈ s.J ∧ i ∈ Icc 1 s.k ∧
    x = (i, i % s.k + 1)}

/-- HOL `d_fun` (HDPLYGY.hl:236); the HOL rows `FST x`/`SND x` are 1-based,
so the `rowSy` indices are `x.1 - 1` / `x.2 - 1`. -/
noncomputable def dFun_p8 (s : StableSy) {m : ℕ} (l : FinVec m 3) : ℝ :=
  s.d + (1 : ℝ) / 10 * sigmaSy_p8 s *
    setSum (J1_SY_p8 s)
      (fun x => cstab - ‖rowSy l (x.1 - 1) - rowSy l (x.2 - 1)‖)

/-- HOL `tau_star` (HDPLYGY.hl:238). -/
noncomputable def tauStar_p8 (s : StableSy) {m : ℕ} (l : FinVec m 3) : ℝ :=
  tauFun (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
    (F_SY_p4 (vecmatsV3_p4 l)) - dFun_p8 s l

/-! ## `_p8` substrate: slice kit and EJRCFJD (localization.hl, NKEZBFC.hl) -/

/-- HOL `order f x y` (localization.hl:24): least `n` with `f^[n] x = y`
(HOL choice; junk value when no such `n`). NEEDS: merge with `order_p2`. -/
noncomputable def order_p8 {α : Type*} (f : α → α) (x y : α) : ℕ :=
  Classical.epsilon fun n => f^[n] x = y ∧ ∀ i, 0 < i → i < n → ¬(f^[i] x = y)

/-- HOL `slicev` (localization.hl:149). NEEDS: merge with `slicev_p2`. -/
noncomputable def slicev_p8 (E : Set (Set V3)) (FF : Set (V3 × V3)) (v w : V3) :
    Set V3 :=
  {u | ∃ n : ℕ, n ≤ order_p8 (rhoNode1 FF) v w ∧ u = (rhoNode1 FF)^[n] v}

/-- HOL `slicee` (localization.hl:151). NEEDS: merge with `slicee_p2`. -/
def slicee_p8 (E : Set (Set V3)) (FF : Set (V3 × V3)) (v w : V3) :
    Set (Set V3) :=
  {e | ∃ u, u ∈ slicev_p8 E FF v w ∧ u ≠ w ∧ e = {u, rhoNode1 FF u}} ∪ {{w, v}}

/-- HOL `slicef` (localization.hl:153). NEEDS: merge with `slicef_p2`. -/
def slicef_p8 (E : Set (Set V3)) (FF : Set (V3 × V3)) (v w : V3) :
    Set (V3 × V3) :=
  {f | ∃ u, u ∈ slicev_p8 E FF v w ∧ u ≠ w ∧ f = (u, rhoNode1 FF u)} ∪ {(w, v)}

/-- HOL `wedge_in_fan_gt` (localization.hl:79). NEEDS: merge with
`wedgeInFanGt_p2`. -/
noncomputable def wedgeInFanGt_p8 (d : V3 × V3) (E : Set (Set V3)) : Set V3 :=
  if 1 < (ee d.1 E).ncard then wedge 0 d.1 d.2 (sigmaFan 0 Set.univ E d.1 d.2)
  else if ee d.1 E = {d.2} then
    {x | x ∉ affGe ({0, d.1} : Set V3) {d.2}}
  else
    {x | x ∉ affineSpan ℝ ({0, d.1} : Set V3)}

/-- HOL `EJRCFJD` conclusion (NKEZBFC.hl:1685): the slicing lemma used as a
hypothesis by `TAU_STAR_COVER`/`IN_B_SY_COVER`/`IN_B_SY2_COVER` (HOL
`mk_imp (EJRCFJD_concl, …)`). NEEDS: merge with `EJRCFJD_ALT` home. -/
def EJRCFJD_p8 : Prop :=
  ∀ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)) (v w : V3),
    convexLocalFan_p4 V E FF → v ∈ V → w ∈ V →
    (∀ u u1 : V3, u ∈ ({v, w} : Set V3) → u1 ∈ V → u ≠ u1 →
      ¬Collinear ℝ ({0, u, u1} : Set V3)) →
    (∀ e ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p8 e E) →
    convexLocalFan_p4 (slicev_p8 E FF v w) (slicee_p8 E FF v w)
      (slicef_p8 E FF v w) ∧
    convexLocalFan_p4 (slicev_p8 E FF w v) (slicee_p8 E FF w v)
      (slicef_p8 E FF w v) ∧
    tauFun V E FF ≥ tauFun (slicev_p8 E FF v w) (slicee_p8 E FF v w)
        (slicef_p8 E FF v w) +
      tauFun (slicev_p8 E FF w v) (slicee_p8 E FF w v) (slicef_p8 E FF w v) ∧
    solLocal E FF = solLocal (slicee_p8 E FF v w) (slicef_p8 E FF v w) +
      solLocal (slicee_p8 E FF w v) (slicef_p8 E FF w v) ∧
    (slicev_p8 E FF v w).ncard < V.ncard ∧ (slicev_p8 E FF w v).ncard < V.ncard

/-- HOL `DETER_RHO_NODE` (Local_lemmas.hl:3093). NEEDS: giant, sorry. -/
theorem DETER_RHO_NODE_p8 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {v w : V3} (_hfan : localFan_p4 V E FF) (_hd : (v, w) ∈ FF) :
    rhoNode1 FF v = w := sorry

/-- HOL `B_SY1` (dih2k.hl:122) with the conditions of `CONDITION1_SY`/
`CONDITION2_SY` inlined (0-based rows via `rowSy`), membership form.
NEEDS: merge with `B_SY1_p4` (image form) at a shared home. -/
def B_SY1_p8 {m : ℕ} (a b : ℕ → ℕ → ℝ) : Set (FinVec m 3) :=
  {l | (∀ i : ℕ, i < m → rowSy l i ∈ ballAnnulus) ∧
    (∀ i j : ℕ, i < m → j < m →
      a i j ≤ ‖rowSy l i - rowSy l j‖ ∧ ‖rowSy l i - rowSy l j‖ ≤ b i j) ∧
    convexLocalFan_p4 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
      (F_SY_p4 (vecmatsV3_p4 l))}

/-! ## The 14 MTUWLUN definitions (MTUWLUN.hl:45-178) -/

/-- HOL `IS_SY` (MTUWLUN.hl:45). -/
def IS_SY (s : StableSy) (p q : ℕ) : Set ℕ :=
  {x | ∃ n m : ℕ, n < m ∧ m < s.k ∧ s.f^[n] x = q ∧ s.f^[m] x = p}

/-- HOL `kl_sy` (MTUWLUN.hl:47). -/
noncomputable def kl_sy (s : StableSy) (p q : ℕ) : ℕ := Nat.card (IS_SY s p q)

/-- HOL `fl_sy` (MTUWLUN.hl:49). -/
def fl_sy (s : StableSy) (p q : ℕ) : ℕ → ℕ :=
  fun i => if i ≠ q then s.f i else p

/-- HOL `COVER1_SY` (MTUWLUN.hl:53). -/
def COVER1_SY (p q : ℕ) (s s1 s2 : StableSy) : Prop :=
  s1.I = IS_SY s p q ∧ s2.I = IS_SY s q p ∧
    s1.f = fl_sy s p q ∧ s2.f = fl_sy s q p

/-- HOL `COVER2_SY` (MTUWLUN.hl:56). -/
def COVER2_SY (s s1 s2 : StableSy) : Prop := s.d ≤ s1.d + s2.d

/-- HOL `COVER3_SY` (MTUWLUN.hl:59). -/
def COVER3_SY (p q : ℕ) (s s1 s2 : StableSy) : Prop :=
  s1.J ⊆ s.J ∪ {{p, q}} ∧ s2.J ⊆ s.J ∪ {{p, q}}

/-- HOL `COVER4_SY` (MTUWLUN.hl:62). -/
def COVER4_SY (p q : ℕ) (s s1 s2 : StableSy) : Prop :=
  (∀ i j, ¬(({i, j} : Set ℕ) = {p, q}) → i ∈ s1.I → j ∈ s1.I →
      s1.a i j = s.a i j ∧ s1.b i j = s.b i j) ∧
    (∀ i j, ¬(({i, j} : Set ℕ) = {p, q}) → i ∈ s2.I → j ∈ s2.I →
      s2.a i j = s.a i j ∧ s2.b i j = s.b i j)

/-- HOL `COVER5_SY` (MTUWLUN.hl:70). -/
def COVER5_SY (p q : ℕ) (s s1 s2 : StableSy) : Prop :=
  s1.a p q ≤ s.a p q ∧ s2.a p q ≤ s.a p q ∧
    s.a p q ≤ s1.b p q ∧ s.a p q ≤ s2.b p q

/-- HOL `COVER6_SY` (MTUWLUN.hl:74). -/
def COVER6_SY (p q : ℕ) (s s1 s2 : StableSy) : Prop :=
  ({p, q} ∈ s1.J ↔ {p, q} ∈ s2.J) ∧
    ({p, q} ∈ s1.J ↔ (earSy_p8 s1 ∨ earSy_p8 s2))

/-- HOL `COVER_SY` (MTUWLUN.hl:78). -/
def COVER_SY (p q : ℕ) (s s1 s2 : StableSy) : Prop :=
  COVER1_SY p q s s1 s2 ∧ COVER2_SY s s1 s2 ∧ COVER3_SY p q s s1 s2 ∧
    COVER4_SY p q s s1 s2 ∧ COVER5_SY p q s s1 s2 ∧ COVER6_SY p q s s1 s2

/-- HOL `pmat1` (MTUWLUN.hl:87): the first `q-1` rows of `A` plus `A`'s last
row (`A$dimindex(:M)$j`); the output dimension `q` is explicit here (HOL
reads it off the result type). -/
def pmat1 {m q : ℕ} (A : FinMat m 3) : FinMat q 3 := fun i j =>
  if h : (i : ℕ) + 1 < q ∧ (i : ℕ) < m then A ⟨i, h.2⟩ j
  else if h' : m - 1 < m then A ⟨m - 1, h'⟩ j else 0

/-- HOL `pmat2` (MTUWLUN.hl:90): rows `dimindex(:M) - q + i` of `A`. -/
def pmat2 {m q : ℕ} (A : FinMat m 3) : FinMat q 3 := fun i j =>
  if h : m - q + i.val < m then A ⟨m - q + i.val, h⟩ j else 0

/-- HOL `DIA_SY` (MTUWLUN.hl:93). -/
def DIA_SY (p q : ℕ) (s : StableSy) : Prop :=
  p ≠ q ∧ p ∈ s.I ∧ q ∈ s.I ∧
    ¬∃ i, i ∈ s.I ∧ ({p, q} : Set ℕ) = {i, s.f i}

/-- HOL `SCHANGE` (MTUWLUN.hl:170). -/
def SCHANGE (f : ℕ → ℕ) (s s1 : StableSy) : Prop :=
  s.k = s1.k ∧ s.d = s1.d ∧ s.I = Set.image f s1.I ∧
    (∀ p q, {f p, f q} ∈ s.J ↔ {p, q} ∈ s1.J) ∧
    (∀ p q, s.a (f p) (f q) = s1.a p q) ∧
    (∀ p q, s.b (f p) (f q) = s1.b p q) ∧
    s1.f = s.f ∘ f

/-! ## Row helpers -/

/-- Helper: `rowSy` of an in-range row is the `vecmatsV3_p4` row. -/
theorem rowSy_of_lt {m : ℕ} {l : FinVec m 3} {i : ℕ} (hi : i < m) :
    rowSy l i = vecmatsV3_p4 l ⟨i, hi⟩ := dif_pos hi

/-- Helper: `V3`-level equality of rows reduces to the plain-function rows. -/
theorem vecmatsV3_row_eq {m : ℕ} {x y : FinVec m 3} (i : Fin m) :
    vecmatsV3_p4 x i = vecmatsV3_p4 y i ↔ vecmats_p4 x i = vecmats_p4 y i :=
  ⟨fun h => by
      have := congrArg (fun v : V3 => (WithLp.ofLp v : Fin 3 → ℝ)) h
      simpa [vecmatsV3_p4] using this,
    fun h => by
      show (WithLp.toLp 2 (vecmats_p4 x i) : V3) = WithLp.toLp 2 (vecmats_p4 y i)
      rw [h]⟩

/-- Helper: equal indices give equal `vecmats_p4` rows. -/
theorem vecmats_p4_congr {m : ℕ} {x y : Fin m} (h : (x : ℕ) = (y : ℕ))
    (A : FinVec m 3) : vecmats_p4 A x = vecmats_p4 A y := by
  rw [Fin.val_injective h]

/-- Helper: `finNext` on an explicit literal. -/
theorem finNext_val {m n : ℕ} (hm : 0 < m) (h : n + 1 < m) :
    finNext (⟨n, by omega⟩ : Fin m) = ⟨n + 1, by omega⟩ :=
  Fin.val_injective (by rw [finNext, Fin.val_mk, Nat.mod_eq_of_lt h])

/-! ## Mechanical theorems (proved) -/

/-- HOL `K_SY_LE2` (MTUWLUN.hl:193). -/
theorem K_SY_LE2 (s : StableSy) : 2 < s.k := by
  have h3 : 3 ≤ s.k := s.stable.1.1
  omega

/-- HOL `IK_SY` (MTUWLUN.hl:182): `I_SY s = 0..(p-1)` pins `k_sy s = p`. -/
theorem IK_SY (s : StableSy) (p : ℕ) (h1 : 1 ≤ p) (h2 : s.I = Icc 0 (p - 1)) :
    s.k = p := by
  have hcard : Nat.card s.I = s.k := s.stable.1.2.2.1.2.2.2.2
  rw [h2] at hcard
  have hIcc : Nat.card (Icc 0 (p - 1) : Set ℕ) = p := by
    rw [Nat.card_coe_set_eq]
    have h := Set.ncard_Icc_nat 0 (p - 1)
    omega
  rw [hIcc] at hcard
  omega

/-- HOL `CARD_I_SY_LT_3` (MTUWLUN.hl:100). -/
theorem CARD_I_SY_LT_3 (s : StableSy) (p q : ℕ) (h : DIA_SY p q s) :
    3 < Nat.card s.I := by
  obtain ⟨hpq, hpI, hqI, hndia⟩ := h
  obtain ⟨hcs, -, -, -⟩ := s.stable
  obtain ⟨h3, -, ht, -, -, -, -⟩ := hcs
  have hmem : ∀ x ∈ s.I, s.f x ∈ s.I := ht.1
  have hinj : ∀ x₁ ∈ s.I, ∀ x₂ ∈ s.I, s.f x₁ = s.f x₂ → x₁ = x₂ := ht.2.1
  have hper : ∀ i x, 0 < i → i < s.k → x ∈ s.I → s.f^[i] x ≠ x := ht.2.2.1
  have hfix : ∀ x ∈ s.I, s.f^[s.k] x = x := ht.2.2.2.1
  have hcard : Nat.card s.I = s.k := ht.2.2.2.2
  by_contra hlt
  push_neg at hlt
  have hkeq : s.k = 3 := le_antisymm (by rw [← hcard]; omega) h3
  have hcard3 : Nat.card s.I = 3 := by rw [hcard, hkeq]
  have hfI : s.f p ∈ s.I := hmem p hpI
  have hffI : s.f (s.f p) ∈ s.I := hmem _ hfI
  have hd1 : s.f p ≠ p := fun hc => hper 1 p (by norm_num) (by omega) hpI hc
  have hd2 : s.f (s.f p) ≠ p := fun hc => hper 2 p (by norm_num) (by omega) hpI hc
  have hd3 : s.f (s.f p) ≠ s.f p := fun hc => hd1 (hinj (s.f p) hfI p hpI hc)
  have hf3 : s.f^[3] p = p := by
    have := hfix p hpI
    rw [hkeq] at this
    exact this
  have hf3' : s.f (s.f (s.f p)) = p := by
    simpa [Function.iterate_succ', Function.iterate_one] using hf3
  -- `q` must be one of the three cycle points, else 4 points lie in `s.I`
  have hqcases : q = p ∨ q = s.f p ∨ q = s.f (s.f p) := by
    by_contra hnone
    push_neg at hnone
    obtain ⟨hqp, hqf, hqff⟩ := hnone
    have hS4 : ({q, p, s.f p, s.f (s.f p)} : Finset ℕ).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hqp, hqf, hqff]),
          Finset.card_insert_of_notMem (by simp [Ne.symm hd1, Ne.symm hd2]),
          Finset.card_insert_of_notMem (by simp [Ne.symm hd3]),
          Finset.card_singleton]
    have hSsub : ∀ x ∈ ({q, p, s.f p, s.f (s.f p)} : Finset ℕ), x ∈ s.I := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hqI
      · exact hpI
      · exact hfI
      · exact hffI
    have hcardS :
        Nat.card ({q, p, s.f p, s.f (s.f p)} : Finset ℕ) = 4 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, hS4]
    haveI hfinI : Finite (↥s.I) := Nat.finite_of_card_ne_zero (by rw [hcard3]; omega)
    have hinj4 : Nat.card ({q, p, s.f p, s.f (s.f p)} : Finset ℕ) ≤ Nat.card s.I :=
      Nat.card_le_card_of_injective
        (f := fun x : {x // x ∈ ({q, p, s.f p, s.f (s.f p)} : Finset ℕ)} =>
          (⟨x.1, hSsub x.1 x.2⟩ : {x // x ∈ s.I}))
        (fun _ _ h => Subtype.ext (by simpa using h))
    rw [hcard3] at hinj4
    omega
  rcases hqcases with hq | hq | hq
  · exact absurd hq.symm hpq
  · exact absurd (⟨p, hpI, by rw [hq]⟩ : ∃ i, i ∈ s.I ∧ ({p, q} : Set ℕ) = {i, s.f i})
      hndia
  · exact absurd
      (⟨s.f (s.f p), hffI, by rw [hq, hf3', Set.pair_comm]⟩ :
        ∃ i, i ∈ s.I ∧ ({p, q} : Set ℕ) = {i, s.f i})
      hndia

/-- HOL `COVER_NOT_EAR_SY` (MTUWLUN.hl:148). -/
theorem COVER_NOT_EAR_SY (s : StableSy) (p q : ℕ) (h : DIA_SY p q s) :
    ¬earSy_p8 s := by
  intro he
  have := CARD_I_SY_LT_3 s p q h
  rw [he.1] at this
  omega

/-- HOL `DIAGONAL_SY` (MTUWLUN.hl:158). -/
theorem DIAGONAL_SY (s : StableSy) (p q : ℕ) (h : DIA_SY p q s) :
    {p, q} ∉ s.J := by
  intro hpq
  obtain ⟨-, -, -, hndia⟩ := h
  obtain ⟨i, hi, heq⟩ := s.stable.1.2.2.2.2.2.1 hpq
  exact hndia ⟨i, hi, heq⟩

/-- HOL `IN_J_IMP_IN_J1_SY` (MTUWLUN.hl:205). -/
theorem IN_J_IMP_IN_J1_SY (s1 : StableSy) (p : ℕ) (h1 : s1.k = p)
    (h2 : s1.I = Icc 0 (p - 1)) (h3 : s1.f = fun i => (i + 1) % p)
    (h4 : {0, p - 1} ∈ s1.J) : (p - 1, p) ∈ J1_SY_p8 s1 := by
  have hp : 2 < s1.k := K_SY_LE2 s1
  rw [h1] at hp
  show (p - 1, p) ∈ {x | ∃ i, {i % s1.k, s1.f (i % s1.k)} ∈ s1.J ∧
    i ∈ Icc 1 s1.k ∧ x = (i, i % s1.k + 1)}
  rw [h1]
  have hm1 : (p - 1) % p = p - 1 := Nat.mod_eq_of_lt (by omega)
  have hm2 : (p - 1 + 1) % p = 0 := by
    rw [show p - 1 + 1 = p from by omega, Nat.mod_self]
  refine ⟨p - 1, ?_, mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  · rw [hm1]
    simp only [h3]
    rw [hm2, Set.pair_comm]
    exact h4
  · rw [hm1, show p - 1 + 1 = p from by omega]

/-! ## The row-slicing matrices (MTUWLUN.hl:2101-2209) -/

/-- HOL `PMAT2_EQ_SY` (MTUWLUN.hl:2101): the second slice of rows.
`row i (vecmats l2) = row (p-2+i) (vecmats l)` (1-based) ↦ 0-based. -/
theorem PMAT2_EQ_SY (k p : ℕ) (s s1 s2 s3 : StableSy)
    (l : FinVec k 3) (l1 : FinVec p 3) (l2 : FinVec (k - p + 2) 3)
    (hM : 1 ≤ k) (hP : 1 ≤ p) (hkp : 1 ≤ k - p)
    (hIs : s.I = Icc 0 (k - 1)) (hfs : s.f = fun i => (i + 1) % k)
    (hIs1 : s1.I = Icc 0 (p - 1)) (hfs1 : s1.f = fun i => (i + 1) % p)
    (hIs3 : s3.I = Icc 0 (k - p + 1)) (hfs3 : s3.f = fun i => (i + 1) % (k - p + 2))
    (_hear : earSy_p8 s2 ↔ earSy_p8 s3)
    (_hdia : DIA_SY 0 (p - 1) s)
    (_hschg : SCHANGE (fun x => if x = 0 then 0 else (p - 2 + x) % k) s2 s3)
    (_hcov : COVER_SY 0 (p - 1) s s1 s2)
    (_hl : l ∈ B_SY1_p8 s.a s.b)
    (_hcstab : ∀ i j : ℕ, {i % k, j % k} ∈ s.J ∪ {{0, p - 1}} →
      ‖rowSy l i - rowSy l j‖ ≤ cstab)
    (_hm1 : matvec_p4 (pmat1 (vecmats_p4 l)) = l1)
    (hm2 : matvec_p4 (pmat2 (vecmats_p4 l)) = l2)
    (i : ℕ) (hi : i < k - p + 2) : rowSy l2 i = rowSy l (p - 2 + i) := by
  have hp3 : 3 ≤ s1.k := s1.stable.1.1
  have hk1 : s1.k = p := IK_SY s1 p hP hIs1
  have h2p : 2 ≤ p := by omega
  have hik : p - 2 + i < k := by omega
  have hveq : vecmats_p4 l2 = pmat2 (vecmats_p4 l) := by
    rw [← hm2]
    exact VECMATS_MATVEC_ID _
  have h1 : p ≤ k := by omega
  have hks : k - (k - p + 2) = p - 2 := by
    rw [show k - (k - p + 2) = k - ((k - p) + 2) from rfl, ← Nat.sub_sub,
      Nat.sub_sub_self h1]
  have e1 : vecmats_p4 l2 ⟨i, hi⟩ = vecmats_p4 l ⟨p - 2 + i, hik⟩ := by
    rw [hveq]
    funext j
    simp only [pmat2, Fin.val_mk]
    have hdcond : k - (k - p + 2) + i < k := by rw [hks]; omega
    have hidx : (⟨k - (k - p + 2) + i, hdcond⟩ : Fin k) = ⟨p - 2 + i, hik⟩ :=
      Fin.val_injective (show (k - (k - p + 2) + i : ℕ) = p - 2 + i by rw [hks])
    rw [dif_pos hdcond, hidx]
  rw [rowSy_of_lt hi, rowSy_of_lt hik]
  show (WithLp.toLp 2 (vecmats_p4 l2 ⟨i, hi⟩) : V3) =
    WithLp.toLp 2 (vecmats_p4 l ⟨p - 2 + i, hik⟩)
  rw [e1]

/-- HOL `PMAT1_EQ_SY` (MTUWLUN.hl:2137): the first slice of rows.
`row i (vecmats l1) = row i (vecmats l)` for `1 ≤ i ≤ p-1` (1-based). -/
theorem PMAT1_EQ_SY (k p : ℕ) (s s1 s2 s3 : StableSy)
    (l : FinVec k 3) (l1 : FinVec p 3) (l2 : FinVec (k - p + 2) 3)
    (hM : 1 ≤ k) (hP : 1 ≤ p) (hkp : 1 ≤ k - p)
    (hIs : s.I = Icc 0 (k - 1)) (hfs : s.f = fun i => (i + 1) % k)
    (hIs1 : s1.I = Icc 0 (p - 1)) (hfs1 : s1.f = fun i => (i + 1) % p)
    (hIs3 : s3.I = Icc 0 (k - p + 1)) (hfs3 : s3.f = fun i => (i + 1) % (k - p + 2))
    (_hear : earSy_p8 s2 ↔ earSy_p8 s3)
    (_hdia : DIA_SY 0 (p - 1) s)
    (_hschg : SCHANGE (fun x => if x = 0 then 0 else (p - 2 + x) % k) s2 s3)
    (_hcov : COVER_SY 0 (p - 1) s s1 s2)
    (_hl : l ∈ B_SY1_p8 s.a s.b)
    (_hcstab : ∀ i j : ℕ, {i % k, j % k} ∈ s.J ∪ {{0, p - 1}} →
      ‖rowSy l i - rowSy l j‖ ≤ cstab)
    (_hm1 : matvec_p4 (pmat1 (vecmats_p4 l)) = l1)
    (_hm2 : matvec_p4 (pmat2 (vecmats_p4 l)) = l2)
    (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ p - 1) :
    rowSy l1 (i - 1) = rowSy l (i - 1) := by
  have hp3 : 3 ≤ s1.k := s1.stable.1.1
  have hk1 : s1.k = p := IK_SY s1 p hP hIs1
  have hik : i - 1 < k := by omega
  have hil : i - 1 < p := by omega
  have hveq : vecmats_p4 l1 = pmat1 (vecmats_p4 l) := by
    rw [← _hm1]
    exact VECMATS_MATVEC_ID _
  have e1 : vecmats_p4 l1 ⟨i - 1, hil⟩ = vecmats_p4 l ⟨i - 1, hik⟩ := by
    rw [hveq]
    funext j
    simp only [pmat1, Fin.val_mk]
    rw [dif_pos (by omega : (i - 1 : ℕ) + 1 < p ∧ i - 1 < k)]
  rw [rowSy_of_lt (m := p) (i := i - 1) hil, rowSy_of_lt (m := k) (i := i - 1) hik]
  show (WithLp.toLp 2 (vecmats_p4 l1 ⟨i - 1, hil⟩) : V3) =
    WithLp.toLp 2 (vecmats_p4 l ⟨i - 1, hik⟩)
  rw [e1]

/-- HOL `PMAT1_EQ_SY_P` (MTUWLUN.hl:2174): the glued corner row.
`row p (vecmats l1) = row k (vecmats l)` (1-based) ↦ 0-based last rows. -/
theorem PMAT1_EQ_SY_P (k p : ℕ) (s s1 s2 s3 : StableSy)
    (l : FinVec k 3) (l1 : FinVec p 3) (l2 : FinVec (k - p + 2) 3)
    (hM : 1 ≤ k) (hP : 1 ≤ p) (hkp : 1 ≤ k - p)
    (hIs : s.I = Icc 0 (k - 1)) (hfs : s.f = fun i => (i + 1) % k)
    (hIs1 : s1.I = Icc 0 (p - 1)) (hfs1 : s1.f = fun i => (i + 1) % p)
    (hIs3 : s3.I = Icc 0 (k - p + 1)) (hfs3 : s3.f = fun i => (i + 1) % (k - p + 2))
    (_hear : earSy_p8 s2 ↔ earSy_p8 s3)
    (_hdia : DIA_SY 0 (p - 1) s)
    (_hschg : SCHANGE (fun x => if x = 0 then 0 else (p - 2 + x) % k) s2 s3)
    (_hcov : COVER_SY 0 (p - 1) s s1 s2)
    (_hl : l ∈ B_SY1_p8 s.a s.b)
    (_hcstab : ∀ i j : ℕ, {i % k, j % k} ∈ s.J ∪ {{0, p - 1}} →
      ‖rowSy l i - rowSy l j‖ ≤ cstab)
    (_hm1 : matvec_p4 (pmat1 (vecmats_p4 l)) = l1)
    (_hm2 : matvec_p4 (pmat2 (vecmats_p4 l)) = l2) :
    rowSy l1 (p - 1) = rowSy l (k - 1) := by
  have hp3 : 3 ≤ s1.k := s1.stable.1.1
  have hk1 : s1.k = p := IK_SY s1 p hP hIs1
  have hik : k - 1 < k := by omega
  have hil : p - 1 < p := by omega
  have hveq : vecmats_p4 l1 = pmat1 (vecmats_p4 l) := by
    rw [← _hm1]
    exact VECMATS_MATVEC_ID _
  have e1 : vecmats_p4 l1 ⟨p - 1, hil⟩ = vecmats_p4 l ⟨k - 1, hik⟩ := by
    rw [hveq]
    funext j
    simp only [pmat1, Fin.val_mk]
    rw [dif_neg (by omega : ¬((p : ℕ) - 1 + 1 < p ∧ (p : ℕ) - 1 < k)), dif_pos hik]
  rw [rowSy_of_lt (m := p) (i := p - 1) hil, rowSy_of_lt (m := k) (i := k - 1) hik]
  show (WithLp.toLp 2 (vecmats_p4 l1 ⟨p - 1, hil⟩) : V3) =
    WithLp.toLp 2 (vecmats_p4 l ⟨k - 1, hik⟩)
  rw [e1]

/-! ## The `rho_node1` row-cycle kit (MTUWLUN.hl:2214-2274) -/

/-- Helper: the cyclic dart `(row i, row (i+1))` lies in `F_SY`. -/
theorem dart_mem_F_SY_p8 {m : ℕ} (l : FinVec m 3) (i : Fin m) :
    (vecmatsV3_p4 l i, vecmatsV3_p4 l (finNext i)) ∈ F_SY_p4 (vecmatsV3_p4 l) := by
  rw [F_SY_p4, Set.mem_image]
  exact ⟨i, Set.mem_univ _, rfl⟩

/-- HOL `POWER_RHO_NODE_SY` (MTUWLUN.hl:2214).
`ITER (i-1) (rho_node1 F) v = u` for `row i = u`, `row 1 = v` (1-based). -/
theorem POWER_RHO_NODE_SY (k : ℕ) (l : FinVec k 3) (u v : V3)
    (hfan : localFan_p4 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
      (F_SY_p4 (vecmatsV3_p4 l)))
    (hM : 1 ≤ k) (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ k)
    (hu : rowSy l (i - 1) = u) (hv : rowSy l 0 = v) :
    (rhoNode1 (F_SY_p4 (vecmatsV3_p4 l)))^[i - 1] v = u := by
  have key : ∀ (n : ℕ) (hn : n < k), (rhoNode1 (F_SY_p4 (vecmatsV3_p4 l)))^[n]
      (vecmatsV3_p4 l ⟨0, hM⟩) = vecmatsV3_p4 l ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
        intro hn
        have hn' : n < k := by omega
        rw [Function.iterate_succ_apply', ih hn']
        have hdart := dart_mem_F_SY_p8 l ⟨n, hn'⟩
        rw [DETER_RHO_NODE_p8 hfan hdart]
        congr 1
        rw [finNext_val (by omega) hn]
  have hk : i - 1 < k := by omega
  rw [← hv, ← hu, rowSy_of_lt (by omega), rowSy_of_lt (by omega)]
  exact key (i - 1) hk

/-- HOL `RHO_NODE_K_SY` (MTUWLUN.hl:2241): `rho_node1 F u = v` for
`row k = u`, `row 1 = v` (1-based). -/
theorem RHO_NODE_K_SY (k : ℕ) (l : FinVec k 3) (u v : V3)
    (hfan : localFan_p4 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
      (F_SY_p4 (vecmatsV3_p4 l)))
    (hM : 1 ≤ k) (hu : rowSy l (k - 1) = u) (hv : rowSy l 0 = v) :
    rhoNode1 (F_SY_p4 (vecmatsV3_p4 l)) u = v := by
  refine DETER_RHO_NODE_p8 hfan ?_
  have h1 : vecmatsV3_p4 l (⟨k - 1, by omega⟩ : Fin k) = u := by
    rw [← rowSy_of_lt (i := k - 1) (by omega)]
    exact hu
  have h2 : vecmatsV3_p4 l (finNext (⟨k - 1, by omega⟩ : Fin k)) = v := by
    have hfin : finNext (⟨k - 1, by omega⟩ : Fin k) = ⟨0, by omega⟩ :=
      Fin.val_injective (by
        simp only [finNext, Fin.val_mk, show k - 1 + 1 = k from by omega,
          Nat.mod_self])
    rw [hfin, ← rowSy_of_lt (i := 0) (by omega)]
    exact hv
  have hdart := dart_mem_F_SY_p8 l (⟨k - 1, by omega⟩ : Fin k)
  rw [h1, h2] at hdart
  exact hdart

/-- HOL `RHO_NODE_SY` (MTUWLUN.hl:2260): `rho_node1 F (row i) =
row (SUC (i MOD k))` (1-based) ↦ 0-based `rowSy l (i % k)`. -/
theorem RHO_NODE_SY (k : ℕ) (l : FinVec k 3)
    (hfan : localFan_p4 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
      (F_SY_p4 (vecmatsV3_p4 l)))
    (hM : 1 ≤ k) (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ k) :
    rhoNode1 (F_SY_p4 (vecmatsV3_p4 l)) (rowSy l (i - 1)) =
      rowSy l (i % k) := by
  have hik : i - 1 < k := by omega
  have hik2 : i % k < k := Nat.mod_lt _ hM
  refine DETER_RHO_NODE_p8 hfan ?_
  have h1 : vecmatsV3_p4 l (⟨i - 1, hik⟩ : Fin k) = rowSy l (i - 1) := by
    rw [← rowSy_of_lt (i := i - 1) hik]
  have h2 : vecmatsV3_p4 l (finNext (⟨i - 1, hik⟩ : Fin k)) = rowSy l (i % k) := by
    have hfin : finNext (⟨i - 1, hik⟩ : Fin k) = ⟨i % k, hik2⟩ :=
      Fin.val_injective (by
        simp only [finNext, Fin.val_mk, show i - 1 + 1 = i from by omega])
    rw [hfin, ← rowSy_of_lt (i := i % k) hik2]
  have hdart := dart_mem_F_SY_p8 l (⟨i - 1, hik⟩ : Fin k)
  rw [h1, h2] at hdart
  exact hdart

/-! ## The covering theorems (skeleton: giants, `sorry`)

The shared hypothesis block is MTUWLUN's verbatim cover context (repeated in
the HOL source before every theorem): dimensions and the three cyclic
`I_SY`/`f_sy` presentations, the ear transfer, the diagonal, the re-indexing
and the cover bundle, `l ∈ B_SY1`, the edge `cstab` bound, the two matrix
identities, and the two distinguished rows `v`/`w`. -/

/-- HOL `D_FUN_COVER_SY` (MTUWLUN.hl:224). -/
theorem D_FUN_COVER_SY (k p : ℕ) (s s1 s2 s3 : StableSy)
    (l : FinVec k 3) (l1 : FinVec p 3) (l2 : FinVec (k - p + 2) 3)
    (hM : 1 ≤ k) (hP : 1 ≤ p) (hkp : 1 ≤ k - p)
    (hIs : s.I = Icc 0 (k - 1)) (hfs : s.f = fun i => (i + 1) % k)
    (hIs1 : s1.I = Icc 0 (p - 1)) (hfs1 : s1.f = fun i => (i + 1) % p)
    (hIs3 : s3.I = Icc 0 (k - p + 1)) (hfs3 : s3.f = fun i => (i + 1) % (k - p + 2))
    (_hear : earSy_p8 s2 ↔ earSy_p8 s3)
    (_hdia : DIA_SY 0 (p - 1) s)
    (_hschg : SCHANGE (fun x => if x = 0 then 0 else (p - 2 + x) % k) s2 s3)
    (_hcov : COVER_SY 0 (p - 1) s s1 s2)
    (_hl : l ∈ B_SY1_p8 s.a s.b)
    (_hcstab : ∀ i j : ℕ, {i % k, j % k} ∈ s.J ∪ {{0, p - 1}} →
      ‖rowSy l i - rowSy l j‖ ≤ cstab)
    (_hm1 : matvec_p4 (pmat1 (vecmats_p4 l)) = l1)
    (_hm2 : matvec_p4 (pmat2 (vecmats_p4 l)) = l2) :
    dFun_p8 s l ≤ dFun_p8 s1 l1 + dFun_p8 s3 l2 := sorry

/-- HOL `ORDER_COVER1_SY` (MTUWLUN.hl:2277): the `v → w` orbit length.
`order (rho_node1 F) v w = p-1` for `v = row k`, `w = row (p-1)`. -/
theorem ORDER_COVER1_SY (k p : ℕ) (s s1 s2 s3 : StableSy)
    (l : FinVec k 3) (l1 : FinVec p 3) (l2 : FinVec (k - p + 2) 3)
    (hM : 1 ≤ k) (hP : 1 ≤ p) (hkp : 1 ≤ k - p)
    (hIs : s.I = Icc 0 (k - 1)) (hfs : s.f = fun i => (i + 1) % k)
    (hIs1 : s1.I = Icc 0 (p - 1)) (hfs1 : s1.f = fun i => (i + 1) % p)
    (hIs3 : s3.I = Icc 0 (k - p + 1)) (hfs3 : s3.f = fun i => (i + 1) % (k - p + 2))
    (_hear : earSy_p8 s2 ↔ earSy_p8 s3)
    (_hdia : DIA_SY 0 (p - 1) s)
    (_hschg : SCHANGE (fun x => if x = 0 then 0 else (p - 2 + x) % k) s2 s3)
    (_hcov : COVER_SY 0 (p - 1) s s1 s2)
    (_hl : l ∈ B_SY1_p8 s.a s.b)
    (_hcstab : ∀ i j : ℕ, {i % k, j % k} ∈ s.J ∪ {{0, p - 1}} →
      ‖rowSy l i - rowSy l j‖ ≤ cstab)
    (_hm1 : matvec_p4 (pmat1 (vecmats_p4 l)) = l1)
    (_hm2 : matvec_p4 (pmat2 (vecmats_p4 l)) = l2)
    (hv : rowSy l (k - 1) = v) (hw : rowSy l (p - 2) = w) :
    order_p8 (rhoNode1 (F_SY_p4 (vecmatsV3_p4 l))) v w = p - 1 := sorry

/-- HOL `ORDER_COVER2_SY` (MTUWLUN.hl:2796): the `w → v` orbit length.
`order (rho_node1 F) w v = k-p+1` for `v = row k`, `w = row (p-1)`. -/
theorem ORDER_COVER2_SY (k p : ℕ) (s s1 s2 s3 : StableSy)
    (l : FinVec k 3) (l1 : FinVec p 3) (l2 : FinVec (k - p + 2) 3)
    (hM : 1 ≤ k) (hP : 1 ≤ p) (hkp : 1 ≤ k - p)
    (hIs : s.I = Icc 0 (k - 1)) (hfs : s.f = fun i => (i + 1) % k)
    (hIs1 : s1.I = Icc 0 (p - 1)) (hfs1 : s1.f = fun i => (i + 1) % p)
    (hIs3 : s3.I = Icc 0 (k - p + 1)) (hfs3 : s3.f = fun i => (i + 1) % (k - p + 2))
    (_hear : earSy_p8 s2 ↔ earSy_p8 s3)
    (_hdia : DIA_SY 0 (p - 1) s)
    (_hschg : SCHANGE (fun x => if x = 0 then 0 else (p - 2 + x) % k) s2 s3)
    (_hcov : COVER_SY 0 (p - 1) s s1 s2)
    (_hl : l ∈ B_SY1_p8 s.a s.b)
    (_hcstab : ∀ i j : ℕ, {i % k, j % k} ∈ s.J ∪ {{0, p - 1}} →
      ‖rowSy l i - rowSy l j‖ ≤ cstab)
    (_hm1 : matvec_p4 (pmat1 (vecmats_p4 l)) = l1)
    (_hm2 : matvec_p4 (pmat2 (vecmats_p4 l)) = l2)
    (hv : rowSy l (k - 1) = v) (hw : rowSy l (p - 2) = w) :
    order_p8 (rhoNode1 (F_SY_p4 (vecmatsV3_p4 l))) w v = k - p + 1 := sorry

/-- HOL `SLICEV_EQ_V_SY` (MTUWLUN.hl:2366): the forward slice vertices.
`slicev E F v w = V_SY (vecmats l1)` for `E = E_SY (vecmats l)`,
`F = F_SY (vecmats l)`. -/
theorem SLICEV_EQ_V_SY (k p : ℕ) (s s1 s2 s3 : StableSy)
    (l : FinVec k 3) (l1 : FinVec p 3) (l2 : FinVec (k - p + 2) 3)
    (hM : 1 ≤ k) (hP : 1 ≤ p) (hkp : 1 ≤ k - p)
    (hIs : s.I = Icc 0 (k - 1)) (hfs : s.f = fun i => (i + 1) % k)
    (hIs1 : s1.I = Icc 0 (p - 1)) (hfs1 : s1.f = fun i => (i + 1) % p)
    (hIs3 : s3.I = Icc 0 (k - p + 1)) (hfs3 : s3.f = fun i => (i + 1) % (k - p + 2))
    (_hear : earSy_p8 s2 ↔ earSy_p8 s3)
    (_hdia : DIA_SY 0 (p - 1) s)
    (_hschg : SCHANGE (fun x => if x = 0 then 0 else (p - 2 + x) % k) s2 s3)
    (_hcov : COVER_SY 0 (p - 1) s s1 s2)
    (_hl : l ∈ B_SY1_p8 s.a s.b)
    (_hcstab : ∀ i j : ℕ, {i % k, j % k} ∈ s.J ∪ {{0, p - 1}} →
      ‖rowSy l i - rowSy l j‖ ≤ cstab)
    (_hm1 : matvec_p4 (pmat1 (vecmats_p4 l)) = l1)
    (_hm2 : matvec_p4 (pmat2 (vecmats_p4 l)) = l2)
    (hv : rowSy l (k - 1) = v) (hw : rowSy l (p - 2) = w) :
    slicev_p8 (E_SY_p4 (vecmatsV3_p4 l)) (F_SY_p4 (vecmatsV3_p4 l)) v w =
      V_SY_p4 (vecmatsV3_p4 l1) := sorry

/-- HOL `SLICEV_EQ_V2_SY` (MTUWLUN.hl:2887): the backward slice vertices.
`slicev E F w v = V_SY (vecmats l2)`. -/
theorem SLICEV_EQ_V2_SY (k p : ℕ) (s s1 s2 s3 : StableSy)
    (l : FinVec k 3) (l1 : FinVec p 3) (l2 : FinVec (k - p + 2) 3)
    (hM : 1 ≤ k) (hP : 1 ≤ p) (hkp : 1 ≤ k - p)
    (hIs : s.I = Icc 0 (k - 1)) (hfs : s.f = fun i => (i + 1) % k)
    (hIs1 : s1.I = Icc 0 (p - 1)) (hfs1 : s1.f = fun i => (i + 1) % p)
    (hIs3 : s3.I = Icc 0 (k - p + 1)) (hfs3 : s3.f = fun i => (i + 1) % (k - p + 2))
    (_hear : earSy_p8 s2 ↔ earSy_p8 s3)
    (_hdia : DIA_SY 0 (p - 1) s)
    (_hschg : SCHANGE (fun x => if x = 0 then 0 else (p - 2 + x) % k) s2 s3)
    (_hcov : COVER_SY 0 (p - 1) s s1 s2)
    (_hl : l ∈ B_SY1_p8 s.a s.b)
    (_hcstab : ∀ i j : ℕ, {i % k, j % k} ∈ s.J ∪ {{0, p - 1}} →
      ‖rowSy l i - rowSy l j‖ ≤ cstab)
    (_hm1 : matvec_p4 (pmat1 (vecmats_p4 l)) = l1)
    (_hm2 : matvec_p4 (pmat2 (vecmats_p4 l)) = l2)
    (hv : rowSy l (k - 1) = v) (hw : rowSy l (p - 2) = w) :
    slicev_p8 (E_SY_p4 (vecmatsV3_p4 l)) (F_SY_p4 (vecmatsV3_p4 l)) w v =
      V_SY_p4 (vecmatsV3_p4 l2) := sorry

/-- HOL `SLICEE_EQ_E_SY` (MTUWLUN.hl:2471): the forward slice edges.
`slicee E F v w = E_SY (vecmats l1)`. -/
theorem SLICEE_EQ_E_SY (k p : ℕ) (s s1 s2 s3 : StableSy)
    (l : FinVec k 3) (l1 : FinVec p 3) (l2 : FinVec (k - p + 2) 3)
    (hM : 1 ≤ k) (hP : 1 ≤ p) (hkp : 1 ≤ k - p)
    (hIs : s.I = Icc 0 (k - 1)) (hfs : s.f = fun i => (i + 1) % k)
    (hIs1 : s1.I = Icc 0 (p - 1)) (hfs1 : s1.f = fun i => (i + 1) % p)
    (hIs3 : s3.I = Icc 0 (k - p + 1)) (hfs3 : s3.f = fun i => (i + 1) % (k - p + 2))
    (_hear : earSy_p8 s2 ↔ earSy_p8 s3)
    (_hdia : DIA_SY 0 (p - 1) s)
    (_hschg : SCHANGE (fun x => if x = 0 then 0 else (p - 2 + x) % k) s2 s3)
    (_hcov : COVER_SY 0 (p - 1) s s1 s2)
    (_hl : l ∈ B_SY1_p8 s.a s.b)
    (_hcstab : ∀ i j : ℕ, {i % k, j % k} ∈ s.J ∪ {{0, p - 1}} →
      ‖rowSy l i - rowSy l j‖ ≤ cstab)
    (_hm1 : matvec_p4 (pmat1 (vecmats_p4 l)) = l1)
    (_hm2 : matvec_p4 (pmat2 (vecmats_p4 l)) = l2)
    (hv : rowSy l (k - 1) = v) (hw : rowSy l (p - 2) = w) :
    slicee_p8 (E_SY_p4 (vecmatsV3_p4 l)) (F_SY_p4 (vecmatsV3_p4 l)) v w =
      E_SY_p4 (vecmatsV3_p4 l1) := sorry

/-- HOL `SLICEF_EQ_F_SY` (MTUWLUN.hl:2631): the forward slice darts.
`slicef E F v w = F_SY (vecmats l1)`. -/
theorem SLICEF_EQ_F_SY (k p : ℕ) (s s1 s2 s3 : StableSy)
    (l : FinVec k 3) (l1 : FinVec p 3) (l2 : FinVec (k - p + 2) 3)
    (hM : 1 ≤ k) (hP : 1 ≤ p) (hkp : 1 ≤ k - p)
    (hIs : s.I = Icc 0 (k - 1)) (hfs : s.f = fun i => (i + 1) % k)
    (hIs1 : s1.I = Icc 0 (p - 1)) (hfs1 : s1.f = fun i => (i + 1) % p)
    (hIs3 : s3.I = Icc 0 (k - p + 1)) (hfs3 : s3.f = fun i => (i + 1) % (k - p + 2))
    (_hear : earSy_p8 s2 ↔ earSy_p8 s3)
    (_hdia : DIA_SY 0 (p - 1) s)
    (_hschg : SCHANGE (fun x => if x = 0 then 0 else (p - 2 + x) % k) s2 s3)
    (_hcov : COVER_SY 0 (p - 1) s s1 s2)
    (_hl : l ∈ B_SY1_p8 s.a s.b)
    (_hcstab : ∀ i j : ℕ, {i % k, j % k} ∈ s.J ∪ {{0, p - 1}} →
      ‖rowSy l i - rowSy l j‖ ≤ cstab)
    (_hm1 : matvec_p4 (pmat1 (vecmats_p4 l)) = l1)
    (_hm2 : matvec_p4 (pmat2 (vecmats_p4 l)) = l2)
    (hv : rowSy l (k - 1) = v) (hw : rowSy l (p - 2) = w) :
    slicef_p8 (E_SY_p4 (vecmatsV3_p4 l)) (F_SY_p4 (vecmatsV3_p4 l)) v w =
      F_SY_p4 (vecmatsV3_p4 l1) := sorry

/-- HOL `SLICEE_EQ_E2_SY` (MTUWLUN.hl:2969): the backward slice edges.
`slicee E F w v = E_SY (vecmats l2)`. -/
theorem SLICEE_EQ_E2_SY (k p : ℕ) (s s1 s2 s3 : StableSy)
    (l : FinVec k 3) (l1 : FinVec p 3) (l2 : FinVec (k - p + 2) 3)
    (hM : 1 ≤ k) (hP : 1 ≤ p) (hkp : 1 ≤ k - p)
    (hIs : s.I = Icc 0 (k - 1)) (hfs : s.f = fun i => (i + 1) % k)
    (hIs1 : s1.I = Icc 0 (p - 1)) (hfs1 : s1.f = fun i => (i + 1) % p)
    (hIs3 : s3.I = Icc 0 (k - p + 1)) (hfs3 : s3.f = fun i => (i + 1) % (k - p + 2))
    (_hear : earSy_p8 s2 ↔ earSy_p8 s3)
    (_hdia : DIA_SY 0 (p - 1) s)
    (_hschg : SCHANGE (fun x => if x = 0 then 0 else (p - 2 + x) % k) s2 s3)
    (_hcov : COVER_SY 0 (p - 1) s s1 s2)
    (_hl : l ∈ B_SY1_p8 s.a s.b)
    (_hcstab : ∀ i j : ℕ, {i % k, j % k} ∈ s.J ∪ {{0, p - 1}} →
      ‖rowSy l i - rowSy l j‖ ≤ cstab)
    (_hm1 : matvec_p4 (pmat1 (vecmats_p4 l)) = l1)
    (_hm2 : matvec_p4 (pmat2 (vecmats_p4 l)) = l2)
    (hv : rowSy l (k - 1) = v) (hw : rowSy l (p - 2) = w) :
    slicee_p8 (E_SY_p4 (vecmatsV3_p4 l)) (F_SY_p4 (vecmatsV3_p4 l)) w v =
      E_SY_p4 (vecmatsV3_p4 l2) := sorry

/-- HOL `SLICEF_EQ_F2_SY` (MTUWLUN.hl:3104): the backward slice darts.
`slicef E F w v = F_SY (vecmats l2)`. -/
theorem SLICEF_EQ_F2_SY (k p : ℕ) (s s1 s2 s3 : StableSy)
    (l : FinVec k 3) (l1 : FinVec p 3) (l2 : FinVec (k - p + 2) 3)
    (hM : 1 ≤ k) (hP : 1 ≤ p) (hkp : 1 ≤ k - p)
    (hIs : s.I = Icc 0 (k - 1)) (hfs : s.f = fun i => (i + 1) % k)
    (hIs1 : s1.I = Icc 0 (p - 1)) (hfs1 : s1.f = fun i => (i + 1) % p)
    (hIs3 : s3.I = Icc 0 (k - p + 1)) (hfs3 : s3.f = fun i => (i + 1) % (k - p + 2))
    (_hear : earSy_p8 s2 ↔ earSy_p8 s3)
    (_hdia : DIA_SY 0 (p - 1) s)
    (_hschg : SCHANGE (fun x => if x = 0 then 0 else (p - 2 + x) % k) s2 s3)
    (_hcov : COVER_SY 0 (p - 1) s s1 s2)
    (_hl : l ∈ B_SY1_p8 s.a s.b)
    (_hcstab : ∀ i j : ℕ, {i % k, j % k} ∈ s.J ∪ {{0, p - 1}} →
      ‖rowSy l i - rowSy l j‖ ≤ cstab)
    (_hm1 : matvec_p4 (pmat1 (vecmats_p4 l)) = l1)
    (_hm2 : matvec_p4 (pmat2 (vecmats_p4 l)) = l2)
    (hv : rowSy l (k - 1) = v) (hw : rowSy l (p - 2) = w) :
    slicef_p8 (E_SY_p4 (vecmatsV3_p4 l)) (F_SY_p4 (vecmatsV3_p4 l)) w v =
      F_SY_p4 (vecmatsV3_p4 l2) := sorry

/-- HOL `TAU_STAR_COVER` (MTUWLUN.hl:3277; hypothesis = `EJRCFJD_concl`
via `mk_imp`, plus the no-collinear side condition): subadditivity of
`tau_star` over the diagonal cover. -/
theorem TAU_STAR_COVER (hEJRCFJD : EJRCFJD_p8) (k p : ℕ) (s s1 s2 s3 : StableSy)
    (l : FinVec k 3) (l1 : FinVec p 3) (l2 : FinVec (k - p + 2) 3)
    (hM : 1 ≤ k) (hP : 1 ≤ p) (hkp : 1 ≤ k - p)
    (hIs : s.I = Icc 0 (k - 1)) (hfs : s.f = fun i => (i + 1) % k)
    (hIs1 : s1.I = Icc 0 (p - 1)) (hfs1 : s1.f = fun i => (i + 1) % p)
    (hIs3 : s3.I = Icc 0 (k - p + 1)) (hfs3 : s3.f = fun i => (i + 1) % (k - p + 2))
    (_hear : earSy_p8 s2 ↔ earSy_p8 s3)
    (_hdia : DIA_SY 0 (p - 1) s)
    (_hschg : SCHANGE (fun x => if x = 0 then 0 else (p - 2 + x) % k) s2 s3)
    (_hcov : COVER_SY 0 (p - 1) s s1 s2)
    (_hl : l ∈ B_SY1_p8 s.a s.b)
    (_hcstab : ∀ i j : ℕ, {i % k, j % k} ∈ s.J ∪ {{0, p - 1}} →
      ‖rowSy l i - rowSy l j‖ ≤ cstab)
    (_hm1 : matvec_p4 (pmat1 (vecmats_p4 l)) = l1)
    (_hm2 : matvec_p4 (pmat2 (vecmats_p4 l)) = l2)
    (hv : rowSy l (k - 1) = v) (hw : rowSy l (p - 2) = w)
    (_hnc : ∀ u u1 : V3, u ∈ ({v, w} : Set V3) →
      u1 ∈ V_SY_p4 (vecmatsV3_p4 l) → u ≠ u1 →
      ¬Collinear ℝ ({0, u, u1} : Set V3)) :
    tauStar_p8 s1 l1 + tauStar_p8 s3 l2 ≤ tauStar_p8 s l := sorry

/-- HOL `IN_B_SY_COVER` (MTUWLUN.hl:3456; hypothesis = `EJRCFJD_concl`):
`l1` stays in the stable-tube, `l1 ∈ B_SY1 (a_sy s1) (b_sy s1)`. -/
theorem IN_B_SY_COVER (hEJRCFJD : EJRCFJD_p8) (k p : ℕ) (s s1 s2 s3 : StableSy)
    (l : FinVec k 3) (l1 : FinVec p 3) (l2 : FinVec (k - p + 2) 3)
    (hM : 1 ≤ k) (hP : 1 ≤ p) (hkp : 1 ≤ k - p)
    (hIs : s.I = Icc 0 (k - 1)) (hfs : s.f = fun i => (i + 1) % k)
    (hIs1 : s1.I = Icc 0 (p - 1)) (hfs1 : s1.f = fun i => (i + 1) % p)
    (hIs3 : s3.I = Icc 0 (k - p + 1)) (hfs3 : s3.f = fun i => (i + 1) % (k - p + 2))
    (_hear : earSy_p8 s2 ↔ earSy_p8 s3)
    (_hdia : DIA_SY 0 (p - 1) s)
    (_hschg : SCHANGE (fun x => if x = 0 then 0 else (p - 2 + x) % k) s2 s3)
    (_hcov : COVER_SY 0 (p - 1) s s1 s2)
    (_hl : l ∈ B_SY1_p8 s.a s.b)
    (_hcstab : ∀ i j : ℕ, {i % k, j % k} ∈ s.J ∪ {{0, p - 1}} →
      ‖rowSy l i - rowSy l j‖ ≤ cstab)
    (_hm1 : matvec_p4 (pmat1 (vecmats_p4 l)) = l1)
    (_hm2 : matvec_p4 (pmat2 (vecmats_p4 l)) = l2)
    (hv : rowSy l (k - 1) = v) (hw : rowSy l (p - 2) = w)
    (_hnc : ∀ u u1 : V3, u ∈ ({v, w} : Set V3) →
      u1 ∈ V_SY_p4 (vecmatsV3_p4 l) → u ≠ u1 →
      ¬Collinear ℝ ({0, u, u1} : Set V3))
    (_hmin : ‖v - w‖ ≤ min (s1.b (p - 1) 0) (s2.b (p - 1) 0)) :
    l1 ∈ B_SY1_p8 s1.a s1.b := sorry

/-- HOL `IN_B_SY2_COVER` (MTUWLUN.hl:4064; hypothesis = `EJRCFJD_concl`):
`l2` stays in the stable-tube, `l2 ∈ B_SY1 (a_sy s3) (b_sy s3)`. -/
theorem IN_B_SY2_COVER (hEJRCFJD : EJRCFJD_p8) (k p : ℕ) (s s1 s2 s3 : StableSy)
    (l : FinVec k 3) (l1 : FinVec p 3) (l2 : FinVec (k - p + 2) 3)
    (hM : 1 ≤ k) (hP : 1 ≤ p) (hkp : 1 ≤ k - p)
    (hIs : s.I = Icc 0 (k - 1)) (hfs : s.f = fun i => (i + 1) % k)
    (hIs1 : s1.I = Icc 0 (p - 1)) (hfs1 : s1.f = fun i => (i + 1) % p)
    (hIs3 : s3.I = Icc 0 (k - p + 1)) (hfs3 : s3.f = fun i => (i + 1) % (k - p + 2))
    (_hear : earSy_p8 s2 ↔ earSy_p8 s3)
    (_hdia : DIA_SY 0 (p - 1) s)
    (_hschg : SCHANGE (fun x => if x = 0 then 0 else (p - 2 + x) % k) s2 s3)
    (_hcov : COVER_SY 0 (p - 1) s s1 s2)
    (_hl : l ∈ B_SY1_p8 s.a s.b)
    (_hcstab : ∀ i j : ℕ, {i % k, j % k} ∈ s.J ∪ {{0, p - 1}} →
      ‖rowSy l i - rowSy l j‖ ≤ cstab)
    (_hm1 : matvec_p4 (pmat1 (vecmats_p4 l)) = l1)
    (_hm2 : matvec_p4 (pmat2 (vecmats_p4 l)) = l2)
    (hv : rowSy l (k - 1) = v) (hw : rowSy l (p - 2) = w)
    (_hnc : ∀ u u1 : V3, u ∈ ({v, w} : Set V3) →
      u1 ∈ V_SY_p4 (vecmatsV3_p4 l) → u ≠ u1 →
      ¬Collinear ℝ ({0, u, u1} : Set V3))
    (_hmin : ‖v - w‖ ≤ min (s1.b (p - 1) 0) (s2.b (p - 1) 0)) :
    l2 ∈ B_SY1_p8 s3.a s3.b := sorry

end Kepler.Text
