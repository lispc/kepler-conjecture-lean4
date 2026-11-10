/-
  Kepler.Text.Reduction1W2d — J4 Wave W2 批 1d：`all_some_generatePolygon`
  （HOL reduction1.hl:1433-1573）。

  路线（冻结包 `DELIVERY_W2E_ASGP2.md` §1-§4 收口）：
  §0 基座 `rotateToEqRotate`（HOL `Pwssrat.rotate_rot_indexl` 的 Lean 形）+
  `listPairs` 的 zip 形；§1 `lastRotateTo`（HOL `prev_el_rot_eq` + `prev_el_hd`
  合用形）；§2 `indexfRotateEq`（HOL `indexf_rotn` + `indexf_hd`）；§3
  `memListPairsRotateTo`（HOL `List_hypermap.rot_list_pairs`，走
  `zipWith_rotate_distrib`，比冻结包 §2 预案的 `is_nextElem` 路线更直）；
  §4 主定理 12 槽总装（消费 `generatePolygonCriteria`，`cb0286d3`）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
  （N1/N2/N3 相对冻结包陈述各加一条 `hnd : F.Nodup`：主定理七前提含
  `∀ l ∈ g.fgraph, l.Nodup`，对 `f.vertices` 直投即可；HOL 对应件
  `rotate_rot_indexl` 本就带 `uniq`。）
-/
import Kepler.Text.Reduction1W2a
import Kepler.Text.Reduction1W2b
import Kepler.Text.Reduction3DefsNewVertex

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (listOfDarts listPairs prevEl)
open Kepler.Graphs (Graph Face generatePolygon subdivFace)
open Kepler.Text.TameCorrList (GoodFacesV3 VerticesSet2Eq)
open Kepler.Text.TameSpine (indexf rotateTo)

/-! ## §0 基座：两库 `rotateTo` 桥 + `rotate_rot_indexl` + `listPairs` zip 形 -/

/-- 两库 `rotate_to`（`TameSpine.rotateTo` 与 `Reduction3.rotateTo`）按定义同值
（`::` 对 `++` 的 `List.cons_append` 即定义性）。 -/
theorem rotateToBridge {α : Type} [BEq α] (vs : List α) (v : α) :
    Kepler.Text.Reduction3.rotateTo vs v = rotateTo vs v := rfl

/-- `idxOf` 在精确分解下的值（`splitAtSpec` 分解 + Nodup 下标单射定位）。 -/
private theorem idxOfSplitSpec {α : Type} [BEq α] [LawfulBEq α] {bef aft : List α} {v : α}
    (hnd : (bef ++ v :: aft).Nodup) : (bef ++ v :: aft).idxOf v = bef.length := by
  have hb : bef.length < (bef ++ v :: aft).length := by simp
  have hget : (bef ++ v :: aft)[bef.length] = v := by simp
  have h1 := hnd.idxOf_getElem bef.length hb
  rw [hget] at h1
  exact h1

/-- **HOL `Pwssrat.rotate_rot_indexl`**（`MEM v vs ∧ uniq vs ⇒
rotate_to vs v = rot (indexl v vs) vs`）。 -/
theorem rotateToEqRotate {α : Type} [BEq α] [LawfulBEq α] {vs : List α} {v : α}
    (hv : v ∈ vs) (hnd : vs.Nodup) : rotateTo vs v = vs.rotate (vs.idxOf v) := by
  obtain ⟨bef, aft, hdec⟩ : ∃ bef aft, Kepler.Graphs.splitAt v vs = (bef, aft) :=
    ⟨_, _, rfl⟩
  have hspec : vs = bef ++ v :: aft := splitAtSpec hdec hv
  subst hspec
  have hrt : rotateTo (bef ++ v :: aft) v = v :: (aft ++ bef) := by
    simp only [Kepler.Text.TameSpine.rotateTo, hdec]
  rw [hrt, idxOfSplitSpec hnd, List.rotate_append_length_eq]
  rfl

/-- `listPairs` 的 zip 形：`l.drop 1 ++ l.take 1` 即 `l.rotate 1`。 -/
theorem listPairsEqZip {α : Type} (l : List α) :
    listPairs l = List.zipWith Prod.mk l (l.rotate 1) := by
  unfold Kepler.Assembly.listPairs
  rw [List.zip_eq_zipWith]
  cases l with
  | nil => simp [List.rotate]
  | cons a t =>
    have hr : (a :: t).rotate 1 = t ++ [a] := by
      rw [List.rotate_cons_succ, List.rotate_zero]
    rw [hr, List.drop_cons (by omega : (0 : ℕ) < 1),
      List.take_cons (by omega : (0 : ℕ) < 1), List.drop_zero, List.take_zero]

/-! ## §1 N1：`prev_el F v = LAST (rotate_to F v)` -/

/-- `getD` 的右半（下标越左段）。 -/
private theorem getDAppendRight {l₁ l₂ : List Nat} {d n : Nat} (h : l₁.length ≤ n) :
    (l₁ ++ l₂).getD n d = l₂.getD (n - l₁.length) d := by
  induction l₁ generalizing n with
  | nil => simp
  | cons a t ih =>
    cases n with
    | zero => exact absurd h (by simp)
    | succ n' =>
      rw [List.cons_append, List.getD_cons_succ, ih (by
          have h' := h
          simp only [List.length_cons] at h'
          omega)]
      simp only [List.length_cons]
      have hidx : n' + 1 - (t.length + 1) = n' - t.length := by omega
      rw [hidx]

/-- `getLastD` 末位下标形（非空表：回落值无关）。 -/
private theorem getLastDNe : ∀ (l : List Nat), l ≠ [] → ∀ (x y : Nat),
    l.getLastD x = l.getD (l.length - 1) y := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons a t ih =>
    intro _ x y
    cases t with
    | nil => simp
    | cons b t' =>
      have hlenL : (b :: t').length - 1 = t'.length := by simp
      have hlenR : (a :: b :: t').length - 1 = t'.length + 1 := by simp
      rw [List.getLastD_cons, ih (List.cons_ne_nil b t') a y, hlenL, hlenR,
        List.getD_cons_succ]

/-- **N1**（HOL `prev_el_rot_eq` + `prev_el_hd` 合用形）：`MEM v F ∧ uniq F ⇒
prev_el F v = LAST (rotate_to F v)`。 -/
theorem lastRotateTo {F : List Nat} {v : Nat} (hv : v ∈ F) (hnd : F.Nodup) :
    prevEl F v = (rotateTo F v).getLast! := by
  obtain ⟨bef, aft, hdec⟩ : ∃ bef aft, Kepler.Graphs.splitAt v F = (bef, aft) :=
    ⟨_, _, rfl⟩
  have hspec : F = bef ++ v :: aft := splitAtSpec hdec hv
  subst hspec
  rw [prevEl, if_neg (not_not.mpr hv), idxOfSplitSpec hnd]
  simp only [Kepler.Text.TameSpine.rotateTo, hdec, List.getLast!_cons_eq_getLastD]
  by_cases hbe : bef = []
  · subst hbe
    rw [List.nil_append, List.length_nil, if_pos rfl, List.getLastD_cons,
      List.append_nil]
  · have hbl : bef.length ≠ 0 := by
      intro hc
      exact hbe (List.length_eq_zero_iff.mp hc)
    rw [if_neg hbl]
    rw [List.getD_append bef (v :: aft) v (bef.length - 1) (by omega)]
    rw [getLastDNe (aft ++ bef) (by simp [hbe]) v v]
    have hlen : aft.length ≤ (aft ++ bef).length - 1 := by
      simp only [List.length_append]; omega
    rw [getDAppendRight hlen]
    simp only [List.length_append]
    have hidx : aft.length + bef.length - 1 - aft.length = bef.length - 1 := by omega
    rw [hidx]

/-! ## §2 N2：`indexf v (rotate_to F v)[i]! F = i` -/

/-- `i < |l| ⇒ l[i]! = l[i]`（`!` 换装）。 -/
private theorem getElem!OfLt {l : List Nat} {i : Nat} (h : i < l.length) :
    l[i]! = l[i] := by
  induction l generalizing i with
  | nil => exact absurd h (Nat.not_lt_zero i)
  | cons a t ih =>
    cases i with
    | zero => rfl
    | succ i' =>
      have h' : i' < t.length := by
        simp only [List.length_cons] at h; omega
      rw [List.getElem!_cons_succ, List.getElem_cons_succ, ih h']

/-- `i < |l| ⇒ l[i]? = some l[i]!`（`?` 换装，避开依赖式下标重写）。 -/
private theorem getElemOptEqSome {l : List Nat} {i : Nat} (h : i < l.length) :
    l[i]? = some l[i]! := by
  rw [List.getElem?_eq_some_iff]
  exact ⟨h, (getElem!OfLt h).symm⟩

/-- **N2**（HOL `indexf_rotn` + `indexf_hd` 合用形）：`MEM v F ∧ uniq F ∧ i < |F| ⇒
indexf v (rotate_to F v)[i]! F = i`。 -/
theorem indexfRotateEq {F : List Nat} {v : Nat} (hv : v ∈ F) (hnd : F.Nodup) :
    ∀ i, i < F.length → indexf v (rotateTo F v)[i]! F = i := by
  have hk : F.idxOf v < F.length := List.idxOf_lt_length_iff.mpr hv
  intro i hi
  rw [rotateToEqRotate hv hnd]
  have hilt : i < (F.rotate (F.idxOf v)).length := by
    rw [List.length_rotate]; exact hi
  rw [getElem!OfLt hilt, List.getElem_rotate F (F.idxOf v) i hilt]
  have hmodlt : (i + F.idxOf v) % F.length < F.length := Nat.mod_lt _ (by omega)
  have hu : F[(i + F.idxOf v) % F.length] ∈ F := List.getElem_mem hmodlt
  simp only [indexf, if_pos (show v ∈ F ∧ F[(i + F.idxOf v) % F.length] ∈ F
    from ⟨hv, hu⟩)]
  rw [hnd.idxOf_getElem _ hmodlt, Nat.mod_add_mod]
  have hsum : (i + F.idxOf v) + (F.length - F.idxOf v) = i + F.length := by omega
  rw [hsum, Nat.add_comm i F.length, Nat.add_mod_left, Nat.mod_eq_of_lt hi]

/-! ## §3 N3：`list_pairs` 旋转不变 -/

/-- **N3**（HOL `List_hypermap.rot_list_pairs`）：`MEM v F ∧ uniq F ⇒
MEM d (list_pairs (rotate_to F v)) ↔ MEM d (list_pairs F)`。 -/
theorem memListPairsRotateTo {F : List Nat} {v : Nat} (hv : v ∈ F) (hnd : F.Nodup)
    {d : Nat × Nat} :
    d ∈ listPairs (rotateTo F v) ↔ d ∈ listPairs F := by
  rw [rotateToEqRotate hv hnd, listPairsEqZip, listPairsEqZip, List.rotate_rotate,
    Nat.add_comm (F.idxOf v) 1, ← List.rotate_rotate F 1 (F.idxOf v),
    ← List.zipWith_rotate_distrib Prod.mk F (F.rotate 1) (F.idxOf v)
      (by rw [List.length_rotate]), List.mem_rotate]

/-! ## §4 主定理 `all_some_generatePolygon` -/

/-- `i < |l| ⇒ (l.map Option.some)[i]! = some l[i]!`。 -/
private theorem getElem!mapSome {l : List Nat} {i : Nat} (h : i < l.length) :
    (l.map Option.some)[i]! = Option.some l[i]! := by
  induction l generalizing i with
  | nil => exact absurd h (Nat.not_lt_zero i)
  | cons a t ih =>
    cases i with
    | zero => rfl
    | succ i' =>
      have h' : i' < t.length := by
        simp only [List.length_cons] at h; omega
      rw [List.map_cons, List.getElem!_cons_succ, List.getElem!_cons_succ, ih h']

/-- `i < |l| ⇒ (l.map Option.some)[i]!.getD 0 = l[i]!`（P19 槽的换装）。 -/
private theorem getElem!mapSomeD {l : List Nat} {i : Nat} (h : i < l.length) :
    (l.map Option.some)[i]!.getD 0 = l[i]! := by
  rw [getElem!mapSome h]
  simp only [Option.getD_some]

private theorem filterMapSome (l : List Nat) :
    (l.map Option.some).filter Option.isSome = l.map Option.some := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

private theorem mapSomeGet (l : List Nat) :
    (l.map Option.some).map Option.get! = l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

/-- **HOL `all_some_generatePolygon`**（reduction1.hl:1433-1445）：
`vs = MAP SOME (rotate_to (FST f) v)` 等七前提 ⇒
`MEM (subdivFace g f vs) (generatePolygon (sizel vs) v f g)`。
（HOL 那条 `all (\t. MEM t (FST f)) (MAP the (filter isSome vs))` 由
`vs = MAP SOME (rotate_to …)` 自动成立，见 `filterMapSome`/`mapSomeGet`。） -/
theorem allSomeGeneratePolygon {g : Graph} {f : Face} {v : Nat} {vs : List (Option Nat)}
    (hvs : vs = (Kepler.Text.Reduction3.rotateTo f.vertices v).map Option.some)
    (h3 : 3 ≤ f.vertices.length)
    (hv : v ∈ f.vertices)
    (hfm : f.vertices ∈ g.fgraph) (hun : ∀ l ∈ g.fgraph, l.Nodup)
    (hgf : GoodFacesV3 g) (hvs2 : VerticesSet2Eq g) :
    subdivFace g f vs ∈ generatePolygon vs.length v f g := by
  have hnd : f.vertices.Nodup := hun f.vertices hfm
  subst hvs
  rw [rotateToBridge]
  -- 此后 `vs` 即 `L.map Option.some`，`L := rotateTo f.vertices v`
  have hlenL : ((rotateTo f.vertices v).map Option.some).length = f.vertices.length := by
    rw [List.length_map, sizeRotateTo hv hnd]
  have hcons : rotateTo f.vertices v =
      v :: ((Kepler.Graphs.splitAt v f.vertices).2 ++
        (Kepler.Graphs.splitAt v f.vertices).1) := rfl
  have hlast?L : (rotateTo f.vertices v).getLast? =
      Option.some (rotateTo f.vertices v).getLast! := by
    rw [hcons, List.getLast?_cons, List.getLast!_cons_eq_getLastD,
      List.getLastD_eq_getLast?]
  have hlastVs : ((rotateTo f.vertices v).map Option.some).getLast! =
      Option.some (rotateTo f.vertices v).getLast! := by
    apply List.getLast!_of_getLast?
    rw [List.getLast?_map, hlast?L]
    simp only [Option.map_some]
  refine generatePolygonCriteria (vs' := rotateTo f.vertices v) ?_ ?_ ?_ ?_ ?_ hfm hun
    hgf hvs2 ?_ ?_ ?_
  · -- 槽 1 `hvs'`：filter/map 消去
    rw [filterMapSome, mapSomeGet]
  · -- 槽 2 `h3`：`3 ≤ vs.length`
    rw [hlenL]; exact h3
  · -- 槽 3 `hhd`：头元（`hd_rotate_to`）
    rw [List.head!_eq_head?_getD, List.head?_map, hcons, List.head?_cons]
    rfl
  · -- 槽 4 `hlastSome`：全 some
    simp only [hlastVs, Option.isSome_some]
  · -- 槽 5 `hprev`：N1
    simp only [hlastVs, Option.getD_some]
    exact lastRotateTo hv hnd
  · -- 槽 10 `hall`：成员（`mem_rotate_to2`）
    intro t ht
    rw [filterMapSome, mapSomeGet] at ht
    exact (memRotateTo2 hv hnd).mpr ht
  · -- 槽 11 `hmono`：N2（hmono 槽的下标界在 vs' 上）
    intro i hi
    have hLL : (rotateTo f.vertices v).length = f.vertices.length :=
      sizeRotateTo hv hnd
    rw [indexfRotateEq hv hnd i (by omega), indexfRotateEq hv hnd (i + 1) (by omega)]
    exact Nat.lt_succ_self i
  · -- 槽 12 `hP19`：N3（内部相邻对旋转保持）
    intro i hi hs1 hs2 hdart
    rw [hlenL] at hi
    have hil : i < f.vertices.length := by omega
    have hLL : (rotateTo f.vertices v).length = f.vertices.length :=
      sizeRotateTo hv hnd
    have hilt : i < (rotateTo f.vertices v).length := by omega
    have hilt1 : i + 1 < (rotateTo f.vertices v).length := by omega
    rw [getElem!mapSomeD hilt, getElem!mapSomeD hilt1]
    have hpair : ((rotateTo f.vertices v)[i]!, (rotateTo f.vertices v)[i + 1]!)
        ∈ listPairs (rotateTo f.vertices v) := by
      rw [listPairsEqZip]
      refine List.mem_of_getElem? (i := i) ?_
      rw [List.getElem?_zipWith_eq_some]
      refine ⟨_, _, getElemOptEqSome hilt, ?_, rfl⟩
      rw [List.getElem?_eq_some_iff]
      refine ⟨by rw [List.length_rotate]; exact hilt, ?_⟩
      rw [List.getElem_rotate, ← getElem!OfLt (Nat.mod_lt _ (by omega)),
        Nat.mod_eq_of_lt hilt1]
    exact (memListPairsRotateTo hv hnd).mp hpair

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.rotateToBridge
#print axioms Kepler.Text.Reduction1.listPairsEqZip
#print axioms Kepler.Text.Reduction1.rotateToEqRotate
#print axioms Kepler.Text.Reduction1.lastRotateTo
#print axioms Kepler.Text.Reduction1.indexfRotateEq
#print axioms Kepler.Text.Reduction1.memListPairsRotateTo
#print axioms Kepler.Text.Reduction1.allSomeGeneratePolygon
