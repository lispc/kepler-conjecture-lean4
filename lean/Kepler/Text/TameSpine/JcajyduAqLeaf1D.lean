/-
  Kepler.Text.TameSpine.JcajyduAqLeaf1D — AQ1 叶第四批：`new1 × new2`（窗口）互不交。

  `new1` 的元素都是窗口 dart 的 `nodeMap` 正幂（`1 ≤ i ≤ ncard−1`），
  `new2`（窗口）是同一面表的 dart；两同一元素 ⇒ 该元素同时在
  `node x ∩ face x`，Simple 塌出它 `= x`，撞 `nodeMap^i x ≠ x`（`injOrbit`）。

  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf1C

namespace Kepler.Text.TameSpine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Kepler.Assembly (nextEl prevEl eList fList GoodList findFaceDarts nList
  listOfDarts listPairs)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nextEl_mem_of_mem prevEl_mem_of_mem)

/-- **`new1 × new2` 互不交**（窗口内两块不相交）。 -/
theorem aq1d_new1DisjNew2 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ∀ d ∈ ((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x)).map (ndSpine L)).flatten,
      ∀ e ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x), d ≠ e := by
  intro d hd e he hde
  -- d = (nList L)^[i] x₀，x₀ ∈ 窗口，i ∈ range' 1 (sz−1)
  obtain ⟨blk, hblk, hdmem⟩ := List.mem_flatten.mp hd
  obtain ⟨x0, hx0, rfl⟩ := List.mem_map.mp hblk
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hdmem
  obtain ⟨i', hi'lt, rfl⟩ := List.mem_range'.mp hi
  have hyr : lYSpine L r x ∈ listOfDarts L := memYtransListOfDarts L hL hgn hm hf
  have hx0dL : x0 ∈ listOfDarts L := mem_darts_of_mem_findFace L (memBetweenOfMem hx0)
  have hx0D : x0 ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hx0dL
  -- e = d ∈ node x0（nodeMap 正幂）
  have hpow : (nList L)^[1 + 1 * i'] x0
      = ((hypermapOfList L hL).nodeMap ^ (1 + 1 * i')) x0 :=
    nListPowEqNodeMapPow L hL hx0dL (1 + 1 * i')
  have hdn : ((nList L)^[1 + 1 * i'] x0) ∈ (hypermapOfList L hL).node x0 := by
    rw [hpow]
    exact (hypermapOfList L hL).pow_nodeMap_mem_node x0 (1 + 1 * i')
  -- e = d ∈ face x0（窗口同面表）
  have hface : e ∈ (hypermapOfList L hL).face x0 := by
    have hfst : e ∈ (hypermapOfList L hL).face (lYSpine L r x) :=
      Kepler.Text.TameCorrCard.faceTableSubset hL hyr (memBetweenOfMem he)
    have hx0face : x0 ∈ (hypermapOfList L hL).face (lYSpine L r x) :=
      Kepler.Text.TameCorrCard.faceTableSubset hL hyr (memBetweenOfMem hx0)
    have hEq : (hypermapOfList L hL).face (lYSpine L r x)
        = (hypermapOfList L hL).face x0 :=
      (hypermapOfList L hL).face_eq_of_mem hx0face
    rw [← hEq]
    exact hfst
  -- Simple 塌缩 ⇒ d = x0
  have hsimple := simpleHypermapList L hL hgn hunL
  have hinter : ((nList L)^[1 + 1 * i'] x0) ∈ (hypermapOfList L hL).node x0
      ∩ (hypermapOfList L hL).face x0 := ⟨hdn, by rw [hde]; exact hface⟩
  rw [hsimple x0 hx0D] at hinter
  have heq : ((nList L)^[1 + 1 * i'] x0) = x0 := Set.mem_singleton_iff.mp hinter
  -- 撞 nodeMap 正幂 ≠ 自身（injOrbit）
  have hsz : ((hypermapOfList L hL).node x0).ncard
      = (L.flatten.filter (fun t => decide (t = x0.1))).length :=
    (szEqNodeCard L hL hgn hx0D).symm
  have h2 : 2 ≤ (L.flatten.filter (fun t => decide (t = x0.1))).length :=
    two_le_sz_of_restricted L hL hgn hm.1.1 hx0D
  have hpoweq : ((hypermapOfList L hL).nodeMap ^ (1 + 1 * i')) x0
      = ((hypermapOfList L hL).nodeMap ^ 0) x0 := by
    rw [pow_zero, Equiv.Perm.coe_one, id_eq]
    rw [← hpow]
    exact heq
  have hsz' : ((hypermapOfList L hL).node x0).ncard
      = (Kepler.Text.orbitMap (hypermapOfList L hL).nodeMap x0).ncard := rfl
  have hinj := (hypermapOfList L hL).nodeMap_permutes.injOrbit_of_lt_ncard
    (x := x0) (m := (Kepler.Text.orbitMap (hypermapOfList L hL).nodeMap x0).ncard - 1)
    (by rw [← hsz']; omega)
  have hbound : 1 + 1 * i'
      ≤ (Kepler.Text.orbitMap (hypermapOfList L hL).nodeMap x0).ncard - 1 := by
    rw [← hsz']; omega
  have hzero := (injOrbit_iff_pairwise (hypermapOfList L hL).nodeMap x0
    ((Kepler.Text.orbitMap (hypermapOfList L hL).nodeMap x0).ncard - 1)).mp hinj
    (1 + 1 * i') 0 hbound (by omega) hpoweq
  omega

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq1d_new1DisjNew2
