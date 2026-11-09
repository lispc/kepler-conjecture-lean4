/-
  Kepler.Text.TameSpine.JcajyduAqSplit1D — E4d-a-1：`f_last split.1` 的
  **共享子树 ⓒ1**（"窗口 darts 首点不进 flatten N / z1 ∉ new1"）。

  件目（5 件，全真证）：
  ① `fListPowYtransNotMemFlatten`（AQ1.hl:261 `f_list_power_ytrans_not_mem_flatten_v0`）：
     `j < l'p → (fList)^[j+1] (l'y) ∉ flatten N`——`l'p` 的 min_num 极小性直投（6 行）；
  ② `nodeEqFstSet`（`GoodListNodesTl` 的 node 首点刻画）：
     `node d = {d' ∈ darts | d'.1 = d.1}`；
  ③ `ndSpineFstEq`：`x' ∈ nd x → x'.1 = x.1`（node 幂同首点）；
  ④ `windowFstNotMemNFlatten`（HOL `betwn_not_in_fst_flatten` AQ1.hl:1247 的 Lean 内核）：
     `d ∈ betwn f y z → d.1 ∉ flatten N 的首点表`——`indexfBetwn` 给 d 是
     `f^j y`（j < l'p）故 d ∉ flatten N（①），而 `d1.1 = d.1`（d1 ∈ flatten N）
     会经 ② 得 `d ∈ node d1`、再经 normal_list 的 node 闭包得 d ∈ flatten N，矛盾；
  ⑤ `z1NotMemNew1`（HOL AQ1:1434-:1448 的 Lean 内核）：`z1 ∉ new1`——
     new1 元素是窗口 darts 的 node 幂（③），其首点 ∉ flatten N 首点表（④）；
     而 `z1 ∈ r ⊆ flatten N`。

  **边界（BLOCKED，见 DELIVERY 续 §E4d）**：`f_last split.1` 还剩
  ⓤ1 `z1 ∉ f1.dropLast`（**新发现需要 `nextEl r y ≠ prevEl r z`**——E4d 原估 30-45
  漏了这一支，HOL 靠 `FST_EQ_NEXT_YTRANS`/`FST_EQ_PREV_ZTRANS` + `QRDYXYJ_list`
  的 `FST y ≠ FST z`；替代证法需 `(fList d).1 = d.2` + 同面首点互异两件）、
  ⓤ2 `idxOf` 收口、ⓑ `d1 = eList z1`、f_last 接线（含空窗支与 `ra = z1` 支）。
  本批只交共享子树（编排者授权口径：ⓒ1 单交）。

  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameSpine.JcajyduAqSplit1C

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

/-- **HOL `f_list_power_ytrans_not_mem_flatten_v0`**（AQ1.hl:261）：
`j < l'p → (f_list)^[j+1] (l'y) ∉ flatten N`——`l'p` 的 min_num 极小性
（`l'p` 的定义集就是 `{p | (fList)^[p+1] l'y ∈ N.flatten}`）。 -/
theorem fListPowYtransNotMemFlatten (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) :
    ∀ j : ℕ, j < lPSpine L N r x → (fList L)^[j + 1] (lYSpine L r x) ∉ N.flatten := by
  intro j hj hmem
  have hle : lPSpine L N r x ≤ j := Nat.sInf_le hmem
  omega

/-- **node 的首点刻画**（`GoodListNodesTl` 的 `nodesOfListSet` 展开）：
`node d = {d' ∈ darts | d'.1 = d.1}`（d ∈ darts）。 -/
theorem nodeEqFstSet (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {d : ℕ × ℕ} (hd : d ∈ (hypermapOfList L hL).darts) :
    (hypermapOfList L hL).node d
      = {d' : ℕ × ℕ | d' ∈ listOfDarts L ∧ d'.1 = d.1} := by
  set H := hypermapOfList L hL
  have hmem : H.node d ∈ H.nodeSet := ⟨d, hd, rfl⟩
  rw [hgn] at hmem
  obtain ⟨v, _hv, hveq⟩ := hmem
  have hveq' : {d' : ℕ × ℕ | d' ∈ listOfDarts L ∧ d'.1 = v} = H.node d := hveq
  have hdv : d.1 = v := by
    have hd' : d ∈ {d' : ℕ × ℕ | d' ∈ listOfDarts L ∧ d'.1 = v} := by
      rw [hveq']
      exact Kepler.Text.Hypermap.mem_node_self H d
    exact hd'.2
  rw [← hveq', hdv]

/-- `ndSpine` 的元素与生成元同首点（node = 同首点 dart 集）。 -/
theorem ndSpineFstEq (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {x x' : ℕ × ℕ} (hx : x ∈ (hypermapOfList L hL).darts)
    (hx' : x' ∈ ndSpine L x) : x'.1 = x.1 := by
  rw [ndSpine] at hx'
  obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hx'
  have hnode : (nList L)^[i] x ∈ (hypermapOfList L hL).node x :=
    ⟨i, (nListPowEqNodeMapPow L hL (List.mem_toFinset.mp hx) i).symm⟩
  rw [nodeEqFstSet L hL hgn hx] at hnode
  exact hnode.2

/-- **窗口 darts 的首点不进 `flatten N` 的首点表**（HOL `betwn_not_in_fst_flatten`，
AQ1.hl:1247 的 Lean 内核）：若 `d.1 = d1.1`（d1 ∈ flatten N），则 d ∈ node d1
（node 首点刻画）→ normal_list 的 node 闭包给 d ∈ flatten N，与
`fListPowYtransNotMemFlatten` 在 `j = indexf y d f − 1` 处矛盾。 -/
theorem windowFstNotMemNFlatten (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {d : ℕ × ℕ}
    (hd : d ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)) :
    d.1 ∉ (N.flatten).map Prod.fst := by
  intro hfst
  have hyd : lYSpine L r x ∈ listOfDarts L := memYtransListOfDarts L hL hgn hm hf
  have hyf : lYSpine L r x ∈ findFaceDarts L (lYSpine L r x) :=
    (dart_in_face L _).mpr hyd
  have hzf : lZSpine L N r x ∈ findFaceDarts L (lYSpine L r x) :=
    zMemFindFaceDarts L hL hgn hunL hm hf
  have hfnd : (findFaceDarts L (lYSpine L r x)).Nodup := findFaceDarts_nodup hL.1 _
  have hne : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hdf : d ∈ findFaceDarts L (lYSpine L r x) := memBetweenOfMem hd
  have hpos : 0 < indexf (lYSpine L r x) d (findFaceDarts L (lYSpine L r x)) :=
    (indexfBetwn hne hfnd hyf hzf hd).1
  have hlt : indexf (lYSpine L r x) d (findFaceDarts L (lYSpine L r x))
      < lPSpine L N r x + 1 := by
    have h2 := (indexfBetwn hne hfnd hyf hzf hd).2
    rwa [indexfYtransSucLp L hL hgn hunL hm hf] at h2
  obtain ⟨d1, hd1, hd1fst⟩ := List.mem_map.mp hfst
  have hd1darts : d1 ∈ (hypermapOfList L hL).darts :=
    List.mem_toFinset.mpr (normalListListOfDarts hm.1.2.1 d1 hd1)
  have hdnode : d ∈ (hypermapOfList L hL).node d1 := by
    rw [nodeEqFstSet L hL hgn hd1darts]
    exact ⟨mem_darts_of_mem_findFace L hdf, hd1fst.symm⟩
  have hdN : d ∈ N.flatten := hm.1.2.1.2.2.2.2 d1 hd1 hdnode
  have hdpow : d = (fList L)^[indexf (lYSpine L r x) d
      (findFaceDarts L (lYSpine L r x))] (lYSpine L r x) := by
    rw [fListPowEqNextElPow L hL (lYSpine L r x) hyf]
    exact (indexfN hyf hdf hfnd).symm
  have hnot := fListPowYtransNotMemFlatten L hL hm
    (indexf (lYSpine L r x) d (findFaceDarts L (lYSpine L r x)) - 1) (by omega)
  apply hnot
  rwa [show indexf (lYSpine L r x) d (findFaceDarts L (lYSpine L r x)) - 1 + 1
      = indexf (lYSpine L r x) d (findFaceDarts L (lYSpine L r x)) from by omega, ← hdpow]

/-- **`z1 ∉ new1`**（HOL AQ1:1434-:1448 的 Lean 内核）：new1 的元素是窗口 darts
的 node 幂（同首点），窗口首点不进 `flatten N` 首点表；而 `z1 ∈ r ⊆ flatten N`。 -/
theorem z1NotMemNew1 (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    prevEl r (lZSpine L N r x) ∉
      ((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x)).map (ndSpine L)).flatten := by
  intro hmem
  obtain ⟨blk, hblk, hin⟩ := List.mem_flatten.mp hmem
  obtain ⟨dd, hdd, rfl⟩ := List.mem_map.mp hblk
  have hddart : dd ∈ (hypermapOfList L hL).darts :=
    List.mem_toFinset.mpr (mem_darts_of_mem_findFace L (memBetweenOfMem hdd))
  have hfsteq : (prevEl r (lZSpine L N r x)).1 = dd.1 :=
    ndSpineFstEq L hL hgn hddart hin
  have hwin : dd.1 ∉ (N.flatten).map Prod.fst :=
    windowFstNotMemNFlatten L hL hgn hunL hm hf hdd
  have hz1r : prevEl r (lZSpine L N r x) ∈ r :=
    prevEl_mem_of_mem (zMemRtransClean L hL hgn hunL hm hf)
  have hz1N : prevEl r (lZSpine L N r x) ∈ N.flatten :=
    List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hz1r⟩
  have hz1map : (prevEl r (lZSpine L N r x)).1 ∈ (N.flatten).map Prod.fst :=
    List.mem_map.mpr ⟨_, hz1N, rfl⟩
  exact hwin (by simpa [hfsteq] using hz1map)

end Kepler.Text.TameSpine

#print axioms Kepler.Text.TameSpine.fListPowYtransNotMemFlatten
#print axioms Kepler.Text.TameSpine.nodeEqFstSet
#print axioms Kepler.Text.TameSpine.ndSpineFstEq
#print axioms Kepler.Text.TameSpine.windowFstNotMemNFlatten
#print axioms Kepler.Text.TameSpine.z1NotMemNew1
