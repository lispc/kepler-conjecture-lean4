/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12W — AQ12 叶 W-F3c-ii（decl 62 装配）。

  HOL：AQ12.hl:3236-:3496（261 行）`cat_fst_split_normal_parts`：
  `parts L (FST split) = rev(map block 窗口) ++ parts L f1`。

  件目：1 件 / 1 文件；估 100–160（≤280）。
  装配：`split1Unfold`（FST = g ++ f1）+ `partsCat`（junction 支：
  `nextEl r (g.getLast!) ≠ fList (eList (g.getLast!))`，由
  `eList (g.getLast!) = l'Y` + `nextRNotEqF` 直取，**无需 HOL 的 y1=z1 三支**）
  + `aq12v_partsNew1Rev`（12V）+ 块形改写 `(ndSpine d).reverse`。
  不吃 h4。

  纪律：零 sorry/admit/native_decide/axiom；既有文件零触碰；主仓 tracked 零改动。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12V

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts eList fList nList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList dart_in_face mem_darts_of_mem_findFace
  findFaceDarts_nodup prevEl_nextEl nextEl_mem_of_mem)

/-! ## §0 块/表私件 -/

private theorem aq12w_getLast!_reverse {α : Type*} [Inhabited α] {l : List α} (h : l ≠ []) :
    l.reverse.getLast! = l.head! := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_reverse, List.head!_eq_head?_getD]

private theorem aq12w_range'NeNil {k : ℕ} (hk : 0 < k) : List.range' 1 k ≠ [] := by
  intro h0
  have hlen : (List.range' 1 k).length = k := List.length_range'
  rw [h0] at hlen
  simp at hlen
  omega

private theorem aq12w_range'_head! {k : ℕ} (hk : 0 < k) : (List.range' 1 k).head! = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [List.range'_succ, List.head!_cons]

private theorem aq12w_headFlattenMap {α : Type*} [Inhabited α] {W : List (List α)}
    (hne : W ≠ []) (hall : ∀ l ∈ W, l ≠ []) : W.flatten.head! = W.head!.head! := by
  cases W with
  | nil => exact absurd rfl hne
  | cons b bs =>
    have hb : b ≠ [] := hall b (List.mem_cons_self ..)
    rw [List.flatten_cons, List.head!_append _ hb, List.head!_cons]

/-- `ndSpine` 块非空（`0 < count-1`）。 -/
private theorem aq12w_ndSpineNe (L : fgraph ℕ) (d : ℕ × ℕ)
    (hk : 0 < (L.flatten.filter (fun t => decide (t = d.1))).length - 1) :
    ndSpine L d ≠ [] := by
  intro h0
  have hlen : (ndSpine L d).length
      = (L.flatten.filter (fun t => decide (t = d.1))).length - 1 := by
    rw [ndSpine, List.length_map, List.length_range']
  rw [h0] at hlen
  have hlen0 : 0 = (L.flatten.filter (fun t => decide (t = d.1))).length - 1 := by
    simpa using hlen
  omega

/-- `ndSpine` 块首 = `nList d`（`0 < count-1`）。 -/
private theorem aq12w_ndSpineHead (L : fgraph ℕ) (d : ℕ × ℕ)
    (hk : 0 < (L.flatten.filter (fun t => decide (t = d.1))).length - 1) :
    (ndSpine L d).head! = nList L d := by
  rw [ndSpine, hdMap _ _ (aq12w_range'NeNil hk), aq12w_range'_head! hk,
    Function.iterate_one]

/-! ## §1 decl 62 装配 -/

/-- **HOL `cat_fst_split_normal_parts`**（AQ12.hl:3236-:3496）：
FST split 的 parts = 窗口块（反序）++ f1 的 parts。 -/
theorem aq12w_catFstSplitNormalParts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    partsSpine L (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).1
      = ((between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
          (fun d => (ndSpine L d).reverse)).reverse
        ++ partsSpine L ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
            (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]) := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hpp := pplhuljV0 L hL hgn hunL hm hf
  have hyf : lYSpine L r x ∈ findFaceDarts L x := hpp.1
  have hzf : lZSpine L N r x ∈ findFaceDarts L x := hpp.2.1
  have hyz : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hfnd : (findFaceDarts L x).Nodup := findFaceDarts_nodup hL.1 x
  have hface : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
    aq10_memFindFaceImpFacesEq hL.1 hyf
  have hnextz1 : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hrnd _
  -- FST = g ++ f1（g = 窗口块展平反序）
  have hdecomp : (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
      (prevEl r (lZSpine L N r x))).1
      = (((between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
          (fun d => (List.range' 1 ((L.flatten.filter (fun t => decide (t = d.1))).length - 1)).map
            (fun i => (nList L)^[i] d))).flatten).reverse
        ++ ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
            (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]) := by
    rw [split1Unfold, hnextz1]
    rfl
  have hun : (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
      (prevEl r (lZSpine L N r x))).1.Nodup := by
    have h := aq1_split1Nodup L hL hgn hunL hm hf
    rwa [hface] at h
  set W : List (ℕ × ℕ) := between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)
    with hWdef
  set g : List (ℕ × ℕ) := (((W.map (fun d =>
      (List.range' 1 ((L.flatten.filter (fun t => decide (t = d.1))).length - 1)).map
        (fun i => (nList L)^[i] d))).flatten)).reverse with hgdef
  set f1 : List (ℕ × ℕ) := [nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
    (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)] with hf1def
  have hW : ∀ d ∈ W, d ∈ listOfDarts L := by
    intro d hd
    rw [hWdef] at hd
    exact mem_darts_of_mem_findFace L (betwnMem hd)
  have hpos := aq12v_szPos L hL hgn hm.1.1 hW
  have hdecomp' : (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
      (prevEl r (lZSpine L N r x))).1 = g ++ f1 := by
    simpa only [← hgdef, ← hf1def] using hdecomp
  by_cases hWne : W = []
  · -- 窗口空：FST = f1，两边都为 parts f1
    have hg0 : g = [] := by
      rw [hgdef, hWne]
      simp
    have hFst : (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).1 = f1 := by
      rw [hdecomp', hg0, List.nil_append]
    rw [hFst, hWne]
    simp
  · -- 窗口非空：partsCat + aq12v_partsNew1Rev
    have hgne : g ≠ [] := by
      rw [hgdef]
      exact aq12v_gNe L hWne hpos rfl
    have hf1ne : f1 ≠ [] := by
      rw [hf1def]; simp
    -- g.getLast! = nList (W.head!)
    have hWne' : W ≠ [] := hWne
    have hnew1ne : ((W.map (fun d =>
        (List.range' 1 ((L.flatten.filter (fun t => decide (t = d.1))).length - 1)).map
          (fun i => (nList L)^[i] d))).flatten) ≠ [] := by
      intro h0
      obtain ⟨d, hdW⟩ := List.exists_mem_of_ne_nil W hWne'
      have hmem : ((List.range' 1 ((L.flatten.filter (fun t => decide (t = d.1))).length - 1)).map
          (fun i => (nList L)^[i] d)) ∈ W.map (fun d =>
            (List.range' 1 ((L.flatten.filter (fun t => decide (t = d.1))).length - 1)).map
              (fun i => (nList L)^[i] d)) := List.mem_map_of_mem hdW
      exact absurd ((List.flatten_eq_nil_iff.mp h0) _ hmem)
        (aq12w_ndSpineNe L d (hpos d hdW))
    have hgLast : g.getLast! = nList L (W.head!) := by
      rw [hgdef, aq12w_getLast!_reverse hnew1ne]
      have hmapne : (W.map (fun d =>
          (List.range' 1 ((L.flatten.filter (fun t => decide (t = d.1))).length - 1)).map
            (fun i => (nList L)^[i] d))) ≠ [] := by
        intro h0
        exact hWne' (List.map_eq_nil_iff.mp h0)
      rw [aq12w_headFlattenMap hmapne (by
          intro l hl
          obtain ⟨d, hdW, rfl⟩ := List.mem_map.mp hl
          exact aq12w_ndSpineNe L d (hpos d hdW)),
        hdMap _ _ hWne']
      exact aq12w_ndSpineHead L (W.head!) (hpos _ (List.head!_mem_self hWne'))
    -- eList (g.getLast!) = l'Y
    have hw0 : W.head! = nextEl (findFaceDarts L x) (lYSpine L r x) := by
      rw [hWdef]
      exact HD_BETWN2 hyf hzf hyz hfnd hWne'
    have hw0face : findFaceDarts L (W.head!) = findFaceDarts L x := by
      rw [hw0]
      exact aq10_memFindFaceImpFacesEq hL.1 (nextEl_mem_of_mem hyf)
    have heLast : eList (g.getLast!) = lYSpine L r x := by
      rw [hgLast, nList, eList_eList, hw0]
      rw [show findFaceDarts L (nextEl (findFaceDarts L x) (lYSpine L r x))
          = findFaceDarts L x from
        aq10_memFindFaceImpFacesEq hL.1 (nextEl_mem_of_mem hyf)]
      exact prevEl_nextEl (findFaceDarts_nodup hL.1 _) hyf
    -- nextEl FST (g.getLast!) = nextEl r l'Y
    have hnextFst : nextEl (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).1 (g.getLast!) = nextEl r (lYSpine L r x) := by
      have h1 := nextElCatLast1 (s := g) (t := f1) (by rw [← hdecomp']; exact hun)
        hgne hf1ne
      rw [← hdecomp'] at h1
      rw [h1]
      rw [hf1def]
      simp
    -- junction：nextEl FST x ≠ fList (eList x)
    have hne : nextEl (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).1 (g.getLast!)
        ≠ fList L (eList (g.getLast!)) := by
      rw [hnextFst, heLast]
      exact nextRNotEqF L hL hgn hunL hm hf
    -- partsCat
    have hcat := partsCat L (u := g) (v := f1) (x := g.getLast!) hdecomp' rfl hgne hf1ne hne hun
    rw [hcat]
    rw [show partsSpine L g
        = ((W.map (fun d => (List.range' 1
            ((L.flatten.filter (fun t => decide (t = d.1))).length - 1)).reverse.map
              (fun i => (nList L)^[i] d))).reverse) from by
      rw [hgdef]
      exact aq12v_partsNew1Rev L hL hgn hm hf (by rwa [← hWdef])]
    -- 块形对齐：(ndSpine d).reverse = range' 反序 map
    simp only [ndSpine, List.map_reverse]

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq12w_catFstSplitNormalParts
