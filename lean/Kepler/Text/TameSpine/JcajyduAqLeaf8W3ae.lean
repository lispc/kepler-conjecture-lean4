/-
  JcajyduAqLeaf8W3ae — AQ8 波 3ae：**B 路收口**（`uniq (core L SND)`，hB 槽落地）。

  目标（hB 形 = JcajyduAqLeaf8W5:47 唯一槽）：`parts SND` 的 `(FST ∘ HD)` 单射，三支：
  ① farc×farc `aq8w3yI_farcHeadsEq`；② 交叉 `aq8w3yII_crossHeadsNe`；
  ③ arc3×arc3：W3z refine 到同一 r-part + **接缝不切**（`lastOfSub`：末元 ≠ y ⇒
  必 = p 末元，否则 f-步/e-步撞 `fListInjDarts` + `isRestrictedEListNondeg`）
  ⇒ `uniqSublistUnique`；再 `nodup_map_iff_inj_on` + `uniqParts` 收口。
  ERRATA（本轮 probe 机器证据）：fLastSpine 路径 `hm.1.2.1.2.2.1 r hm.1.2.2.1` ✓；
  loopListSpine 是 `hm.1.2.1.2.2.2.1 r hm.1.2.2.1`（前任 §AQ8W3ae-0 少一 `.2`）。
  纪律：零 axiom/sorry/admit/native_decide；既有文件零触碰；注释 depth ≤ 1。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W5
import Kepler.Text.TameSpine.JcajyduAqLeaf8W3ad
import Kepler.Text.TameSpine.JcajyduAqLeaf8W1a
import Kepler.Text.TameSpine.JcajyduAqLeaf10F
import Kepler.Text.TameSpine.JcajyduRed2Trans
import Kepler.Text.TameSpine.JcajyduAqLeaf8W3b

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)

private noncomputable abbrev aq8w3aeArc3 (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (x : ℕ × ℕ) : List (ℕ × ℕ) :=
  [lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x) ++ [lYSpine L r x]

private noncomputable abbrev aq8w3aeFarc (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (x : ℕ × ℕ) : List (ℕ × ℕ) :=
  between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)

private noncomputable abbrev aq8w3aeSn (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (x : ℕ × ℕ) : List (ℕ × ℕ) :=
  aq8w3aeArc3 L N r x ++ aq8w3aeFarc L N r x

private theorem aq8w3ae_getLastMem {α : Type} [Inhabited α] {s : List α}
    (h : s ≠ []) : s.getLast! ∈ s := by
  have hpos : 0 < s.length := List.length_pos_of_ne_nil h
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (by omega)]
  simp

/-- **split 折平桥**：`nextElPrevElUniq` 把 `nextEl r (prevEl r z)` 折成 `z`，
SND 第二分量 = `arc3 ++ farc`（`rfl` 级）。 -/
private theorem aq8w3ae_sndEq (L : fgraph ℕ) (f : List (ℕ × ℕ))
    {r : List (ℕ × ℕ)} {z y : ℕ × ℕ} (hrnd : r.Nodup) (hzr : z ∈ r) :
    (splitNormalListSpine L r f y (prevEl r z)).2
      = ([z] ++ between r z y ++ [y]) ++ between f y z := by
  have hprev : nextEl r (prevEl r z) = z := nextElPrevElUniq hrnd z
  simp only [splitNormalListSpine, hprev]

/-- **接缝不切**：`w ∈ parts SND`、`w ⊆ p ∈ parts r`、`w ⊆ arc3` 且末元 ≠ y
⇒ `w` 的末元 = `p` 的末元（否则断点落在 r-part 内部，f-步与 e-步相撞）。 -/
private theorem aq8w3ae_lastOfSub (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hsN : aq8w3aeSn L N r x ∈ ntransSpine L N r x 1)
    {w p : List (ℕ × ℕ)} (hw : w ∈ partsSpine L (aq8w3aeSn L N r x))
    (hp : p ∈ partsSpine L r) (hwsub : ∀ a ∈ w, a ∈ p)
    (hw3 : ∀ a ∈ w, a ∈ aq8w3aeArc3 L N r x)
    (hwlast : w.getLast! ≠ lYSpine L r x) :
    w.getLast! = p.getLast! := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hnN : NormalListSpine hL (ntransSpine L N r x 1) :=
    aqs_aqNormalList L hL (aq1 L hL) (aq2 L hL) (aq3 L hL) (aq4 L hL) (aq5 L hL) hgn hm
  obtain ⟨hndS, hneS⟩ := normalListUniqNonnil hnN hsN
  obtain ⟨hrnd, hrne⟩ := normalListUniqNonnil hm.1.2.1 hm.1.2.2.1
  have hzrd : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hyrd : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzy : lZSpine L N r x ≠ lYSpine L r x :=
    fun h => hqymrtx3List L hL hgn hunL hm hf h.symm
  have hwne : w ≠ [] := partsAllNonnil L hndS hneS w hw
  have hwmem : w.getLast! ∈ w := aq8w3ae_getLastMem hwne
  have hwp : w.getLast! ∈ p := hwsub _ hwmem
  have hwl3 : w.getLast! ∈ aq8w3aeArc3 L N r x := hw3 _ hwmem
  by_contra hne
  have h1 : nextEl r w.getLast! = fList L (eList w.getLast!) :=
    (nextElPartsUnlast L hrnd hrne hp hwp hne).trans
      (partsNextUnlast L hrnd hrne p hp w.getLast! hwp hne)
  have h2 : nextEl (aq8w3aeSn L N r x) w.getLast! = nextEl r w.getLast! := by
    have harcnd : (aq8w3aeArc3 L N r x).Nodup := (List.nodup_append.mp hndS).1
    have hlast3 : (aq8w3aeArc3 L N r x).getLast! = lYSpine L r x :=
      aq10_suffixLast ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x))
        (lYSpine L r x)
    have hx2 : w.getLast! ≠ (aq8w3aeArc3 L N r x).getLast! := by
      rw [hlast3]; exact hwlast
    have hSnEq : aq8w3aeSn L N r x = aq8w3aeArc3 L N r x ++ aq8w3aeFarc L N r x := rfl
    rw [hSnEq]
    exact (nextElCat1 harcnd hwl3 hx2).trans
      (aq10_nextElPrefix r hrnd hzrd hyrd hzy hwl3 hwlast)
  have h3 : nextEl (aq8w3aeSn L N r x) w.getLast! = fList L w.getLast! :=
    normalListPartsNextLast L hL hnN hsN hw
  have hD : w.getLast! ∈ listOfDarts L := partsDarts L hnN hsN hw hwmem
  have heD : eList w.getLast! ∈ listOfDarts L := goodListEList hL hD
  have hcon : fList L (eList w.getLast!) = fList L w.getLast! := by
    rw [← h1, ← h2, h3]
  exact isRestrictedEListNondeg hL hm.1.1 hD ((fListInjDarts L hL hD heD).mp hcon.symm).symm

private theorem aq8w3ae_noTwoInParent (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hsN : aq8w3aeSn L N r x ∈ ntransSpine L N r x 1)
    {p u v : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r)
    (hu : u ∈ partsSpine L (aq8w3aeSn L N r x))
    (hv : v ∈ partsSpine L (aq8w3aeSn L N r x))
    (husub : ∀ a ∈ u, a ∈ p) (hvsub : ∀ a ∈ v, a ∈ p)
    (hu3 : ∀ a ∈ u, a ∈ aq8w3aeArc3 L N r x)
    (hv3 : ∀ a ∈ v, a ∈ aq8w3aeArc3 L N r x) (hne : u ≠ v) : False := by
  have hnN : NormalListSpine hL (ntransSpine L N r x 1) :=
    aqs_aqNormalList L hL (aq1 L hL) (aq2 L hL) (aq3 L hL) (aq4 L hL) (aq5 L hL) hgn hm
  obtain ⟨hndS, hneS⟩ := normalListUniqNonnil hnN hsN
  have hflat : (partsSpine L (aq8w3aeSn L N r x)).flatten.Nodup := by
    rw [partsFlatten L hndS hneS]; exact hndS
  have hune : u ≠ [] := partsAllNonnil L hndS hneS u hu
  have hvne : v ≠ [] := partsAllNonnil L hndS hneS v hv
  have humem : u.getLast! ∈ u := aq8w3ae_getLastMem hune
  have hvmem : v.getLast! ∈ v := aq8w3ae_getLastMem hvne
  have hlast : u.getLast! = v.getLast! := by
    by_cases hyp : lYSpine L r x ∈ p
    · have hnot : p.getLast! ∉ aq8w3aeArc3 L N r x := by
        have h := aqs_lastPartsYNotCat L hL hgn hm hf hp hyp
        rwa [← List.append_assoc] at h
      have huP : u.getLast! ≠ p.getLast! := by
        intro h; exact hnot (h.symm ▸ hu3 _ humem)
      have hvP : v.getLast! ≠ p.getLast! := by
        intro h; exact hnot (h.symm ▸ hv3 _ hvmem)
      have huy : u.getLast! = lYSpine L r x := by
        by_cases h : u.getLast! = lYSpine L r x
        · exact h
        · exact absurd (aq8w3ae_lastOfSub L hL hgn hm hf hsN hu hp husub hu3 h) huP
      have hvy : v.getLast! = lYSpine L r x := by
        by_cases h : v.getLast! = lYSpine L r x
        · exact h
        · exact absurd (aq8w3ae_lastOfSub L hL hgn hm hf hsN hv hp hvsub hv3 h) hvP
      rw [huy, hvy]
    · have huy : u.getLast! ≠ lYSpine L r x := by
        intro h; exact hyp (h ▸ husub _ humem)
      have hvy : v.getLast! ≠ lYSpine L r x := by
        intro h; exact hyp (h ▸ hvsub _ hvmem)
      exact (aq8w3ae_lastOfSub L hL hgn hm hf hsN hu hp husub hu3 huy).trans
        (aq8w3ae_lastOfSub L hL hgn hm hf hsN hv hp hvsub hv3 hvy).symm
  exact hne (uniqSublistUnique (partsSpine L (aq8w3aeSn L N r x)) hflat u hu v hv
    ⟨u.getLast!, humem, hlast ▸ hvmem⟩)

private theorem aq8w3ae_partsArc3OfHead (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hsN : aq8w3aeSn L N r x ∈ ntransSpine L N r x 1) :
    ∀ w ∈ partsSpine L (aq8w3aeSn L N r x),
      w.head! ∈ aq8w3aeArc3 L N r x → ∀ a ∈ w, a ∈ aq8w3aeArc3 L N r x := by
  have hnN : NormalListSpine hL (ntransSpine L N r x 1) :=
    aqs_aqNormalList L hL (aq1 L hL) (aq2 L hL) (aq3 L hL) (aq4 L hL) (aq5 L hL) hgn hm
  obtain ⟨hndS, hneS⟩ := normalListUniqNonnil hnN hsN
  intro w hw hwh
  have hwne : w ≠ [] := partsAllNonnil L hndS hneS w hw
  by_cases hfarne : aq8w3aeFarc L N r x = []
  · have hSn3 : aq8w3aeSn L N r x = aq8w3aeArc3 L N r x := by
      show aq8w3aeArc3 L N r x ++ aq8w3aeFarc L N r x = aq8w3aeArc3 L N r x
      rw [hfarne, List.append_nil]
    have hnd3 : (aq8w3aeArc3 L N r x).Nodup := hSn3 ▸ hndS
    have hne3 : aq8w3aeArc3 L N r x ≠ [] := by rw [← hSn3]; exact hneS
    have hw3' : w ∈ partsSpine L (aq8w3aeArc3 L N r x) := hSn3 ▸ hw
    exact fun a ha => memPartsImp L hnd3 hne3 hw3' a ha
  · have hsplit := aq8w3ab_partsSndSplit L hL hgn (aq1 L hL) (aq2 L hL) (aq3 L hL)
      (aq4 L hL) (aq5 L hL) hm hf hsN hfarne
    have hw' : w ∈ partsSpine L (aq8w3aeArc3 L N r x) ++ partsSpine L (aq8w3aeFarc L N r x) :=
      hsplit ▸ hw
    rcases List.mem_append.mp hw' with h3 | hf'
    · have hnd3 : (aq8w3aeArc3 L N r x).Nodup := (List.nodup_append.mp hndS).1
      have hne3 : aq8w3aeArc3 L N r x ≠ [] := by
        intro h0
        have hmem : lZSpine L N r x ∈ aq8w3aeArc3 L N r x :=
          List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_singleton_self _))))
        rw [h0] at hmem
        exact List.not_mem_nil hmem
      exact fun a ha => memPartsImp L hnd3 hne3 h3 a ha
    · exfalso
      have hndf : (aq8w3aeFarc L N r x).Nodup := (List.nodup_append.mp hndS).2.1
      have hfh : w.head! ∈ aq8w3aeFarc L N r x :=
        memPartsImp L hndf hfarne hf' w.head! (List.head!_mem_self hwne)
      exact (aq8w3ad_arcFarcExcl L hL hgn (aq1 L hL) (aq2 L hL) (aq3 L hL)
        (aq4 L hL) (aq5 L hL) hm hf hsN _ hwh _ hfh) rfl

/-- **AQ8 B 路单射**：`parts SND` 上 `(FST ∘ HD)` 单射（三支分派）。 -/
theorem aq8w3ae_partsFstHdInjSND (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hsN : aq8w3aeSn L N r x ∈ ntransSpine L N r x 1) :
    ∀ u ∈ partsSpine L (aq8w3aeSn L N r x),
      ∀ v ∈ partsSpine L (aq8w3aeSn L N r x),
        (u.head!).1 = (v.head!).1 → u = v := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hnN : NormalListSpine hL (ntransSpine L N r x 1) :=
    aqs_aqNormalList L hL (aq1 L hL) (aq2 L hL) (aq3 L hL) (aq4 L hL) (aq5 L hL) hgn hm
  obtain ⟨hndS, hneS⟩ := normalListUniqNonnil hnN hsN
  obtain ⟨hrnd, hrne⟩ := normalListUniqNonnil hm.1.2.1 hm.1.2.2.1
  have hq : (partsSpine L r).map (fun q => q.head!.1) ∈ quotientListSpine L N := by
    show _ ∈ coreListSpine (N.map (partsSpine L))
    exact List.mem_map.mpr ⟨partsSpine L r, List.mem_map.mpr ⟨r, hm.1.2.2.1, rfl⟩, rfl⟩
  have hinj : ∀ q ∈ partsSpine L r, ∀ q' ∈ partsSpine L r,
      (q.head!).1 = (q'.head!).1 → q = q' :=
    (List.nodup_map_iff_inj_on (uniqParts L hrnd hrne)).mp
      ((hm.1.2.2.2.2.1).1 _ hq)
  have harc3r : ∀ a ∈ aq8w3aeArc3 L N r x, a ∈ r :=
    aq8w3b_arcSubset L hL hgn hm hf (s := aq8w3aeArc3 L N r x) rfl
  intro u hu v hv heq
  have hune : u ≠ [] := partsAllNonnil L hndS hneS u hu
  have hvne : v ≠ [] := partsAllNonnil L hndS hneS v hv
  have huSplit : u.head! ∈ aq8w3aeArc3 L N r x ∨ u.head! ∈ aq8w3aeFarc L N r x := by
    have h := memPartsImp L hndS hneS hu u.head! (List.head!_mem_self hune)
    rw [show aq8w3aeSn L N r x = aq8w3aeArc3 L N r x ++ aq8w3aeFarc L N r x from rfl] at h
    exact List.mem_append.mp h
  have hvSplit : v.head! ∈ aq8w3aeArc3 L N r x ∨ v.head! ∈ aq8w3aeFarc L N r x := by
    have h := memPartsImp L hndS hneS hv v.head! (List.head!_mem_self hvne)
    rw [show aq8w3aeSn L N r x = aq8w3aeArc3 L N r x ++ aq8w3aeFarc L N r x from rfl] at h
    exact List.mem_append.mp h
  rcases huSplit with hu3 | huf
  · rcases hvSplit with hv3 | hvf
    · -- ③ arc3 × arc3
      by_contra hne
      have hu3s := aq8w3ae_partsArc3OfHead L hL hgn hm hf hsN u hu hu3
      have hv3s := aq8w3ae_partsArc3OfHead L hL hgn hm hf hsN v hv hv3
      obtain ⟨p, hp, husub, hfu⟩ :=
        aq8w3z_partsSubArcRefine L hL hgn (aq1 L hL) (aq2 L hL) (aq3 L hL)
          (aq4 L hL) (aq5 L hL) hm hf hsN hu (fun a ha => harc3r a (hu3s a ha))
      obtain ⟨p', hp', hvsub, hfv⟩ :=
        aq8w3z_partsSubArcRefine L hL hgn (aq1 L hL) (aq2 L hL) (aq3 L hL)
          (aq4 L hL) (aq5 L hL) hm hf hsN hv (fun a ha => harc3r a (hv3s a ha))
      have hpp : p = p' := hinj p hp p' hp' (hfu.symm.trans (heq.trans hfv))
      exact aq8w3ae_noTwoInParent L hL hgn hm hf hsN hp hu hv husub
        (fun a ha => hpp ▸ hvsub a ha) hu3s hv3s hne
    · -- ② arc3 × farc
      exact absurd heq.symm (aq8w3yII_crossHeadsNe L hL hgn hm hf hvf hu3)
  · rcases hvSplit with hv3 | hvf
    · -- ② farc × arc3
      exact absurd heq (aq8w3yII_crossHeadsNe L hL hgn hm hf huf hv3)
    · -- ① farc × farc
      exact aq8w3yI_farcHeadsEq L hL hgn (aq1 L hL) (aq2 L hL) (aq3 L hL)
        (aq4 L hL) (aq5 L hL) hm hf hsN hu hv huf hvf heq

/-- **AQ8 B 路收口**：`core L SND` 无重（= `hB` 槽逐字陈述）。 -/
theorem aq8w3ae_coreSNDNodup (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ((partsSpine L (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2).map
        (fun p => p.head!.1)).Nodup := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hnN : NormalListSpine hL (ntransSpine L N r x 1) :=
    aqs_aqNormalList L hL (aq1 L hL) (aq2 L hL) (aq3 L hL) (aq4 L hL) (aq5 L hL) hgn hm
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hzrd : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hbridge := aq8w3ae_sndEq L (findFaceDarts L (lYSpine L r x))
    (y := lYSpine L r x) (z := lZSpine L N r x) hrnd hzrd
  have hsN : aq8w3aeSn L N r x ∈ ntransSpine L N r x 1 := by
    rw [ntrans1 L N r x hf]
    refine List.mem_append.mpr (Or.inl ?_)
    rw [hbridge]
    exact memReplaceFstMem hm.1.2.2.1 (List.mem_singleton_self _)
  obtain ⟨hndS, hneS⟩ := normalListUniqNonnil hnN hsN
  rw [hbridge]
  exact (List.nodup_map_iff_inj_on (uniqParts L hndS hneS)).mpr
    (aq8w3ae_partsFstHdInjSND L hL hgn hm hf hsN)

/-- **AQ8 叶主证**（HOL `AQ8_concl`，AQ8.hl:3341）：B 路代入 W5 装配骨架。 -/
theorem aq8 (L : fgraph ℕ) (hL : GoodList L) : aq8Concl L hL :=
  aq8Concl_of_uniqSnd L hL
    (fun N r x hgn hm hf => aq8w3ae_coreSNDNodup L hL hgn hm hf)

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq8w3ae_partsFstHdInjSND
#print axioms Kepler.Text.TameSpine.aq8w3ae_coreSNDNodup
#print axioms Kepler.Text.TameSpine.aq8
