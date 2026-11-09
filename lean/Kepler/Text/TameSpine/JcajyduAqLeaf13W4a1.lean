/-
  JcajyduAqLeaf13W4a1 — AQ13 W4a1：共享定位/断口引理 + S 窗口 + F node。
  件目：① A3n `nextEl f2 d = nextEl r d`（d∈f2, d≠l'y）
        ② A3a 共享定位 `∃ p1∈parts r, p1.getLast! = y`
        ③ S 窗口段（⑭ + absurd）
        ④ F node 块（LAST p = nList d, eList = prevEl f d, ⑦/⑮+⑭）
  纪律：零 axiom/sorry/admit/native_decide；主仓 tracked 零改动。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf13W3
import Kepler.Text.TameSpine.JcajyduAqLeaf13W1b
import Kepler.Text.TameSpine.JcajyduAqLeaf12B
import Kepler.Graphs.GraphProps
import Kepler.Text.TameSpine.TameList19

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList GoodList findFaceDarts listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList dart_in_face findFaceDarts_nodup
  prevEl_mem_of_mem mem_darts_of_mem_findFace getD_eq_getElem_of_lt)

/-! ## §0 列表私件 -/

private theorem aq13w4a1_head!_map {α β : Type*} [Inhabited α] [Inhabited β]
    (f : α → β) {l : List α} (h : l ≠ []) : (l.map f).head! = f l.head! := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rfl

private theorem aq13w4a1_getLast!_eq_getLast {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! = l.getLast h := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast h]
  rfl

private theorem aq13w4a1_getLast!_append_of_ne {α : Type*} [Inhabited α]
    (s t : List α) (ht : t ≠ []) : (s ++ t).getLast! = t.getLast! := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast!_eq_getLast?_getD, List.getLast?_append]
  cases h : t.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp h) ht
  | some x => simp

/-- `nextEl (a :: l) a = l.head!`（l 非空）。 -/
private theorem aq13w4a1_nextEl_cons_head {α : Type*} [Inhabited α] [BEq α]
    [LawfulBEq α] [DecidableEq α] {a : α} {l : List α} (hl : l ≠ []) :
    nextEl (a :: l) a = l.head! := by
  have hlen : 1 < (a :: l).length := by
    rw [List.length_cons]
    exact Nat.succ_lt_succ (List.length_pos_of_ne_nil hl)
  have hidx : (a :: l).idxOf a = 0 := by simp
  unfold nextEl
  rw [if_neg (by omega), hidx]
  cases l with
  | nil => exact absurd rfl hl
  | cons b t =>
    rw [getD_eq_getElem_of_lt (by simp)]
    rfl

/-- `range' 1 k` 非空（k≠0）。 -/
private theorem aq13w4a1_range'_ne (k : ℕ) (hk : k ≠ 0) : List.range' 1 k ≠ [] := by
  intro h
  have hlen := congrArg List.length h
  rw [List.length_range'] at hlen
  simp at hlen
  omega

/-! ## §1 A3n：f2 断口转移 -/

/-- **A3n**（W4a1 唯一新引擎）：`d∈f2`、`d≠l'y` ⇒ `nextEl f2 d = nextEl r d`，
`f2 = [z]++betwn r z y++[y]`。 -/
theorem aq13w4a1_nextEl_f2 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {d : ℕ × ℕ}
    (hd : d ∈ [lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
        ++ [lYSpine L r x])
    (hdy : d ≠ lYSpine L r x) :
    nextEl ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
        ++ [lYSpine L r x]) d = nextEl r d := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hz : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hy : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hyz : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hzy : lZSpine L N r x ≠ lYSpine L r x := hyz.symm
  set B := between r (lZSpine L N r x) (lYSpine L r x) with hBdef
  set z := lZSpine L N r x with hzdef
  set y := lYSpine L r x with hydef
  have hBnd : B.Nodup := uniqBetwn hrnd hz hy hzy
  have hzB : z ∉ B := notBetwn1 hrnd hy
  have hyB : y ∉ B := notBetwn2 hrnd
  -- f2 = [z] ++ (B ++ [y])
  have hf2eq : ([z] ++ B ++ [y]) = [z] ++ (B ++ [y]) := List.append_assoc _ _ _
  have hf2nd : ([z] ++ B ++ [y]).Nodup := by
    rw [hf2eq, List.nodup_append]
    refine ⟨List.nodup_singleton z, ?_, ?_⟩
    · rw [List.nodup_append]
      exact ⟨hBnd, List.nodup_singleton y, fun a ha b hb => by
        rw [List.mem_singleton] at hb; subst hb
        exact fun h => hyB (h ▸ ha)⟩
    · intro a ha b hb
      rw [List.mem_singleton] at ha; subst ha
      rw [List.mem_append] at hb
      rcases hb with hb | hb
      · exact fun h => hzB (h ▸ hb)
      · rw [List.mem_singleton] at hb; subst hb; exact hzy
  have hBynd : (B ++ [y]).Nodup := by
    have h := hf2nd
    rw [hf2eq] at h
    exact (List.nodup_append.mp h).2.1
  have hmem : d ∈ ([z] ++ B ++ [y]) := hd
  rw [hf2eq] at hmem ⊢
  rcases List.mem_append.mp hmem with hdz | hdBy
  · -- d = z
    have hdz' : d = z := List.mem_singleton.mp hdz
    subst hdz'
    have hnxt : nextEl ([z] ++ (B ++ [y])) z = (B ++ [y]).head! := by
      have hcons : [z] ++ (B ++ [y]) = z :: (B ++ [y]) := rfl
      rw [hcons]
      exact aq13w4a1_nextEl_cons_head (l := B ++ [y]) (by simp)
    rw [hnxt]
    by_cases hB : B = []
    · rw [hB, List.nil_append, List.head!_cons]
      have hznext : y = nextEl r z := (betwnNil hrnd hzy hz hy).mp hB
      rw [← hznext]
    · have hhead : (B ++ [y]).head! = B.head! := by
        rw [List.head!_append]; exact hB
      rw [hhead, aqs_hdBetwn2 hrnd hz hy hzy hB]
  · rcases List.mem_append.mp hdBy with hdB | hdyMem
    · -- d ∈ B
      have hBne : B ≠ [] := List.ne_nil_of_mem hdB
      by_cases hdlast : d = B.getLast!
      · -- B 末元：nextEl f2 d = y
        have hdtlast : d ≠ (B ++ [y]).getLast! := by
          rw [aq13w4a1_getLast!_append_of_ne B [y] (by simp)]
          exact hdy
        have hf2 : nextEl ([z] ++ (B ++ [y])) d = y := by
          rw [nextElCat2 (s := [z]) (t := B ++ [y]) hf2nd
            (List.mem_append.mpr (Or.inl hdB)) hdtlast, hdlast,
            nextElCatLast1 (s := B) (t := [y]) hBynd hBne (by simp)]
          rfl
        rw [hf2]
        have hgl := aq13w4a1_getLast!_eq_getLast (l := B) hBne
        have hnextr := nextLastBetwn hz hy hrnd hzy hBne
        rw [← hgl] at hnextr
        rw [hdlast]
        exact hnextr.symm
      · -- B 内部：nextEl f2 d = nextEl B d = nextEl r d
        have hnextB : nextEl r d ∈ B := by
          have hgl := aq13w4a1_getLast!_eq_getLast (l := B) hBne
          have hlastne : B.getLast hBne ≠ d := by
            rw [← hgl]
            exact fun h => hdlast h.symm
          exact (aq10_eqMemNextElLast hzy hz hy hdB hrnd).mpr hlastne
        have hdtlast : d ≠ (B ++ [y]).getLast! := by
          rw [aq13w4a1_getLast!_append_of_ne B [y] (by simp)]
          exact hdy
        have hf2 : nextEl ([z] ++ (B ++ [y])) d = nextEl B d := by
          rw [nextElCat2 (s := [z]) (t := B ++ [y]) hf2nd
            (List.mem_append.mpr (Or.inl hdB)) hdtlast,
            nextElCat1 (s := B) (t := [y]) hBnd hdB hdlast]
        rw [hf2]
        exact aq10_nextElBetwnSame hzy hz hy hdB hnextB hrnd
    · -- d = y：排除
      have hdy' : d = y := List.mem_singleton.mp hdyMem
      exact absurd hdy' hdy

/-! ## §2 A3a 共享定位引理 -/

private theorem aq13w4a1_getLast!_mem {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! ∈ l := by
  rw [aq13w4a1_getLast!_eq_getLast h]
  exact List.getLast_mem h

/-- **A3a 共享定位**：`y` 是 `g` 的某 part 的末元（`g` 为 `r` 的切片、
断口在 `y` 处与 `r` 同步）⇒ `r` 的某 part 也以 `y` 为末元。 -/
theorem aq13w4a1_existsPartsLast (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} {r g p : List (ℕ × ℕ)} {y : ℕ × ℕ}
    (hn : NormalListSpine hL N) (hrN : r ∈ N)
    (hp : p ∈ partsSpine L g) (hyp : y ∈ p) (hylast : y = p.getLast!)
    (hyg : y ∈ g) (hgy : y ≠ g.getLast!) (hgnd : g.Nodup)
    (hgr : ∀ d ∈ g, d ∈ r) (hnextg : nextEl g y = nextEl r y) :
    ∃ p1 ∈ partsSpine L r, p1.getLast! = y := by
  obtain ⟨hrnd, hrne⟩ := normalListUniqNonnil hn hrN
  have hgne : g ≠ [] := List.ne_nil_of_mem hyg
  rcases partsMemExists L hrnd (hgr y hyg) with ⟨p1, hp1, hyp1⟩
  by_cases hyr : y = r.getLast!
  · -- y 是 r 的末元：p1 是 parts r 的末 part
    have hpartsne : partsSpine L r ≠ [] := partsNonnil L hrnd hrne
    set p2 := (partsSpine L r).getLast! with hp2def
    have hp2mem : p2 ∈ partsSpine L r :=
      aq13w4a1_getLast!_mem hpartsne
    have hp2last : p2.getLast! = r.getLast! :=
      aqs_lastParts L hL hn hrN rfl
    have hp2ne : p2 ≠ [] :=
      (partsUniqNonnil L hL hn hrN hp2mem).2.2.2.1
    have hy2 : y ∈ p2 := by
      rw [hyr, ← hp2last]
      exact aq13w4a1_getLast!_mem hp2ne
    have hflat : (partsSpine L r).flatten.Nodup := by
      rw [partsFlatten L hrnd hrne]; exact hrnd
    have heq : p1 = p2 :=
      uniqSublistUnique (partsSpine L r) hflat p1 hp1 p2 hp2mem ⟨y, hyp1, hy2⟩
    refine ⟨p1, hp1, ?_⟩
    rw [heq, hp2last]
    exact hyr.symm
  · -- y 不是 r 的末元：断口同步 ⇒ p1 的末元 = y
    have hbreakG : ¬(nextEl g y = fList L (eList y)) :=
      (aqs_conditionLastParts L hgnd hgne hp hyp hgy).mpr hylast
    have hbreakR : ¬(nextEl r y = fList L (eList y)) := by
      rw [← hnextg]; exact hbreakG
    have hlastp1 : y = p1.getLast! :=
      (aqs_conditionLastParts L hrnd hrne hp1 hyp1 hyr).mp hbreakR
    exact ⟨p1, hp1, hlastp1.symm⟩

/-! ## §3 S 窗口段 -/

/-- **S 窗口段**：`p=[d]`（`d∈W`）且 `y=LAST p` 时，⑭ 给 `y∈sList rtr`，
与 `y∉sList rtr` 矛盾。 -/
theorem aq13w4a1_windowContra (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hnf : ¬finalListSpine L (rtransSpine L N r x 1)) {d y : ℕ × ℕ}
    (hd : d ∈ between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x))
    (hylast : y = ([d] : List (ℕ × ℕ)).getLast!)
    (hyNot : y ∉ sListSpine L (rtransSpine L N r x 1) x) : False := by
  have hdS : d ∈ sListSpine L (rtransSpine L N r x 1) x :=
    aq13w1b_betwnMemSListRtrans L hL hgn hm hf hnf hd
  apply hyNot
  rwa [hylast]

/-! ## §4 F node 块 -/

/-- **F node 块**：`p = (ndSpine d).reverse`（`d∈W`）时
`eList (LAST p) = prevEl f d ∈ sList rtr`（⑦ 或 ⑮+⑭）。 -/
theorem aq13w4a1_nodeBlockMemSList (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hnf : ¬finalListSpine L (rtransSpine L N r x 1)) {d : ℕ × ℕ}
    (hd : d ∈ between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)) :
    eList ((ndSpine L d).reverse.getLast!) ∈
      sListSpine L (rtransSpine L N r x 1) x := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hpp := pplhuljV0 L hL hgn hunL hm hf
  have hyf : lYSpine L r x ∈ findFaceDarts L x := hpp.1
  have hzf : lZSpine L N r x ∈ findFaceDarts L x := hpp.2.1
  have hyz : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hfnd : (findFaceDarts L x).Nodup := findFaceDarts_nodup hL.1 x
  have hDmem : ∀ e ∈ between (findFaceDarts L x) (lYSpine L r x)
      (lZSpine L N r x), e ∈ listOfDarts L :=
    fun e he => mem_darts_of_mem_findFace L (betwnMem (f := findFaceDarts L x) he)
  have hk : 0 < (L.flatten.filter (fun t => decide (t = d.1))).length - 1 :=
    aq12v_szPos L hL hgn hm.1.1 hDmem d hd
  have hkne : (L.flatten.filter (fun t => decide (t = d.1))).length - 1 ≠ 0 := by omega
  have hlast : (ndSpine L d).reverse.getLast! = nList L d := by
    rw [Kepler.Graphs.getLast!_reverse]
    rw [ndSpine]
    rw [aq13w4a1_head!_map _ (aq13w4a1_range'_ne _ hkne)]
    rw [hdIota hkne]
    rw [Function.iterate_one]
  have hel : eList ((ndSpine L d).reverse.getLast!) = prevEl (findFaceDarts L x) d := by
    rw [hlast, aqs_eListNList]
    rw [aq10_memFindFaceImpFacesEq hL.1 (betwnMem hd)]
  rw [hel]
  by_cases hd1 : prevEl (findFaceDarts L x) d = lYSpine L r x
  · rw [hd1]
    exact aq13w1_yMemSListRtrans L hL hgn hm hf hnf
  · have hcase := aq13w3_caseBetwnPrevEl (r := findFaceDarts L x)
      (y := lYSpine L r x) (z := lZSpine L N r x) (d := d) hyz hyf hzf hfnd hd
    rcases hcase with h | h
    · exact absurd h hd1
    · exact aq13w1b_betwnMemSListRtrans L hL hgn hm hf hnf h

/-! 公理审计锚（编译即执行；预期标准三，零 sorryAx）。 -/
#print axioms Kepler.Text.TameSpine.aq13w4a1_nextEl_f2
#print axioms Kepler.Text.TameSpine.aq13w4a1_existsPartsLast
#print axioms Kepler.Text.TameSpine.aq13w4a1_windowContra
#print axioms Kepler.Text.TameSpine.aq13w4a1_nodeBlockMemSList
