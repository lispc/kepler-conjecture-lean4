/- JcajyduAqLeaf13W4a2 — AQ13 W4a2a：B2n（f1 断口转移）。0 禁词；主仓零改动。 -/
import Kepler.Text.TameSpine.JcajyduAqLeaf13W4a1
import Kepler.Text.TameSpine.JcajyduAqLeaf13W3
import Kepler.Text.TameSpine.JcajyduAqLeaf8W2b
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
namespace Kepler.Text.TameSpine
open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList GoodList findFaceDarts listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList dart_in_face findFaceDarts_nodup
  nextEl_mem_of_mem prevEl_mem_of_mem getD_eq_getElem_of_lt)
private theorem aq13w4a2_getLast!_eq_getLast {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! = l.getLast h := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast h]
  rfl

private theorem aq13w4a2_getLast!_append_of_ne {α : Type*} [Inhabited α]
    (s t : List α) (ht : t ≠ []) : (s ++ t).getLast! = t.getLast! := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast!_eq_getLast?_getD, List.getLast?_append]
  cases h : t.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp h) ht
  | some x => simp

private theorem aq13w4a2_nextEl_cons_head {α : Type*} [Inhabited α] [BEq α]
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

/-- **B2n**：`d∈f1`、`d≠z1` ⇒ `nextEl f1 d = nextEl r d`。 -/
theorem aq13w4a2_nextEl_f1 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {d : ℕ × ℕ}
    (hd : d ∈ [nextEl r (lYSpine L r x)] ++
        between r (nextEl r (lYSpine L r x)) (prevEl r (lZSpine L N r x)) ++
        [prevEl r (lZSpine L N r x)])
    (hdz : d ≠ prevEl r (lZSpine L N r x)) :
    nextEl ([nextEl r (lYSpine L r x)] ++
        between r (nextEl r (lYSpine L r x)) (prevEl r (lZSpine L N r x)) ++
        [prevEl r (lZSpine L N r x)]) d = nextEl r d := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hy : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hz : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  set a := nextEl r (lYSpine L r x) with hadef
  set b := prevEl r (lZSpine L N r x) with hbdef
  have ha : a ∈ r := nextEl_mem_of_mem hy
  have hb : b ∈ r := prevEl_mem_of_mem hz
  -- f1.Nodup（从 ntrans flatten + FST split 成员）
  have hndNt : (ntransSpine L N r x 1).flatten.Nodup := aq1 L hL N r x hgn hm
  have hsplit1 : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).1 =
      ((((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).map (fun d => ndSpine L d)).flatten).reverse) ++
        ([a] ++ between r a b ++ [b]) := by
    dsimp only [splitNormalListSpine]
    simp only [ndSpine]
    rw [hbdef, nextElPrevElUniq hrnd _, ← hadef, ← hbdef]
  have hnd1 : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).1.Nodup :=
    uniqFlattenUniq _ hndNt _ (aq8w2b_fstMemRtran1 L hf)
  have hf1nd : ([a] ++ between r a b ++ [b]).Nodup := by
    have h := hnd1
    rw [hsplit1] at h
    exact (List.nodup_append.mp h).2.1
  have hab : a ≠ b := by
    intro hab
    have hmem : a ∈ between r a b ++ [a] :=
      List.mem_append.mpr (Or.inr (List.mem_singleton_self a))
    have hnot : a ∉ between r a b ++ [a] := by
      have h := hf1nd
      rw [show ([a] ++ between r a b ++ [b]) = a :: (between r a b ++ [b]) from rfl] at h
      have h2 := (List.nodup_cons.mp h).1
      rw [← hab] at h2 ⊢
      exact h2
    exact hnot hmem
  set B := between r a b with hBdef
  have hBnd : B.Nodup := uniqBetwn hrnd ha hb hab
  have haB : a ∉ B := notBetwn1 hrnd hb
  have hbB : b ∉ B := notBetwn2 hrnd
  have hf1eq : ([a] ++ B ++ [b]) = [a] ++ (B ++ [b]) := List.append_assoc _ _ _
  have hf1nd' : ([a] ++ (B ++ [b])).Nodup := by
    rw [← hf1eq]; exact hf1nd
  have hBynd : (B ++ [b]).Nodup := (List.nodup_append.mp hf1nd').2.1
  have hmem : d ∈ ([a] ++ B ++ [b]) := hd
  rw [hf1eq] at hmem ⊢
  rcases List.mem_append.mp hmem with hda | hdBy
  · have hda' : d = a := List.mem_singleton.mp hda
    subst hda'
    have hnxt : nextEl ([a] ++ (B ++ [b])) a = (B ++ [b]).head! := by
      have hcons : [a] ++ (B ++ [b]) = a :: (B ++ [b]) := rfl
      rw [hcons]
      exact aq13w4a2_nextEl_cons_head (l := B ++ [b]) (by simp)
    rw [hnxt]
    by_cases hB : B = []
    · rw [hB, List.nil_append, List.head!_cons]
      have hanext : b = nextEl r a := (betwnNil hrnd hab ha hb).mp hB
      rw [← hanext]
    · have hhead : (B ++ [b]).head! = B.head! := by
        rw [List.head!_append]; exact hB
      rw [hhead, aqs_hdBetwn2 hrnd ha hb hab hB]
  · rcases List.mem_append.mp hdBy with hdB | hdb
    · have hBne : B ≠ [] := List.ne_nil_of_mem hdB
      by_cases hdlast : d = B.getLast!
      · have hdtlast : d ≠ (B ++ [b]).getLast! := by
          rw [aq13w4a2_getLast!_append_of_ne B [b] (by simp)]
          exact hdz
        have hf1 : nextEl ([a] ++ (B ++ [b])) d = b := by
          rw [nextElCat2 (s := [a]) (t := B ++ [b]) hf1nd'
            (List.mem_append.mpr (Or.inl hdB)) hdtlast, hdlast,
            nextElCatLast1 (s := B) (t := [b]) hBynd hBne (by simp)]
          rfl
        rw [hf1]
        have hgl := aq13w4a2_getLast!_eq_getLast (l := B) hBne
        have hnextr := nextLastBetwn ha hb hrnd hab hBne
        rw [← hgl] at hnextr
        rw [hdlast]
        exact hnextr.symm
      · have hnextB : nextEl r d ∈ B := by
          have hgl := aq13w4a2_getLast!_eq_getLast (l := B) hBne
          have hlastne : B.getLast hBne ≠ d := by
            rw [← hgl]
            exact fun h => hdlast h.symm
          exact (aq10_eqMemNextElLast hab ha hb hdB hrnd).mpr hlastne
        have hdtlast : d ≠ (B ++ [b]).getLast! := by
          rw [aq13w4a2_getLast!_append_of_ne B [b] (by simp)]
          exact hdz
        have hf1 : nextEl ([a] ++ (B ++ [b])) d = nextEl B d := by
          rw [nextElCat2 (s := [a]) (t := B ++ [b]) hf1nd'
            (List.mem_append.mpr (Or.inl hdB)) hdtlast,
            nextElCat1 (s := B) (t := [b]) hBnd hdB hdlast]
        rw [hf1]
        exact aq10_nextElBetwnSame hab ha hb hdB hnextB hrnd
    · have hdb' : d = b := List.mem_singleton.mp hdb
      exact absurd hdb' hdz

#print axioms Kepler.Text.TameSpine.aq13w4a2_nextEl_f1
