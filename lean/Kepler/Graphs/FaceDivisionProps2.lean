/-
Port of the second block (lines 1132–1846) of the Isabelle AFP
"Flyspeck-Tame" theory `FaceDivisionProps.thy`: the `between is_nextElem`,
`is_nextElem edges`, `nextVertex`, `split_face` and `verticesFrom` sections.

Source: `reference/afp-flyspeck-tame/FaceDivisionProps.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

Correspondence notes: as in `FaceDivisionProps1.lean`
(`hd`/`last`/`butlast` ↦ `List.head!`/`List.getLast!`/`List.dropLast`,
`distinct` ↦ `List.Nodup`, set equalities and empty intersections rendered as
membership (non-)implications).  The definitions `pre_split_face` and
`verticesFrom` live in this block of the source file and are ported here.
-/
import Kepler.Graphs.FaceDivisionProps1

namespace Kepler.Graphs

variable {α : Type _}

/-! ### between - is_nextElem -/

section BetweenIsNextElem

variable [BEq α] [LawfulBEq α] [Inhabited α]

/-- FaceDivisionProps.thy: is_nextElem_or1 -/
theorem is_nextElem_or1 {vs : List α} {ram₁ ram₂ x y : α}
    (hp : pre_between vs ram₁ ram₂) (hne : is_nextElem vs x y)
    (hb : before vs ram₁ ram₂) :
    is_sublist [x, y] (ram₁ :: between vs ram₁ ram₂ ++ [ram₂]) ∨
      is_sublist [x, y] (ram₂ :: between vs ram₂ ram₁ ++ [ram₁]) := by
  have hr1 : ram₁ ∈ vs := hp.2.1
  have rule1 : x ∈ ram₁ :: between vs ram₁ ram₂ →
      is_sublist [x, y] (ram₁ :: between vs ram₁ ram₂ ++ [ram₂]) := by
    intro xin
    have xin2 : x ∈ ram₁ :: between vs ram₁ ram₂ ++ [ram₂] :=
      List.mem_append_left _ xin
    have sub1 : is_sublist (ram₁ :: (splitAt ram₁ vs).2) vs := splitAt_is_sublist2R hr1
    have hr2s : ram₂ ∈ (splitAt ram₁ vs).2 := before_dist_r2 hp.1 hb
    have hpref : is_prefix ((splitAt ram₂ (splitAt ram₁ vs).2).1 ++ [ram₂])
        (splitAt ram₁ vs).2 := splitAt_is_prefix hr2s
    have hpref2 : is_prefix ([ram₁] ++ ((splitAt ram₂ (splitAt ram₁ vs).2).1 ++ [ram₂]))
        ([ram₁] ++ (splitAt ram₁ vs).2) := is_prefix_add hpref
    have hbtw : between vs ram₁ ram₂ = (splitAt ram₂ (splitAt ram₁ vs).2).1 :=
      between_simp1 hb hp
    have subl : is_sublist (ram₁ :: between vs ram₁ ram₂ ++ [ram₂]) vs := by
      apply is_sublist_trans _ sub1
      have e : ram₁ :: between vs ram₁ ram₂ ++ [ram₂] =
          [ram₁] ++ ((splitAt ram₂ (splitAt ram₁ vs).2).1 ++ [ram₂]) := by
        rw [hbtw]; rfl
      rw [e]
      exact is_prefix_sublist hpref2
    have db : (ram₁ :: between vs ram₁ ram₂ ++ [ram₂]).Nodup :=
      between_distinct_r12 hp.1 hp.2.2.2
    have xnlb : x ≠ (ram₁ :: between vs ram₁ ram₂ ++ [ram₂]).getLast! := by
      rw [getLast!_concat]
      rcases List.mem_cons.mp xin with h | h
      · exact fun e => hp.2.2.2 (h.symm.trans e)
      · exact fun e => between_not_r2 hp.1 (e ▸ h)
    exact is_sublist_is_nextElem hp.1 hne subl xin2 xnlb
  have rule2 : x ∈ ram₂ :: between vs ram₂ ram₁ →
      is_sublist [x, y] (ram₂ :: between vs ram₂ ram₁ ++ [ram₁]) := by
    intro xin
    set cs1 := ram₂ :: (splitAt ram₂ vs).2 with hcs1
    have cs1ne : cs1 ≠ [] := List.cons_ne_nil _ _
    set cs2 := (splitAt ram₁ vs).1 with hcs2
    have hbtw2 : between vs ram₂ ram₁ = (splitAt ram₂ vs).2 ++ (splitAt ram₁ vs).1 :=
      between_simp2 hb hp
    have hbs2 : ram₂ :: between vs ram₂ ram₁ ++ [ram₁] = cs1 ++ cs2 ++ [ram₁] := by
      rw [hbtw2, hcs1, hcs2]; rfl
    have hsubcs1 : is_sublist cs1 vs := splitAt_is_sublist2R hp.2.2.1
    have hcase1 : x ∈ cs1 → x ≠ cs1.getLast! →
        is_sublist [x, y] (ram₂ :: between vs ram₂ ram₁ ++ [ram₁]) := by
      intro hxin hxnl
      obtain ⟨as, bs', hsub⟩ := is_sublist_is_nextElem hp.1 hne hsubcs1 hxin hxnl
      exact ⟨as, bs' ++ cs2 ++ [ram₁], by rw [hbs2, hsub]; simp [List.append_assoc]⟩
    have hcase2 : x = cs1.getLast! →
        is_sublist [x, y] (ram₂ :: between vs ram₂ ram₁ ++ [ram₁]) := by
      intro xl
      have hvs2 : vs = (splitAt ram₂ vs).1 ++ ram₂ :: (splitAt ram₂ vs).2 :=
        splitAt_ram hp.2.2.1
      have hlv : vs.getLast! = cs1.getLast! := by
        rw [hvs2, hcs1]
        exact getLast!_append_right _ (List.cons_ne_nil _ _)
      have xlv : x = vs.getLast! := xl.trans hlv.symm
      have yhd : y = vs.head! := is_nextElem_last_hd hp.1 hne xlv
      have hvs1 : vs = (splitAt ram₁ vs).1 ++ ram₁ :: (splitAt ram₁ vs).2 :=
        splitAt_ram hp.2.1
      have hcs2r : cs2 ++ [ram₁] ≠ [] :=
        List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
      have yhd2 : y = (cs2 ++ [ram₁]).head! := by
        rw [yhd, hvs1, ← hcs2]
        have e : cs2 ++ ram₁ :: (splitAt ram₁ vs).2 =
            (cs2 ++ [ram₁]) ++ (splitAt ram₁ vs).2 := by simp [List.append_assoc]
        rw [e]
        exact List.head!_append _ hcs2r
      rw [hbs2]
      refine ⟨cs1.dropLast, (cs2 ++ [ram₁]).tail, ?_⟩
      have t1 : cs1 = cs1.dropLast ++ [x] := by
        have e1 := (dropLast_concat_getLast! cs1ne).symm
        rwa [← xl] at e1
      have e2 : cs2 ++ [ram₁] = y :: (cs2 ++ [ram₁]).tail := by
        conv_rhs => rw [yhd2]
        exact (List.cons_head!_tail hcs2r).symm
      calc cs1 ++ cs2 ++ [ram₁] = cs1 ++ (cs2 ++ [ram₁]) := List.append_assoc _ _ _
        _ = (cs1.dropLast ++ [x]) ++ (y :: (cs2 ++ [ram₁]).tail) := by
            conv_lhs => rw [t1, e2]
        _ = cs1.dropLast ++ [x, y] ++ (cs2 ++ [ram₁]).tail := by
            simp [List.append_assoc]
    have incs1 : x ∈ cs1 → is_sublist [x, y] (ram₂ :: between vs ram₂ ram₁ ++ [ram₁]) := by
      intro hxin
      by_cases hxl : x = cs1.getLast!
      · exact hcase2 hxl
      · exact hcase1 hxin hxl
    have hcase3 : x ∈ cs2 → is_sublist [x, y] (ram₂ :: between vs ram₂ ram₁ ++ [ram₁]) := by
      intro xin2'
      have xin2 : x ∈ cs2 ++ [ram₁] := List.mem_append_left _ xin2'
      have hsub : is_sublist (cs2 ++ [ram₁]) vs := by
        rw [hcs2]
        exact splitAt_is_sublist1R hp.2.1
      have xnr1 : x ≠ ram₁ := by
        have hvs1 : vs = cs2 ++ ram₁ :: (splitAt ram₁ vs).2 := by
          rw [hcs2]; exact splitAt_ram hp.2.1
        have hd' : (cs2 ++ ram₁ :: (splitAt ram₁ vs).2).Nodup := hvs1 ▸ hp.1
        intro e
        rw [e] at xin2'
        exact (List.nodup_append.mp hd').2.2 ram₁ xin2' ram₁ List.mem_cons_self rfl
      have xnlcs2 : x ≠ (cs2 ++ [ram₁]).getLast! := by
        rw [getLast!_concat]
        exact xnr1
      obtain ⟨as, bs', hsub2⟩ := is_sublist_is_nextElem hp.1 hne hsub xin2 xnlcs2
      refine ⟨cs1 ++ as, bs', ?_⟩
      rw [hbs2, show (cs1 ++ cs2) ++ [ram₁] = cs1 ++ (cs2 ++ [ram₁]) from
        List.append_assoc _ _ _, hsub2]
      simp [List.append_assoc]
    have hxmem : x ∈ cs1 ++ cs2 := by
      have e : ram₂ :: between vs ram₂ ram₁ = cs1 ++ cs2 := by
        rw [hbtw2, hcs1, hcs2]; rfl
      rw [e] at xin
      exact xin
    rcases List.mem_append.mp hxmem with h | h
    · exact incs1 h
    · exact hcase3 h
  have hxvs : x ∈ vs := is_nextElem_a hne
  rcases between_in hb hp hxvs with h | h | h | h
  · exact Or.inl (rule1 (List.mem_cons.mpr (Or.inl h)))
  · exact Or.inl (rule1 (List.mem_cons.mpr (Or.inr h)))
  · exact Or.inr (rule2 (List.mem_cons.mpr (Or.inl h)))
  · exact Or.inr (rule2 (List.mem_cons.mpr (Or.inr h)))

/-- FaceDivisionProps.thy: is_nextElem_or -/
theorem is_nextElem_or {vs : List α} {ram₁ ram₂ x y : α}
    (hp : pre_between vs ram₁ ram₂) (hne : is_nextElem vs x y) :
    is_sublist [x, y] (ram₁ :: between vs ram₁ ram₂ ++ [ram₂]) ∨
      is_sublist [x, y] (ram₂ :: between vs ram₂ ram₁ ++ [ram₁]) := by
  by_cases hb : before vs ram₁ ram₂
  · exact is_nextElem_or1 hp hne hb
  · have hb' : before vs ram₂ ram₁ := (before_xor hp).mp hb
    rcases is_nextElem_or1 (pre_between_symI hp) hne hb' with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- FaceDivisionProps.thy: between_eq2 -/
theorem between_eq2 {vs : List α} {ram₁ ram₂ : α}
    (hp : pre_between vs ram₁ ram₂) (hb : before vs ram₂ ram₁) :
    ∃ as bs cs, between vs ram₁ ram₂ = cs ++ as ∧
      vs = as ++ [ram₂] ++ bs ++ [ram₁] ++ cs := by
  have hp' : pre_between vs ram₂ ram₁ := pre_between_symI hp
  refine ⟨(splitAt ram₂ vs).1, (splitAt ram₁ (splitAt ram₂ vs).2).1,
    (splitAt ram₁ vs).2, ?_, ?_⟩
  · exact between_simp2 hb hp'
  · conv_lhs => rw [before_vs hp.1 hb]
    simp [List.append_assoc]

/-- FaceDivisionProps.thy: is_sublist_same_len -/
@[simp]
theorem is_sublist_same_len {xs ys : List α} (h : xs.length = ys.length) :
    is_sublist xs ys ↔ xs = ys := by
  constructor
  · rintro ⟨as, bs, rfl⟩
    have h2 : as.length + bs.length = 0 := by
      have := h
      simp [List.length_append] at this
      omega
    have ha : as = [] := List.length_eq_zero_iff.mp (by omega)
    have hb : bs = [] := List.length_eq_zero_iff.mp (by omega)
    subst ha; subst hb; simp
  · rintro rfl
    exact is_sublist_id

/-- FaceDivisionProps.thy: is_nextElem_between_empty -/
@[simp]
theorem is_nextElem_between_empty {vs : List α} {a b : α}
    (hd : vs.Nodup) (h : is_nextElem vs a b) : between vs a b = [] := by
  rcases h with hsub | ⟨hne, hx, hy⟩
  · obtain ⟨as, bs, hvs⟩ := hsub
    have hsp : (as, b :: bs) = splitAt a vs :=
      splitAt_dist_ram hd (by rw [hvs]; simp [List.append_assoc])
    have hcont : ((splitAt a vs).2.contains b) = true := by
      rw [← hsp]
      exact List.contains_iff_mem.mpr List.mem_cons_self
    rw [between_def, if_pos hcont, ← hsp]
    exact congrArg Prod.fst (splitAt_self_cons b bs)
  · have ham : a ∈ vs := by rw [hx]; exact getLast!_mem hne
    have hsp := splitAt_ram ham
    have hs2 : (splitAt a vs).2 = [] := by
      by_contra h2
      obtain ⟨s, ss, hss⟩ := List.exists_cons_of_ne_nil h2
      have ha2 : a ∈ (splitAt a vs).2 := by
        have e : vs.getLast! = (s :: ss).getLast! := by
          have e1 : vs = ((splitAt a vs).1 ++ [a]) ++ (s :: ss) := by
            conv_lhs => rw [hsp]
            rw [hss]; simp [List.append_assoc]
          rw [e1]
          exact getLast!_append_right _ (List.cons_ne_nil _ _)
        rw [hss]
        exact (hx.trans e).symm ▸ getLast!_mem (List.cons_ne_nil _ _)
      have hd' : ((splitAt a vs).1 ++ a :: (splitAt a vs).2).Nodup := hsp ▸ hd
      exact (List.nodup_cons.mp (List.nodup_append.mp hd').2.1).1 ha2
    have hcont : ¬ (((splitAt a vs).2.contains b) = true) := by
      rw [hs2, List.contains_nil]
      exact fun h => Bool.noConfusion h
    rw [between_def, if_neg hcont, hs2, List.nil_append]
    rw [hs2] at hsp
    by_cases hFn : (splitAt a vs).1 = []
    · rw [hFn]; rfl
    · have hbh : b = (splitAt a vs).1.head! := by
        rw [hy]
        conv_lhs => rw [hsp]
        exact List.head!_append _ hFn
      have hFb : (splitAt a vs).1 = b :: (splitAt a vs).1.tail := by
        rw [hbh]
        exact (List.cons_head!_tail hFn).symm
      have e : (splitAt b (splitAt a vs).1).1 = [] := by
        rw [hFb]
        exact congrArg Prod.fst (splitAt_self_cons b _)
      exact e

/-- FaceDivisionProps.thy: is_nextElem_between_empty' -/
theorem is_nextElem_between_empty' {vs : List α} {a b : α}
    (h : between vs a b = []) (hd : vs.Nodup) (ha : a ∈ vs) (hb : b ∈ vs)
    (hab : a ≠ b) : is_nextElem vs a b := by
  by_cases hcase : b ∈ (splitAt a vs).2
  · have hcont : ((splitAt a vs).2.contains b) = true := List.contains_iff_mem.mpr hcase
    rw [between_def, if_pos hcont] at h
    have hsp := splitAt_ram hcase
    rw [h] at hsp
    have hsp2 := splitAt_ram ha
    rw [hsp] at hsp2
    exact Or.inl ⟨(splitAt a vs).1, (splitAt b (splitAt a vs).2).2, by
      conv_lhs => rw [hsp2]
      simp [List.append_assoc]⟩
  · have hcont : ¬ (((splitAt a vs).2.contains b) = true) :=
      fun hc => hcase (List.contains_iff_mem.mp hc)
    rw [between_def, if_neg hcont, List.append_eq_nil_iff] at h
    obtain ⟨hs2, hf2⟩ := h
    have hsp2 := splitAt_ram ha
    rw [hs2] at hsp2
    have hgl : a = vs.getLast! := by
      rw [hsp2]
      exact (getLast!_concat _ _).symm
    have hF : b ∈ (splitAt a vs).1 := by
      have hbv : b ∈ vs := hb
      rw [hsp2] at hbv
      rcases List.mem_append.mp hbv with hbm | hbm
      · exact hbm
      · exact absurd (List.mem_singleton.mp hbm).symm hab
    have hsp3 := splitAt_ram hF
    rw [hf2] at hsp3
    have hhd : b = vs.head! := by
      rw [hsp2, hsp3, List.nil_append, List.cons_append]
      exact (List.head!_cons _ _).symm
    exact Or.inr ⟨List.ne_nil_of_mem ha, hgl, hhd⟩

/-- FaceDivisionProps.thy: between_nextElem -/
theorem between_nextElem {vs : List α} {u v : α}
    (hp : pre_between vs u v) :
    between vs u (nextElem vs vs.head! v) = between vs u v ++ [v] := by
  have hd : vs.Nodup := hp.1
  rcases pre_between_before hp with hb | hb
  · obtain ⟨as, bs, cs, -, hvs⟩ := between_eq2 (pre_between_symI hp) hb
    have hvn : v ∉ as ++ u :: bs := by
      have hvs2 : vs = (as ++ u :: bs) ++ v :: cs := by rw [hvs]; simp [List.append_assoc]
      have hd' : ((as ++ u :: bs) ++ v :: cs).Nodup := hvs2 ▸ hd
      intro hm
      exact (List.nodup_append.mp hd').2.2 v hm v List.mem_cons_self rfl
    have hne : nextElem vs vs.head! v = nextElem (v :: cs) vs.head! v := by
      have hvs2 : vs = (as ++ u :: bs) ++ (v :: cs) := by rw [hvs]; simp [List.append_assoc]
      have e := nextElem_append hvn (v :: cs) vs.head!
      rwa [← hvs2] at e
    have hspu : (as, bs ++ v :: cs) = splitAt u vs :=
      splitAt_dist_ram hd (by rw [hvs]; simp [List.append_assoc])
    have hdbs : (bs ++ v :: cs).Nodup := by
      have hvs2 : vs = as ++ u :: (bs ++ v :: cs) := by rw [hvs]; simp [List.append_assoc]
      have hd' : (as ++ u :: (bs ++ v :: cs)).Nodup := hvs2 ▸ hd
      exact (List.nodup_cons.mp (List.nodup_append.mp hd').2.1).2
    have hspv : (bs, cs) = splitAt v (bs ++ v :: cs) := splitAt_dist_ram hdbs rfl
    have hbtuv : between vs u v = bs := by
      rw [between_simp1 hb hp, ← hspu]
      show (splitAt v (bs ++ v :: cs)).1 = bs
      rw [← hspv]
    cases cs with
    | nil =>
      rw [hne, nextElem_cons_nil, if_pos (beq_self_eq_true v), hbtuv]
      cases as with
      | nil =>
        have hhd : vs.head! = u := by
          have e : vs = u :: (bs ++ [v]) := by rw [hvs]; simp
          rw [e]
          exact List.head!_cons _ _
        rw [hhd]
        have hspu2 : (([] : List α), bs ++ [v]) = splitAt u vs :=
          splitAt_dist_ram hd (by rw [hvs]; simp)
        have hcont : ¬ (((splitAt u vs).2.contains u) = true) := by
          rw [← hspu2]
          intro hc
          have hm : u ∈ bs ++ [v] := List.contains_iff_mem.mp hc
          have hvs3 : vs = u :: (bs ++ [v]) := by rw [hvs]; simp
          have hd' : (u :: (bs ++ [v])).Nodup := hvs3 ▸ hd
          exact (List.nodup_cons.mp hd').1 hm
        rw [between_def, if_neg hcont, ← hspu2]
        simp [splitAt, splitAtRec]
      | cons a as' =>
        have hvs3 : vs = a :: (as' ++ u :: bs ++ [v]) := by rw [hvs]; simp [List.append_assoc]
        have hhd : vs.head! = a := by
          rw [hvs3]
          exact List.head!_cons _ _
        rw [hhd]
        have hbau : before vs a u := ⟨[], as', bs ++ [v], by rw [hvs]; simp [List.append_assoc]⟩
        have hpa : pre_between vs a u := by
          refine ⟨hd, ?_, hp.2.1, ?_⟩
          · rw [hvs3]; exact List.mem_cons_self
          · intro e
            have hvs4 : vs = u :: (as' ++ u :: bs ++ [v]) := by rw [hvs3, e]
            have hd' : (u :: (as' ++ u :: bs ++ [v])).Nodup := hvs4 ▸ hd
            have hm : u ∈ as' ++ u :: bs ++ [v] := by simp
            exact (List.nodup_cons.mp hd').1 hm
        rw [between_simp2 hbau hpa]
        have e1 : (a :: as', bs ++ [v]) = splitAt u vs :=
          splitAt_dist_ram hd (by rw [hvs]; simp [List.append_assoc])
        have e2 : splitAt a vs = ([], as' ++ u :: bs ++ [v]) := by
          rw [hvs3]; exact splitAt_self_cons _ _
        rw [← e1, e2]
        simp
    | cons c cs' =>
      have hne2 : nextElem (v :: c :: cs') vs.head! v = c := by
        rw [nextElem_cons_cons, if_pos (beq_self_eq_true v)]
      rw [hne, hne2, hbtuv]
      have hbc : before vs u c := ⟨as, bs ++ [v], cs', by rw [hvs]; simp [List.append_assoc]⟩
      have hpc : pre_between vs u c := by
        refine ⟨hd, hp.2.1, ?_, ?_⟩
        · rw [hvs]; simp
        · intro e
          have hvs3 : vs = as ++ u :: (bs ++ v :: c :: cs') := by
            rw [hvs]; simp [List.append_assoc]
          rw [e] at hvs3
          have hd' : (as ++ c :: (bs ++ v :: c :: cs')).Nodup := hvs3 ▸ hd
          have hm : c ∈ bs ++ v :: c :: cs' :=
            List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
          exact (List.nodup_cons.mp (List.nodup_append.mp hd').2.1).1 hm
      rw [between_simp1 hbc hpc, ← hspu]
      show (splitAt c (bs ++ v :: c :: cs')).1 = bs ++ [v]
      have e : (bs ++ [v], cs') = splitAt c (bs ++ v :: c :: cs') :=
        splitAt_dist_ram hdbs (by simp [List.append_assoc])
      rw [← e]
  · obtain ⟨as, bs, cs, hbtw, hvs⟩ := between_eq2 hp hb
    have hvn : v ∉ as := by
      have hvs2 : vs = as ++ v :: (bs ++ u :: cs) := by rw [hvs]; simp [List.append_assoc]
      have hd' : (as ++ v :: (bs ++ u :: cs)).Nodup := hvs2 ▸ hd
      intro hm
      exact (List.nodup_append.mp hd').2.2 v hm v List.mem_cons_self rfl
    have hne : nextElem vs vs.head! v = nextElem (v :: (bs ++ u :: cs)) vs.head! v := by
      have hvs2 : vs = as ++ (v :: (bs ++ u :: cs)) := by rw [hvs]; simp [List.append_assoc]
      have e := nextElem_append hvn (v :: (bs ++ u :: cs)) vs.head!
      rwa [← hvs2] at e
    cases bs with
    | nil =>
      have hne2 : nextElem (v :: (([] : List α) ++ u :: cs)) vs.head! v = u := by
        show nextElem (v :: u :: cs) vs.head! v = u
        rw [nextElem_cons_cons, if_pos (beq_self_eq_true v)]
      rw [hne, hne2, hbtw]
      have hspu : (as ++ [v], cs) = splitAt u vs :=
        splitAt_dist_ram hd (by rw [hvs]; simp [List.append_assoc])
      have hcont : ¬ (((splitAt u vs).2.contains u) = true) := by
        rw [← hspu]
        intro hc
        have hm : u ∈ cs := List.contains_iff_mem.mp hc
        have hvs3 : vs = (as ++ [v]) ++ u :: cs := by rw [hvs]; simp
        have hd' : ((as ++ [v]) ++ u :: cs).Nodup := hvs3 ▸ hd
        exact (List.nodup_cons.mp (List.nodup_append.mp hd').2.1).1 hm
      rw [between_def, if_neg hcont, ← hspu]
      show cs ++ (splitAt u (as ++ [v])).1 = cs ++ as ++ [v]
      have hun : u ∉ as ++ [v] := by
        intro hm
        rcases List.mem_append.mp hm with hm | hm
        · have hvs3 : vs = as ++ v :: (u :: cs) := by rw [hvs]; simp
          have hd' : (as ++ v :: u :: cs).Nodup := hvs3 ▸ hd
          exact (List.nodup_append.mp hd').2.2 u hm u
            (List.mem_cons_of_mem _ List.mem_cons_self) rfl
        · exact hp.2.2.2 (List.mem_singleton.mp hm)
      rw [splitAt_no_ram hun]
      simp [List.append_assoc]
    | cons b bs' =>
      have hne2 : nextElem (v :: ((b :: bs') ++ u :: cs)) vs.head! v = b := by
        show nextElem (v :: b :: (bs' ++ u :: cs)) vs.head! v = b
        rw [nextElem_cons_cons, if_pos (beq_self_eq_true v)]
      rw [hne, hne2, hbtw]
      have hbu : before vs b u :=
        ⟨as ++ [v], bs', cs, by rw [hvs]; simp [List.append_assoc]⟩
      have hpb : pre_between vs b u := by
        refine ⟨hd, ?_, hp.2.1, ?_⟩
        · rw [hvs]; simp
        · intro e
          have hvs3 : vs = (as ++ v :: b :: bs') ++ u :: cs := by
            rw [hvs]; simp [List.append_assoc]
          have hd' : ((as ++ v :: b :: bs') ++ u :: cs).Nodup := hvs3 ▸ hd
          have hm : u ∈ as ++ v :: b :: bs' := by
            rw [← e]
            exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
          exact (List.nodup_append.mp hd').2.2 u hm u List.mem_cons_self rfl
      rw [between_simp2 hbu hpb]
      have e1 : (as ++ v :: b :: bs', cs) = splitAt u vs :=
        splitAt_dist_ram hd (by rw [hvs]; simp [List.append_assoc])
      have e2 : (as ++ [v], bs' ++ u :: cs) = splitAt b vs :=
        splitAt_dist_ram hd (by rw [hvs]; simp [List.append_assoc])
      rw [← e1, ← e2]
      simp [List.append_assoc]

end BetweenIsNextElem

/-! ### nextVertices, is_nextElem - edges, nextVertex -/

section NextElemEdges

/-- FaceDivisionProps.thy: nextVertices_in_face -/
@[simp]
theorem nextVertices_in_face {f : Face} {v : Vertex} (hv : v ∈ f.vertices) (n : Nat) :
    f.nextVertices n v ∈ f.vertices := by
  induction n with
  | zero => exact hv
  | succ m ih => exact nextVertex_in_face ih

/-- FaceDivisionProps.thy: is_nextElem_edges1 -/
theorem is_nextElem_edges1 {f : Face} {a b : Vertex} (hd : f.vertices.Nodup)
    (h : (a, b) ∈ f.edges) : is_nextElem f.vertices a b :=
  is_nextElem1 hd (edges_face_eq.mp h).2 (edges_face_eq.mp h).1

/-- FaceDivisionProps.thy: is_nextElem_edges2 -/
theorem is_nextElem_edges2 {f : Face} {a b : Vertex} (hd : f.vertices.Nodup)
    (h : is_nextElem f.vertices a b) : (a, b) ∈ f.edges :=
  edges_face_eq.mpr ⟨is_nextElem2 hd (is_nextElem_a h) h, is_nextElem_a h⟩

/-- FaceDivisionProps.thy: is_nextElem_edges_eq -/
@[simp]
theorem is_nextElem_edges_eq {f : Face} {a b : Vertex} (hd : f.vertices.Nodup) :
    (a, b) ∈ f.edges ↔ is_nextElem f.vertices a b :=
  ⟨is_nextElem_edges1 hd, is_nextElem_edges2 hd⟩

/-- FaceDivisionProps.thy: nextElem_suc2 -/
theorem nextElem_suc2 {f : Face} {v : Vertex} (hd : f.vertices.Nodup)
    (hl : f.vertices.getLast! = v) (_hv : v ∈ f.vertices) :
    f.nextVertex v = f.vertices.head! := by
  show nextElem f.vertices f.vertices.head! v = f.vertices.head!
  rw [← hl]
  exact nextElem_last hd

end NextElemEdges

/-! ### split_face -/

section SplitFace

/-- FaceDivisionProps.thy: pre_split_face.  The set intersection emptiness is
rendered as a membership non-implication, per project convention. -/
def pre_split_face (oldF : Face) (ram₁ ram₂ : Vertex) (newVertexList : List Vertex) : Prop :=
  oldF.vertices.Nodup ∧ newVertexList.Nodup ∧
    (∀ x ∈ oldF.vertices, x ∉ newVertexList) ∧
    ram₁ ∈ oldF.vertices ∧ ram₂ ∈ oldF.vertices ∧ ram₁ ≠ ram₂

/-- FaceDivisionProps.thy: pre_split_face_p_between -/
theorem pre_split_face_p_between {oldF : Face} {ram₁ ram₂ : Vertex} {newVs : List Vertex}
    (h : pre_split_face oldF ram₁ ram₂ newVs) : pre_between oldF.vertices ram₁ ram₂ :=
  ⟨h.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- FaceDivisionProps.thy: pre_split_face_symI -/
theorem pre_split_face_symI {oldF : Face} {ram₁ ram₂ : Vertex} {newVs : List Vertex}
    (h : pre_split_face oldF ram₁ ram₂ newVs) : pre_split_face oldF ram₂ ram₁ newVs :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.1, fun e => h.2.2.2.2.2 e.symm⟩

/-- FaceDivisionProps.thy: pre_split_face_rev -/
theorem pre_split_face_rev {oldF : Face} {ram₁ ram₂ : Vertex} {newVs : List Vertex}
    (h : pre_split_face oldF ram₁ ram₂ newVs) :
    pre_split_face oldF ram₁ ram₂ newVs.reverse :=
  ⟨h.1, List.nodup_reverse.mpr h.2.1,
    fun x hx hm => h.2.2.1 x hx (List.mem_reverse.mp hm), h.2.2.2⟩

/-- FaceDivisionProps.thy: split_face_distinct1 -/
theorem split_face_distinct1 {f12 f21 oldF : Face} {ram₁ ram₂ : Vertex} {newVs : List Vertex}
    (hsplit : (f12, f21) = split_face oldF ram₁ ram₂ newVs)
    (hp : pre_split_face oldF ram₁ ram₂ newVs) : f12.vertices.Nodup := by
  have hv12 : f12.vertices =
      newVs.reverse ++ (ram₁ :: between oldF.vertices ram₁ ram₂ ++ [ram₂]) := by
    have hf : f12 = (split_face oldF ram₁ ram₂ newVs).1 := congrArg Prod.fst hsplit
    rw [hf]; rfl
  rw [hv12]
  apply List.nodup_append.mpr
  refine ⟨List.nodup_reverse.mpr hp.2.1, between_distinct_r12 hp.1 hp.2.2.2.2.2, ?_⟩
  intro x hx y hy hxy
  have hyv : y ∈ oldF.vertices := by
    rcases List.mem_append.mp hy with hy | hy
    · rcases List.mem_cons.mp hy with h | h
      · exact h.symm ▸ hp.2.2.2.1
      · exact inbetween_inset h
    · exact (List.mem_singleton.mp hy).symm ▸ hp.2.2.2.2.1
  exact hp.2.2.1 y hyv (hxy ▸ List.mem_reverse.mp hx)

/-- FaceDivisionProps.thy: split_face_distinct1' -/
theorem split_face_distinct1' {oldF : Face} {ram₁ ram₂ : Vertex} {newVs : List Vertex}
    (hp : pre_split_face oldF ram₁ ram₂ newVs) :
    (split_face oldF ram₁ ram₂ newVs).1.vertices.Nodup :=
  split_face_distinct1 rfl hp

/-- FaceDivisionProps.thy: split_face_distinct2 -/
theorem split_face_distinct2 {f12 f21 oldF : Face} {ram₁ ram₂ : Vertex} {newVs : List Vertex}
    (hsplit : (f12, f21) = split_face oldF ram₁ ram₂ newVs)
    (hp : pre_split_face oldF ram₁ ram₂ newVs) : f21.vertices.Nodup := by
  have hv21 : f21.vertices =
      (ram₂ :: between oldF.vertices ram₂ ram₁ ++ [ram₁]) ++ newVs := by
    have hf : f21 = (split_face oldF ram₁ ram₂ newVs).2 := congrArg Prod.snd hsplit
    rw [hf]; rfl
  rw [hv21]
  apply List.nodup_append.mpr
  refine ⟨between_distinct_r12 hp.1 (fun e => hp.2.2.2.2.2 e.symm), hp.2.1, ?_⟩
  intro x hx y hy hxy
  have hxv : x ∈ oldF.vertices := by
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_cons.mp hx with h | h
      · exact h.symm ▸ hp.2.2.2.2.1
      · exact inbetween_inset h
    · exact (List.mem_singleton.mp hx).symm ▸ hp.2.2.2.1
  exact hp.2.2.1 x hxv (hxy.symm ▸ hy)

/-- FaceDivisionProps.thy: split_face_distinct2' -/
theorem split_face_distinct2' {oldF : Face} {ram₁ ram₂ : Vertex} {newVs : List Vertex}
    (hp : pre_split_face oldF ram₁ ram₂ newVs) :
    (split_face oldF ram₁ ram₂ newVs).2.vertices.Nodup :=
  split_face_distinct2 rfl hp

/-- FaceDivisionProps.thy: split_face_edges_or -/
theorem split_face_edges_or {f12 f21 oldF : Face} {a b ram₁ ram₂ : Vertex}
    {newVs : List Vertex}
    (hsplit : (f12, f21) = split_face oldF ram₁ ram₂ newVs)
    (hp : pre_split_face oldF ram₁ ram₂ newVs)
    (h : (a, b) ∈ oldF.edges) : (a, b) ∈ f12.edges ∨ (a, b) ∈ f21.edges := by
  have d2 : f12.vertices.Nodup := split_face_distinct1 hsplit hp
  have d3 : f21.vertices.Nodup := split_face_distinct2 hsplit hp
  have hp' : pre_between oldF.vertices ram₁ ram₂ := pre_split_face_p_between hp
  have hne : is_nextElem oldF.vertices a b := is_nextElem_edges1 hp.1 h
  rcases is_nextElem_or hp' hne with hsub | hsub
  · left
    have hv12 : f12.vertices =
        newVs.reverse ++ (ram₁ :: between oldF.vertices ram₁ ram₂ ++ [ram₂]) := by
      have hf : f12 = (split_face oldF ram₁ ram₂ newVs).1 := congrArg Prod.fst hsplit
      rw [hf]; rfl
    have hne2 : is_nextElem f12.vertices a b := by
      apply is_nextElem_sublistI
      rw [hv12]
      obtain ⟨as, bs, hsub'⟩ := hsub
      exact ⟨newVs.reverse ++ as, bs, by rw [hsub']; simp [List.append_assoc]⟩
    exact is_nextElem_edges2 d2 hne2
  · right
    have hv21 : f21.vertices =
        (ram₂ :: between oldF.vertices ram₂ ram₁ ++ [ram₁]) ++ newVs := by
      have hf : f21 = (split_face oldF ram₁ ram₂ newVs).2 := congrArg Prod.snd hsplit
      rw [hf]; rfl
    have hne2 : is_nextElem f21.vertices a b := by
      apply is_nextElem_sublistI
      rw [hv21]
      obtain ⟨as, bs, hsub'⟩ := hsub
      exact ⟨as, bs ++ newVs, by rw [hsub']; simp [List.append_assoc]⟩
    exact is_nextElem_edges2 d3 hne2

end SplitFace

/-! ### verticesFrom -/

section VerticesFrom

/-- FaceDivisionProps.thy: verticesFrom -/
def verticesFrom (f : Face) (v : Vertex) : List Vertex := rotate_to f.vertices v

/-- FaceDivisionProps.thy: len_vFrom -/
@[simp]
theorem len_vFrom {f : Face} {v : Vertex} (hv : v ∈ f.vertices) :
    (verticesFrom f v).length = f.vertices.length := by
  show (rotate_to f.vertices v).length = f.vertices.length
  rw [rotate_to_eq_rotate hv, List.length_rotate]

/-- FaceDivisionProps.thy: verticesFrom_empty -/
@[simp]
theorem verticesFrom_empty {f : Face} {v : Vertex} (hv : v ∈ f.vertices) :
    (verticesFrom f v = []) ↔ (f.vertices = []) := by
  show (rotate_to f.vertices v = []) ↔ _
  rw [rotate_to_eq_rotate hv, List.rotate_eq_nil_iff]

/-- FaceDivisionProps.thy: verticesFrom_congs -/
theorem verticesFrom_congs {f : Face} {v : Vertex} (hv : v ∈ f.vertices) :
    cong f.vertices (verticesFrom f v) :=
  cong_rotate_to hv

/-- FaceDivisionProps.thy: verticesFrom_hd -/
theorem verticesFrom_hd (f : Face) (v : Vertex) : (verticesFrom f v).head! = v := by
  show ((v :: (splitAt v f.vertices).2) ++ (splitAt v f.vertices).1).head! = v
  exact (List.head!_append _ (List.cons_ne_nil _ _)).trans (List.head!_cons _ _)

/-- FaceDivisionProps.thy: verticesFrom_eq_if_vertices_cong -/
theorem verticesFrom_eq_if_vertices_cong {f f' : Face} {x : Vertex}
    (hd : f.vertices.Nodup) (_hd' : f'.vertices.Nodup)
    (hc : cong f.vertices f'.vertices) (hx : x ∈ f.vertices) :
    verticesFrom f x = verticesFrom f' x := by
  obtain ⟨n, hn⟩ := hc
  have hne : f.vertices ≠ [] := List.ne_nil_of_mem hx
  have hlen : 0 < f.vertices.length := List.length_pos_iff.mpr hne
  have hx' : x ∈ f'.vertices := hn ▸ List.mem_rotate.mpr hx
  have e1 : verticesFrom f x = f.vertices.rotate (splitAt x f.vertices).1.length :=
    rotate_to_eq_rotate hx
  have e2 : verticesFrom f' x =
      f.vertices.rotate (n + (splitAt x f'.vertices).1.length) := by
    show rotate_to f'.vertices x = _
    rw [rotate_to_eq_rotate hx']
    nth_rewrite 1 [hn]
    rw [List.rotate_rotate]
  rw [e1, e2]
  apply (List.Nodup.rotate_congr_iff hd).mpr
  left
  have h1 : f.vertices[(splitAt x f.vertices).1.length % f.vertices.length]! = x := by
    have hh : (f.vertices.rotate (splitAt x f.vertices).1.length).head! = x := by
      rw [← e1]; exact verticesFrom_hd f x
    rwa [List.head!_eq_getElem!,
      getElem!_rotate f.vertices _ 0 (by rw [List.length_rotate]; exact hlen),
      Nat.zero_add] at hh
  have h2 : f.vertices[(n + (splitAt x f'.vertices).1.length) % f.vertices.length]! = x := by
    have hh : (f.vertices.rotate (n + (splitAt x f'.vertices).1.length)).head! = x := by
      rw [← e2]; exact verticesFrom_hd f' x
    rwa [List.head!_eq_getElem!,
      getElem!_rotate f.vertices _ 0 (by rw [List.length_rotate]; exact hlen),
      Nat.zero_add] at hh
  exact (List.getElem!_inj (Nat.mod_lt _ hlen) (Nat.mod_lt _ hlen) hd).mp (h1.trans h2.symm)

/-- FaceDivisionProps.thy: verticesFrom_in -/
theorem verticesFrom_in {f : Face} {v a : Vertex} (hv : v ∈ f.vertices)
    (ha : a ∈ f.vertices) : a ∈ verticesFrom f v :=
  (cong_mem (verticesFrom_congs hv)).mp ha

/-- FaceDivisionProps.thy: verticesFrom_in' -/
theorem verticesFrom_in' {f : Face} {a v : Vertex} (ha : a ∈ verticesFrom f v)
    (hne : a ≠ v) : a ∈ f.vertices := by
  by_cases hv : v ∈ f.vertices
  · exact (cong_mem (verticesFrom_congs hv)).mpr ha
  · have hsp : splitAt v f.vertices = (f.vertices, []) := splitAt_no_ram hv
    have hvf : verticesFrom f v = v :: f.vertices := by
      show (v :: (splitAt v f.vertices).2) ++ (splitAt v f.vertices).1 = v :: f.vertices
      rw [hsp]; rfl
    rw [hvf] at ha
    rcases List.mem_cons.mp ha with h | h
    · exact absurd h hne
    · exact h

/-- FaceDivisionProps.thy: set_verticesFrom (membership form) -/
theorem set_verticesFrom {f : Face} {v : Vertex} (hv : v ∈ f.vertices) (a : Vertex) :
    a ∈ verticesFrom f v ↔ a ∈ f.vertices :=
  (cong_mem (verticesFrom_congs hv)).symm

/-- FaceDivisionProps.thy: verticesFrom_distinct -/
@[simp]
theorem verticesFrom_distinct {f : Face} {v : Vertex} (hd : f.vertices.Nodup)
    (hv : v ∈ f.vertices) : (verticesFrom f v).Nodup :=
  (cong_distinct (verticesFrom_congs hv)).mp hd

/-- FaceDivisionProps.thy: verticesFrom_nextElem_eq -/
theorem verticesFrom_nextElem_eq {f : Face} {v u : Vertex} (hd : f.vertices.Nodup)
    (hv : v ∈ f.vertices) (hu : u ∈ f.vertices) :
    nextElem (verticesFrom f v) (verticesFrom f v).head! u =
      nextElem f.vertices f.vertices.head! u :=
  (nextElem_congs_eq (verticesFrom_congs hv) hd hu).symm

/-- Auxiliary: the `ind` subproof of FaceDivisionProps.thy `nextElem_vFrom_suc1`. -/
theorem nextElem_eq_getElem!_succ_of_Nodup [BEq α] [LawfulBEq α] [Inhabited α]
    {ls : List α} {u c : α} {i : Nat} (hd : ls.Nodup) (hi : i < ls.length)
    (hlast : ls.getLast! ≠ u) (hith : ls[i]! = u) :
    nextElem ls c u = ls[i + 1]! := by
  revert hd hi hlast hith
  induction ls generalizing i with
  | nil => intro _ hi _ _; simp at hi
  | cons m ms ih =>
    intro hd hi hlast hith
    cases i with
    | zero =>
      rw [List.getElem!_cons_zero] at hith
      subst hith
      cases ms with
      | nil => exact absurd rfl hlast
      | cons m' ms' =>
        rw [nextElem_cons_cons, if_pos (beq_self_eq_true m),
          List.getElem!_cons_succ, List.getElem!_cons_zero]
    | succ j =>
      rw [List.getElem!_cons_succ] at hith
      have hlt' : j < ms.length := by
        rw [List.length_cons] at hi; omega
      have hms : ms ≠ [] := List.ne_nil_of_length_pos (by omega)
      have hum : u ≠ m := by
        intro e
        have h01 : (m :: ms)[0]! = (m :: ms)[j + 1]! := by
          rw [List.getElem!_cons_zero, List.getElem!_cons_succ]
          exact e.symm.trans hith.symm
        have hinj := (List.getElem!_inj (by rw [List.length_cons]; omega) hi hd).mp h01
        exact (Nat.succ_ne_zero j) hinj.symm
      have egl : (m :: ms).getLast! = ms.getLast! := by
        rw [List.getLast!_eq_getElem!, List.getLast!_eq_getElem!, List.length_cons]
        have hj : ms.length + 1 - 1 = ms.length - 1 + 1 := by
          have : 0 < ms.length := List.length_pos_iff.mpr hms
          omega
        rw [hj, List.getElem!_cons_succ]
      have hlast' : ms.getLast! ≠ u := egl ▸ hlast
      rw [nextElem_cons, if_neg (beq_ne_true_of_ne hum), List.getElem!_cons_succ]
      exact ih (List.nodup_cons.mp hd).2 hlt' hlast' hith

/-- FaceDivisionProps.thy: nextElem_vFrom_suc1 -/
theorem nextElem_vFrom_suc1 {f : Face} {v u : Vertex} {i : Nat}
    (hd : f.vertices.Nodup) (hv : v ∈ f.vertices) (hi : i < f.vertices.length)
    (hlast : (verticesFrom f v).getLast! ≠ u) (hith : (verticesFrom f v)[i]! = u) :
    f.nextVertex u = (verticesFrom f v)[i + 1]! := by
  have hc : cong f.vertices (verticesFrom f v) := verticesFrom_congs hv
  have hlen : (verticesFrom f v).length = f.vertices.length := (cong_length hc).symm
  have hu : u ∈ f.vertices := by
    have hlt : i < (verticesFrom f v).length := by rw [hlen]; exact hi
    have hum : u ∈ verticesFrom f v := by
      have hm : (verticesFrom f v)[i]! ∈ verticesFrom f v := by
        rw [getElem!_pos (verticesFrom f v) i hlt]
        exact List.getElem_mem hlt
      rwa [hith] at hm
    exact (cong_mem hc).mpr hum
  have hd2 : (verticesFrom f v).Nodup := verticesFrom_distinct hd hv
  have h2 : nextElem (verticesFrom f v) (verticesFrom f v).head! u =
      (verticesFrom f v)[i + 1]! :=
    nextElem_eq_getElem!_succ_of_Nodup hd2 (by rw [hlen]; exact hi) hlast hith
  show nextElem f.vertices f.vertices.head! u = (verticesFrom f v)[i + 1]!
  rwa [← verticesFrom_nextElem_eq hd hv hu]

/-- FaceDivisionProps.thy: verticesFrom_nth -/
theorem verticesFrom_nth {f : Face} {v : Vertex} (hd : f.vertices.Nodup) {d : Nat}
    (hdlt : d < f.vertices.length) (hv : v ∈ f.vertices) :
    (verticesFrom f v)[d]! = f.nextVertices d v := by
  revert hdlt
  induction d with
  | zero =>
    intro _
    exact List.head!_eq_getElem!.symm.trans (verticesFrom_hd f v)
  | succ n ih =>
    intro hdlt
    have hlt : n < f.vertices.length := by omega
    have hih := ih hlt
    have hc : cong f.vertices (verticesFrom f v) := verticesFrom_congs hv
    have hlen : (verticesFrom f v).length = f.vertices.length := (cong_length hc).symm
    have hd2 : (verticesFrom f v).Nodup := verticesFrom_distinct hd hv
    by_cases hlast : (verticesFrom f v).getLast! = f.nextVertices n v
    · exfalso
      have h1 : (verticesFrom f v).getLast! =
          (verticesFrom f v)[(verticesFrom f v).length - 1]! := List.getLast!_eq_getElem!
      have h3 : (verticesFrom f v)[n]! =
          (verticesFrom f v)[(verticesFrom f v).length - 1]! :=
        (hih.trans hlast.symm).trans h1
      have hpos : 0 < (verticesFrom f v).length := by rw [hlen]; omega
      have hn1 : n = (verticesFrom f v).length - 1 :=
        (List.getElem!_inj (by rw [hlen]; exact hlt) (by omega) hd2).mp h3
      rw [hlen] at hn1
      omega
    · exact (nextElem_vFrom_suc1 hd hv hlt hlast hih).symm

/-- FaceDivisionProps.thy: verticesFrom_length -/
theorem verticesFrom_length {f : Face} {v : Vertex} (_hd : f.vertices.Nodup)
    (hv : v ∈ f.vertices) : (verticesFrom f v).length = f.vertices.length :=
  len_vFrom hv

/-- FaceDivisionProps.thy: verticesFrom_between -/
theorem verticesFrom_between {f : Face} {u v v' : Vertex} (hv' : v' ∈ f.vertices)
    (hp : pre_between f.vertices u v) :
    between f.vertices u v = between (verticesFrom f v') u v :=
  between_congs hp (verticesFrom_congs hv')

/-- FaceDivisionProps.thy: verticesFrom_is_nextElem -/
theorem verticesFrom_is_nextElem {f : Face} {a b v : Vertex} (hv : v ∈ f.vertices) :
    is_nextElem f.vertices a b ↔ is_nextElem (verticesFrom f v) a b :=
  is_nextElem_congs_eq (verticesFrom_congs hv)

/-- FaceDivisionProps.thy: verticesFrom_is_nextElem_last -/
theorem verticesFrom_is_nextElem_last {f : Face} {v v' : Vertex}
    (hv' : v' ∈ f.vertices) (hd : f.vertices.Nodup)
    (h : is_nextElem (verticesFrom f v') (verticesFrom f v').getLast! v) : v = v' := by
  have d2 := verticesFrom_distinct hd hv'
  have hne : verticesFrom f v' ≠ [] := List.ne_nil_of_mem (verticesFrom_in hv' hv')
  have hmem : (verticesFrom f v').getLast! ∈ verticesFrom f v' := getLast!_mem hne
  rw [nextElem_is_nextElem d2 hmem, nextElem_last d2, verticesFrom_hd] at h
  exact h.symm

/-- FaceDivisionProps.thy: verticesFrom_is_nextElem_hd -/
theorem verticesFrom_is_nextElem_hd {f : Face} {u v' : Vertex}
    (hv' : v' ∈ f.vertices) (hd : f.vertices.Nodup)
    (h : is_nextElem (verticesFrom f v') u v') : u = (verticesFrom f v').getLast! := by
  have d2 := verticesFrom_distinct hd hv'
  rcases h with hsub | ⟨-, hx, -⟩
  · exact absurd hsub (is_sublist_y_hd d2 (verticesFrom_hd f v').symm)
  · exact hx

/-- FaceDivisionProps.thy: verticesFrom_pres_nodes1 (membership form) -/
theorem verticesFrom_pres_nodes1 {f : Face} {v : Vertex} (hv : v ∈ f.vertices) (w : Vertex) :
    w ∈ f.vertices ↔ w ∈ verticesFrom f v :=
  cong_mem (verticesFrom_congs hv)

/-- FaceDivisionProps.thy: verticesFrom_pres_nodes -/
theorem verticesFrom_pres_nodes {f : Face} {v w : Vertex} (hv : v ∈ f.vertices)
    (hw : w ∈ f.vertices) : w ∈ verticesFrom f v :=
  verticesFrom_in hv hw

/-- FaceDivisionProps.thy: before_verticesFrom -/
theorem before_verticesFrom {f : Face} {v w : Vertex} (hd : f.vertices.Nodup)
    (hv : v ∈ f.vertices) (hw : w ∈ f.vertices) (hne : v ≠ w) :
    before (verticesFrom f v) v w := by
  have hne2 : verticesFrom f v ≠ [] := List.ne_nil_of_mem (verticesFrom_in hv hv)
  have h1 : verticesFrom f v = (verticesFrom f v).head! :: (verticesFrom f v).tail :=
    (List.cons_head!_tail hne2).symm
  rw [verticesFrom_hd] at h1
  have h2 : w ∈ (verticesFrom f v).tail := by
    have hw2 := verticesFrom_in hv hw
    rw [h1] at hw2
    rcases List.mem_cons.mp hw2 with h | h
    · exact absurd h.symm hne
    · exact h
  obtain ⟨a, b, hab⟩ := List.append_of_mem h2
  exact ⟨[], a, b, by rw [h1, hab]; rfl⟩

/-- FaceDivisionProps.thy: last_vFrom -/
theorem last_vFrom {f : Face} {x : Vertex} (hd : f.vertices.Nodup) (hx : x ∈ f.vertices) :
    (verticesFrom f x).getLast! = f.prevVertex x := by
  obtain ⟨A, B, hvs⟩ := List.append_of_mem hx
  have hsp : (A, B) = splitAt x f.vertices := splitAt_dist_ram hd hvs
  have hvf : verticesFrom f x = (x :: B) ++ A := by
    show (x :: (splitAt x f.vertices).2) ++ (splitAt x f.vertices).1 = (x :: B) ++ A
    rw [← hsp]
  have hrev : f.vertices.reverse = B.reverse ++ x :: A.reverse := by
    rw [hvs]
    simp [List.reverse_append]
  have hxB : x ∉ B.reverse := by
    rw [List.mem_reverse]
    intro hm
    have hd' : (A ++ x :: B).Nodup := hvs ▸ hd
    exact (List.nodup_cons.mp (List.nodup_append.mp hd').2.1).1 hm
  show (verticesFrom f x).getLast! = nextElem f.vertices.reverse f.vertices.getLast! x
  rw [hrev, nextElem_append hxB (x :: A.reverse) f.vertices.getLast!]
  by_cases hA : A = []
  · subst hA
    rw [hvf, List.append_nil, List.reverse_nil, nextElem_cons_nil,
      if_pos (beq_self_eq_true x), hvs, List.nil_append]
  · obtain ⟨a', as', hA'⟩ := List.exists_cons_of_ne_nil (List.reverse_ne_nil_iff.mpr hA)
    rw [hvf, hA', nextElem_cons_cons, if_pos (beq_self_eq_true x)]
    have ha' : a' = A.getLast! := by
      have e : A.getLast! = A.reverse.head! := (head!_reverse A).symm
      rw [hA', List.head!_cons] at e
      exact e.symm
    rw [ha']
    exact getLast!_append_right _ hA

/-- Auxiliary for `rotate_before_vFrom`: from an explicit split of
`f.vertices` at `v`, any decomposition witnessing `before` applies.
(Replaces the list-manipulation combinatorics of the Isabelle proof.) -/
theorem before_verticesFrom_of_split {f : Face} {r u v : Vertex}
    (hd : f.vertices.Nodup) {P S α β γ : List Vertex}
    (hsplit : f.vertices = P ++ v :: S)
    (hgoal : (v :: S) ++ P = α ++ r :: β ++ u :: γ) : before (verticesFrom f v) r u := by
  have hspv : (P, S) = splitAt v f.vertices := splitAt_dist_ram hd hsplit
  have hvfv : verticesFrom f v = (v :: S) ++ P := by
    show (v :: (splitAt v f.vertices).2) ++ (splitAt v f.vertices).1 = (v :: S) ++ P
    rw [← hspv]
  rw [hvfv]
  exact ⟨α, β, γ, hgoal⟩

/-- FaceDivisionProps.thy: rotate_before_vFrom -/
theorem rotate_before_vFrom {f : Face} {r u v : Vertex}
    (hd : f.vertices.Nodup) (hr : r ∈ f.vertices) (hru : r ≠ u)
    (h : before (verticesFrom f r) u v) : before (verticesFrom f v) r u := by
  obtain ⟨A, B, hvs⟩ := List.append_of_mem hr
  have hsp : (A, B) = splitAt r f.vertices := splitAt_dist_ram hd hvs
  have hvfr : verticesFrom f r = r :: (B ++ A) := by
    show (r :: (splitAt r f.vertices).2) ++ (splitAt r f.vertices).1 = r :: (B ++ A)
    rw [← hsp]
    rfl
  obtain ⟨a, b, c, hdec⟩ := h
  rw [hvfr] at hdec
  have d2 : (r :: (B ++ A)).Nodup := hvfr ▸ verticesFrom_distinct hd hr
  have hane : a ≠ [] := by
    intro hnil
    subst hnil
    rw [List.nil_append] at hdec
    have e1 : (r :: (B ++ A)).head! = r := List.head!_cons _ _
    rw [hdec, List.head!_append _ (List.cons_ne_nil _ _), List.head!_cons] at e1
    exact hru e1.symm
  have har : a.head! = r := by
    have e1 : (r :: (B ++ A)).head! = r := List.head!_cons _ _
    rw [hdec, List.head!_append _ (List.append_ne_nil_of_left_ne_nil hane _),
      List.head!_append _ hane] at e1
    exact e1
  obtain ⟨a', ha⟩ : ∃ a', a = r :: a' :=
    ⟨a.tail, by rw [← har]; exact (List.cons_head!_tail hane).symm⟩
  subst ha
  have hdec2 : B ++ A = a' ++ u :: b ++ v :: c := by
    have e : r :: (B ++ A) = r :: ((a' ++ u :: b) ++ (v :: c)) := hdec
    exact (List.cons.inj e).2
  rcases List.append_eq_append_iff.mp hdec2 with ⟨t, h1, h2⟩ | ⟨t, h1, h2⟩
  · -- `a' ++ (u :: b) = B ++ t`, `A = t ++ (v :: c)`
    apply before_verticesFrom_of_split hd
      (P := t) (S := c ++ r :: B) (α := v :: c) (β := a') (γ := b)
    · rw [hvs, h2]; simp [List.append_assoc]
    · simp [List.append_assoc, ← h1]
  · cases t with
    | nil =>
      rw [List.nil_append] at h2
      rw [List.append_nil] at h1
      -- `B = a' ++ (u :: b)`, `A = v :: c`
      apply before_verticesFrom_of_split hd
        (P := []) (S := c ++ r :: B) (α := v :: c) (β := a') (γ := b)
      · rw [hvs, ← h2]; simp [List.append_assoc]
      · simp [List.append_assoc, h1]
    | cons t₀ t' =>
      have e2 : v :: c = t₀ :: (t' ++ A) := h2
      obtain ⟨ht0, hcA⟩ := List.cons.inj e2
      subst ht0
      -- `B = (a' ++ (u :: b)) ++ (v :: t')`, `c = t' ++ A`
      apply before_verticesFrom_of_split hd
        (P := A ++ r :: a' ++ u :: b) (S := t')
        (α := v :: (t' ++ A)) (β := a') (γ := b)
      · rw [hvs, h1]; simp [List.append_assoc]
      · simp [List.append_assoc]

/-- FaceDivisionProps.thy: before_between -/
theorem before_between {f : Face} {x y z : Vertex}
    (hb : before (verticesFrom f x) y z) (hd : f.vertices.Nodup) (hx : x ∈ f.vertices)
    (hne : x ≠ y) : y ∈ between f.vertices x z := by
  have d2 : (verticesFrom f x).Nodup := verticesFrom_distinct hd hx
  have hzm : z ∈ verticesFrom f x := before_r2 hb
  have hzv : z ∈ f.vertices := (cong_mem (verticesFrom_congs hx)).mpr hzm
  have hxz : x ≠ z := by
    rintro rfl
    obtain ⟨a, b, c, hdec⟩ := hb
    have e : verticesFrom f x = (a ++ y :: b) ++ x :: c := by
      rw [hdec]
    have hd' : ((a ++ y :: b) ++ x :: c).Nodup := e ▸ d2
    have hne2 : (a ++ y :: b) ≠ [] :=
      List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
    have hx1 : x ∈ a ++ y :: b := by
      have e1 : (a ++ y :: b).head! = x := by
        have t : (verticesFrom f x).head! = x := verticesFrom_hd f x
        rw [e, List.head!_append _ hne2] at t
        exact t
      rw [← e1]
      exact head!_mem hne2
    exact (List.nodup_append.mp hd').2.2 x hx1 x List.mem_cons_self rfl
  have hp : pre_between f.vertices x z := ⟨hd, hx, hzv, hxz⟩
  have hne3 : verticesFrom f x ≠ [] := List.ne_nil_of_mem hzm
  have h1 : verticesFrom f x = (verticesFrom f x).head! :: (verticesFrom f x).tail :=
    (List.cons_head!_tail hne3).symm
  rw [verticesFrom_hd] at h1
  have hzt : z ∈ (verticesFrom f x).tail := by
    rw [h1] at hzm
    rcases List.mem_cons.mp hzm with h | h
    · exact absurd h.symm hxz
    · exact h
  obtain ⟨T1, T2, hT⟩ := List.append_of_mem hzt
  have hbxz : before (verticesFrom f x) x z := ⟨[], T1, T2, by rw [h1, hT]; rfl⟩
  have hp2 : pre_between (verticesFrom f x) x z :=
    ⟨d2, verticesFrom_in hx hx, hzm, hxz⟩
  have hspx : splitAt x (verticesFrom f x) = ([], (verticesFrom f x).tail) := by
    rw [h1]; exact splitAt_self_cons _ _
  have hdt : (verticesFrom f x).tail.Nodup := (List.nodup_cons.mp (h1 ▸ d2)).2
  have hspz : (T1, T2) = splitAt z (verticesFrom f x).tail := splitAt_dist_ram hdt hT
  have hbt : between (verticesFrom f x) x z = T1 := by
    rw [between_simp1 hbxz hp2, hspx]
    show (splitAt z (verticesFrom f x).tail).1 = T1
    rw [← hspz]
  obtain ⟨a, b, c, hdec⟩ := hb
  have hane : a ≠ [] := by
    intro hnil
    subst hnil
    rw [List.nil_append] at hdec
    have e1 : (verticesFrom f x).head! = y := by
      rw [hdec, List.head!_append _ (List.cons_ne_nil _ _), List.head!_cons]
    exact hne ((verticesFrom_hd f x).symm.trans e1)
  have har : a.head! = x := by
    have t : (verticesFrom f x).head! = a.head! := by
      rw [hdec, List.head!_append _ (List.append_ne_nil_of_left_ne_nil hane _),
        List.head!_append _ hane]
    rw [verticesFrom_hd] at t
    exact t.symm
  obtain ⟨a', ha⟩ : ∃ a', a = x :: a' :=
    ⟨a.tail, by rw [← har]; exact (List.cons_head!_tail hane).symm⟩
  subst ha
  have htail : (verticesFrom f x).tail = a' ++ y :: b ++ z :: c := by
    have e : verticesFrom f x = x :: ((a' ++ y :: b) ++ (z :: c)) := hdec
    rw [h1] at e
    exact (List.cons.inj e).2
  have hspz2 : (a' ++ y :: b, c) = splitAt z (verticesFrom f x).tail :=
    splitAt_dist_ram hdt (by rw [htail])
  have hT1 : T1 = a' ++ y :: b := congrArg Prod.fst (hspz.trans hspz2.symm)
  rw [verticesFrom_between hx hp, hbt, hT1]
  exact List.mem_append_right _ List.mem_cons_self

/-- FaceDivisionProps.thy: before_between2 -/
theorem before_between2 {f : Face} {u v w : Vertex}
    (hb : before (verticesFrom f u) v w) (hd : f.vertices.Nodup) (hu : u ∈ f.vertices) :
    u = v ∨ u ∈ between f.vertices w v := by
  have d2 : (verticesFrom f u).Nodup := verticesFrom_distinct hd hu
  have hvm : v ∈ verticesFrom f u := before_r1 hb
  have hwm : w ∈ verticesFrom f u := before_r2 hb
  have hvw : v ≠ w := by
    intro e
    obtain ⟨a, b, c, hdec⟩ := hb
    rw [← e] at hdec
    have e' : verticesFrom f u = (a ++ v :: b) ++ v :: c := by
      rw [hdec]
    have hd' : ((a ++ v :: b) ++ v :: c).Nodup := e' ▸ d2
    exact (List.nodup_append.mp hd').2.2 v (List.mem_append_right _ List.mem_cons_self) v
      List.mem_cons_self rfl
  have hvf : v ∈ f.vertices := (cong_mem (verticesFrom_congs hu)).mpr hvm
  have hwf : w ∈ f.vertices := (cong_mem (verticesFrom_congs hu)).mpr hwm
  have hp : pre_between f.vertices w v := ⟨hd, hwf, hvf, fun e => hvw e.symm⟩
  have hp2 : pre_between (verticesFrom f u) v w := ⟨d2, hvm, hwm, hvw⟩
  rw [verticesFrom_between hu hp]
  obtain ⟨a, b, c, hdec⟩ := hb
  have hbtw : between (verticesFrom f u) w v = c ++ a := by
    rw [between_simp2 ⟨a, b, c, hdec⟩ hp2]
    have e1 : (a, b ++ w :: c) = splitAt v (verticesFrom f u) :=
      splitAt_dist_ram d2 (by rw [hdec]; simp [List.append_assoc])
    have e2 : (a ++ v :: b, c) = splitAt w (verticesFrom f u) :=
      splitAt_dist_ram d2 (by rw [hdec])
    rw [← e1, ← e2]
  rw [hbtw]
  cases a with
  | nil =>
    left
    have e : (verticesFrom f u).head! = v := by
      rw [hdec, List.nil_append, List.head!_append _ (List.cons_ne_nil _ _),
        List.head!_cons]
    exact ((verticesFrom_hd f u).symm.trans e)
  | cons a₀ a' =>
    right
    have e : (verticesFrom f u).head! = a₀ := by
      rw [hdec, List.head!_append _
        (List.append_ne_nil_of_left_ne_nil (List.cons_ne_nil _ _) _),
        List.head!_append _ (List.cons_ne_nil _ _), List.head!_cons]
    have hua : u = a₀ := (verticesFrom_hd f u).symm.trans e
    rw [hua]
    exact List.mem_append_right _ List.mem_cons_self

end VerticesFrom

end Kepler.Graphs
