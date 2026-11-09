/-
  JcajyduAqLeaf13W1 — AQ13 叶 W1（原生路线 B）：轨道下界引理。
  HOL 折叠：AQ13.hl 的 ② lm_le(63) ③ s_list_subset(35) ⑥ lm_lt(113)
  ⑦ y_in_s_list(51) ⑬ betwn_lt(288) ⑭ betwn_in_s_list(43) = 593 行，
  折叠为「l'm rtr ≥ l'm r + |W| + 1」（W = betwn f l'y l'z）。
  证明内核：rtr = A ++ W（A = [z]++betwn r z y++[y]）上，x→z 前段
  nextEl rtr 与 fList 一致（12X 幂等式 + W 的 f-orbit 枚举）。
  纪律：零 axiom/sorry/admit/native_decide；主仓 tracked 零改动。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf12X
import Kepler.Text.TameSpine.JcajyduAqLeaf7
import Kepler.Text.TameSpine.JcajyduAqLeaf10G

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts eList fList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList dart_in_face findFaceDarts_nodup
  getD_eq_getElem_of_lt nextEl_eq_getD)

/-- AQ13 W1 的 A 段：`[z] ++ betwn r z y ++ [y]`。 -/
noncomputable def aq13A (L : fgraph ℕ) (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ))
    (x : ℕ × ℕ) : List (ℕ × ℕ) :=
  [lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x) ++ [lYSpine L r x]

/-- AQ13 W1 的 W 段：`betwn f y z`（f = findFaceDarts L x）。 -/
noncomputable def aq13W (L : fgraph ℕ) (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ))
    (x : ℕ × ℕ) : List (ℕ × ℕ) :=
  between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)

/-! ## §0 列表私件 -/

private theorem aq13w1_head!_eq_getElem {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.head! = l[0]'(List.length_pos_of_ne_nil h) := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rfl

private theorem aq13w1_getLast!_append_singleton {α : Type*} [Inhabited α]
    (l : List α) (a : α) : (l ++ [a]).getLast! = a := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_append]
  simp

private theorem aq13w1_getLast!_append_of_ne {α : Type*} [Inhabited α]
    (s t : List α) (ht : t ≠ []) : (s ++ t).getLast! = t.getLast! := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast!_eq_getLast?_getD, List.getLast?_append]
  cases h : t.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp h) ht
  | some x => simp

private theorem aq13w1_getLast!_eq_getLast {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! = l.getLast h := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast h]
  rfl

/-- `d` 非末元时，环后继 = 表内下一位。 -/
private theorem aq13w1_nextEl_of_ne_last {α : Type*} [Inhabited α] [BEq α]
    [LawfulBEq α] [DecidableEq α] {s : List α} {d : α} (hd : d ∈ s)
    (hlast : d ≠ s.getLast!) :
    nextEl s d = s[s.idxOf d + 1]'(by
      have h1 : s.idxOf d < s.length := List.idxOf_lt_length_iff.mpr hd
      have h2 : s.idxOf d ≠ s.length - 1 := by
        intro h
        apply hlast
        have hne : s ≠ [] := by
          intro hc; rw [hc] at hd; exact List.not_mem_nil hd
        have hgl : s.getLast! = s[s.length - 1]'(by
            have := List.length_pos_of_mem hd; omega) := by
          rw [aq13w1_getLast!_eq_getLast hne, List.getLast_eq_getElem]
        have hidx : s[s.length - 1]'(by
            have := List.length_pos_of_mem hd; omega) = d := by
          simpa [h] using (List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hd))
        rw [hgl]
        exact hidx.symm
      omega) := by
  have h1 : s.idxOf d < s.length := List.idxOf_lt_length_iff.mpr hd
  have h2 : s.idxOf d ≠ s.length - 1 := by
    intro h
    apply hlast
    have hne : s ≠ [] := by
      intro hc; rw [hc] at hd; exact List.not_mem_nil hd
    have hgl : s.getLast! = s[s.length - 1]'(by
        have := List.length_pos_of_mem hd; omega) := by
      rw [aq13w1_getLast!_eq_getLast hne, List.getLast_eq_getElem]
    have hidx : s[s.length - 1]'(by
        have := List.length_pos_of_mem hd; omega) = d := by
      simpa [h] using (List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hd))
    rw [hgl]
    exact hidx.symm
  unfold nextEl
  rw [if_neg h2, getD_eq_getElem_of_lt (by omega)]

/-! ## §1 betwn 的 idxOf 公式 -/

/-- idxOf 在 append 右段的平移（左段不含 `a`）。 -/
private theorem aq13w1_idxOf_append_right {α : Type*} [BEq α] [LawfulBEq α]
    {l₁ l₂ : List α} {a : α} (h : a ∉ l₁) :
    (l₁ ++ l₂).idxOf a = l₁.length + l₂.idxOf a := by
  induction l₁ with
  | nil => simp
  | cons b t ih =>
    have hb : (b == a) = false := by
      rw [beq_eq_false_iff_ne]
      intro hba; exact h (hba ▸ List.mem_cons_self ..)
    have ht : a ∉ t := fun ha => h (List.mem_cons_of_mem _ ha)
    rw [List.cons_append, List.idxOf_cons, hb, ih ht]
    simp [Nat.add_comm, Nat.add_assoc]

/-- `d ∈ betwn s u v` 时 `idxOf` 在 betwn 内的位置 = `indexf u d s - 1`。 -/
private theorem aq13w1_idxOf_betwn {α : Type*} [BEq α] [LawfulBEq α] {s : List α}
    {u v d : α} (hnd : s.Nodup) (hu : u ∈ s) (hv : v ∈ s) (huv : u ≠ v)
    (hd : d ∈ between s u v) :
    (between s u v).idxOf d = indexf u d s - 1 := by
  have hds : d ∈ s := betwnMem hd
  have hu_lt : s.idxOf u < s.length := List.idxOf_lt_length_iff.mpr hu
  have hd_lt : s.idxOf d < s.length := List.idxOf_lt_length_iff.mpr hds
  have hv_lt : s.idxOf v < s.length := List.idxOf_lt_length_iff.mpr hv
  rw [betwnTakeDrop hnd hv] at hd ⊢
  split_ifs at hd ⊢ with hij
  · -- 直段
    have hdrop : d ∈ s.drop (s.idxOf u + 1) := List.mem_of_mem_take hd
    have hle : s.idxOf u + 1 ≤ s.idxOf d := (memDropIndex hnd hds).mp hdrop
    have hidxD : (s.drop (s.idxOf u + 1)).idxOf d = s.idxOf d - (s.idxOf u + 1) :=
      idxOfDropNodup hnd hds hle
    have hlt : (s.drop (s.idxOf u + 1)).idxOf d
        < s.idxOf v - (s.idxOf u + 1) := by
      rw [hidxD]
      have := (memTakeIndex hdrop).mp hd
      omega
    have htake : ((s.drop (s.idxOf u + 1)).take
        (s.idxOf v - (s.idxOf u + 1))).idxOf d
        = (s.drop (s.idxOf u + 1)).idxOf d :=
      idxOfTakeNodup (uniqDrop hnd) hdrop hlt
    rw [htake, hidxD, indexfCond hu hds]
    rw [if_pos (show s.idxOf u ≤ s.idxOf d by omega), Nat.sub_sub]
  · -- 环段
    have hne : s.idxOf u ≠ s.idxOf v := fun e => huv ((List.idxOf_inj hu).mp e)
    have hiu_gt : s.idxOf v < s.idxOf u := by omega
    rcases List.mem_append.mp hd with hdrop | htake
    · have hle : s.idxOf u + 1 ≤ s.idxOf d := (memDropIndex hnd hds).mp hdrop
      have hidxD : (s.drop (s.idxOf u + 1)).idxOf d = s.idxOf d - (s.idxOf u + 1) :=
        idxOfDropNodup hnd hds hle
      rw [List.idxOf_append_of_mem hdrop, hidxD, indexfCond hu hds,
        if_pos (show s.idxOf u ≤ s.idxOf d by omega)]
      omega
    · have hdlt : s.idxOf d < s.idxOf v := by
        have := (memTakeIndex hds).mp htake; omega
      have hnot : d ∉ s.drop (s.idxOf u + 1) := by
        rw [memDropIndex hnd hds]; omega
      have hidxD : (s.take (s.idxOf v)).idxOf d = s.idxOf d :=
        idxOfTakeNodup hnd hds hdlt
      rw [aq13w1_idxOf_append_right hnot, List.length_drop, hidxD,
        indexfCond hu hds, if_neg (by omega)]
      omega


/-! ## §2 事实包 -/

/-- W1 的公共事实包（避免每件重算 setup）。 -/
private structure Aq13W1 (L : fgraph ℕ) (hL : GoodList L)
    (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ)) (x : ℕ × ℕ) where
  hunL : ∀ l ∈ L, l.Nodup
  hrnd : r.Nodup
  hyf : lYSpine L r x ∈ findFaceDarts L x
  hzf : lZSpine L N r x ∈ findFaceDarts L x
  hyz : lYSpine L r x ≠ lZSpine L N r x
  hfnd : (findFaceDarts L x).Nodup
  hndRtr : (rtransSpine L N r x 1).Nodup
  hrtr : rtransSpine L N r x 1 = aq13A L N r x ++ aq13W L N r x
  hAne : aq13A L N r x ≠ []
  hAlast : (aq13A L N r x).getLast! = lYSpine L r x
  hndA : (aq13A L N r x).Nodup
  hndW : (aq13W L N r x).Nodup
  hcanon : findFaceDarts L (lYSpine L r x) = findFaceDarts L x

private theorem aq13w1_facts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    Aq13W1 L hL N r x := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hpp := pplhuljV0 L hL hgn hunL hm hf
  have hyf : lYSpine L r x ∈ findFaceDarts L x := hpp.1
  have hzf : lZSpine L N r x ∈ findFaceDarts L x := hpp.2.1
  have hyz : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hfnd : (findFaceDarts L x).Nodup := findFaceDarts_nodup hL.1 x
  have hndNt : (ntransSpine L N r x 1).flatten.Nodup := aq1 L hL N r x hgn hm
  have h1 : rtransSpine L N r x 1 =
      (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).2 := by
    show ((transformListSpine L x)^[1] (N, r)).2 = _
    rw [Function.iterate_one]
    simp only [transformListSpine, if_neg hf]
  have hmemS : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 ∈ ntransSpine L N r x 1 :=
    sndMemRtran1 L hm.1.2.2.1 hf
  have hndS : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2.Nodup :=
    uniqFlattenUniq _ hndNt _ hmemS
  have hndRtr : (rtransSpine L N r x 1).Nodup := by
    rw [h1]; exact hndS
  have hfindcanon : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
    aq10_memFindFaceImpFacesEq hL.1 hyf
  have hnextz : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hrnd _
  have hrtr : rtransSpine L N r x 1 = aq13A L N r x ++ aq13W L N r x := by
    rw [h1, hfindcanon]
    dsimp only [splitNormalListSpine, aq13A, aq13W]
    rw [hnextz]
  have hAne : aq13A L N r x ≠ [] := by
    dsimp only [aq13A]
    simp
  have hAlast : (aq13A L N r x).getLast! = lYSpine L r x := by
    have h := aq13w1_getLast!_append_singleton
      ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x))
      (lYSpine L r x)
    simpa only [aq13A, List.append_assoc] using h
  have hndAW : (aq13A L N r x ++ aq13W L N r x).Nodup := by rw [← hrtr]; exact hndRtr
  exact ⟨hunL, hrnd, hyf, hzf, hyz, hfnd, hndRtr, hrtr, hAne, hAlast,
    (List.nodup_append.mp hndAW).1, (List.nodup_append.mp hndAW).2.1, hfindcanon⟩


/-! ## §3 W 的 f-orbit 枚举 -/

private theorem aq13w1_W_getElem (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {i : ℕ} (hi : i < (between (findFaceDarts L x) (lYSpine L r x)
      (lZSpine L N r x)).length) :
    (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x))[i]'hi =
      (nextEl (findFaceDarts L x))^[i + 1] (lYSpine L r x) := by
  let F := aq13w1_facts L hL hgn hm hf
  have hlen : (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).length
      = indexf (lYSpine L r x) (lZSpine L N r x) (findFaceDarts L x) - 1 :=
    sizeBetwn F.hfnd F.hyf F.hzf F.hyz
  have hidxlt : i + 1 < indexf (lYSpine L r x) (lZSpine L N r x) (findFaceDarts L x) := by
    omega
  have hidxlt' : i + 1 < (findFaceDarts L x).length :=
    lt_trans hidxlt (indexfLtSizel F.hyf F.hzf)
  have hdf : (nextEl (findFaceDarts L x))^[i + 1] (lYSpine L r x) ∈ findFaceDarts L x :=
    memPowerNextEl F.hyf (i + 1)
  have hidx : indexf (lYSpine L r x) ((nextEl (findFaceDarts L x))^[i + 1]
      (lYSpine L r x)) (findFaceDarts L x) = i + 1 :=
    nextElnIndexf F.hyf hdf F.hfnd rfl hidxlt'
  have hdmem : (nextEl (findFaceDarts L x))^[i + 1] (lYSpine L r x)
      ∈ between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x) :=
    (indexfBetwnEq F.hyz F.hfnd F.hyf F.hzf).mpr ⟨by omega, by omega⟩
  have hpos : (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).idxOf
      ((nextEl (findFaceDarts L x))^[i + 1] (lYSpine L r x)) = i := by
    rw [aq13w1_idxOf_betwn F.hfnd F.hyf F.hzf F.hyz hdmem, hidx]
    omega
  have hgl : (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x))[
      (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).idxOf
        ((nextEl (findFaceDarts L x))^[i + 1] (lYSpine L r x))]'(by
          rw [hpos]; exact hi) =
      (nextEl (findFaceDarts L x))^[i + 1] (lYSpine L r x) :=
    List.getElem_idxOf (by rw [hpos]; exact hi)
  have hndW : (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).Nodup := by
    simpa only [aq13W] using F.hndW
  have hinj : (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x))[i]'hi =
      (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x))[
        (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).idxOf
          ((nextEl (findFaceDarts L x))^[i + 1] (lYSpine L r x))]'(by rw [hpos]; exact hi) :=
    (List.Nodup.getElem_inj_iff hndW).mpr (by omega)
  exact hinj.trans hgl

/-! ## §4 rtr 在 y 与 W 上的后继（HOL ⑧⑨） -/

private theorem aq13w1_nextEl_rtr_y (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    nextEl (rtransSpine L N r x 1) (lYSpine L r x) =
      nextEl (findFaceDarts L x) (lYSpine L r x) := by
  let F := aq13w1_facts L hL hgn hm hf
  have hAhead : (aq13A L N r x).head! = lZSpine L N r x := by
    dsimp only [aq13A]
    simp
  by_cases hW : aq13W L N r x = []
  · have hrtrA : rtransSpine L N r x 1 = aq13A L N r x := by
      rw [F.hrtr, hW, List.append_nil]
    have hnext : nextEl (rtransSpine L N r x 1) (lYSpine L r x)
        = (aq13A L N r x).head! := by
      rw [hrtrA]
      have hHd := nextElLastHd (h := aq13A L N r x) F.hndA F.hAne
      rw [← aq13w1_getLast!_eq_getLast (l := aq13A L N r x) F.hAne, F.hAlast] at hHd
      exact hHd
    have hznext : lZSpine L N r x = nextEl (findFaceDarts L x) (lYSpine L r x) := by
      have h := (betwnNil F.hfnd F.hyz F.hyf F.hzf).mp hW
      exact h
    rw [hnext, hAhead, ← hznext]
  · have hWne : aq13W L N r x ≠ [] := hW
    have hndApp : (aq13A L N r x ++ aq13W L N r x).Nodup := by
      rw [← F.hrtr]; exact F.hndRtr
    have hnext : nextEl (rtransSpine L N r x 1) (lYSpine L r x)
        = (aq13W L N r x).head! := by
      rw [F.hrtr]
      have hHd := nextElCatLast1 hndApp F.hAne hWne
      rwa [F.hAlast] at hHd
    have hW0 : (aq13W L N r x)[0]'(List.length_pos_of_ne_nil hWne)
        = (nextEl (findFaceDarts L x))^[0 + 1] (lYSpine L r x) := by
      have := aq13w1_W_getElem L hL hgn hm hf (i := 0)
        (List.length_pos_of_ne_nil hWne)
      simpa only [aq13W] using this
    have hhead : (aq13W L N r x).head! = (aq13W L N r x)[0]'
        (List.length_pos_of_ne_nil hWne) :=
      aq13w1_head!_eq_getElem hWne
    rw [hnext, hhead, hW0]
    simp

private theorem aq13w1_nextEl_rtr_of_mem_W (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {d : ℕ × ℕ} (hd : d ∈ between (findFaceDarts L x) (lYSpine L r x)
      (lZSpine L N r x)) :
    nextEl (rtransSpine L N r x 1) d = nextEl (findFaceDarts L x) d := by
  let F := aq13w1_facts L hL hgn hm hf
  have hWne : between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x) ≠ [] :=
    List.ne_nil_of_mem hd
  have hndApp : (aq13A L N r x ++ aq13W L N r x).Nodup := by
    rw [← F.hrtr]; exact F.hndRtr
  have hArtr : aq13A L N r x = aq13A L N r x := rfl
  have hWrtr : aq13W L N r x = between (findFaceDarts L x) (lYSpine L r x)
      (lZSpine L N r x) := rfl
  by_cases hlast : d = (aq13W L N r x).getLast!
  · have hndApp' : (aq13A L N r x ++ aq13W L N r x).Nodup := hndApp
    have hneApp : (aq13A L N r x ++ aq13W L N r x) ≠ [] := by
      intro h; have := List.append_eq_nil_iff.mp h; exact F.hAne this.1
    have hlastEq : (aq13A L N r x ++ aq13W L N r x).getLast!
        = (aq13W L N r x).getLast! :=
      aq13w1_getLast!_append_of_ne _ _ hWne
    have hHd := nextElLastHd (h := aq13A L N r x ++ aq13W L N r x) hndApp' hneApp
    rw [← aq13w1_getLast!_eq_getLast (l := aq13A L N r x ++ aq13W L N r x) hneApp,
      hlastEq, ← hlast] at hHd
    have hheadApp : (aq13A L N r x ++ aq13W L N r x).head! = lZSpine L N r x := by
      dsimp only [aq13A]
      rw [List.cons_append]
      exact List.head!_cons _ _
    have hznext : nextEl (findFaceDarts L x) d = lZSpine L N r x := by
      have hb := nextLastBetwn F.hyf F.hzf F.hfnd F.hyz hWne
      rw [← aq13w1_getLast!_eq_getLast
        (l := between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)) hWne] at hb
      have hlast' : d = (between (findFaceDarts L x) (lYSpine L r x)
          (lZSpine L N r x)).getLast! := by simpa only [aq13W] using hlast
      rwa [← hlast'] at hb
    rw [F.hrtr, hHd, hheadApp, hznext]
  · rw [F.hrtr, nextElCat2 hndApp (by simpa only [aq13W] using hd)
      (by simpa only [aq13W] using hlast)]
    change nextEl (between (findFaceDarts L x) (lYSpine L r x)
      (lZSpine L N r x)) d = nextEl (findFaceDarts L x) d
    rw [aq13w1_nextEl_of_ne_last (s := between (findFaceDarts L x) (lYSpine L r x)
      (lZSpine L N r x)) hd (by simpa only [aq13W] using hlast)]
    have hidxlt : (between (findFaceDarts L x) (lYSpine L r x)
        (lZSpine L N r x)).idxOf d + 1 < (between (findFaceDarts L x)
          (lYSpine L r x) (lZSpine L N r x)).length := by
      have h1 : (between (findFaceDarts L x) (lYSpine L r x)
          (lZSpine L N r x)).idxOf d < (between (findFaceDarts L x)
            (lYSpine L r x) (lZSpine L N r x)).length :=
        List.idxOf_lt_length_iff.mpr hd
      by_contra hcon
      have h2 : (between (findFaceDarts L x) (lYSpine L r x)
          (lZSpine L N r x)).idxOf d = (between (findFaceDarts L x)
            (lYSpine L r x) (lZSpine L N r x)).length - 1 := by omega
      apply hlast
      have hgl := List.getElem_idxOf (x := d) (xs := between (findFaceDarts L x)
        (lYSpine L r x) (lZSpine L N r x)) h1
      have hgl' : (between (findFaceDarts L x) (lYSpine L r x)
          (lZSpine L N r x))[(between (findFaceDarts L x) (lYSpine L r x)
            (lZSpine L N r x)).length - 1]'(by omega) = d := by
        simpa [h2] using hgl
      change d = (between (findFaceDarts L x) (lYSpine L r x)
        (lZSpine L N r x)).getLast!
      rw [aq13w1_getLast!_eq_getLast (l := between (findFaceDarts L x)
        (lYSpine L r x) (lZSpine L N r x)) hWne, List.getLast_eq_getElem]
      exact hgl'.symm
    have hstep := aq13w1_W_getElem L hL hgn hm hf (i :=
      (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).idxOf d + 1)
      hidxlt
    have hdEq : d = (between (findFaceDarts L x) (lYSpine L r x)
        (lZSpine L N r x))[(between (findFaceDarts L x) (lYSpine L r x)
          (lZSpine L N r x)).idxOf d]'(
        List.idxOf_lt_length_iff.mpr hd) :=
      (List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hd)).symm
    have hdStep := aq13w1_W_getElem L hL hgn hm hf (i :=
      (between (findFaceDarts L x) (lYSpine L r x)
        (lZSpine L N r x)).idxOf d) (List.idxOf_lt_length_iff.mpr hd)
    rw [hstep]
    rw [show (between (findFaceDarts L x) (lYSpine L r x)
        (lZSpine L N r x)).idxOf d + 1 + 1
        = ((between (findFaceDarts L x) (lYSpine L r x)
          (lZSpine L N r x)).idxOf d + 1) + 1 from rfl]
    rw [Function.iterate_succ_apply']
    rw [← hdStep]
    rw [← hdEq]

/-! ## §5 轨道一致（x → y → z 前段） -/

private theorem aq13w1_agree (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ∀ k : ℕ, k ≤ lMSpine L r x + 1 →
      (nextEl (rtransSpine L N r x 1))^[k] x = (fList L)^[k] x := by
  have hwr : nextEl (findFaceDarts L x) x = nextEl r x :=
    (hm.1.2.2.2.2.2.1).symm
  intro k hk
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0]
    rfl
  · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hk' : k' ≤ lMSpine L r x := by omega
    calc (nextEl (rtransSpine L N r x 1))^[k' + 1] x
        = (nextEl (rtransSpine L N r x 1))^[k'] (nextEl (rtransSpine L N r x 1) x) :=
          Function.iterate_succ_apply _ _ _
      _ = (nextEl (rtransSpine L N r x 1))^[k'] (nextEl (findFaceDarts L x) x) := by
          rw [aq10 L hL N r x hgn hm]
          rfl
      _ = (nextEl r)^[k'] (nextEl (findFaceDarts L x) x) :=
          aqs_powerNextSListEqRtrans L hL hgn hm hf k' hk'
      _ = (nextEl r)^[k'] (nextEl r x) := by rw [hwr]
      _ = (nextEl r)^[k' + 1] x := (Function.iterate_succ_apply _ _ _).symm
      _ = (fList L)^[k'] (nextEl r x) :=
          minNotEqImpEq (nextEl r) (fList L) x (lMSpine L r x) rfl k' hk'
      _ = (fList L)^[k'] (fList L x) := by rw [hm.1.2.2.2.2.2.1]
      _ = (fList L)^[k' + 1] x := (Function.iterate_succ_apply _ _ _).symm

/-! ## §6 逐 m 的条件失败 -/

private theorem aq13w1_walk (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ∀ j : ℕ, j ≤ (between (findFaceDarts L x) (lYSpine L r x)
        (lZSpine L N r x)).length →
      (nextEl (rtransSpine L N r x 1))^[j] (lYSpine L r x) =
        (nextEl (findFaceDarts L x))^[j] (lYSpine L r x) := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    by_cases hk0 : k = 0
    · subst hk0
      calc (nextEl (rtransSpine L N r x 1))^[0 + 1] (lYSpine L r x)
          = nextEl (rtransSpine L N r x 1) ((nextEl (rtransSpine L N r x 1))^[0]
              (lYSpine L r x)) := Function.iterate_succ_apply' _ _ _
        _ = nextEl (rtransSpine L N r x 1) (lYSpine L r x) := by
            rw [Function.iterate_zero_apply]
        _ = nextEl (findFaceDarts L x) (lYSpine L r x) :=
            aq13w1_nextEl_rtr_y L hL hgn hm hf
        _ = nextEl (findFaceDarts L x) ((nextEl (findFaceDarts L x))^[0]
              (lYSpine L r x)) := by rw [Function.iterate_zero_apply]
        _ = (nextEl (findFaceDarts L x))^[0 + 1] (lYSpine L r x) :=
            (Function.iterate_succ_apply' _ _ _).symm
    · have hkpos : 1 ≤ k := by omega
      have hkW : k - 1 < (between (findFaceDarts L x) (lYSpine L r x)
          (lZSpine L N r x)).length := by omega
      have hd : (nextEl (findFaceDarts L x))^[k] (lYSpine L r x) =
          (between (findFaceDarts L x) (lYSpine L r x)
            (lZSpine L N r x))[k - 1]'hkW := by
        have hstep := aq13w1_W_getElem L hL hgn hm hf (i := k - 1) hkW
        rw [show k - 1 + 1 = k by omega] at hstep
        exact hstep.symm
      calc (nextEl (rtransSpine L N r x 1))^[k + 1] (lYSpine L r x)
          = nextEl (rtransSpine L N r x 1)
              ((nextEl (rtransSpine L N r x 1))^[k] (lYSpine L r x)) :=
            Function.iterate_succ_apply' _ _ _
        _ = nextEl (rtransSpine L N r x 1)
              ((nextEl (findFaceDarts L x))^[k] (lYSpine L r x)) := by
            rw [ih (by omega)]
        _ = nextEl (rtransSpine L N r x 1)
              ((between (findFaceDarts L x) (lYSpine L r x)
                (lZSpine L N r x))[k - 1]'hkW) := by rw [hd]
        _ = nextEl (findFaceDarts L x)
              ((between (findFaceDarts L x) (lYSpine L r x)
                (lZSpine L N r x))[k - 1]'hkW) :=
            aq13w1_nextEl_rtr_of_mem_W L hL hgn hm hf (List.getElem_mem hkW)
        _ = nextEl (findFaceDarts L x)
              ((nextEl (findFaceDarts L x))^[k] (lYSpine L r x)) := by rw [hd]
        _ = (nextEl (findFaceDarts L x))^[k + 1] (lYSpine L r x) :=
            (Function.iterate_succ_apply' _ _ _).symm

private theorem aq13w1_cond_false (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {m : ℕ} (hmN : m ≤ lMSpine L r x +
      (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).length) :
    (nextEl (rtransSpine L N r x 1))^[m + 2] x =
      fList L ((nextEl (rtransSpine L N r x 1))^[m + 1] x) := by
  let F := aq13w1_facts L hL hgn hm hf
  by_cases hmlt : m < lMSpine L r x
  · -- A: m < l'm，两位置都在一致段
    have h1 := aq13w1_agree L hL hgn hm hf (m + 1) (by omega)
    have h2 := aq13w1_agree L hL hgn hm hf (m + 2) (by omega)
    rw [h1, h2]
    rw [show (fList L)^[m + 2] x = fList L ((fList L)^[m + 1] x) from by
      rw [show m + 2 = (m + 1) + 1 by omega, Function.iterate_succ_apply']]
  · by_cases hmeq : m = lMSpine L r x
    · -- B: m = l'm，位置 m+1 = y，用 ⑧
      subst hmeq
      have h1 := aq13w1_agree L hL hgn hm hf (lMSpine L r x + 1) (by omega)
      rw [show lMSpine L r x + 2 = (lMSpine L r x + 1) + 1 by omega,
        Function.iterate_succ_apply']
      rw [h1]
      change nextEl (rtransSpine L N r x 1) (lYSpine L r x) =
        fList L (lYSpine L r x)
      rw [aq13w1_nextEl_rtr_y L hL hgn hm hf]
      simp only [fList, F.hcanon]
    · -- C: m > l'm，位置 m+1 ∈ W
      have hmlm : lMSpine L r x < m := by omega
      set j := m - lMSpine L r x with hjdef
      have hjpos : 1 ≤ j := by omega
      have hjle : j ≤ (between (findFaceDarts L x) (lYSpine L r x)
          (lZSpine L N r x)).length := by omega
      have hposY : (nextEl (rtransSpine L N r x 1))^[lMSpine L r x + 1] x =
          lYSpine L r x := by
        have h := aq13w1_agree L hL hgn hm hf (lMSpine L r x + 1) (by omega)
        rw [h]
        rfl
      have hmid : (nextEl (rtransSpine L N r x 1))^[m + 1] x =
          (nextEl (findFaceDarts L x))^[j] (lYSpine L r x) := by
        calc (nextEl (rtransSpine L N r x 1))^[m + 1] x
            = (nextEl (rtransSpine L N r x 1))^[j + (lMSpine L r x + 1)] x := by
              rw [show j + (lMSpine L r x + 1) = m + 1 by omega]
          _ = (nextEl (rtransSpine L N r x 1))^[j]
                ((nextEl (rtransSpine L N r x 1))^[lMSpine L r x + 1] x) :=
              Function.iterate_add_apply _ _ _ _
          _ = (nextEl (rtransSpine L N r x 1))^[j] (lYSpine L r x) := by rw [hposY]
          _ = (nextEl (findFaceDarts L x))^[j] (lYSpine L r x) :=
              aq13w1_walk L hL hgn hm hf j hjle
      have hdW : (nextEl (findFaceDarts L x))^[j] (lYSpine L r x)
          ∈ between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x) := by
        have hj1 : j - 1 < (between (findFaceDarts L x) (lYSpine L r x)
            (lZSpine L N r x)).length := by omega
        have hstep := aq13w1_W_getElem L hL hgn hm hf (i := j - 1) hj1
        rw [show j - 1 + 1 = j by omega] at hstep
        rw [← hstep]
        exact List.getElem_mem hj1
      have hstep2 : (nextEl (rtransSpine L N r x 1))^[m + 2] x =
          nextEl (rtransSpine L N r x 1)
            ((nextEl (findFaceDarts L x))^[j] (lYSpine L r x)) := by
        rw [show m + 2 = (m + 1) + 1 by omega, Function.iterate_succ_apply', hmid]
      rw [hstep2, hmid]
      rw [aq13w1_nextEl_rtr_of_mem_W L hL hgn hm hf hdW]
      simp only [fList, aq10_memFindFaceImpFacesEq hL.1 (betwnMem hdW)]

/-! ## §7 W1 主定理：轨道下界（折叠 ②③⑥⑦⑬⑭） -/

/-- **W1 主定理**（HOL ②⑥⑬ 的合并原生形）：
`l'm rtr ≥ l'm r + |W| + 1`，`W = betwn f l'y l'z`。
前提 `¬finalListSpine L r`（marked）+ `¬finalListSpine L rtr`（AQ13 主证槽）。 -/
theorem aq13w1_lmLtRtrans (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hnf : ¬finalListSpine L (rtransSpine L N r x 1)) :
    lMSpine L r x
        + (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).length + 1
      ≤ lMSpine L (rtransSpine L N r x 1) x := by
  let F := aq13w1_facts L hL hgn hm hf
  have hSdef : lMSpine L (rtransSpine L N r x 1) x =
      sInf {m : ℕ | (nextEl (rtransSpine L N r x 1))^[m + 2] x ≠
        fList L ((nextEl (rtransSpine L N r x 1))^[m + 1] x)} := rfl
  rw [hSdef]
  apply le_csInf
  · have hxrtr : x ∈ rtransSpine L N r x 1 := aq7 L hL N r x hgn hm
    have hnf' := hnf
    rw [finalListSpine] at hnf'
    push Not at hnf'
    obtain ⟨d, hdmem, hdne⟩ := hnf'
    have hord := indexfN hxrtr hdmem F.hndRtr
    have hjpos : 0 < indexf x d (rtransSpine L N r x 1) := by
      rcases Nat.eq_zero_or_pos (indexf x d (rtransSpine L N r x 1)) with h0 | hpos
      · exfalso
        apply hdne
        have hdx : d = x := by rw [← hord, h0]; rfl
        rw [hdx]
        exact (aq10 L hL N r x hgn hm).symm
      · exact hpos
    refine ⟨indexf x d (rtransSpine L N r x 1) - 1, ?_⟩
    have e1 : indexf x d (rtransSpine L N r x 1) - 1 + 2 =
        indexf x d (rtransSpine L N r x 1) + 1 := by omega
    have e2 : indexf x d (rtransSpine L N r x 1) - 1 + 1 =
        indexf x d (rtransSpine L N r x 1) := by omega
    simp only [Set.mem_setOf_eq]
    rw [e1, e2, Function.iterate_succ_apply', hord]
    exact Ne.symm hdne
  · intro b hb
    by_contra hlt
    push Not at hlt
    exact hb (aq13w1_cond_false L hL hgn hm hf (by omega))

/-- **W1 推论 ②**（HOL `lm_le_rtrans_suc`）：`l'm r ≤ l'm rtr`。 -/
theorem aq13w1_lmLeRtrans (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hnf : ¬finalListSpine L (rtransSpine L N r x 1)) :
    lMSpine L r x ≤ lMSpine L (rtransSpine L N r x 1) x := by
  have := aq13w1_lmLtRtrans L hL hgn hm hf hnf
  omega

/-- **W1 推论 ⑥**（HOL `lm_lt_rtrans_suc`）：`l'm r < l'm rtr`。 -/
theorem aq13w1_lmStrictRtrans (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hnf : ¬finalListSpine L (rtransSpine L N r x 1)) :
    lMSpine L r x < lMSpine L (rtransSpine L N r x 1) x := by
  have := aq13w1_lmLtRtrans L hL hgn hm hf hnf
  omega

/-- **W1 推论 ③**（HOL `s_list_subset_s_list_rtrans`）：
`sList r x ⊆ sList rtr x`（同一幂见证，长度界由 ② 给）。 -/
theorem aq13w1_sListSubsetRtrans (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hnf : ¬finalListSpine L (rtransSpine L N r x 1)) {d : ℕ × ℕ}
    (hd : d ∈ sListSpine L r x) :
    d ∈ sListSpine L (rtransSpine L N r x 1) x := by
  simp only [sListSpine, List.mem_map, List.mem_range] at hd ⊢
  obtain ⟨i, hi, hie⟩ := hd
  exact ⟨i, lt_of_lt_of_le hi (aq13w1_lmLeRtrans L hL hgn hm hf hnf), hie⟩

/-- **W1 推论 ⑦**（HOL `y_in_s_list_suc`）：`l'y ∈ sList rtr x`。 -/
theorem aq13w1_yMemSListRtrans (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hnf : ¬finalListSpine L (rtransSpine L N r x 1)) :
    lYSpine L r x ∈ sListSpine L (rtransSpine L N r x 1) x := by
  simp only [sListSpine, List.mem_map, List.mem_range]
  exact ⟨lMSpine L r x, aq13w1_lmStrictRtrans L hL hgn hm hf hnf, rfl⟩

/-! 公理审计锚（编译即执行；预期标准三，零 sorryAx）。 -/
#print axioms Kepler.Text.TameSpine.aq13w1_lmLtRtrans
#print axioms Kepler.Text.TameSpine.aq13w1_lmLeRtrans
#print axioms Kepler.Text.TameSpine.aq13w1_lmStrictRtrans
#print axioms Kepler.Text.TameSpine.aq13w1_sListSubsetRtrans
#print axioms Kepler.Text.TameSpine.aq13w1_yMemSListRtrans
