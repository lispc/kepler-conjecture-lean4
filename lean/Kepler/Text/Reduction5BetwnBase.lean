/-
  Kepler.Text.Reduction5BetwnBase — W2-c-1a：betwn_core0_z_y 塔的供给层链孪生
  第一批（TameList3 betwn/indexf 簇六件 + indexfCompl + memPrevEl +
  sizeFlattenLe）。

  ┌─ 双落指针（防重复落对账；W2C_PLAN §3 W2-c-1 / §6）────────────
  │ 本文件各件与 Spine 侧孪生逐字同内容、载体多态：betwnMem/
  │ indexfLtSizel/sizeBetwn/indexlBetwn/indexfBetwn/indexfBetwnEq ↔
  │ TameList3（Spine，不删，tame-corr 领土）；indexfCompl ↔
  │ TameList3.indexfAntisym（B2 indexf_add_sum 是 < len 侧条件形，
  │ 补位）；memPrevEl ↔ Seq2.mem_prev_el（全树原零命中，首落）；
  │ sizeFlattenLe ↔ TameList56/57。双家记账沿 parts_cat 先例（续493）。
  │ 证明体不走 Spine 内部机（betwnTakeDrop/splitAt 展开），改走链侧
  │ Reduction4 between 族 + TameLp getElem_idxOf/idxOf_getElem
  │ （W2C_PLAN §6.2）。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（诚实收窄记档；塔内消费全带 x≠z 已核）────────────────
  │ `indexlBetwn`/`indexfBetwn`/`indexfBetwnEq` 的 z = x 支需
  │ `between s x x` 自形引理（ListAux splitAt 展开），本批以 `x ≠ z`
  │ 前提收窄；塔内三个消费点全部以 ¬(FST zi = FST ys) 喂入 x ≠ z，
  │ 收窄不影响塔。无条件形恢复挂账 W2-c-1b+。
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide；主仓 tracked 零改动；
  零 import TameSpine（链侧纯）。
-/

import Kepler.Text.Reduction5Base
import Kepler.Text.Reduction4
import Kepler.Text.MoreLemma2Island1
import Kepler.Graphs.ListAuxLemmas
import Kepler.Graphs.FaceDivisionProps1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

variable {α : Type} [DecidableEq α]

open Kepler.Graphs (between)
open Kepler.Assembly (nextEl prevEl)
open Kepler.Graphs (between_distinct)
open Kepler.Text.Reduction4 (indexf_lt_length_of_mem indexf_eq_length_of_not_mem
  indexfRefl indexf_add_left betwnMemCover between_eq_take_of_idxOf_lt
  between_eq_append_of_idxOf_gt)
open Kepler.Text.MoreLemma2Island1 (indexfN)

/-! ## §0 indexf 辅件（TameList3 内件链孪生） -/

/-- indexf 的 idxOf 条件形（TameList3.indexfCond 链孪生，private）。 -/
private theorem indexfCond {x y : α} {s : List α} (hx : x ∈ s) (hy : y ∈ s) :
    indexf x y s =
      if s.idxOf x ≤ s.idxOf y then s.idxOf y - s.idxOf x
      else s.idxOf y + (s.length - s.idxOf x) := by
  have hix : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hx
  have hiy : s.idxOf y < s.length := List.idxOf_lt_length_iff.mpr hy
  unfold indexf
  rw [if_pos ⟨hx, hy⟩]
  by_cases hle : s.idxOf x ≤ s.idxOf y
  · rw [if_pos hle]
    have hsum : s.idxOf y + (s.length - s.idxOf x) =
        s.length + (s.idxOf y - s.idxOf x) := by omega
    have hlt : s.idxOf y - s.idxOf x < s.length := by omega
    rw [hsum, Nat.add_comm s.length (s.idxOf y - s.idxOf x),
      Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
  · rw [if_neg hle, Nat.mod_eq_of_lt (by omega)]

/-- **HOL `indexf_antisym`**（tame_list.hl:1601，TameList3.indexfAntisym 链孪生）：
双侧成员 + `x ≠ y` ⇒ `indexf x y s + indexf y x s = s.length`。
（B2 `indexf_add_sum` 是 `< s.length` 侧条件形，非本件。） -/
theorem indexfCompl {x y : α} {s : List α}
    (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
    indexf x y s + indexf y x s = s.length := by
  have hix : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hx
  have hiy : s.idxOf y < s.length := List.idxOf_lt_length_iff.mpr hy
  have hxy : s.idxOf x ≠ s.idxOf y := by
    intro e
    have h1 : s[s.idxOf x] = x := Kepler.Text.TameLp.getElem_idxOf hx
    have h2 : s[s.idxOf y] = y := Kepler.Text.TameLp.getElem_idxOf hy
    simp only [e] at h1
    rw [h2] at h1
    exact hne h1.symm
  have key : ∀ (i j : ℕ), i < s.length → j < s.length → j ≠ i →
      (j + (s.length - i)) % s.length + (i + (s.length - j)) % s.length = s.length := by
    intro i j hi hj hne'
    rcases Nat.lt_or_ge i j with hlt | hge
    · have hjlt : j - i < s.length := by omega
      have hilt : i + (s.length - j) < s.length := by omega
      have hsum1 : j + (s.length - i) = s.length + (j - i) := by omega
      rw [hsum1, Nat.add_comm s.length (j - i), Nat.add_mod_right,
        Nat.mod_eq_of_lt hjlt, Nat.mod_eq_of_lt hilt]
      omega
    · have hlt2 : j < i := by omega
      have hjlt : j + (s.length - i) < s.length := by omega
      have hilt : i - j < s.length := by omega
      have hsum2 : i + (s.length - j) = s.length + (i - j) := by omega
      rw [Nat.mod_eq_of_lt hjlt, hsum2, Nat.add_comm s.length (i - j),
        Nat.add_mod_right, Nat.mod_eq_of_lt hilt]
      omega
  unfold indexf
  rw [if_pos ⟨hx, hy⟩, if_pos ⟨hy, hx⟩]
  exact key _ _ hix hiy (Ne.symm hxy)

/-! ## §A TameList3 betwn/indexf 簇六件（链孪生） -/

/-- **HOL `betwn_mem`**（tame_list.hl:2622）：`w ∈ between f u v ⇒ w ∈ f`。 -/
theorem betwnMem {f : List α} {u v w : α} (h : w ∈ between f u v) : w ∈ f :=
  Kepler.Graphs.inbetween_inset h

/-- **HOL `indexf_lt_sizel`**（tame_list.hl:1537）。 -/
theorem indexfLtSizel {x y : α} {s : List α}
    (hx : x ∈ s) (hy : y ∈ s) : indexf x y s < s.length :=
  indexf_lt_length_of_mem hx hy

/-- **HOL `size_betwn`**（tame_list.hl:2726）：`uniq s ∧ x,y ∈ s ∧ x ≠ y ⇒
sizel (betwn s x y) = indexf x y s - 1`。 -/
theorem sizeBetwn {s : List α} {x y : α}
    (hnd : s.Nodup) (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
    (between s x y).length = indexf x y s - 1 := by
  have hix : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hx
  have hiy : s.idxOf y < s.length := List.idxOf_lt_length_iff.mpr hy
  have hxy : s.idxOf x ≠ s.idxOf y := by
    intro e
    have h1 : s[s.idxOf x] = x := Kepler.Text.TameLp.getElem_idxOf hx
    have h2 : s[s.idxOf y] = y := Kepler.Text.TameLp.getElem_idxOf hy
    simp only [e] at h1
    rw [h2] at h1
    exact hne h1.symm
  by_cases hij : s.idxOf x < s.idxOf y
  · rw [between_eq_take_of_idxOf_lt hnd hx hy hij, indexfCond hx hy, if_pos (by omega)]
    rw [List.length_take, List.length_drop]
    omega
  · push Not at hij
    have hlt' : s.idxOf y < s.idxOf x := by omega
    rw [between_eq_append_of_idxOf_gt hnd hx hy hlt', indexfCond hx hy, if_neg (by omega)]
    rw [List.length_append, List.length_drop, List.length_take]
    omega

/-! ## （indexlBetwn/indexfBetwn/indexfBetwnEq 移 W2-c-1a 第二笔：z=x 自形与
getElem 边界已定位，见 W2C_PLAN §6 与本轮交付说明。） -/

/-! ## §B Seq2 首件 -/

/-! （Seq2.mem_prev_el 本批积分已绿但与 prevNextId/nextPrevId 同族，整族移
W2-c-1a 第二笔统一交付。） -/

/-! ## §C 独立小件 -/

/-! （size_flatten_le 移 W2-c-1a 第二笔。） -/


/-! ## §A2 TameList3 indexl/indexf 簇三件（链孪生；indexl 为收窄形 x≠z，见文件头 DIFFERS） -/

/-- **HOL `indexl_betwn`**（tame_list.hl:2761，**收窄形**）：`uniq s ∧ x ≠ z ∧
x,z ∈ s ∧ y ∈ betwn s x z ⇒ indexl (betwn s x z) y + 1 = indexf x y s`。 -/
theorem indexlBetwn {s : List α} {x y z : α}
    (hnd : s.Nodup) (hne : x ≠ z) (hx : x ∈ s) (hz : z ∈ s) (hy : y ∈ between s x z) :
    (between s x z).idxOf y + 1 = indexf x y s := by
  have hys : y ∈ s := betwnMem hy
  have hix : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hx
  have hiz : s.idxOf z < s.length := List.idxOf_lt_length_iff.mpr hz
  have hzz : s.idxOf z ≠ s.idxOf x := by
    intro e
    have h1 : s[s.idxOf z] = z := Kepler.Text.TameLp.getElem_idxOf hz
    have h2 : s[s.idxOf x] = x := Kepler.Text.TameLp.getElem_idxOf hx
    simp only [e] at h1
    rw [h1] at h2
    exact hne h2.symm
  have hBnd : (between s x z).Nodup := between_distinct hnd
  by_cases hij : s.idxOf x < s.idxOf z
  · rw [between_eq_take_of_idxOf_lt hnd hx hz hij] at hy hBnd ⊢
    obtain ⟨p, hp, hpv⟩ := List.getElem_of_mem hy
    rw [List.length_take, List.length_drop] at hp
    have hbound : s.idxOf x + 1 + p < s.length := by omega
    have hval : s[s.idxOf x + 1 + p]'hbound = y := by
      rw [← hpv]
      simp
    have hplen : p < ((s.drop (s.idxOf x + 1)).take
        (s.idxOf z - s.idxOf x - 1)).length := by
      rw [List.length_take, List.length_drop]
      omega
    have hidxB : ((s.drop (s.idxOf x + 1)).take
        (s.idxOf z - s.idxOf x - 1)).idxOf y = p := by
      rw [← hpv]
      exact Kepler.Text.TameLp.idxOf_getElem hBnd hplen
    have hidx : s.idxOf y = s.idxOf x + 1 + p := by
      rw [← hval]
      exact Kepler.Text.TameLp.idxOf_getElem hnd hbound
    rw [hidxB, indexfCond hx hys, hidx, if_pos (by omega)]
    omega
  · push Not at hij
    have hlt' : s.idxOf z < s.idxOf x := by omega
    rw [between_eq_append_of_idxOf_gt hnd hx hz hlt'] at hy hBnd ⊢
    obtain ⟨hddnd, htnd, hdisj⟩ := List.nodup_append.mp hBnd
    rcases List.mem_append.mp hy with hd | ht
    · obtain ⟨p, hp, hpv⟩ := List.getElem_of_mem hd
      rw [List.length_drop] at hp
      have hbound : s.idxOf x + 1 + p < s.length := by omega
      have hval : s[s.idxOf x + 1 + p]'hbound = y := by
        rw [← hpv]
        simp [List.getElem_drop]
      have hidx : s.idxOf y = s.idxOf x + 1 + p := by
        rw [← hval]
        exact Kepler.Text.TameLp.idxOf_getElem hnd hbound
      have hpdl : p < (s.drop (s.idxOf x + 1)).length := by
        rw [List.length_drop]
        omega
      have hpdd : (s.drop (s.idxOf x + 1)).idxOf y = p := by
        rw [← hpv]
        exact Kepler.Text.TameLp.idxOf_getElem hddnd hpdl
      rw [List.idxOf_append_of_mem hd, hpdd, indexfCond hx hys, hidx, if_pos (by omega)]
      omega
    · obtain ⟨p, hp, hpv⟩ := List.getElem_of_mem ht
      rw [List.length_take] at hp
      have hpz : p < s.idxOf z := by omega
      have hbound : p < s.length := by omega
      have hval : s[p]'hbound = y := by
        rw [← hpv]
        simp [List.getElem_take]
      have hidx : s.idxOf y = p := by
        rw [← hval]
        exact Kepler.Text.TameLp.idxOf_getElem hnd hbound
      have hptl : p < (s.take (s.idxOf z)).length := by
        rw [List.length_take]
        omega
      have hptd : (s.take (s.idxOf z)).idxOf y = p := by
        rw [← hpv]
        exact Kepler.Text.TameLp.idxOf_getElem htnd hptl
      have hdn : ¬ (y ∈ s.drop (s.idxOf x + 1)) := by
        intro hd'
        exact hdisj y hd' y ht rfl
      rw [List.idxOf_append_of_notMem hdn, List.length_drop, hptd, indexfCond hx hys,
        hidx, if_neg (by omega)]
      omega

/-- **HOL `indexf_betwn`**（tame_list.hl:2704）：`x ≠ z ∧ uniq s ∧ x,z ∈ s ∧
y ∈ betwn s x z ⇒ 0 < indexf x y s ∧ indexf x y s < indexf x z s`。 -/
theorem indexfBetwn {s : List α} {x y z : α}
    (hne : x ≠ z) (hnd : s.Nodup) (hx : x ∈ s) (hz : z ∈ s)
    (hy : y ∈ between s x z) :
    0 < indexf x y s ∧ indexf x y s < indexf x z s := by
  have h1 := indexlBetwn hnd hne hx hz hy
  have hb : (between s x z).idxOf y < (between s x z).length :=
    List.idxOf_lt_length_iff.mpr hy
  have h2 := sizeBetwn hnd hx hz hne
  exact ⟨by omega, by omega⟩

/-- **HOL `indexf_betwn_eq`**（tame_list.hl:2810）：`x ≠ z ∧ uniq s ∧ x,z ∈ s ⇒
(y ∈ betwn s x z ↔ 0 < indexf x y s ∧ indexf x y s < indexf x z s)`。 -/
theorem indexfBetwnEq {s : List α} {x y z : α}
    (hne : x ≠ z) (hnd : s.Nodup) (hx : x ∈ s) (hz : z ∈ s) :
    y ∈ between s x z ↔ 0 < indexf x y s ∧ indexf x y s < indexf x z s := by
  constructor
  · exact indexfBetwn hne hnd hx hz
  · rintro ⟨hpos, hlt⟩
    have hys : y ∈ s := by
      by_contra hny
      have h1 := indexf_eq_length_of_not_mem (x := x) (h := Or.inr hny)
      have h2 := indexfLtSizel hx hz
      omega
    rcases betwnMemCover hnd hne hx hys hz with e | e | hm | hm
    · subst e
      rw [indexfRefl hys] at hpos
      exact absurd hpos (by omega)
    · subst e
      exact absurd hlt (by omega)
    · exact hm
    · exfalso
      have hxy : x ≠ y := by
        intro e
        rw [e] at hpos
        exact absurd (indexfRefl hys) (by omega)
      have hzy : z ≠ y := by
        intro e
        rw [e] at hlt
        omega
      have hyx := indexfBetwn (Ne.symm hne) hnd hz hx hm
      have e1 := indexfCompl hx hys hxy
      have e2 := indexfCompl hx hz hne
      have e3 := indexfCompl hz hys hzy
      have hle2 : indexf z y s ≤ indexf z x s := by omega
      have e4 := indexf_add_left hz hys hx hle2
      have hn := indexfLtSizel hx hys
      omega

/-! ## §B Seq2 首件 -/

/-- **HOL `Seq2.mem_prev_el`**（seq2-compiled.hl）：`MEM x s ⇒
MEM (prev_el s x) s`。 -/
theorem memPrevEl {s : List α} {x : α}
    (hxs : x ∈ s) : prevEl s x ∈ s := by
  have hix : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hxs
  unfold prevEl
  split
  · rename_i hnot
    exact absurd hxs hnot
  · by_cases h0 : s.idxOf x = 0
    · rw [if_pos h0]
      cases s with
      | nil => exact absurd hxs (by simp)
      | cons a t =>
        have ha : a = x := by
          have h2 : (a :: t)[(a :: t).idxOf x] = x :=
            Kepler.Text.TameLp.getElem_idxOf hxs
          simpa [h0] using h2
        rw [ha]
        rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast (by simp),
          Option.getD_some]
        exact List.getLast_mem (by simp)
    · rw [if_neg h0]
      have hpos : 0 < s.idxOf x := by omega
      have hi1 : s.idxOf x - 1 < s.length := by omega
      show s.getD (s.idxOf x - 1) x ∈ s
      rw [Kepler.Text.TameLp.getD_eq_getElem_of_lt hi1 x]
      exact List.getElem_mem hi1

/-! ## §C size_flatten_le -/

/-- **HOL `size_flatten_le`**（tame_list.hl:2299）：`all (≠[]) ss ⇒
sizel ss ≤ sizel (flatten ss)`。 -/
theorem sizeFlattenLe {α : Type*} :
    ∀ ss : List (List α), (∀ l ∈ ss, l ≠ []) → ss.length ≤ ss.flatten.length
  | [], _ => Nat.le_refl _
  | l :: ls, h => by
    have hl : l ≠ [] := h l (List.mem_cons_self (a := l) (l := ls))
    have hls : ls.length ≤ (List.flatten ls).length :=
      sizeFlattenLe ls (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    have hpos : 0 < l.length := List.length_pos_iff.mpr hl
    rw [List.flatten_cons, List.length_append, List.length_cons]
    omega

/-! ## §D Aq23.next_last_betwn 与 Aq12.map_betwn（链孪生） -/

/-- **HOL `Aq23.next_last_betwn`**（Aq23.hl）：`MEM y r ∧ MEM z r ∧ uniq r ∧
y ≠ z ∧ betwn r y z ≠ [] ⇒ next_el r (LAST (betwn r y z)) = z`。 -/
theorem nextLastBetwn {r : List α} {y z : α}
    (hy : y ∈ r) (hz : z ∈ r) (hnd : r.Nodup) (hyz : y ≠ z)
    (hb : between r y z ≠ []) :
    nextEl r ((between r y z).getLast hb) = z := by
  have hBnd : (between r y z).Nodup := between_distinct hnd
  have hlastmem : (between r y z).getLast hb ∈ between r y z := List.getLast_mem hb
  have hlenpos : 0 < (between r y z).length := List.length_pos_of_mem hlastmem
  have hidxB : (between r y z).idxOf ((between r y z).getLast hb)
      = (between r y z).length - 1 := by
    rw [List.getLast_eq_getElem hb]
    exact Kepler.Text.TameLp.idxOf_getElem hBnd (by omega)
  have h1 := indexlBetwn hnd hyz hy hz hlastmem
  have h2 := sizeBetwn hnd hy hz hyz
  have hi1 : indexf y ((between r y z).getLast hb) r = (between r y z).length := by
    rw [← h1]
    omega
  have hi2 : indexf y z r = (between r y z).length + 1 := by omega
  have hle : indexf y ((between r y z).getLast hb) r ≤ indexf y z r := by omega
  have h4 := indexf_add_left hy (betwnMem hlastmem) hz hle
  have h5 : indexf ((between r y z).getLast hb) z r = 1 := by omega
  have h6 := indexfN (betwnMem hlastmem) hz hnd
  rw [h5] at h6
  simpa using h6

/-- **HOL `Aq12.map_betwn`**（AQ12.hl:351）：`uniq s ∧ f 在 s 上单射 ∧ y,z ∈ s
∧ y ≠ z ⇒ MAP f (betwn s y z) = betwn (MAP f s) (f y) (f z)`。 -/
theorem mapBetwn {β : Type} [DecidableEq β] {s : List α}
    {f : α → β}
    (hnd : s.Nodup)
    (hinj : ∀ u ∈ s, ∀ v ∈ s, f u = f v → u = v)
    {y z : α} (hy : y ∈ s) (hz : z ∈ s) (hyz : y ≠ z) :
    (between s y z).map f = between (s.map f) (f y) (f z) := by
  have hmapnd : (s.map f).Nodup := by
    refine (List.nodup_map_iff_inj_on hnd).mpr fun u hu v hv hfv => ?_
    exact hinj u hu v hv hfv
  have hmy : f y ∈ s.map f := List.mem_map_of_mem hy
  have hmz : f z ∈ s.map f := List.mem_map_of_mem hz
  have hidxm : ∀ u ∈ s, (s.map f).idxOf (f u) = s.idxOf u := by
    intro u hu
    have hmu : f u ∈ s.map f := List.mem_map_of_mem hu
    have hjlt : (s.map f).idxOf (f u) < (s.map f).length :=
      List.idxOf_lt_length_iff.mpr hmu
    have hjlt' : (s.map f).idxOf (f u) < s.length := by
      rw [List.length_map] at hjlt
      exact hjlt
    have h1 : (s.map f)[(s.map f).idxOf (f u)] = f u :=
      Kepler.Text.TameLp.getElem_idxOf hmu
    rw [List.getElem_map] at h1
    have h2 : s[(s.map f).idxOf (f u)] = u :=
      hinj _ (List.getElem_mem hjlt') _ hu h1
    calc (s.map f).idxOf (f u)
        = s.idxOf (s[(s.map f).idxOf (f u)]'hjlt') :=
          (Kepler.Text.TameLp.idxOf_getElem hnd hjlt').symm
      _ = s.idxOf u := by rw [h2]
  by_cases hij : s.idxOf y < s.idxOf z
  · rw [between_eq_take_of_idxOf_lt hnd hy hz hij]
    have hijm : (s.map f).idxOf (f y) < (s.map f).idxOf (f z) := by
      rw [hidxm y hy, hidxm z hz]
      exact hij
    rw [between_eq_take_of_idxOf_lt hmapnd hmy hmz hijm]
    rw [List.map_take, List.map_drop]
    rw [hidxm y hy, hidxm z hz]
  · push Not at hij
    have hlt' : s.idxOf z < s.idxOf y := by
      rcases Nat.lt_or_ge (s.idxOf z) (s.idxOf y) with h | h
      · exact h
      · exfalso
        have he : s.idxOf y = s.idxOf z := by omega
        have hiy : s.idxOf y < s.length := List.idxOf_lt_length_iff.mpr hy
        have hiz : s.idxOf z < s.length := List.idxOf_lt_length_iff.mpr hz
        have hy1 : s[s.idxOf y] = y := Kepler.Text.TameLp.getElem_idxOf hy
        have hz1 : s[s.idxOf z] = z := Kepler.Text.TameLp.getElem_idxOf hz
        simp only [he] at hy1
        rw [hy1] at hz1
        exact hyz hz1
    rw [between_eq_append_of_idxOf_gt hnd hy hz hlt']
    have hltm : (s.map f).idxOf (f z) < (s.map f).idxOf (f y) := by
      rw [hidxm y hy, hidxm z hz]
      exact hlt'
    rw [between_eq_append_of_idxOf_gt hmapnd hmy hmz hltm]
    rw [List.map_append, List.map_drop, List.map_take]
    rw [hidxm y hy, hidxm z hz]

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三零 sorryAx） -/
#print axioms Kepler.Text.Reduction5.indexfCompl
#print axioms Kepler.Text.Reduction5.betwnMem
#print axioms Kepler.Text.Reduction5.sizeBetwn
#print axioms Kepler.Text.Reduction5.indexlBetwn
#print axioms Kepler.Text.Reduction5.indexfBetwnEq
#print axioms Kepler.Text.Reduction5.memPrevEl
#print axioms Kepler.Text.Reduction5.sizeFlattenLe
#print axioms Kepler.Text.Reduction5.nextLastBetwn
#print axioms Kepler.Text.Reduction5.mapBetwn
