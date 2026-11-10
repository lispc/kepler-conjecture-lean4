/-
  Kepler.Text.TameSpine.Reduction3J5IndexfYltSizelAtom — tame-corr nb14：双怪件
  第②段的核（单 dart atom 子集引理的局部化件）：
  **边界条件 ⇒ `[d] ∈ parts L r`**（双怪件 `indexf_y_lt_sizel` 的原子子集步）。

  ┌─ 归属对账（HOL `more_lemma2.hl` :470-:607 的局部几何）───────────────
  │ HOL 子集步 `{p | ∃d, p=[d] ∧ d ∈ r ∧ indexf w d r < q} ⊆ set_of_list (parts L r)`
  │ 的 Lean 原子核：若 d 的「前/后」两处都是 atom 切点（或 d 是表头/表尾），
  │ 则 `[d]` 本身是一个 atom。证 = 两次 `partsCat` 拆
  │ `r = u ++ [d] ++ v'` + `partsPure`（`[d]` 为纯表）+ 链/spine 桥。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3J5IndexfYltSizelBase
import Kepler.Text.TameSpine.Reduction3J5PowerCore
import Kepler.Text.TameSpine.Reduction3J5M2Cores
import Kepler.Text.TameSpine.TameList9
import Kepler.Text.TameSpine.TameList67
import Kepler.Graphs.FaceDivisionProps4

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl fList eList)
open Kepler.Text.Reduction5 (Dart parts indexf)

/-! ## §0 列表/索引辅件 -/

/-- `(l.take i).getLast! = l[i-1]`（`0 < i ≤ l.length`）。 -/
private theorem take_getLastBang {α : Type} [Inhabited α] {l : List α} {i : ℕ}
    (hi0 : 0 < i) (hi : i ≤ l.length) :
    (l.take i).getLast! = l[i - 1]'(by omega) := by
  have hmin : min i l.length = i := Nat.min_eq_left hi
  rw [List.getLast!_eq_getElem!, List.length_take, hmin,
    List.getElem!_eq_getElem?_getD, List.getElem?_take,
    if_pos (by omega : i - 1 < i),
    List.getElem?_eq_getElem (by omega : i - 1 < l.length)]
  rfl

/-- `r = u ++ v` 且末元处理下，`partsSpine` 的分裂式折回链层 `parts`。 -/
private theorem partsCatChain (L : fgraph ℕ) {r u v : List Dart} {x : Dart}
    (hruv : r = u ++ v) (hx : u.getLast! = x) (hu : u ≠ []) (hv : v ≠ [])
    (hne : nextEl r x ≠ fList L (eList x)) (hun : r.Nodup) :
    parts L r = parts L u ++ parts L v := by
  have h := Kepler.Text.TameSpine.partsCat L hruv hx hu hv hne hun
  simpa only [← Kepler.Text.ChainBridge.parts_eq_partsSpine] using h

/-- 纯表 `parts` 的链层形：`parts L s = [s]`。 -/
private theorem partsPureChain (L : fgraph ℕ) {s : List Dart} (hne : s ≠ [])
    (hun : s.Nodup)
    (hp : ∀ x ∈ s, x = s.getLast! ∨ nextEl s x = fList L (eList x)) :
    parts L s = [s] := by
  have h := Kepler.Text.TameSpine.partsPure L hne hun hp
  simpa only [← Kepler.Text.ChainBridge.parts_eq_partsSpine] using h

/-- `drop (idxOf d + 1) ≠ []` ⇒ `d ≠ r.getLast!`（`d ∈ r`，Dart 专用）。 -/
private theorem neGetLastOfDropSuccNe {r : List Dart} {d : Dart}
    (hnd : r.Nodup) (hd : d ∈ r) (hne : r.drop (r.idxOf d + 1) ≠ []) :
    d ≠ r.getLast! := by
  have hi := List.idxOf_lt_length_iff.mpr hd
  have hpos : 0 < r.length := by omega
  have hlt : r.idxOf d + 1 < r.length := by
    have hposd : 0 < (r.drop (r.idxOf d + 1)).length :=
      List.length_pos_of_ne_nil hne
    rw [List.length_drop] at hposd
    omega
  have hgl : r.getLast! = r[r.length - 1]'(by omega) := by
    rw [List.getLast!_eq_getElem!, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  intro hdlast
  have heq : r[r.idxOf d]'hi = r[r.length - 1]'(by omega) := by
    rw [Kepler.Text.TameLp.getElem_idxOf hd, hdlast, hgl]
  have hidxj := (List.Nodup.getElem_inj_iff hnd).mp heq
  omega

/-- `(d :: v').getLast! ≠ d`（`v' ≠ []` 且无重）。 -/
private theorem consHeadNeGetLast {α : Type} [Inhabited α] {d : α} {v' : List α}
    (hne : v' ≠ []) (hnd : (d :: v').Nodup) : d ≠ (d :: v').getLast! := by
  intro h
  rw [Kepler.Graphs.getLast!_cons_of_ne_nil hne] at h
  have hmem : v'.getLast! ∈ v' := memLastBang v' hne
  rw [← h] at hmem
  exact (List.nodup_cons.mp hnd).1 hmem

/-! ## §1 单 dart atom：边界条件 ⇒ `[d] ∈ parts L r` -/

/-- **双怪件第②段核心**：`d ∈ r` 且 d 的左右两处均为 atom 切点（或 d 是表头/
表尾），则 `[d]` 是一个 atom。 -/
theorem memPartsSingleton (L : fgraph ℕ) {r : List Dart} (hnd : r.Nodup) {d : Dart}
    (hd : d ∈ r)
    (hhead : d = r.head! ∨ nextEl r (Kepler.Assembly.prevEl r d)
      ≠ fList L (eList (Kepler.Assembly.prevEl r d)))
    (hlast : d = r.getLast! ∨ nextEl r d ≠ fList L (eList d)) :
    [d] ∈ parts L r := by
  -- 索引与两侧分解
  set i := r.idxOf d with hi_def
  have hi_lt : i < r.length := List.idxOf_lt_length_iff.mpr hd
  have hget : r[i]'hi_lt = d := Kepler.Text.TameLp.getElem_idxOf hd
  set u := r.take i with hu_def
  set v := r.drop i with hv_def
  have hruv : r = u ++ v := (List.take_append_drop i r).symm
  have hu_len : u.length = i := by rw [hu_def, List.length_take]; omega
  have hv_eq : v = d :: r.drop (i + 1) := by
    rw [hv_def, List.drop_eq_getElem_cons hi_lt, hget]
  have hv_ne : v ≠ [] := by rw [hv_eq]; simp
  -- `[d]` 的 parts 是 `[[d]]`
  have hpd : parts L [d] = [[d]] := by
    have h := partsPureChain L (s := [d]) (by simp) (by simp) (by
      intro x hx
      left
      simpa using hx)
    simpa using h
  -- 关键否定：v' ≠ [] 时 d ≠ r.getLast! 且 d ≠ v.getLast!
  by_cases hu0 : u = []
  · -- u = []：d 是表头；r = [d] ++ v'
    have hi0 : i = 0 := by
      have h := hu_len
      rw [hu0] at h
      simp at h
      omega
    have hrv : r = d :: r.drop (i + 1) := by
      nth_rewrite 1 [hruv]
      rw [hu0]
      exact hv_eq
    set v' := r.drop (i + 1) with hv'_def
    have hrv' : r = [d] ++ v' := by rw [hrv]; rfl
    by_cases hv'0 : v' = []
    · -- r = [d]
      have hrd : r = [d] := by rw [hrv', hv'0, List.append_nil]
      have h := partsPureChain L (s := r) (by rw [hrd]; simp) hnd (by
        intro x hx
        left
        rw [hrd] at hx ⊢
        simpa using hx)
      rw [h, hrd]
      simp
    · -- r = [d] ++ v'，v' ≠ []：在 d 处切
      have hb : nextEl r d ≠ fList L (eList d) := by
        rcases hlast with h | h
        · exact absurd h (neGetLastOfDropSuccNe hnd hd (by rw [← hv'_def]; exact hv'0))
        · exact h
      have hcat := partsCatChain L (r := r) (u := [d]) (v := v') (x := d)
        hrv' rfl (by simp) hv'0 hb hnd
      rw [hcat, hpd]
      exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
  · -- u ≠ []：d 非表头；在 pd = u.getLast! 与 d 两处切
    have hu_pos : 0 < u.length := List.length_pos_of_ne_nil hu0
    have hi0 : 0 < i := by omega
    have hdnehead : d ≠ r.head! := by
      intro h
      have h0 : i = 0 := by
        rw [hi_def, h]
        exact indexHd0 (List.ne_nil_of_mem hd)
      omega
    have hlastu : nextEl r u.getLast! = d := by
      have h1 : nextEl (u ++ v) u.getLast! = v.head! :=
        Kepler.Text.TameSpine.nextElCatLast1 (by rw [← hruv]; exact hnd) hu0 hv_ne
      rw [← hruv] at h1
      rwa [hv_eq] at h1
    have hprev : Kepler.Assembly.prevEl r d = u.getLast! := by
      rw [← hlastu]
      exact Kepler.Text.TameLp.prevEl_nextEl hnd (by
        rw [hruv]
        exact List.mem_append.mpr (Or.inl (memLastBang u hu0)))
    have hbpd : nextEl r u.getLast! ≠ fList L (eList u.getLast!) := by
      rcases hhead with h | h
      · exact absurd h hdnehead
      · rwa [hprev] at h
    have hcat1 := partsCatChain L (r := r) (u := u) (v := v) (x := u.getLast!)
      hruv rfl hu0 hv_ne hbpd hnd
    -- 现在证 `[d] ∈ parts L v`
    have hnd_uv : (u ++ v).Nodup := by rw [← hruv]; exact hnd
    have hndv : v.Nodup := List.Sublist.nodup (List.sublist_append_right u v) hnd_uv
    have hdv : d ∈ v := by rw [hv_eq]; exact List.mem_cons_self ..
    by_cases hv'0 : r.drop (i + 1) = []
    · -- v = [d]
      have hvd : v = [d] := by rw [hv_eq, hv'0]
      have hpv : parts L v = [[d]] := by
        rw [hvd]
        exact hpd
      rw [hcat1, hpv]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
    · -- v = [d] ++ v'
      have hndv' : (d :: r.drop (i + 1)).Nodup := by rw [← hv_eq]; exact hndv
      have hvlast : d ≠ v.getLast! := by
        rw [hv_eq]
        exact consHeadNeGetLast hv'0 hndv'
      have hb : nextEl r d ≠ fList L (eList d) := by
        rcases hlast with h | h
        · exact absurd h (neGetLastOfDropSuccNe hnd hd hv'0)
        · exact h
      have hrv : nextEl r d = nextEl v d := by
        rw [hruv]
        exact nextElCat2 hnd_uv hdv hvlast
      have hbv : nextEl v d ≠ fList L (eList d) := by
        intro hc
        exact hb (hrv.trans hc)
      have hruv2 : v = [d] ++ r.drop (i + 1) := by rw [hv_eq]; rfl
      have hcat2 := partsCatChain L (r := v) (u := [d]) (v := r.drop (i + 1)) (x := d)
        hruv2 rfl (by simp) hv'0 hbv hndv
      have hpv : [d] ∈ parts L v := by
        rw [hcat2, hpd]
        exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
      rw [hcat1]
      exact List.mem_append.mpr (Or.inr hpv)

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.memPartsSingleton
