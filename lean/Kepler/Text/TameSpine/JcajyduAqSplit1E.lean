/-
  Kepler.Text.TameSpine.JcajyduAqSplit1E — E4d-a-2（f_last 前的部分）：
  `betwnSelf` 头、idxOf/nextEl 收口（ⓤ2 泛型核 + f1 两支）、ⓑ `d1 = e_list z1`。

  件目（7 件，全真证）：
  ① `nextElOfIdxLast`：`x` 在末位（`idxOf = len-1`）⇒ `nextEl = head!`；
  ② `nextElAppendOfNotMem`：`x ∉ a` ∧ `b.idxOf x + 1 < b.length` ⇒
     `nextEl (a++b) x = nextEl b x`（idxOf 搬运 + `getD_append_right`）；
  ③ `nextElAppendSingletonOfNotMem`：`a ≠ []` ∧ `x ∉ a` ⇒ `nextEl (a ++ [x]) x = a.head!`
     （`ⓤ2` 的末元回绕形）；
  ④ `z1NotMemF1Prefix`：`z1 ∉ [ra] ++ betwn r ra z1`（`ra ≠ z1` + `notBetwn2`）；
  ⑤ `nextElF1Z1OfNe`：**f1 末位收口（`ra ≠ z1` 支）** `nextEl f1 z1 = ra`；
  ⑥ `betweenSelfNeNil`：`x ∈ r`、`r.Nodup`、`r ≠ [x]` ⇒ `betwn r x x ≠ []`
     （splitAt 分解：`post ++ pre = [] ⇒ r = [x]`）；
  ⑦ **`lastWindowEqEListZ1`（ⓑ）**：`(betwn f y z).getLast = e_list z1`——
     `fList d1 = z`（`nextLastBetwn` 面侧 + `findFaceDarts_congr_of_mem`）与
     `fList (e_list z1) = z`（`loopListSpine` z1 二择一：`prevRNotEqF` 排除
     `fList z1 = z`，余 `nextEl r z1 = z` 直落）经 `fListInjDarts` 合流。

  边界（BLOCKED，见 DELIVERY 续 §E4d-a-2）：f_last 接线（ⓓ）未落。剩余 =
  `split1EqSpine`（split.1 展开为 `new1.reverse ++ f1`）→ `getLast! split.1 = z1`
  → `new1` 空/非空 × `ra = z1`/`ra ≠ z1` 四支（其中 `ra = z1` 支由 ⑤ 的类比
  `nextEl f1 z1 = z`（⑥+`HD_BETWN1`）撞 `prevRNotEqF` 闭合；非空支用 ⑤ +
  `lastNew1EqFList`（E4b）；空窗支用 `betwnNilNextOfNodup` + `nextRNotEqF`/
  `prevRNotEqF` + `fListInjDarts`）。

  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameSpine.JcajyduAqSplit1D

namespace Kepler.Text.TameSpine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Kepler.Assembly (nextEl prevEl eList fList GoodList findFaceDarts nList
  listOfDarts listPairs)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nextEl_mem_of_mem prevEl_mem_of_mem getD_eq_getElem_of_lt)

/-! ## §1 通用 idxOf/nextEl 收口（ⓤ2 的泛型核） -/

/-- `x` 落在末位 ⇒ `nextEl` 回绕到头。 -/
theorem nextElOfIdxLast {α : Type*} [Inhabited α] [BEq α] [LawfulBEq α] {s : List α} {x : α}
    (hne : s ≠ [])
    (h : s.idxOf x = s.length - 1) : nextEl s x = s.head! := by
  unfold nextEl
  rw [if_pos h]
  cases s with
  | nil => exact absurd rfl hne
  | cons a t => rfl

/-- `x ∉ a` 且 `x` 在 `b` 中不居末位 ⇒ `nextEl (a ++ b) x = nextEl b x`
（idxOf 搬运 + getElem 切分）。 -/
theorem nextElAppendOfNotMem {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α] {a b : List α} {x : α}
    (hxa : x ∉ a) (hxb : b.idxOf x + 1 < b.length) :
    nextEl (a ++ b) x = nextEl b x := by
  have hidx : (a ++ b).idxOf x = a.length + b.idxOf x :=
    List.idxOf_append_of_notMem hxa
  have hlen : (a ++ b).length = a.length + b.length := List.length_append
  have h1 : (a ++ b).getD (a.length + b.idxOf x + 1) x = b.getD (b.idxOf x + 1) x := by
    rw [List.getD_append_right (l := a) (l' := b) (d := x)
      (n := a.length + b.idxOf x + 1) (by omega)]
    rw [show a.length + b.idxOf x + 1 - a.length = b.idxOf x + 1 from by omega]
  unfold nextEl
  rw [hidx, if_neg (by omega), if_neg (by omega)]
  exact h1

/-- `r ≠ [x]`（x ∈ r、r 无重）⇒ `betwn r x x ≠ []`（循环余部非空）。 -/
theorem betweenSelfNeNil {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α] {r : List α} {x : α}
    (hx : x ∈ r) (hnd : r.Nodup) (hne : r ≠ [x]) : between r x x ≠ [] := by
  have hpre : x ∉ (Kepler.Graphs.splitAt x r).1 :=
    Kepler.Graphs.splitAt_distinct_ram_fst hnd
  have hcont : ¬ (Kepler.Graphs.splitAt x r).2.contains x :=
    mt List.contains_iff_mem.mp (Kepler.Graphs.splitAt_distinct_ram_snd hnd)
  have hb : between r x x = (Kepler.Graphs.splitAt x r).2 ++ (Kepler.Graphs.splitAt x r).1 := by
    rw [Kepler.Graphs.between_def, if_neg hcont, Kepler.Graphs.splitAt_no_ram hpre]
  intro h0
  rw [hb] at h0
  obtain ⟨h2, h1⟩ := List.append_eq_nil_iff.mp h0
  apply hne
  rw [Kepler.Graphs.splitAt_ram hx, h1, h2]
  rfl


/-- `x ∉ a`、`a ≠ []` ⇒ `nextEl (a ++ [x]) x = a.head!`（末位回绕）。 -/
theorem nextElAppendSingletonOfNotMem {α : Type*} [Inhabited α] [BEq α] [LawfulBEq α]
    {a : List α} {x : α} (hane : a ≠ []) (hx : x ∉ a) :
    nextEl (a ++ [x]) x = a.head! := by
  have hidx : (a ++ [x]).idxOf x = a.length := by
    rw [List.idxOf_append_of_notMem hx]
    simp
  rw [nextElOfIdxLast (by simp) (by simpa using hidx)]
  exact List.head!_append [x] hane

/-- `z1 ∉ [y] ++ betwn r y z1`（`y ≠ z1`、r 无重）。 -/
theorem z1NotMemF1Prefix {α : Type*} [BEq α] [LawfulBEq α] {r : List α} {y z1 : α}
    (hnd : r.Nodup) (hra : y ≠ z1) : z1 ∉ [y] ++ between r y z1 := by
  intro h
  rcases List.mem_append.mp h with h1 | h2
  · exact hra (List.mem_singleton.mp h1).symm
  · exact notBetwn2 hnd h2

/-- **f1 末位收口（`ra ≠ z1` 支）**：`nextEl f1 z1 = nextEl r y`。 -/
theorem nextElF1Z1OfNe {α : Type*} [Inhabited α] [BEq α] [LawfulBEq α] {r : List α} {y z1 : α}
    (hnd : r.Nodup) (hra : y ≠ z1) :
    nextEl ([y] ++ between r y z1 ++ [z1]) z1 = y := by
  have hA : ([y] ++ between r y z1) ≠ [] := by simp
  rw [nextElAppendSingletonOfNotMem hA (z1NotMemF1Prefix hnd hra)]
  simp

/-! ## §2 ⓑ：`LAST (betwn f y z) = e_list z1`（AQ23:502-:669 的 d1 支） -/

/-- **窗口末元 = `e_list z1`**：`fList d1 = z`（`nextLastBetwn` 面侧）与
`fList (e_list z1) = z`（`loopListSpine` z1 + `nextElPrevElZ` + `prevRNotEqF`）
经 `fListInjDarts` 合流。 -/
theorem lastWindowEqEListZ1 (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {hne : between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x) ≠ []} :
    (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x)).getLast hne
      = eList (prevEl r (lZSpine L N r x)) := by
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hyd : lYSpine L r x ∈ listOfDarts L := memYtransListOfDarts L hL hgn hm hf
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hz1r : prevEl r (lZSpine L N r x) ∈ r := prevEl_mem_of_mem hzr
  have hyz : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hyf : lYSpine L r x ∈ findFaceDarts L (lYSpine L r x) :=
    (dart_in_face L _).mpr hyd
  have hzf : lZSpine L N r x ∈ findFaceDarts L (lYSpine L r x) :=
    zMemFindFaceDarts L hL hgn hunL hm hf
  have hfnd : (findFaceDarts L (lYSpine L r x)).Nodup := findFaceDarts_nodup hL.1 _
  -- fList d1 = z
  have hd1f : (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)).getLast hne ∈ findFaceDarts L (lYSpine L r x) :=
    memBetweenOfMem (List.getLast_mem hne)
  have hd1n : (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)).getLast hne ∈ listOfDarts L :=
    mem_darts_of_mem_findFace L hd1f
  have hfl1 : fList L ((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)).getLast hne) = lZSpine L N r x := by
    show nextEl (findFaceDarts L _) _ = lZSpine L N r x
    rw [findFaceDarts_congr_of_mem hL.1 hyd hd1f]
    exact nextLastBetwn hyf hzf hfnd hyz hne
  -- fList (eList z1) = z
  have hloop : loopListSpine L r := hm.1.2.1.2.2.2.1 r hm.1.2.2.1
  have hnextz1 : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hrnd _
  have hfl2 : fList L (eList (prevEl r (lZSpine L N r x))) = lZSpine L N r x := by
    rcases (hloop _ hz1r).2 with h1 | h1
    · exact absurd (h1.symm.trans hnextz1) (prevRNotEqF L hL hgn hunL hm hf)
    · rw [hnextz1] at h1
      exact h1.symm
  have he : eList (prevEl r (lZSpine L N r x)) ∈ listOfDarts L :=
    hL.2.2 _ ((hloop _ hz1r).1)
  exact (fListInjDarts L hL hd1n he).mp (hfl1.trans hfl2.symm)

end Kepler.Text.TameSpine

#print axioms Kepler.Text.TameSpine.nextElOfIdxLast
#print axioms Kepler.Text.TameSpine.nextElAppendOfNotMem
#print axioms Kepler.Text.TameSpine.nextElAppendSingletonOfNotMem
#print axioms Kepler.Text.TameSpine.z1NotMemF1Prefix
#print axioms Kepler.Text.TameSpine.nextElF1Z1OfNe
#print axioms Kepler.Text.TameSpine.betweenSelfNeNil
#print axioms Kepler.Text.TameSpine.lastWindowEqEListZ1
