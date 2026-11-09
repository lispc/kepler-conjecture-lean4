/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12N — AQ12 叶 W6b（F2，decls 45–46）。

  HOL 锚：reference/flyspeck/text_formalization/tame/AQ12.hl:1944-:2149（206 HOL 行）
  · decl 45 `exists_contour_snd_not_fst`（:1944-:2044，101 行）
  · decl 46 `exists_contour_not_fst_snd`（:2045-:2149，105 行）

  ┌─ 开工报价（件目 + 行数区间 + 依赖 + 拆分表）──────────────────
  │ 2 件；开工估 260–320 行。若单文件 >300 则按下列边界拆：
  │   W6b-i  = decl 45（12N，含 §0 公共辅件）；
  │   W6b-ii = decl 46（12O，import 12N 复用辅件）。
  │ **依赖：吃 `h4 : aq4Concl` 槽（W5b 同款；本波 DIFFERS 记账）**——
  │ 两件都要 `loopListSpine L r2`（SND split 行）供 existsConnectedLoop；
  │ AQ4 的 `aq4_loopS1`（FST 半）仍未收，故显式槽 + `sndMemRtran1` 投影。
  │ 新件：`SFlagListSpine` 首合取（`hm.2.2 hf`）给 final dart 之间的 contour；
  │ `eList x` / `fList (eList x)` 落 `FinalDartListSpine L N`（AQ11 + 合取 7）；
  │ `x ∈ r2`（aq7+aq10，W6a 同款）；`FinalDartList N ⊆ target`
  │ （`memReplaceOfNeMem`：r 非 final，final 行不经 replace 换掉）。
  │ HOL 目标里的 `SND split` 用 `r2`（hr2 代入）；`FST split` 按字面保留。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线 ─────────────────────────────────────────────────────────
  │ 45：s = SFlag contour(u → eList x)；s1 = SND contour(nextEl f x → v)；
  │     拼 s ++ s1，junction = `one_step_e_list_w`。
  │ 46：s1 = SND contour(u → x)；s = SFlag contour(fList (eList x) → v)；
  │     拼 s1 ++ s，junction = `one_step_e_list_x`。
  │ 支撑：s ⊆ FinalDartList N ⊆ target；s1 ⊆ r2 ⊆ target。
  └────────────────────────────────────────────────────────────────

  纪律：零 sorry/admit/native_decide/axiom 声明；既有文件零触碰；主仓
  tracked 零改动（本文件经 patch 交付）。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12M
import Kepler.Text.TameSpine.JcajyduAqLeaf11

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts eList fList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList nextEl_mem_of_mem)

/-! ## §0 公共辅件 -/

/-- `r ∈ N ∧ d ∈ [r2] ⇒ d ∈ replaceSpine r [r2] N`（私件，与 12L 同证）。 -/
private theorem aq12n_memReplaceSpineOfMem {α : Type} [DecidableEq α] {z x : α}
    {ys xs : List α} (hz : z ∈ xs) (hx : x ∈ ys) : x ∈ replaceSpine z ys xs := by
  induction xs with
  | nil => exact absurd hz (List.not_mem_nil)
  | cons a as ih =>
    by_cases haz : a = z
    · rw [replaceSpine, if_pos haz]
      exact List.mem_append.mpr (Or.inl hx)
    · rw [replaceSpine, if_neg haz]
      rcases List.mem_cons.mp hz with h | h
      · exact absurd h.symm haz
      · exact List.mem_cons_of_mem _ (ih h)

/-- SND 行（r2）的 Nodup 与 loopListSpine（h4 投影）。 -/
private theorem aq12n_sndRowFacts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (h4 : aq4Concl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (f : List (ℕ × ℕ)) {y z1 : ℕ × ℕ} {r2 : List (ℕ × ℕ)}
    (hy : lYSpine L r x = y) (hz1c : prevEl r (lZSpine L N r x) = z1)
    (hr2 : (splitNormalListSpine L r f y z1).2 = r2)
    (hfindcanon : findFaceDarts L (lYSpine L r x) = f) :
    r2.Nodup ∧ loopListSpine L r2 := by
  have hsplit_eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x)))
      = splitNormalListSpine L r f y z1 := by
    rw [← hfindcanon, ← hy, ← hz1c]
  have hmem : (splitNormalListSpine L r f y z1).2 ∈ ntransSpine L N r x 1 := by
    rw [← hsplit_eq]
    exact sndMemRtran1 L hm.1.2.2.1 hf
  have hNflat : (ntransSpine L N r x 1).flatten.Nodup := aq1 L hL N r x hgn hm
  have hnd : (splitNormalListSpine L r f y z1).2.Nodup := uniqFlattenUniq _ hNflat _ hmem
  have hl : loopListSpine L (splitNormalListSpine L r f y z1).2 := h4 N r x hgn hm _ hmem
  exact ⟨hr2 ▸ hnd, hr2 ▸ hl⟩

/-- `x ∈ r2`（aq7 + aq10 + rtrans→canonical→f-split 三段落，W6a 同款）。 -/
private theorem aq12n_xMemSplitSnd (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (f : List (ℕ × ℕ)) {z y z1 : ℕ × ℕ} {r2 : List (ℕ × ℕ)}
    (hz : lZSpine L N r x = z) (hy : lYSpine L r x = y) (hz1 : prevEl r z = z1)
    (hr2 : (splitNormalListSpine L r f y z1).2 = r2)
    (hfind : findFaceDarts L x = f) : x ∈ r2 := by
  have hz1c : prevEl r (lZSpine L N r x) = z1 := by rw [hz]; exact hz1
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hfindcanon : findFaceDarts L (lYSpine L r x) = f :=
    (aq10_memFindFaceImpFacesEq hL.1 (pplhuljV0 L hL hgn hunL hm hf).1).trans hfind
  have hsplit_eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x)))
      = splitNormalListSpine L r f y z1 := by
    rw [← hfindcanon, ← hy, ← hz1c]
  have hr' : rtransSpine L N r x 1
      = (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 := by
    show ((transformListSpine L x)^[1] (N, r)).2 = _
    rw [Function.iterate_one]
    simp only [transformListSpine, if_neg hf]
  have hconv : rtransSpine L N r x 1 = r2 := by rw [hr', hsplit_eq, hr2]
  have h7 := aq7 L hL N r x hgn hm
  rwa [hconv] at h7

/-- `eList x ∈ FinalDartListSpine L N`（合取 7 的 final 行 + memFindList1）。 -/
private theorem aq12n_eListMemFinal (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) : eList x ∈ FinalDartListSpine L N := by
  have hfl : eList x ∈ N.flatten := aq11_eListMemFlatten L hL hgn hm
  have hin : eList x ∈ findListSpine N (eList x) := memFindList1 hfl
  have hrowN : findListSpine N (eList x) ∈ N := findListSpineMemN hfl
  have hfin : finalListSpine L (findListSpine N (eList x)) := hm.1.2.2.2.2.2.2
  exact List.mem_flatten.mpr
    ⟨_, List.mem_filter.mpr ⟨hrowN, by simpa using hfin⟩, hin⟩

/-- `fList L (eList x) ∈ FinalDartListSpine L N`（同行，`fLast` + `nextEl_mem`）。 -/
private theorem aq12n_fListEListMemFinal (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) : fList L (eList x) ∈ FinalDartListSpine L N := by
  have hfl : eList x ∈ N.flatten := aq11_eListMemFlatten L hL hgn hm
  have hin : eList x ∈ findListSpine N (eList x) := memFindList1 hfl
  have hrowN : findListSpine N (eList x) ∈ N := findListSpineMemN hfl
  have hfin : finalListSpine L (findListSpine N (eList x)) := hm.1.2.2.2.2.2.2
  have hmem : fList L (eList x) ∈ findListSpine N (eList x) := by
    rw [hfin (eList x) hin]
    exact nextEl_mem_of_mem hin
  exact List.mem_flatten.mpr
    ⟨_, List.mem_filter.mpr ⟨hrowN, by simpa using hfin⟩, hmem⟩

/-- final 行（∈ N）的元素落 `FinalDartListSpine L N`。 -/
private theorem aq12n_memFinalOfRow {L : fgraph ℕ} {N : List (List (ℕ × ℕ))}
    {r' : List (ℕ × ℕ)} (hrN : r' ∈ N) (hfin : finalListSpine L r') :
    ∀ d ∈ r', d ∈ FinalDartListSpine L N := by
  intro d hd
  exact List.mem_flatten.mpr ⟨r', List.mem_filter.mpr ⟨hrN, by simpa using hfin⟩, hd⟩

/-- `FinalDartListSpine L N ⊆ target`（r 非 final ⇒ final 行不经 replace 换掉）。 -/
private theorem aq12n_finalDartSubset (L : fgraph ℕ)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {r1 r2 : List (ℕ × ℕ)}
    (hf : ¬finalListSpine L r) :
    ∀ d ∈ FinalDartListSpine L N, d ∈ ((replaceSpine r [r2] N ++ [r1]).filter
      (fun l => decide (finalListSpine L l))).flatten := by
  intro d hd
  obtain ⟨l, hl, hdl⟩ := List.mem_flatten.mp hd
  obtain ⟨hlN, hlfin⟩ := List.mem_filter.mp hl
  have hlfin' : finalListSpine L l := decide_eq_true_iff.mp hlfin
  have hmem : l ∈ replaceSpine r [r2] N := memReplaceOfNeMem (fun h => hf (h ▸ hlfin')) hlN
  exact List.mem_flatten.mpr
    ⟨l, List.mem_filter.mpr ⟨List.mem_append.mpr (Or.inl hmem), by simpa using hlfin'⟩, hdl⟩

/-- SND 行（r2）⊆ target 左段。 -/
private theorem aq12n_rowMemTarget (L : fgraph ℕ) {N : List (List (ℕ × ℕ))}
    {r r1 r2 : List (ℕ × ℕ)} (hrN : r ∈ N) (hfin2 : finalListSpine L r2) :
    ∀ d ∈ r2, d ∈ ((replaceSpine r [r2] N ++ [r1]).filter
      (fun l => decide (finalListSpine L l))).flatten := by
  intro d hd
  have hmem : r2 ∈ replaceSpine r [r2] N :=
    aq12n_memReplaceSpineOfMem hrN (List.mem_singleton_self _)
  exact List.mem_flatten.mpr
    ⟨r2, List.mem_filter.mpr ⟨List.mem_append.mpr (Or.inl hmem), by simpa using hfin2⟩, hd⟩

/-! ## §1 HOL AQ12.hl:1944 `exists_contour_snd_not_fst` -/

/-- **HOL `exists_contour_snd_not_fst`**（AQ12.hl:1944-:2044）：
`u ∈ r1`（r1 ∈ N、final）、`v ∈ r2`（SND split、final）⇒ 存在 contour u → v。 -/
theorem aqs_existsContourSndNotFst (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (h4 : aq4Concl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (f : List (ℕ × ℕ))
    {z y z1 : ℕ × ℕ} {r1 r2 : List (ℕ × ℕ)} {u v : ℕ × ℕ}
    (hz : lZSpine L N r x = z) (hy : lYSpine L r x = y) (hz1 : prevEl r z = z1)
    (hfin1 : finalListSpine L r1) (hfin2 : finalListSpine L r2)
    (hr2 : (splitNormalListSpine L r f y z1).2 = r2)
    (hr1N : r1 ∈ N) (hfind : findFaceDarts L x = f)
    (hv : v ∈ r2) (hu : u ∈ r1) :
    ∃ s : List (ℕ × ℕ), ContourListSpine L s ∧ s ≠ [] ∧ s.head! = u ∧
      s.getLast! = v ∧ setOfListSpine s ⊆
        setOfListSpine ((replaceSpine r [r2] N
          ++ [(splitNormalListSpine L r f y z1).1]).filter
            (fun l => decide (finalListSpine L l))).flatten := by
  have hz1c : prevEl r (lZSpine L N r x) = z1 := by rw [hz]; exact hz1
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hfindcanon : findFaceDarts L (lYSpine L r x) = f :=
    (aq10_memFindFaceImpFacesEq hL.1 (pplhuljV0 L hL hgn hunL hm hf).1).trans hfind
  obtain ⟨hnd2, hloop2⟩ :=
    aq12n_sndRowFacts L hL hgn h4 hm hf f hy hz1c hr2 hfindcanon
  have hw2 : nextEl f x ∈ r2 :=
    aqs_wMemSplitSnd L hL hgn hm hf f hz hy hz1 hr2 hfind rfl
  obtain ⟨s1, hc1, hhd1, hlast1, hsub1, hne1⟩ :=
    aqs_existsConnectedLoop (L := L) (s := r2) (x := nextEl f x) (y := v)
      hnd2 hloop2 hw2 hv
  have hsf : SFlagListSpine L N r x := hm.2.2 hf
  have huF : u ∈ FinalDartListSpine L N := aq12n_memFinalOfRow hr1N hfin1 u hu
  obtain ⟨s, hcs, hne, hhd, hlast, hsF⟩ :=
    hsf.1 u huF (eList x) (aq12n_eListMemFinal L hL hgn hm)
  have hcat : ContourListSpine L (s ++ s1) := by
    refine (aqs_contourListCat hne hne1).mpr ⟨hcs, hc1, ?_⟩
    rw [hlast, hhd1]
    exact aqs_oneStepEListW L hL hgn hm hf f hfind rfl
  refine ⟨s ++ s1, hcat, ?_, ?_, ?_, ?_⟩
  · exact List.ne_nil_of_mem (List.mem_append_left _ (aqs_headMem hne))
  · rw [List.head!_append _ hne, hhd]
  · rw [aqs_getLastAppend, if_neg hne1, hlast1]
  · intro d hd
    rcases List.mem_append.mp hd with hdS | hd1
    · exact aq12n_finalDartSubset (L := L) (N := N) (r := r)
        (r1 := (splitNormalListSpine L r f y z1).1) (r2 := r2) hf d (hsF d hdS)
    · exact aq12n_rowMemTarget (L := L) (N := N) (r := r)
        (r1 := (splitNormalListSpine L r f y z1).1) (r2 := r2) hm.1.2.2.1 hfin2 d (hsub1 hd1)


/-! ## §2 HOL AQ12.hl:2045 `exists_contour_not_fst_snd` -/

/-- **HOL `exists_contour_not_fst_snd`**（AQ12.hl:2045-:2149）：
`u ∈ r2`（SND split、final）、`v ∈ r1`（r1 ∈ N、final）⇒ 存在 contour u → v。 -/
theorem aqs_existsContourNotFstSnd (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (h4 : aq4Concl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (f : List (ℕ × ℕ))
    {z y z1 : ℕ × ℕ} {r1 r2 : List (ℕ × ℕ)} {u v : ℕ × ℕ}
    (hz : lZSpine L N r x = z) (hy : lYSpine L r x = y) (hz1 : prevEl r z = z1)
    (hfin1 : finalListSpine L r1) (hfin2 : finalListSpine L r2)
    (hr2 : (splitNormalListSpine L r f y z1).2 = r2)
    (hr1N : r1 ∈ N) (hfind : findFaceDarts L x = f)
    (hu : u ∈ r2) (hv : v ∈ r1) :
    ∃ s : List (ℕ × ℕ), ContourListSpine L s ∧ s ≠ [] ∧ s.head! = u ∧
      s.getLast! = v ∧ setOfListSpine s ⊆
        setOfListSpine ((replaceSpine r [r2] N
          ++ [(splitNormalListSpine L r f y z1).1]).filter
            (fun l => decide (finalListSpine L l))).flatten := by
  have hz1c : prevEl r (lZSpine L N r x) = z1 := by rw [hz]; exact hz1
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hfindcanon : findFaceDarts L (lYSpine L r x) = f :=
    (aq10_memFindFaceImpFacesEq hL.1 (pplhuljV0 L hL hgn hunL hm hf).1).trans hfind
  obtain ⟨hnd2, hloop2⟩ :=
    aq12n_sndRowFacts L hL hgn h4 hm hf f hy hz1c hr2 hfindcanon
  have hx2 : x ∈ r2 := aq12n_xMemSplitSnd L hL hgn hm hf f hz hy hz1 hr2 hfind
  obtain ⟨s1, hc1, hhd1, hlast1, hsub1, hne1⟩ :=
    aqs_existsConnectedLoop (L := L) (s := r2) (x := u) (y := x)
      hnd2 hloop2 hu hx2
  have hsf : SFlagListSpine L N r x := hm.2.2 hf
  have hvF : v ∈ FinalDartListSpine L N := aq12n_memFinalOfRow hr1N hfin1 v hv
  obtain ⟨s, hcs, hne, hhd, hlast, hsF⟩ :=
    hsf.1 (fList L (eList x)) (aq12n_fListEListMemFinal L hL hgn hm) v hvF
  have hcat : ContourListSpine L (s1 ++ s) := by
    refine (aqs_contourListCat hne1 hne).mpr ⟨hc1, hcs, ?_⟩
    rw [hlast1, hhd]
    exact aqs_oneStepEListX L hL hgn hm hf f hfind rfl
  refine ⟨s1 ++ s, hcat, ?_, ?_, ?_, ?_⟩
  · exact List.ne_nil_of_mem (List.mem_append_left _ (aqs_headMem hne1))
  · rw [List.head!_append _ hne1, hhd1]
  · rw [aqs_getLastAppend, if_neg hne, hlast]
  · intro d hd
    rcases List.mem_append.mp hd with hd1 | hdS
    · exact aq12n_rowMemTarget (L := L) (N := N) (r := r)
        (r1 := (splitNormalListSpine L r f y z1).1) (r2 := r2) hm.1.2.2.1 hfin2 d (hsub1 hd1)
    · exact aq12n_finalDartSubset (L := L) (N := N) (r := r)
        (r1 := (splitNormalListSpine L r f y z1).1) (r2 := r2) hf d (hsF d hdS)

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aqs_existsContourSndNotFst
#print axioms Kepler.Text.TameSpine.aqs_existsContourNotFstSnd
