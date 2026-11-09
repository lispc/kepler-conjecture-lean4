/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12S — AQ12 叶 W9（decl 54，F2 收口件）。

  HOL：AQ12.hl:2693-:2906（214 行）`exists_contour_combinatoric`：
  `r1, r2 ∈ cat (replace r [SND split] N) [FST split]`、`u ∈ r1`、`v ∈ r2`
  ⇒ 存在 contour u → v，支撑 ⊆ flatten(filter final (cat (replace ...) [FST]))。

  件目/依赖（开工报价）：1 件 / 1 文件；估 180–280（≤400）。
  · 9 支调度（r1/r2 各自 ∈ N / = SND split / = FST split）：
    (N,N) = SFlag 首合取；(N,S)=decl 45；(N,F)=decl 53；(S,N)=decl 46；
    (S,S) = existsConnectedLoop on SND；(S,F)=decl 40；(F,N)=decl 51；
    (F,S)=decl 41；(F,F) = existsConnectedLoop on FST。
  · **`h4 : aq4Concl` 槽：吃**（45/46/51/53/40/41 + 两条 loop 支的 FST/SND 行
    loopListSpine）。DIFFERS：W5b/W6b/W8a-ii/W8b/W9 吃，W7/W8a-i 不吃。
  · 行来源分解：`List.mem_append` + `memReplaceCases`（TowerBase:116 公开件）。
  · 陈述对表：HOL 的全部前提（含 `MEM r1/r2 (cat ...)`）逐项对应；唯一附加 = `h4`。

  纪律：零 sorry/admit/native_decide/axiom；既有文件零触碰；主仓 tracked 零改动。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12R

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts eList fList)
open Kepler.Text.TameLp (GoodListNodesTl)

/-- **HOL `exists_contour_combinatoric`**（AQ12.hl:2693-:2906）：
目标行表中任两行（r1 含 u、r2 含 v）之间的 contour。 -/
theorem aqs_existsContourCombinatoric (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (h4 : aq4Concl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (f : List (ℕ × ℕ))
    {z y z1 : ℕ × ℕ} {r1 r2 : List (ℕ × ℕ)} {u v : ℕ × ℕ}
    (hz : lZSpine L N r x = z) (hy : lYSpine L r x = y) (hz1 : prevEl r z = z1)
    (hfin1 : finalListSpine L r1) (hfin2 : finalListSpine L r2)
    (h1mem : r1 ∈ replaceSpine r [(splitNormalListSpine L r f y z1).2] N
      ++ [(splitNormalListSpine L r f y z1).1])
    (h2mem : r2 ∈ replaceSpine r [(splitNormalListSpine L r f y z1).2] N
      ++ [(splitNormalListSpine L r f y z1).1])
    (hfind : findFaceDarts L x = f)
    (hv : v ∈ r2) (hu : u ∈ r1) :
    ∃ s : List (ℕ × ℕ), ContourListSpine L s ∧ s ≠ [] ∧ s.head! = u ∧
      s.getLast! = v ∧ setOfListSpine s ⊆
        setOfListSpine ((replaceSpine r [(splitNormalListSpine L r f y z1).2] N
          ++ [(splitNormalListSpine L r f y z1).1]).filter
            (fun l => decide (finalListSpine L l))).flatten := by
  -- §0 行来源三分：∈ N / = SND split / = FST split
  have hdec1 : r1 ∈ N ∨ r1 = (splitNormalListSpine L r f y z1).2
      ∨ r1 = (splitNormalListSpine L r f y z1).1 := by
    rcases List.mem_append.mp h1mem with h | h
    · rcases memReplaceCases h with hN | ⟨-, hS⟩
      · exact Or.inl hN
      · exact Or.inr (Or.inl (List.mem_singleton.mp hS))
    · exact Or.inr (Or.inr (List.mem_singleton.mp h))
  have hdec2 : r2 ∈ N ∨ r2 = (splitNormalListSpine L r f y z1).2
      ∨ r2 = (splitNormalListSpine L r f y z1).1 := by
    rcases List.mem_append.mp h2mem with h | h
    · rcases memReplaceCases h with hN | ⟨-, hS⟩
      · exact Or.inl hN
      · exact Or.inr (Or.inl (List.mem_singleton.mp hS))
    · exact Or.inr (Or.inr (List.mem_singleton.mp h))
  -- §1 公用：目标包含 FinalDartList N
  have hfinalSubset : ∀ d ∈ FinalDartListSpine L N, d ∈ ((replaceSpine r
      [(splitNormalListSpine L r f y z1).2] N
      ++ [(splitNormalListSpine L r f y z1).1]).filter
        (fun l => decide (finalListSpine L l))).flatten := by
    intro d hd
    obtain ⟨l', hl', hdl⟩ := List.mem_flatten.mp hd
    obtain ⟨hl'N, hl'fin⟩ := List.mem_filter.mp hl'
    have hl'fin' : finalListSpine L l' := decide_eq_true_iff.mp hl'fin
    have hl'r : l' ≠ r := fun h => hf (h ▸ hl'fin')
    have hmem : l' ∈ replaceSpine r [(splitNormalListSpine L r f y z1).2] N :=
      memReplaceOfNeMem hl'r hl'N
    exact List.mem_flatten.mpr
      ⟨l', List.mem_filter.mpr
        ⟨List.mem_append.mpr (Or.inl hmem), by simpa using hl'fin'⟩, hdl⟩
  -- §1b canonical ↔ f-split 与两行成员（h4 投影共用）
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hz1c : prevEl r (lZSpine L N r x) = z1 := by rw [hz]; exact hz1
  have hfindcanon : findFaceDarts L (lYSpine L r x) = f :=
    (aq10_memFindFaceImpFacesEq hL.1 (pplhuljV0 L hL hgn hunL hm hf).1).trans hfind
  have hsplit_eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x)))
      = splitNormalListSpine L r f y z1 := by
    rw [← hfindcanon, ← hy, ← hz1c]
  have hmemS : (splitNormalListSpine L r f y z1).2 ∈ ntransSpine L N r x 1 := by
    rw [← hsplit_eq]
    exact sndMemRtran1 L hm.1.2.2.1 hf
  have hmemF : (splitNormalListSpine L r f y z1).1 ∈ ntransSpine L N r x 1 := by
    rw [← hsplit_eq]
    exact aq8w2b_fstMemRtran1 L hf
  -- §2 九支调度
  rcases hdec1 with h1N | h1S | h1F
  · -- r1 ∈ N
    rcases hdec2 with h2N | h2S | h2F
    · -- (N,N)：SFlag 首合取
      have huF : u ∈ FinalDartListSpine L N :=
        List.mem_flatten.mpr
          ⟨r1, List.mem_filter.mpr ⟨h1N, by simpa using hfin1⟩, hu⟩
      have hvF : v ∈ FinalDartListSpine L N :=
        List.mem_flatten.mpr
          ⟨r2, List.mem_filter.mpr ⟨h2N, by simpa using hfin2⟩, hv⟩
      obtain ⟨s, hcs, hne, hhd, hlast, hsF⟩ := (hm.2.2 hf).1 u huF v hvF
      refine ⟨s, hcs, hne, hhd, hlast, ?_⟩
      intro d hd
      exact hfinalSubset d (hsF d hd)
    · -- (N,S)：decl 45
      exact aqs_existsContourSndNotFst L hL hgn h4 hm hf f hz hy hz1
        hfin1 (h2S ▸ hfin2) rfl h1N hfind (h2S ▸ hv) hu
    · -- (N,F)：decl 53
      exact aqs_existsContourFstNotSnd L hL hgn h4 hm hf f hz hy hz1
        hfin1 (h2F ▸ hfin2) h1N rfl hfind (h2F ▸ hv) hu
  · -- r1 = SND split
    rcases hdec2 with h2N | h2S | h2F
    · -- (S,N)：decl 46（u ∈ SND，v ∈ N-row）
      exact aqs_existsContourNotFstSnd L hL hgn h4 hm hf f hz hy hz1
        hfin2 (h1S ▸ hfin1) rfl h2N hfind (h1S ▸ hu) hv
    · -- (S,S)：SND 行内 existsConnectedLoop
      have hndS : (splitNormalListSpine L r f y z1).2.Nodup :=
        uniqFlattenUniq _ (aq1 L hL N r x hgn hm) _ hmemS
      have hloopS : loopListSpine L (splitNormalListSpine L r f y z1).2 :=
        h4 N r x hgn hm _ hmemS
      have hfinS : finalListSpine L (splitNormalListSpine L r f y z1).2 := h1S ▸ hfin1
      have hSmem : (splitNormalListSpine L r f y z1).2 ∈ replaceSpine r
          [(splitNormalListSpine L r f y z1).2] N
          ++ [(splitNormalListSpine L r f y z1).1] := h1S ▸ h1mem
      obtain ⟨s, hcs, hhd, hlast, hsub, hne⟩ :=
        aqs_existsConnectedLoop hndS hloopS (h1S ▸ hu) (h2S ▸ hv)
      refine ⟨s, hcs, hne, hhd, hlast, ?_⟩
      intro d hd
      exact List.mem_flatten.mpr
        ⟨_, List.mem_filter.mpr ⟨hSmem, by simpa using hfinS⟩, hsub hd⟩
    · -- (S,F)：decl 40
      exact aqs_existsContourSndFst L hL hgn h4 hm hf f hz hy hz1
        (h2F ▸ hfin2) (h1S ▸ hfin1) rfl rfl hfind (h2F ▸ hv) (h1S ▸ hu)
  · -- r1 = FST split
    rcases hdec2 with h2N | h2S | h2F
    · -- (F,N)：decl 51
      exact aqs_existsContourNotSndFst L hL hgn h4 hm hf f hz hy hz1
        (h1F ▸ hfin1) hfin2 h2N rfl hfind hv (h1F ▸ hu)
    · -- (F,S)：decl 41
      exact aqs_existsContourFstSnd L hL hgn h4 hm hf f hz hy hz1
        (h1F ▸ hfin1) (h2S ▸ hfin2) rfl rfl hfind (h2S ▸ hv) (h1F ▸ hu)
    · -- (F,F)：FST 行内 existsConnectedLoop
      have hndF : (splitNormalListSpine L r f y z1).1.Nodup :=
        uniqFlattenUniq _ (aq1 L hL N r x hgn hm) _ hmemF
      have hloopF : loopListSpine L (splitNormalListSpine L r f y z1).1 :=
        h4 N r x hgn hm _ hmemF
      have hfinF : finalListSpine L (splitNormalListSpine L r f y z1).1 := h1F ▸ hfin1
      have hFmem : (splitNormalListSpine L r f y z1).1 ∈ replaceSpine r
          [(splitNormalListSpine L r f y z1).2] N
          ++ [(splitNormalListSpine L r f y z1).1] :=
        List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
      obtain ⟨s, hcs, hhd, hlast, hsub, hne⟩ :=
        aqs_existsConnectedLoop hndF hloopF (h1F ▸ hu) (h2F ▸ hv)
      refine ⟨s, hcs, hne, hhd, hlast, ?_⟩
      intro d hd
      exact List.mem_flatten.mpr
        ⟨_, List.mem_filter.mpr ⟨hFmem, by simpa using hfinF⟩, hsub hd⟩

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aqs_existsContourCombinatoric
