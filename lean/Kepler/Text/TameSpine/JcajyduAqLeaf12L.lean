/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12L — AQ12 叶 W5b（F2，decls 40–41）。

  HOL 锚：reference/flyspeck/text_formalization/tame/AQ12.hl:1658-:1828（171 HOL 行）
  · decl 40 `exists_contour_snd_fst`（:1658-:1742，85 行）
  · decl 41 `exists_contour_fst_snd`（:1743-:1828，86 行）

  ┌─ 件目与分段（开工报）────────────────────────────────────────────
  │ 本波 2 件，共用同一装配骨架（HOL 两段证体几乎逐行同构，只换
  │ exists_conected_loop 的两端与 cat 顺序）：
  │   40：s1 = contour(u → y) ⊆ SND，s2 = contour(nextEl r y → v) ⊆ FST，
  │        cat s1 s2（junction = one_step_ytran）；
  │   41：s1 = contour(z → v) ⊆ SND，s2 = contour(u → z1) ⊆ FST，
  │        cat s2 s1（junction = one_step_ztran）。
  │ 估行数：210–330（2 件 × 80–120 + 头注/私件；W5a 的 1.05× 不适用，
  │ 因为本波要装配 existsConnectedLoop ×2 + cat + filter 子集，非定义性）。
  │ 实测若 >450 则拆 W5b-i（40）/ W5b-ii（41）；预计不需要。
  └────────────────────────────────────────────────────────────────────

  ┌─ 前置与条件槽（UNRESOLVED 报告，AGENTS §2 / §7）──────────────────
  │ HOL 证体的 `Aq4.AQ4` 槽 = `loop_list (ntrans … 1)`；本树 `aq4` 本体
  │ **尚未落库**（AQ4 车道 W3a 止损：`aq4_loopS1` = FST 半的 loopListSpine
  │ 未收，见 `~/c17_backup/lane_snapshots/aq4-fin/w3/DELIVERY_W3.md` §2/§6）。
  │ 按「先报告、按条件槽落、不许等、不许重造」：本文件两件**显式接收
  │ `(h4 : aq4Concl L hL)`**，从它投影 `loopListSpine L r2` / `L r1`
  │ （`aq4Concl` 的五合取第 4 槽 + `sndMemRtran1` / `aq8w2b_fstMemRtran1`）。
  │ `aq4` 落库后，消费点一行实例化 `h4 := aq4 L hL`（塔顶装配同款，
  │ 与 AQ8 的 `aqs_aqNormalList` 的 h1–h5 条件槽先例一致）。
  │ **未重建 `aq4_loopS1`、未新增任何公理/占位。**
  └────────────────────────────────────────────────────────────────────

  ┌─ 路线（比 HOL 少掉全部 indexf/next_el 逐支论证）─────────────────
  │ ① 两行的 Nodup 由 `aq1`（`(ntrans 1).flatten.Nodup`）+ 行成员性；
  │ ② 两行的 loopListSpine 由 `h4` + `sndMemRtran1`/`fstMemRtran1`；
  │ ③ 端点成员由 W5a 四件（34/35/37/39）直接给；
  │ ④ `aqs_existsConnectedLoop` 造两条 contour（decl 33）；
  │ ⑤ `aqs_contourListCat`（decl 30）拼一条，junction 由 W5a 的 36/38 给；
  │ ⑥ 支撑子集：contour ⊆ r2/r1，r2/r1 均 final 故保留在
  │    `filter finalListSpine (replaceSpine r [r2] N ++ [r1])` 的 flatten 中。
  └────────────────────────────────────────────────────────────────────

  载体：`List (ℕ × ℕ)`。纪律：零 sorry/admit/native_decide/axiom 声明；
  既有文件零触碰；主仓 tracked 零改动（本文件经 patch 交付）。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12K
import Kepler.Text.TameSpine.JcajyduAqLeaf1F
import Kepler.Text.TameSpine.JcajyduAqLeaf8W0
import Kepler.Text.TameSpine.JcajyduAqLeaf8W2b

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts eList fList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)

/-! ## §0 私件：`replaceSpine` 的成员正投（HOL `MEM2_replace` 的 replaceSpine 形） -/

/-- `r ∈ N ∧ d ∈ L ⇒ d ∈ replaceSpine r L N`（私件；与 8W0 的 private 同证，
本文件自用，不外露公开面）。 -/
private theorem aq12l_memReplaceSpineOfMem {α : Type} [DecidableEq α] {z x : α}
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

/-! ## §1 两行的公共前提（canonical split、Nodup、loopListSpine、端点成员） -/

/-- 公共装配：给定 h4 与 marked/¬final，得到 canonical split 两行的
Nodup + loopListSpine，以及 f-split 与 canonical split 的形状相等。 -/
private theorem aq12l_splitRowFacts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (h4 : aq4Concl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (f : List (ℕ × ℕ)) {y z1 : ℕ × ℕ}
    (hy : lYSpine L r x = y) (hz1 : prevEl r (lZSpine L N r x) = z1)
    (hfind : findFaceDarts L x = f) :
    (splitNormalListSpine L r f y z1).1.Nodup ∧
      (splitNormalListSpine L r f y z1).2.Nodup ∧
      loopListSpine L (splitNormalListSpine L r f y z1).1 ∧
      loopListSpine L (splitNormalListSpine L r f y z1).2 := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hpp := pplhuljV0 L hL hgn hunL hm hf
  have hfindcanon : findFaceDarts L (lYSpine L r x) = f :=
    (aq10_memFindFaceImpFacesEq hL.1 hpp.1).trans hfind
  have hsplit_eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x)))
      = splitNormalListSpine L r f y z1 := by
    rw [← hfindcanon, ← hy, ← hz1]
  have hmem1c : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).1 ∈ ntransSpine L N r x 1 :=
    aq8w2b_fstMemRtran1 L hf
  have hmem2c : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 ∈ ntransSpine L N r x 1 :=
    sndMemRtran1 L hm.1.2.2.1 hf
  have hmem1 : (splitNormalListSpine L r f y z1).1 ∈ ntransSpine L N r x 1 := by
    rw [← hsplit_eq]; exact hmem1c
  have hmem2 : (splitNormalListSpine L r f y z1).2 ∈ ntransSpine L N r x 1 := by
    rw [← hsplit_eq]; exact hmem2c
  have hNflat : (ntransSpine L N r x 1).flatten.Nodup := aq1 L hL N r x hgn hm
  have hnd1 : (splitNormalListSpine L r f y z1).1.Nodup :=
    uniqFlattenUniq _ hNflat _ hmem1
  have hnd2 : (splitNormalListSpine L r f y z1).2.Nodup :=
    uniqFlattenUniq _ hNflat _ hmem2
  have hl1 : loopListSpine L (splitNormalListSpine L r f y z1).1 :=
    h4 N r x hgn hm _ hmem1
  have hl2 : loopListSpine L (splitNormalListSpine L r f y z1).2 :=
    h4 N r x hgn hm _ hmem2
  exact ⟨hnd1, hnd2, hl1, hl2⟩

/-! ## §2 HOL AQ12.hl:1658 `exists_contour_snd_fst` -/

/-- **HOL `exists_contour_snd_fst`**（AQ12.hl:1658-:1742）：
`u ∈ SND`、`v ∈ FST` ⇒ 存在 contour 从 `u` 到 `v`，支撑 ⊆ final 过滤后的
`replace r [SND] N ++ [FST]` 的 flatten。 -/
theorem aqs_existsContourSndFst (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (h4 : aq4Concl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (f : List (ℕ × ℕ))
    {z y z1 : ℕ × ℕ} {r1 r2 : List (ℕ × ℕ)} {u v : ℕ × ℕ}
    (hz : lZSpine L N r x = z) (hy : lYSpine L r x = y) (hz1 : prevEl r z = z1)
    (hfin1 : finalListSpine L r1) (hfin2 : finalListSpine L r2)
    (hr2 : (splitNormalListSpine L r f y z1).2 = r2)
    (hr1 : (splitNormalListSpine L r f y z1).1 = r1)
    (hfind : findFaceDarts L x = f)
    (hv : v ∈ r1) (hu : u ∈ r2) :
    ∃ s : List (ℕ × ℕ), ContourListSpine L s ∧ s ≠ [] ∧ s.head! = u ∧
      s.getLast! = v ∧ setOfListSpine s ⊆
        setOfListSpine ((replaceSpine r [r2] N ++ [r1]).filter
          (fun l => decide (finalListSpine L l))).flatten := by
  -- ① 两行的 Nodup / loopListSpine
  have hz1canon : prevEl r (lZSpine L N r x) = z1 := by rw [hz]; exact hz1
  obtain ⟨hnd1, hnd2, hl1, hl2⟩ :=
    aq12l_splitRowFacts L hL hgn h4 hm hf f hy hz1canon hfind
  have hndF : r1.Nodup := hr1 ▸ hnd1
  have hndS : r2.Nodup := hr2 ▸ hnd2
  have hloopF : loopListSpine L r1 := hr1 ▸ hl1
  have hloopS : loopListSpine L r2 := hr2 ▸ hl2
  -- ② 端点成员（W5a 四件）
  have huS : u ∈ r2 := hu
  have hyS : y ∈ r2 := aqs_yMemSplitSnd L hL hgn hm f hz hy hz1 hr2
  have hy1F : nextEl r y ∈ r1 := aqs_nextYMemSplitSnd L hL hgn hm f hz hy hz1 hr1
  have hvF : v ∈ r1 := hv
  -- ③ 两条 contour
  obtain ⟨s1, hc1, hhd1, hlast1, hsub1, hne1⟩ :=
    aqs_existsConnectedLoop (L := L) (s := r2) (x := u) (y := y) hndS hloopS huS hyS
  obtain ⟨s2, hc2, hhd2, hlast2, hsub2, hne2⟩ :=
    aqs_existsConnectedLoop (L := L) (s := r1) (x := nextEl r y) (y := v) hndF hloopF hy1F hvF
  -- ④ 拼接
  have hcat : ContourListSpine L (s1 ++ s2) := by
    refine (aqs_contourListCat hne1 hne2).mpr ⟨hc1, hc2, ?_⟩
    rw [hlast1, hhd2, ← hy]
    exact aqs_oneStepYtran L hL hgn hm hf
  refine ⟨s1 ++ s2, hcat, ?_, ?_, ?_, ?_⟩
  · exact List.ne_nil_of_mem (List.mem_append_left _ (aqs_headMem hne1))
  · rw [List.head!_append _ hne1, hhd1]
  · rw [aqs_getLastAppend, if_neg hne2, hlast2]
  · -- ⑤ 支撑子集
    have htargetS : ∀ d ∈ r2, d ∈ ((replaceSpine r [r2] N ++ [r1]).filter
        (fun l => decide (finalListSpine L l))).flatten := by
      intro d hd
      have hr2N : r2 ∈ replaceSpine r [r2] N :=
        aq12l_memReplaceSpineOfMem hm.1.2.2.1 (List.mem_singleton_self _)
      have hr2cat : r2 ∈ replaceSpine r [r2] N ++ [r1] :=
        List.mem_append.mpr (Or.inl hr2N)
      have hr2f : r2 ∈ (replaceSpine r [r2] N ++ [r1]).filter
          (fun l => decide (finalListSpine L l)) :=
        List.mem_filter.mpr ⟨hr2cat, by simpa using hfin2⟩
      exact List.mem_flatten.mpr ⟨r2, hr2f, hd⟩
    have htargetF : ∀ d ∈ r1, d ∈ ((replaceSpine r [r2] N ++ [r1]).filter
        (fun l => decide (finalListSpine L l))).flatten := by
      intro d hd
      have hr1cat : r1 ∈ replaceSpine r [r2] N ++ [r1] :=
        List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
      have hr1f : r1 ∈ (replaceSpine r [r2] N ++ [r1]).filter
          (fun l => decide (finalListSpine L l)) :=
        List.mem_filter.mpr ⟨hr1cat, by simpa using hfin1⟩
      exact List.mem_flatten.mpr ⟨r1, hr1f, hd⟩
    intro d hd
    rcases List.mem_append.mp hd with hd1 | hd2
    · exact htargetS d (hsub1 hd1)
    · exact htargetF d (hsub2 hd2)

/-! ## §3 HOL AQ12.hl:1743 `exists_contour_fst_snd` -/

/-- **HOL `exists_contour_fst_snd`**（AQ12.hl:1743-:1828）：
`u ∈ FST`、`v ∈ SND` ⇒ 存在 contour 从 `u` 到 `v`，支撑同上。 -/
theorem aqs_existsContourFstSnd (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (h4 : aq4Concl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (f : List (ℕ × ℕ))
    {z y z1 : ℕ × ℕ} {r1 r2 : List (ℕ × ℕ)} {u v : ℕ × ℕ}
    (hz : lZSpine L N r x = z) (hy : lYSpine L r x = y) (hz1 : prevEl r z = z1)
    (hfin1 : finalListSpine L r1) (hfin2 : finalListSpine L r2)
    (hr2 : (splitNormalListSpine L r f y z1).2 = r2)
    (hr1 : (splitNormalListSpine L r f y z1).1 = r1)
    (hfind : findFaceDarts L x = f)
    (hv : v ∈ r2) (hu : u ∈ r1) :
    ∃ s : List (ℕ × ℕ), ContourListSpine L s ∧ s ≠ [] ∧ s.head! = u ∧
      s.getLast! = v ∧ setOfListSpine s ⊆
        setOfListSpine ((replaceSpine r [r2] N ++ [r1]).filter
          (fun l => decide (finalListSpine L l))).flatten := by
  have hz1canon : prevEl r (lZSpine L N r x) = z1 := by rw [hz]; exact hz1
  obtain ⟨hnd1, hnd2, hl1, hl2⟩ :=
    aq12l_splitRowFacts L hL hgn h4 hm hf f hy hz1canon hfind
  have hndF : r1.Nodup := hr1 ▸ hnd1
  have hndS : r2.Nodup := hr2 ▸ hnd2
  have hloopF : loopListSpine L r1 := hr1 ▸ hl1
  have hloopS : loopListSpine L r2 := hr2 ▸ hl2
  have hzS : z ∈ r2 := aqs_zMemSplitSnd L hL hgn hm f hz hy hz1 hr2
  have hvS : v ∈ r2 := hv
  have huF : u ∈ r1 := hu
  have hz1F : z1 ∈ r1 := aqs_prevZMemSplitSnd L hL hgn hm f hz hy hz1 hr1
  obtain ⟨s1, hc1, hhd1, hlast1, hsub1, hne1⟩ :=
    aqs_existsConnectedLoop (L := L) (s := r2) (x := z) (y := v) hndS hloopS hzS hvS
  obtain ⟨s2, hc2, hhd2, hlast2, hsub2, hne2⟩ :=
    aqs_existsConnectedLoop (L := L) (s := r1) (x := u) (y := z1) hndF hloopF huF hz1F
  have hcat : ContourListSpine L (s2 ++ s1) := by
    refine (aqs_contourListCat hne2 hne1).mpr ⟨hc2, hc1, ?_⟩
    rw [hlast2, hhd1, ← hz1, ← hz]
    exact aqs_oneStepZtran L hL hgn hm hf
  refine ⟨s2 ++ s1, hcat, ?_, ?_, ?_, ?_⟩
  · exact List.ne_nil_of_mem (List.mem_append_left _ (aqs_headMem hne2))
  · rw [List.head!_append _ hne2, hhd2]
  · rw [aqs_getLastAppend, if_neg hne1, hlast1]
  · have htargetS : ∀ d ∈ r2, d ∈ ((replaceSpine r [r2] N ++ [r1]).filter
        (fun l => decide (finalListSpine L l))).flatten := by
      intro d hd
      have hr2N : r2 ∈ replaceSpine r [r2] N :=
        aq12l_memReplaceSpineOfMem hm.1.2.2.1 (List.mem_singleton_self _)
      have hr2cat : r2 ∈ replaceSpine r [r2] N ++ [r1] :=
        List.mem_append.mpr (Or.inl hr2N)
      have hr2f : r2 ∈ (replaceSpine r [r2] N ++ [r1]).filter
          (fun l => decide (finalListSpine L l)) :=
        List.mem_filter.mpr ⟨hr2cat, by simpa using hfin2⟩
      exact List.mem_flatten.mpr ⟨r2, hr2f, hd⟩
    have htargetF : ∀ d ∈ r1, d ∈ ((replaceSpine r [r2] N ++ [r1]).filter
        (fun l => decide (finalListSpine L l))).flatten := by
      intro d hd
      have hr1cat : r1 ∈ replaceSpine r [r2] N ++ [r1] :=
        List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
      have hr1f : r1 ∈ (replaceSpine r [r2] N ++ [r1]).filter
          (fun l => decide (finalListSpine L l)) :=
        List.mem_filter.mpr ⟨hr1cat, by simpa using hfin1⟩
      exact List.mem_flatten.mpr ⟨r1, hr1f, hd⟩
    intro d hd
    rcases List.mem_append.mp hd with hd2 | hd1
    · exact htargetF d (hsub2 hd2)
    · exact htargetS d (hsub1 hd1)

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aqs_existsContourSndFst
#print axioms Kepler.Text.TameSpine.aqs_existsContourFstSnd
