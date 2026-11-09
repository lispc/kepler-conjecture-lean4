/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12P — AQ12 叶 W8a-i（decl 51 前置）。

  任务：decl 51 `exists_contour_not_snd_fst`（HOL AQ12.hl:2342-:2487，146 行）的
  **前置缺口**：`lp = LAST p`（y ∈ p）落在 **FST split 行** `r1 = split.1`。
  W8a-ii（12Q）的 contour 装配需要本件 + `h4 : aq4Concl`（FST 行 loopListSpine）。

  ┌─ 拆分与依赖（按编排者 2026-11-10 批准）──────────────────────────
  │ W8a-i（本文件，估 150–220，≤300）：
  │   ① `aq12p_betwnSubF1`：`between r y z ⊆ f1`（f1 = split.1 的 f1 段）；
  │   ② `aq12p_lastPartsMemFstSplit`：`lp ∈ split.1`。
  │ W8a-ii（12Q，110–150）：decl 51 装配（`h4` 槽 + 两条 contour + cat + 支撑）。
  │ 本文件**不吃 `h4`**（纯 parts/between 层）；`h4` 在 W8a-ii 吃
  │ （DIFFERS 记账：W5b/W6b/W8a-ii 吃，W7/W8a-i 不吃）。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线（比 HOL 短：HOL 用零命中 `case_hd_betwn_last`，82 行，不补）──
  │ ① `lp ∈ between r y z`：`betwnCases` 四支 + 三件排除
  │    （`aq8w1_lastPartsYNotY` / `_NotZ` / `aqs_lastPartsYNotCat`）；
  │ ② `between r y z ⊆ f1`：反向包含走计数——
  │    `aq1f_f1SubBetwn` 给 f1 ⊆ between；`aq12p_betwnF1LengthEq` 给
  │    |f1| = |between|（`sizeBetwn` + `nextElIndexf` + `indexfAddSum` +
  │    私件 `aq12p_indexfY1Z1`，后者是 Leaf1F private 的同证重推）；
  │    Nodup + 同长 + 包含 ⇒ 反向包含（`toFinset_card_*` + `card_le_card`）。
  │ ③ split.1 展开（`split1Unfold`）⇒ lp ∈ f1 段 ⇒ lp ∈ split.1。
  └────────────────────────────────────────────────────────────────

  纪律：零 sorry/admit/native_decide/axiom 声明；既有文件零触碰；主仓
  tracked 零改动（本文件经 patch 交付）。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12O
import Kepler.Text.TameSpine.JcajyduAqLeaf1
import Kepler.Text.TameSpine.JcajyduAqLeaf1F
import Kepler.Text.TameSpine.JcajyduAqSplit1F

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl nextEl_mem_of_mem prevEl_mem_of_mem)

/-! ## §0 私件：`indexf (nextEl r y) z1 r = indexf y z1 r - 1`

（Leaf1F 的 `aq1f_indexfY1Z1` 是 private，本文件同证重推。） -/
private theorem aq12p_indexfY1Z1 {r : List (ℕ × ℕ)} {y z z1 : ℕ × ℕ}
    (hrnd : r.Nodup) (hy : y ∈ r) (hz : z ∈ r) (hne : y ≠ z)
    (hz1r : z1 ∈ r) (hnext : nextEl r z1 = z) (hy1z : nextEl r y ≠ z)
    (hra : nextEl r y ≠ z1) :
    indexf (nextEl r y) z1 r = indexf y z1 r - 1 := by
  have hy1r : nextEl r y ∈ r := nextEl_mem_of_mem hy
  have hlen : 1 < r.length := sizelGt1 hy hz hne
  have hi1 : indexf y (nextEl r y) r = 1 := nextElIndexf hy hy1r hrnd rfl hlen
  have hneLast : indexf (nextEl r y) z1 r ≠ r.length - 1 := by
    intro h
    have hanti := indexfAntisym hy1r hz1r hra
    have h1 : indexf z1 (nextEl r y) r = 1 := by omega
    have h2 : nextEl r z1 = nextEl r y := indexfOne hz1r hy1r hrnd h1
    exact hy1z (by rw [← h2]; exact hnext)
  have hsum : indexf y (nextEl r y) r + indexf (nextEl r y) z1 r
      = indexf y z1 r :=
    indexfAddSum hy hy1r hz1r (by
      have := indexfLtSizel hy1r hz1r
      omega)
  omega

/-! ## §1 私件：Nodup + 包含 + 等长 ⇒ 反向包含（Finset 计数） -/

private theorem aq12p_lengthLeOfSubset {α : Type} [DecidableEq α] {l1 l2 : List α}
    (h1 : l1.Nodup) (hsub : ∀ a ∈ l1, a ∈ l2) : l1.length ≤ l2.length := by
  have hsub' : l1.toFinset ⊆ l2.toFinset := by
    intro a ha
    rw [List.mem_toFinset] at ha ⊢
    exact hsub a ha
  calc l1.length = l1.toFinset.card := (List.toFinset_card_of_nodup h1).symm
    _ ≤ l2.toFinset.card := Finset.card_le_card hsub'
    _ ≤ l2.length := List.toFinset_card_le l2

private theorem aq12p_subsetOfNodupSubsetOfLength {α : Type} [DecidableEq α]
    {l1 l2 : List α} (h1 : l1.Nodup) (hsub : ∀ a ∈ l1, a ∈ l2)
    (hlen : l1.length = l2.length) : ∀ a ∈ l2, a ∈ l1 := by
  intro a ha2
  by_contra ha1
  have hnd : (a :: l1).Nodup := List.nodup_cons.mpr ⟨ha1, h1⟩
  have hsub' : ∀ b ∈ (a :: l1), b ∈ l2 := by
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact ha2
    · exact hsub b hb'
  have hle := aq12p_lengthLeOfSubset hnd hsub'
  rw [List.length_cons] at hle
  omega

/-! ## §2 私件：f1 的 Nodup 与等长 -/

private theorem aq12p_f1Nodup {r : List (ℕ × ℕ)} {y z1 : ℕ × ℕ}
    (hrnd : r.Nodup) (hy : y ∈ r) (hz1r : z1 ∈ r) (hra : nextEl r y ≠ z1) :
    (([nextEl r y] ++ between r (nextEl r y) z1) ++ [z1]).Nodup := by
  have hy1r : nextEl r y ∈ r := nextEl_mem_of_mem hy
  have hB : (between r (nextEl r y) z1).Nodup := uniqBetwn hrnd hy1r hz1r hra
  have hy1B : nextEl r y ∉ between r (nextEl r y) z1 := notBetwn1 hrnd hz1r
  have hz1B : z1 ∉ between r (nextEl r y) z1 := notBetwn2 hrnd
  have hAB : ([nextEl r y] ++ between r (nextEl r y) z1).Nodup := by
    rw [List.nodup_append]
    refine ⟨by simp, hB, ?_⟩
    intro x hx y hy
    rw [List.mem_singleton] at hx
    subst hx
    exact fun h => hy1B (h ▸ hy)
  rw [List.nodup_append]
  refine ⟨hAB, by simp, ?_⟩
  intro x hx y hy
  rw [List.mem_singleton] at hy
  subst hy
  rcases List.mem_append.mp hx with h | h
  · rw [List.mem_singleton] at h
    intro hcon
    exact hra (h.symm.trans hcon)
  · intro hcon
    exact hz1B (hcon ▸ h)

/-- `|f1| = |between r y z|`（`f1 = [y1] ++ between r y1 z1 ++ [z1]`）。 -/
private theorem aq12p_betwnF1LengthEq {r : List (ℕ × ℕ)} {y z z1 : ℕ × ℕ}
    (hrnd : r.Nodup) (hy : y ∈ r) (hz : z ∈ r) (hne : y ≠ z)
    (hz1r : z1 ∈ r) (hnext : nextEl r z1 = z) (hy1z : nextEl r y ≠ z)
    (hra : nextEl r y ≠ z1) :
    (([nextEl r y] ++ between r (nextEl r y) z1) ++ [z1]).length
      = (between r y z).length := by
  have hy1r : nextEl r y ∈ r := nextEl_mem_of_mem hy
  have hlen : 1 < r.length := sizelGt1 hy hz hne
  have hz1mem : z1 ∈ between r y z :=
    aq1f_z1MemBetwn hrnd hy hz hne hz1r hnext hy1z
  have hpos : 0 < indexf y z1 r := (indexfBetwn hne hrnd hy hz hz1mem).1
  have hz1z : indexf z1 z r = 1 := nextElIndexf hz1r hz hrnd hnext hlen
  have hadd : indexf y z1 r + indexf z1 z r = indexf y z r :=
    indexfAddBetwn hne hrnd hy hz1mem hz
  have hidx : indexf (nextEl r y) z1 r = indexf y z1 r - 1 :=
    aq12p_indexfY1Z1 hrnd hy hz hne hz1r hnext hy1z hra
  have hszZ : (between r y z).length = indexf y z r - 1 := sizeBetwn hrnd hy hz hne
  have hszW : (between r (nextEl r y) z1).length = indexf (nextEl r y) z1 r - 1 :=
    sizeBetwn hrnd hy1r hz1r hra
  have hy1pos : 0 < indexf (nextEl r y) z1 r :=
    Nat.pos_of_ne_zero (fun h => hra (indexfZeroEq hy1r hz1r h))
  have hone : ([nextEl r y] ++ between r (nextEl r y) z1).length
      = (between r (nextEl r y) z1).length + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hgoal : (([nextEl r y] ++ between r (nextEl r y) z1) ++ [z1]).length
      = (between r (nextEl r y) z1).length + 2 := by
    simp only [List.length_append, List.length_singleton, hone]
  rw [hgoal, hszW, hidx, hszZ]
  have hadd' : indexf y z1 r + 1 = indexf y z r := by simpa [hz1z] using hadd
  omega

/-! ## §3 `between r y z ⊆ f1`（`f1 = [nextEl r y] ++ between r (nextEl r y) z1 ++ [z1]`） -/

/-- `between r y z ⊆ f1`（反向包含：f1 ⊆ between + Nodup + 等长 + Finset 计数）。 -/
theorem aq12p_betwnSubF1 {r : List (ℕ × ℕ)} {y z z1 : ℕ × ℕ}
    (hrnd : r.Nodup) (hy : y ∈ r) (hz : z ∈ r) (hne : y ≠ z)
    (hz1r : z1 ∈ r) (hnext : nextEl r z1 = z) (hy1z : nextEl r y ≠ z)
    (hra : nextEl r y ≠ z1) :
    ∀ d ∈ between r y z, d ∈ ([nextEl r y] ++ between r (nextEl r y) z1) ++ [z1] := by
  have hsub : ∀ d ∈ ([nextEl r y] ++ between r (nextEl r y) z1) ++ [z1],
      d ∈ between r y z :=
    aq1f_f1SubBetwn hrnd hy hz hne hz1r hnext hy1z hra
  have hnd := aq12p_f1Nodup hrnd hy hz1r hra
  have hlen := aq12p_betwnF1LengthEq hrnd hy hz hne hz1r hnext hy1z hra
  exact aq12p_subsetOfNodupSubsetOfLength hnd hsub hlen

/-! ## §4 `lp ∈ FST split` -/

/-- **W8a 前置**：`lp = LAST p`（p 为含 y 的 part）落在 FST split 行。 -/
theorem aq12p_lastPartsMemFstSplit (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r)
    (hyp : lYSpine L r x ∈ p) {lp : ℕ × ℕ} (hlast : p.getLast! = lp)
    (f : List (ℕ × ℕ)) {z y z1 : ℕ × ℕ} {r1 : List (ℕ × ℕ)}
    (hz : lZSpine L N r x = z) (hy : lYSpine L r x = y) (hz1 : prevEl r z = z1)
    (hr1 : (splitNormalListSpine L r f y z1).1 = r1)
    (hfind : findFaceDarts L x = f) :
    lp ∈ r1 := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hyz : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hz1r : prevEl r (lZSpine L N r x) ∈ r := prevEl_mem_of_mem hzr
  have hnextz1 : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hrnd _
  have hy1z : nextEl r (lYSpine L r x) ≠ lZSpine L N r x :=
    aq1_nextElYNeZ L hL hgn hunL hm hf
  have hra : nextEl r (lYSpine L r x) ≠ prevEl r (lZSpine L N r x) :=
    aq1_nextElYNePrevElZ L hL hgn hunL hm hf
  -- lp ∈ r
  have hpne : p ≠ [] := List.ne_nil_of_mem hyp
  have hlpMem : lp ∈ p := by
    rw [← hlast, getLast!EqGetLast hpne]
    exact List.getLast_mem hpne
  have hlpR : lp ∈ r :=
    memPartsImp L hrnd (List.ne_nil_of_mem hm.1.2.2.2.1) hp lp hlpMem
  -- lp ∈ between r y z（四支排除）
  rcases betwnCases hyz hrnd hyr hlpR hzr with heq | heq | hb | hb
  · exact absurd (hlast.trans heq)
      (aq8w1_lastPartsYNotY L hL hgn hm hf hp hyp)
  · exact absurd (hlast.trans heq)
      (aq8w1_lastPartsYNotZ L hL hgn hm hf hp hyp)
  · -- 主支：lp ∈ between r y z
    have hmem := aq12p_betwnSubF1 hrnd hyr hzr hyz hz1r hnextz1 hy1z hra lp hb
    have hmem' : lp ∈ [nextEl r (lYSpine L r x)]
        ++ between r (nextEl r (lYSpine L r x)) (prevEl r (lZSpine L N r x))
        ++ [prevEl r (lZSpine L N r x)] := by
      simpa only [List.append_assoc] using hmem
    have hcanon : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).1
        = ((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
              (lZSpine L N r x)).map (ndSpine L)).flatten.reverse
          ++ ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
              (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]) := by
      rw [split1Unfold L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (prevEl r (lZSpine L N r x)), hnextz1]
    have hmemCanon : lp ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (prevEl r (lZSpine L N r x))).1 := by
      rw [hcanon]
      exact List.mem_append.mpr (Or.inr hmem')
    -- canonical → f-split → r1
    have hz1c : prevEl r (lZSpine L N r x) = z1 := by rw [hz]; exact hz1
    have hfindcanon : findFaceDarts L (lYSpine L r x) = f :=
      (aq10_memFindFaceImpFacesEq hL.1 (pplhuljV0 L hL hgn hunL hm hf).1).trans hfind
    have hsplit_eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (prevEl r (lZSpine L N r x)))
        = splitNormalListSpine L r f y z1 := by
      rw [← hfindcanon, ← hy, ← hz1c]
    have hmemF : lp ∈ (splitNormalListSpine L r f y z1).1 := by
      rw [← hsplit_eq]
      exact hmemCanon
    rwa [hr1] at hmemF
  · exact absurd (by
        rw [hlast]
        exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hb))))
      (aqs_lastPartsYNotCat L hL hgn hm hf hp hyp)

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq12p_betwnSubF1
#print axioms Kepler.Text.TameSpine.aq12p_lastPartsMemFstSplit
