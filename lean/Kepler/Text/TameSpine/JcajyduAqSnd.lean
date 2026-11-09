/-
  Kepler.Text.TameSpine.JcajyduAqSnd — hsnd 批 1b（AQ 塔第 3 叶收口）：
  交错三件 + 总装 + aq3Split2FLast 无条件形。

  **面锚点约定（本文件所有 congr/成员推导统一遵守）**：
  `findFaceDarts_congr_of_mem (hn : (listOfDarts L).Nodup)
      {z d} (hd : d ∈ listOfDarts L) (hz : z ∈ findFaceDarts L d) :
      findFaceDarts L z = findFaceDarts L d`
  —— `hd` 恒为**面锚点 d 侧**（目标等式的第二个表）的 darts 成员，不是 z 侧；
  `mem_darts_of_mem_findFace` 的隐参也按 d 侧解析。每次 congr 前先对齐目标
  两端的锚点位置（三次踩坑记档）。

  件目：
  ① `inRtransSucNotRtransNewV0`（HOJODCM.hl:107）：r' = rtrans…1 中不属于 r
     的 d 必落面窗（rtransCat 分解 + A 侧 ⊆ r 三件：z∈r 免债/窗口⊆r/y∈r）；
  ② `indexfInRtransSucNotRtransNew2`（AQ1.hl:194）：同前提再加 MEM d f
     （窗口 ⊆ 面，memBetweenOfMem 直投）；
  ③ `betwnNotInRtrans`（AQ1.hl:358）：**交错定理**——d ∈ 面窗 → d ∉ r。
     窗口位置界 = `indexlBetwn` + `sizeBetwn`（§0 两行组合）+ z 的位置
     `indexfYtransSucLp`（批 1a）+ l'p 极小 `fListPowYtransNotMem`（批 1a）
     ——HOL 证词里的 PPLHULJ_v0 槽由 `pplhuljV0`（8ea034dc）填齐（债-free）；
  ④ `hsndClean`（HOL uniq_snd_split_norm AQ1.hl:413）：split.2.Nodup——
     [z]++betwn r z y++[y] Nodup（r 侧）+ betwn f y z Nodup（面侧）+
     两侧不交（③）+ append 收口；
  ⑤ `aq3Split2FLastClean`：E2 条件形三槽全干净供给 → **无条件形**。

  纪律：零 sorry/admit/native_decide/axiom；主仓树零写入（经 patch 交付）。
-/
import Kepler.Text.TameSpine.TameList17
import Kepler.Text.TameSpine.JcajyduAqTowerBase
import Kepler.Text.TameSpine.JcajyduAqTowerE2
import Kepler.Text.TameSpine.JcajyduAqZUnlock
import Kepler.Text.TameSpine.JcajyduAqZIndexf

namespace Kepler.Text.TameSpine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Kepler.Assembly (nextEl prevEl eList fList GoodList findFaceDarts nList
  listOfDarts)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nextEl_mem_of_mem faceMap_hypermapOfList)

/-! ## §0 窗口位置界与 r 侧 Nodup 辅件 -/

/-- 窗口位置界：`d ∈ betwn f y z → indexf y d f < indexf y z f`
（`indexlBetwn` + `sizeBetwn` 组合）。 -/
theorem indexfBetwnLt {α : Type*} [BEq α] [LawfulBEq α] {f : List α} {y z d : α}
    (hnd : f.Nodup) (hy : y ∈ f) (hz : z ∈ f) (hyz : y ≠ z)
    (hd : d ∈ between f y z) :
    indexf y d f < indexf y z f := by
  have hdf : d ∈ f := memBetweenOfMem hd
  have hpos := indexlBetwn hnd hy hz hd
  have hsize := sizeBetwn hnd hy hz hyz
  have hidxlt : (between f y z).idxOf d < (between f y z).length :=
    List.idxOf_lt_length_iff.mpr hd
  omega

/-- `[z] ++ betwn r z y ++ [y]` 的 Nodup（Ohcgkfu.uniq_append_betwn 的
Spine 形）：r.Nodup + 端点 ∈ r + z≠y + 端点排除（notBetwn1/2）。 -/
theorem uniqAppendBetwn {α : Type*} [BEq α] [LawfulBEq α] {r : List α} {z y : α}
    (hnd : r.Nodup) (hz : z ∈ r) (hy : y ∈ r) (hzy : z ≠ y) :
    ([z] ++ between r z y ++ [y]).Nodup := by
  have hwin : (between r z y).Nodup := uniqBetwn hnd hz hy hzy
  have hzw : ([z] ++ between r z y).Nodup := by
    rw [List.nodup_append]
    refine ⟨List.nodup_singleton z, hwin, ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton] at ha
    subst ha
    subst hab
    exact notBetwn1 hnd hy hb
  rw [List.nodup_append]
  refine ⟨hzw, List.nodup_singleton y, ?_⟩
  intro a ha b hb hab
  rw [List.mem_singleton] at hb
  subst hb
  rcases List.mem_append.mp ha with hz' | hw
  · rw [List.mem_singleton] at hz'
    exact hzy (hz'.symm.trans hab)
  · exact notBetwn2 hnd (hab ▸ hw)

/-! ## §1 r' 的新元素落面窗（HOL in_rtrans_suc_not_rtrans_new_v0 / _new2） -/

/-- **HOL `in_rtrans_suc_not_rtrans_new_v0`**（HOJODCM.hl:107）：
`d ∈ rtrans…(SUC 0) ∧ d ∉ r → d ∈ betwn f (l'y) (l'z)`——`rtransCat`
分解 A ++ T（A = [z]++betwn r z y++[y] ⊆ r 三件）。 -/
theorem inRtransSucNotRtransNewV0 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {d : ℕ × ℕ} (hd : d ∈ rtransSpine L N r x 1) (hdr : d ∉ r) :
    d ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x) := by
  obtain ⟨hr1, -⟩ := normalListUniqNonnil hm.1.2.1 hm.1.2.2.1
  rw [rtransCat L N r x hf hr1] at hd
  rcases List.mem_append.mp hd with hA | hT
  · exfalso
    apply hdr
    rcases List.mem_append.mp hA with hA1 | hy
    · rcases List.mem_append.mp hA1 with hz | hw
      · rw [List.mem_singleton] at hz
        subst hz
        exact zMemRtransClean L hL hgn hunL hm hf
      · exact memBetweenOfMem hw
    · rw [List.mem_singleton] at hy
      subst hy
      exact ytransMemRtrans L hL hgn hm hf
  · exact hT

/-- **HOL `indexf_in_rtrans_suc_not_rtrans_new2_v0`**（AQ1.hl:194）：
同前提再加 `MEM d f`（窗口 ⊆ 面）。 -/
theorem indexfInRtransSucNotRtransNew2 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {d : ℕ × ℕ} (hd : d ∈ rtransSpine L N r x 1) (hdr : d ∉ r) :
    d ∈ findFaceDarts L (lYSpine L r x) ∧
      d ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x) :=
  ⟨memBetweenOfMem
      (inRtransSucNotRtransNewV0 L hL hgn hunL hm hf hd hdr),
    inRtransSucNotRtransNewV0 L hL hgn hunL hm hf hd hdr⟩

/-! ## §2 交错定理（HOL betwn_not_in_rtrans，AQ1.hl:358） -/

/-- **HOL `betwn_not_in_rtrans`**（AQ1.hl:358）：`d ∈ betwn f (l'y) (l'z) →
d ∉ r`。证：窗口位置界给 k := indexf y d f < indexf y z f = l'p + 1
（批 1a indexfYtransSucLp）；k ≥ 1（d ≠ y）；d = f^k y（indexfN +
批 1a fListPowEqNextElPow）→ 批 1a `fListPowYtransNotMem` 在 j = k-1 处
排除。HOL 证词里的 PPLHULJ_v0 槽由 pplhuljV0（8ea034dc）填齐位置。 -/
theorem betwnNotInRtrans (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {d : ℕ × ℕ}
    (hd : d ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)) :
    d ∉ r := by
  have hyne : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hyd : lYSpine L r x ∈ listOfDarts L := memYtransListOfDarts L hL hgn hm hf
  have hyf : lYSpine L r x ∈ findFaceDarts L (lYSpine L r x) :=
    (dart_in_face L (lYSpine L r x)).mpr hyd
  have hzf : lZSpine L N r x ∈ findFaceDarts L (lYSpine L r x) :=
    zMemFindFaceDarts L hL hgn hunL hm hf
  have hfnd : (findFaceDarts L (lYSpine L r x)).Nodup :=
    findFaceDarts_nodup hL.1 (lYSpine L r x)
  have hdf : d ∈ findFaceDarts L (lYSpine L r x) := memBetweenOfMem hd
  have hlt := indexfBetwnLt hfnd hyf hzf hyne hd
  have hzpos := indexfYtransSucLp L hL hgn hunL hm hf
  rw [hzpos] at hlt
  have hdy : d ≠ lYSpine L r x := by
    intro hcon
    subst hcon
    exact notBetwn1 hfnd hzf hd
  have hk1 : 1 ≤ indexf (lYSpine L r x) d (findFaceDarts L (lYSpine L r x)) := by
    rcases Nat.eq_zero_or_pos
      (indexf (lYSpine L r x) d (findFaceDarts L (lYSpine L r x))) with h0 | h1
    · exfalso
      exact hdy (indexfZeroEq (x := lYSpine L r x) (y := d)
        (s := findFaceDarts L (lYSpine L r x)) hyf hdf h0).symm
    · exact h1
  have hdpow : d = (fList L)^[indexf (lYSpine L r x) d (findFaceDarts L (lYSpine L r x))]
      (lYSpine L r x) :=
    (indexfN hyf hdf hfnd).symm.trans
      (fListPowEqNextElPow L hL (lYSpine L r x) hyf _).symm
  intro hmem
  have hj : indexf (lYSpine L r x) d (findFaceDarts L (lYSpine L r x)) - 1
      < lPSpine L N r x := by omega
  have hnot := fListPowYtransNotMem L hL hm
    (indexf (lYSpine L r x) d (findFaceDarts L (lYSpine L r x)) - 1) hj
  apply hnot
  rw [show indexf (lYSpine L r x) d (findFaceDarts L (lYSpine L r x)) - 1 + 1
      = indexf (lYSpine L r x) d (findFaceDarts L (lYSpine L r x)) from by omega,
    ← hdpow]
  exact hmem

/-! ## §3 总装：split.2 的 Nodup（HOL uniq_snd_split_norm，AQ1.hl:413） -/

/-- **HOL `uniq_snd_split_norm`**（AQ1.hl:413）：
`(SND (split_normal_list L r (find_face L (l'y)) (l'y) (prev_el r (l'z)))).Nodup`
——A = [z]++betwn r z y++[y]（§0 uniqAppendBetwn）+ T = betwn f y z
（uniqBetwn 面侧）+ 两侧不交（§2 交错定理）→ append Nodup。 -/
theorem hsndClean (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (prevEl r (lZSpine L N r x))).2.Nodup := by
  obtain ⟨hr1, -⟩ := normalListUniqNonnil hm.1.2.1 hm.1.2.2.1
  have hw : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hr1 _
  have hS2 : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2
      = ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
          ++ [lYSpine L r x]) ++ between (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (lZSpine L N r x) := by
    simp only [splitNormalListSpine]
    rw [hw]
  rw [hS2]
  have hyne : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hA : ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
      ++ [lYSpine L r x]).Nodup :=
    uniqAppendBetwn hr1 (zMemRtransClean L hL hgn hunL hm hf)
      (ytransMemRtrans L hL hgn hm hf) (Ne.symm hyne)
  have hyd : lYSpine L r x ∈ listOfDarts L := memYtransListOfDarts L hL hgn hm hf
  have hT : (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)).Nodup :=
    uniqBetwn (r := findFaceDarts L (lYSpine L r x))
      (z := lYSpine L r x) (y := lZSpine L N r x)
      (findFaceDarts_nodup hL.1 (lYSpine L r x))
      ((dart_in_face L (lYSpine L r x)).mpr hyd)
      (zMemFindFaceDarts L hL hgn hunL hm hf) hyne
  rw [List.nodup_append]
  refine ⟨hA, hT, ?_⟩
  intro a ha b hb hab
  have har : a ∈ r := by
    rcases List.mem_append.mp ha with hA1 | hy
    · rcases List.mem_append.mp hA1 with hz | hw'
      · rw [List.mem_singleton] at hz
        subst hz
        exact zMemRtransClean L hL hgn hunL hm hf
      · exact memBetweenOfMem hw'
    · rw [List.mem_singleton] at hy
      subst hy
      exact ytransMemRtrans L hL hgn hm hf
  have hbr : b ∉ r := betwnNotInRtrans L hL hgn hunL hm hf hb
  exact hbr (hab ▸ har)

/-! ## §4 aq3Split2FLast 收口（三槽全干净供给 → 无条件形） -/

/-- **aq3Split2FLast 无条件形**（E2 条件形 + 三槽：hyneSupply /
zMemFindFaceDarts / hsndClean）——AQ 塔第 3 叶的 split.2 支正式落地。 -/
theorem aq3Split2FLastClean (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    fLastSpine L (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 :=
  aq3Split2FLast L hL hgn hm hf
    (hyneSupply L hL hgn hunL hm hf)
    (zMemFindFaceDarts L hL hgn hunL hm hf)
    (hsndClean L hL hgn hunL hm hf)

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三 ⊆ [propext, Classical.choice,
Quot.sound]，零 sorryAx——本批全部件零消费 TameList16:1095 债链。） -/
#print axioms Kepler.Text.TameSpine.indexfBetwnLt
#print axioms Kepler.Text.TameSpine.uniqAppendBetwn
#print axioms Kepler.Text.TameSpine.inRtransSucNotRtransNewV0
#print axioms Kepler.Text.TameSpine.indexfInRtransSucNotRtransNew2
#print axioms Kepler.Text.TameSpine.betwnNotInRtrans
#print axioms Kepler.Text.TameSpine.hsndClean
#print axioms Kepler.Text.TameSpine.aq3Split2FLastClean
