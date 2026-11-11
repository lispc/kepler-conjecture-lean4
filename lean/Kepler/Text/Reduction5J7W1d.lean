/-
  Kepler.Text.Reduction5J7W1d — J5-7 W1 收官段（1/2）：
  · `uniqFstFindFace` —— 塔件 #1（HOL betwn_core0_z_y.hl:46-83）：
    `(find_face x).map FST` 无重。证 = 终态 `transform_count` 处 final
    （`finalListTransformCount`）+ 该态 `core = map FST`（`coreFinal`）+
    `quotientAllUniq` 给 core 无重 + `finalListRot` 把 `map FST f` 旋到该态。
  · `indexfZLtSizelYtran` —— **B5 严格形**（W1-2 主件）：
    `indexf zi yi f < (parts L r).toFinset.card`。在 J7W1c 非严格计数基础上
    补第二排除（`yi` 的 part `py ∉ T`，用 `indexfFArcPow` 的指数唯一性）：
    支 1 `pz ≠ py` 纯 Finset 基数（`n-1 ≤ |P|-2`）；支 2 `pz = py` 用
    `partsFst` + 塔件 #1 的 FST-单射 + `indexfRefl` 得 `n = 0`，撞 `n > 0`。
    **无需 QCDVKEA/indexfAddLeft 算术**。
  · W1-3 `indexf3_final_lemmas` 见 J7W1e（本件绿后做）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction5J7W1c
import Kepler.Text.Reduction5J5Termination
import Kepler.Text.TameSpine.Reduction3J5CoreFinal
import Kepler.Text.MoreLemma2PartsFst
import Kepler.Text.Reduction5McCore
import Kepler.Text.TameSpine.Reduction3J5PowerCore
import Kepler.Text.TameSpine.JcajyduRed2Tav2

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts eList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)

/-- f-弧 `indexf` 迭代 = 指数（与 J7W1c 私有件同构；private 不跨文件）。 -/
private theorem indexfFArcPow {f : List Dart} {zi : Dart} (hzi : zi ∈ f)
    (hnd : f.Nodup) {k : ℕ} (hk : k < f.length) :
    Kepler.Text.Reduction5.indexf zi ((nextEl f)^[k] zi) f = k := by
  have hdi : (nextEl f)^[k] zi ∈ f :=
    Kepler.Text.TameSpine.memPowerNextEl hzi k
  have hp : (@nextEl Dart instBEqOfDecidableEq f)^[k] zi = (nextEl f)^[k] zi :=
    (Kepler.Text.Reduction5.iterateInstEq f zi k).symm
  exact Kepler.Text.MoreLemma2Island1.nextElnIndexf hzi hdi hnd hp hk

/-- **塔件 #1（HOL `uniq_fst_find_face`，betwn_core0_z_y.hl:46-83）**：
`good_list ∧ good_list_nodes ∧ is_restricted ∧ marked_list ⇒
uniq (MAP FST (find_face L x))`。 -/
theorem uniqFstFindFace (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) :
    (findFaceDarts L x).map (fun d => d.1) |>.Nodup := by
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' i' =>
      Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' i'
  -- 终态 k：final + marked
  set k := transformCount L N r x with hk
  have hfinK : finalList L (rtrans L N r x k) :=
    Kepler.Text.Reduction5.finalListTransformCount L hL hgn haq hm (t := k) rfl
  have hmK : Kepler.Text.ChainLists.markedList L hL
      (ntrans L N r x k) (rtrans L N r x k) x := haq hgn N r x hm k
  -- 终态 core 无重
  have hcoreK : (core L (rtrans L N r x k)).Nodup := by
    have hq := Kepler.Text.MoreLemma2a23.quotientAllUniq L hL hmK
    refine hq (core L (rtrans L N r x k)) ?_
    rw [Kepler.Text.Reduction5.quotientList]
    exact List.mem_map.mpr
      ⟨Kepler.Text.Reduction5.parts L (rtrans L N r x k),
        List.mem_map.mpr ⟨rtrans L N r x k, hmK.2.2.1, rfl⟩, rfl⟩
  -- core = map FST（final）
  have hcoreFinal : core L (rtrans L N r x k)
      = (rtrans L N r x k).map (fun d => d.1) :=
    Kepler.Text.TameSpine.coreFinal L hL hmK hfinK
  have hmapK : ((rtrans L N r x k).map (fun d => d.1)).Nodup := by
    rw [← hcoreFinal]
    exact hcoreK
  have hrndK : (rtrans L N r x k).Nodup :=
    (List.nodup_flatten.mp hmK.2.1.1).1 (rtrans L N r x k) hmK.2.2.1
  have hxrK : x ∈ rtrans L N r x k := hmK.2.2.2.1
  have hxd : x ∈ listOfDarts L := Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
  obtain ⟨n, hn⟩ := Kepler.Text.Reduction5.finalListRot hL hfinK hxrK hrndK hxd
  -- map FST f = rotate (map FST rk)
  have hrot : (findFaceDarts L x).map (fun d => d.1)
      = ((rtrans L N r x k).map (fun d => d.1)).rotate n := by
    rw [← hn, List.map_rotate]
  rw [hrot]
  exact List.nodup_rotate.mpr hmapK

/-- **B5 严格形（W1-2 主件）**：`indexf zi yi f < (parts L r).toFinset.card`。
在非严格计数（J7W1c）上补第二排除 `py ∉ T`；支 1 纯基数，支 2 用塔件 #1
的 FST-单射把 `pz = py` 化成 `zi = yi` ⇒ `n = 0` 撞 `n > 0`。 -/
theorem indexfZLtSizelYtran (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {i : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf2 : ¬ finalList L (rtrans L N r x (i + 1)))
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) :
    indexf (ztrans L N r x i) (ytrans L N r x (i + 1)) f
      < (parts L r).toFinset.card := by
  set zi := ztrans L N r x i with hzi
  set yi := ytrans L N r x (i + 1) with hyi
  set n := indexf zi yi f with hn
  show n < (parts L r).toFinset.card
  have hziF : zi ∈ f := by
    have h := Kepler.Text.TameSpine.ztranMeFChain L hL hgn haq hm i
    rwa [hfind] at h
  have hyiF : yi ∈ f := Kepler.Text.MoreLemma2a23.ytranMeF L hL hm hfind.symm (i + 1)
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
  have hnlt : n < f.length := indexfLtSizel hziF hyiF
  have hunL : ∀ l ∈ L, l.Nodup :=
    (Kepler.Text.TameSpine.simpleHypermapUniq L hL hgn).mp hm.1.simple
  have hnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- n = 0：P 非空即可（zi ∈ r）
    have hziR : zi ∈ r :=
      pnxvwfs2 L hL hgn haq i (Kepler.Text.Reduction5.finalListInduct i hf2) hm
    obtain ⟨pz, hpz, -⟩ := Kepler.Text.MoreLemma2Naming.partsMemExists L hnd hziR
    have hPpos : 0 < (parts L r).toFinset.card :=
      Finset.card_pos.mpr ⟨pz, List.mem_toFinset.mpr hpz⟩
    omega
  · -- n > 0：像集 T + 双排除
    set φ : ℕ → List Dart := fun k => [(nextEl f)^[k + 1] zi] with hφ
    have hmem : ∀ k ∈ Finset.range (n - 1), φ k ∈ (parts L r).toFinset := by
      intro k hk
      have hk' : k < n - 1 := Finset.mem_range.mp hk
      exact List.mem_toFinset.mpr
        (singletonPartOfFArc L hL hgn haq hm hf2 hfind hw
          (k := k + 1) (by show 0 < k + 1; omega) (by show k + 1 < n; omega))
    have hinj : ∀ a ∈ Finset.range (n - 1), ∀ b ∈ Finset.range (n - 1),
        φ a = φ b → a = b := by
      intro a ha b hb heq
      have ha' : a < n - 1 := Finset.mem_range.mp ha
      have hb' : b < n - 1 := Finset.mem_range.mp hb
      have hpa : (nextEl f)^[a + 1] zi = (nextEl f)^[b + 1] zi :=
        List.singleton_inj.mp heq
      have hia : indexf zi ((nextEl f)^[a + 1] zi) f = a + 1 :=
        indexfFArcPow hziF hfnd (by show a + 1 < f.length; omega)
      have hib : indexf zi ((nextEl f)^[b + 1] zi) f = b + 1 :=
        indexfFArcPow hziF hfnd (by show b + 1 < f.length; omega)
      rw [hpa] at hia
      omega
    have hcard : ((Finset.range (n - 1)).image φ).card = n - 1 := by
      rw [Finset.card_image_of_injOn hinj]
      simp
    -- 两个被排除的 part
    have hziR : zi ∈ r :=
      pnxvwfs2 L hL hgn haq i (Kepler.Text.Reduction5.finalListInduct i hf2) hm
    have hyiR : yi ∈ r := pnxvwfs1 L hL hgn haq (i + 1) hf2 hm
    obtain ⟨pz, hpz, hzipz⟩ := Kepler.Text.MoreLemma2Naming.partsMemExists L hnd hziR
    obtain ⟨py, hpy, hyipy⟩ := Kepler.Text.MoreLemma2Naming.partsMemExists L hnd hyiR
    have hpzM : pz ∈ (parts L r).toFinset := List.mem_toFinset.mpr hpz
    have hpyM : py ∈ (parts L r).toFinset := List.mem_toFinset.mpr hpy
    have hpzT : pz ∉ (Finset.range (n - 1)).image φ := by
      intro hmem'
      obtain ⟨k, hk, hkφ⟩ := Finset.mem_image.mp hmem'
      have hk' : k < n - 1 := Finset.mem_range.mp hk
      have hziIn : zi ∈ φ k := by
        rw [hkφ]
        exact hzipz
      have hzid : zi = (nextEl f)^[k + 1] zi := List.mem_singleton.mp hziIn
      have hidx : indexf zi ((nextEl f)^[k + 1] zi) f = k + 1 :=
        indexfFArcPow hziF hfnd (by show k + 1 < f.length; omega)
      have hsame : indexf zi zi f = indexf zi ((nextEl f)^[k + 1] zi) f := by
        rw [← hzid]
      have h0 : indexf zi zi f = 0 := Kepler.Text.Reduction4.indexfRefl hziF
      rw [h0] at hsame
      omega
    have hpyT : py ∉ (Finset.range (n - 1)).image φ := by
      intro hmem'
      obtain ⟨k, hk, hkφ⟩ := Finset.mem_image.mp hmem'
      have hk' : k < n - 1 := Finset.mem_range.mp hk
      have hyiIn : yi ∈ φ k := by
        rw [hkφ]
        exact hyipy
      have hyid : yi = (nextEl f)^[k + 1] zi := List.mem_singleton.mp hyiIn
      have hidx : indexf zi ((nextEl f)^[k + 1] zi) f = k + 1 :=
        indexfFArcPow hziF hfnd (by show k + 1 < f.length; omega)
      have hsame : indexf zi yi f = indexf zi ((nextEl f)^[k + 1] zi) f := by
        rw [← hyid]
      have hval : n = k + 1 := by
        rw [hn, hsame, hidx]
      omega
    by_cases hEq : pz = py
    · -- 支 2：pz = py ⇒ FST zi = FST yi ⇒ zi = yi ⇒ n = 0，撞 n > 0
      have hfst : zi.1 = yi.1 := by
        have h1 : zi.1 = pz.head!.1 :=
          Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hpz hzipz
        have h2 : yi.1 = py.head!.1 :=
          Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hpy hyipy
        rw [h1, h2, hEq]
      have huniqFst : (f.map (fun d => d.1)).Nodup := by
        rw [← hfind]
        exact uniqFstFindFace L hL hgn hres hm
      have hinjFst : ∀ a ∈ f, ∀ b ∈ f, a.1 = b.1 → a = b :=
        (List.nodup_map_iff_inj_on hfnd).mp huniqFst
      have hzid : zi = yi := hinjFst zi hziF yi hyiF hfst
      have hzero : indexf zi yi f = 0 := by
        rw [hzid]
        exact Kepler.Text.Reduction4.indexfRefl hyiF
      omega
    · -- 支 1：T ⊆ P \ {pz, py} ⇒ n-1 ≤ |P|-2 ⇒ n < |P|
      have hsub : (Finset.range (n - 1)).image φ
          ⊆ ((parts L r).toFinset.erase pz).erase py := by
        intro q hq
        have hqP : q ∈ (parts L r).toFinset := by
          obtain ⟨k, hk, hkφ⟩ := Finset.mem_image.mp hq
          rw [← hkφ]
          exact hmem k hk
        have hq_ne_pz : q ≠ pz := by
          intro hqp
          exact hpzT (hqp ▸ hq)
        have hq_ne_py : q ≠ py := by
          intro hqp
          exact hpyT (hqp ▸ hq)
        exact Finset.mem_erase.mpr
          ⟨hq_ne_py, Finset.mem_erase.mpr ⟨hq_ne_pz, hqP⟩⟩
      have hpyErase : py ∈ (parts L r).toFinset.erase pz :=
        Finset.mem_erase.mpr ⟨fun h => hEq h.symm, hpyM⟩
      have hcle := Finset.card_le_card hsub
      rw [hcard, Finset.card_erase_of_mem hpyErase,
        Finset.card_erase_of_mem hpzM] at hcle
      -- P ≥ 2（pz, py 两个相异成员）
      have hP2 : 2 ≤ (parts L r).toFinset.card := by
        have hsub2 : ({pz, py} : Finset (List Dart)) ⊆ (parts L r).toFinset := by
          intro q hq
          rcases Finset.mem_insert.mp hq with rfl | hq
          · exact hpzM
          · rw [Finset.mem_singleton.mp hq]
            exact hpyM
        have hc2 := Finset.card_le_card hsub2
        have hpair : ({pz, py} : Finset (List Dart)).card = 2 := by
          rw [Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact hEq),
            Finset.card_singleton]
        omega
      omega

/-- **W1-3：HOL `indexf3_final_lemmas`**（more_lemma2.hl:1758-1800）链形：
`SUC i < k ⇒ indexf (FST zi) (FST yi) (core L r) = indexf zi yi f`
（zi = ztrans i、yi = ytrans (SUC i)、f = find_face L x）。
证 = `nextPowerCoreYtran`（幂对齐）+ `betwnZtranYtransSucConstChain` +
`indexfN`（`(nextEl f)^[n] zi = yi`）+ `nextElnIndexf`（`n < |core|` 由 B5 严格形
+ `coreLengthEqParts` + `uniqParts` 供）。 -/
theorem indexf3FinalLemmas (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hk : transformCount L N r x = k) {i : ℕ} (hi : i + 1 < k) :
    indexf (ztrans L N r x i).1 (ytrans L N r x (i + 1)).1 (core L r)
      = indexf (ztrans L N r x i) (ytrans L N r x (i + 1)) (findFaceDarts L x) := by
  have hk0 : 0 < k := by omega
  -- finality
  have hf0 : ¬ finalList L (rtrans L N r x 0) :=
    Kepler.Text.Reduction4.transformCount_not 0 (by rw [hk]; omega)
  have hf : ¬ finalList L r := by
    rwa [Kepler.Text.Reduction5.rtrans_zero] at hf0
  have hf2 : ¬ finalList L (rtrans L N r x (i + 1)) :=
    Kepler.Text.Reduction4.transformCount_not (i + 1) (by rw [hk]; omega)
  have hfI : ¬ finalList L (rtrans L N r x i) :=
    Kepler.Text.Reduction5.finalListInduct i hf2
  -- memberships
  have hziR : ztrans L N r x i ∈ r := pnxvwfs2 L hL hgn haq i hfI hm
  have hyiR : ytrans L N r x (i + 1) ∈ r := pnxvwfs1 L hL hgn haq (i + 1) hf2 hm
  have hziCore : (ztrans L N r x i).1 ∈ core L r :=
    Kepler.Text.Reduction5.memCore (L := L) hL hgn hm hziR hf
  have hyiCore : (ytrans L N r x (i + 1)).1 ∈ core L r :=
    Kepler.Text.Reduction5.memCore (L := L) hL hgn hm hyiR hf
  have hcoreNodup : (core L r).Nodup := by
    have hq := Kepler.Text.MoreLemma2a23.quotientAllUniq L hL hm
    refine hq (core L r) ?_
    rw [Kepler.Text.Reduction5.quotientList]
    exact List.mem_map.mpr ⟨Kepler.Text.Reduction5.parts L r,
      List.mem_map.mpr ⟨r, hm.2.2.1, rfl⟩, rfl⟩
  set n := indexf (ztrans L N r x i) (ytrans L N r x (i + 1)) (findFaceDarts L x) with hn
  have hnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  have hrne : r ≠ [] := List.ne_nil_of_mem hm.2.2.2.1
  -- n < |core|
  have hnlt : n < (core L r).length := by
    show n < (core L r).length
    rw [Kepler.Text.TameSpine.coreLengthEqParts,
      ← List.toFinset_card_of_nodup (Kepler.Text.MoreLemma2Island2.uniqParts L hnd hrne)]
    exact indexfZLtSizelYtran L hL hgn hres haq hm hf2 (hfind := rfl) (hw := rfl)
  -- 幂对齐：(nextEl (core r))^n (FST zi) = FST yi
  have hpow1 := Kepler.Text.TameSpine.nextPowerCoreYtran L hL hgn haq hm hk hi
    (hfind := rfl) (hw := rfl) (zi := ztrans L N r x i) (hzi := rfl)
    (yi := ytrans L N r x (i + 1)) (hyi := rfl) (n := n) (le_refl n)
  have hB := Kepler.Text.TameSpine.betwnZtranYtransSucConstChain L hL hgn haq hm i hf2
    (hfind := rfl) (hw := rfl) (n := n) (le_refl n)
  have hziF : ztrans L N r x i ∈ findFaceDarts L x :=
    Kepler.Text.TameSpine.ztranMeFChain L hL hgn haq hm i
  have hyiF : ytrans L N r x (i + 1) ∈ findFaceDarts L x :=
    Kepler.Text.MoreLemma2a23.ytranMeF L hL hm rfl (i + 1)
  have hfndF : (findFaceDarts L x).Nodup :=
    Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
  have hif : (nextEl (findFaceDarts L x))^[n] (ztrans L N r x i)
      = ytrans L N r x (i + 1) := by
    rw [hn, Kepler.Text.Reduction3.indexf_eq_spine]
    exact Kepler.Text.TameSpine.indexfN hziF hyiF hfndF
  have hpow : (nextEl (core L r))^[n] (ztrans L N r x i).1
      = (ytrans L N r x (i + 1)).1 := by
    rw [hpow1, hB, hif]
  -- 实例桥 + nextElnIndexf
  have hidx := Kepler.Text.MoreLemma2Island1.nextElnIndexf
    hziCore hyiCore hcoreNodup hpow hnlt
  rw [hidx, hn]

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期标准三，零 sorryAx） -/
#print axioms Kepler.Text.Reduction5.uniqFstFindFace
#print axioms Kepler.Text.Reduction5.indexfZLtSizelYtran
#print axioms Kepler.Text.Reduction5.indexf3FinalLemmas
