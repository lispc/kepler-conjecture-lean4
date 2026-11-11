/-
  Kepler.Text.Reduction5J7W1c — J5-7 W1-2b 计数步（B1-B4 + B6，**非严格形**）：
  `indexf zi yi f ≤ (parts L r).toFinset.card`（= `sizel (core L r)` 的链形）。

  证 = f-弧像集 `T = {[(nextEl f)^{k+1} zi] | k < n-1}`：
  · B2 成员：`singletonPartOfFArc`（W1b 绿）；
  · B3 单射/基数：f-弧 `indexf` 迭代 = 指数（`indexfFArcPow`：`nextElnIndexf` +
    `iterateInstEq`）+ `Finset.card_image_of_injOn`；
  · B4 排除 zi 的 part（`partsMemExists` + `indexfRefl` 撞 `= k+1 > 0`）；
  · B6 基数：`T ⊆ parts.erase (part zi)` ⇒ `n-1 ≤ |parts|-1` ⇒ `n ≤ |parts|`。
  **严格形（`n < |parts|`，HOL 的最后一步）未含**——需再排除 `yi` 的 part：
  见 DELIVERY_J5J7_W1C §2（两条路线：HOL 的 QCDVKEA 算术 / 先落
  `uniq_fst_find_face` 走 FST-单射捷径）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction5J7W1b
import Kepler.Text.Reduction5J5Pnxvwfs
import Kepler.Text.Reduction5Kbwpbhq
import Kepler.Text.MoreLemma2Naming
import Kepler.Text.Reduction4
import Kepler.Text.TameSpine.Reduction3J5IndexfYltSizelBase

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts eList)
open Kepler.Text.TameLp (GoodListNodesTl)

/-- **B3 引擎（f-弧版）**：`k < f.length ⇒ indexf zi ((nextEl f)^k zi) f = k`
（`nextElnIndexf` + `iterateInstEq` 桥，与 `indexfWLePartsCard` 私有件同构）。 -/
private theorem indexfFArcPow {f : List Dart} {zi : Dart} (hzi : zi ∈ f)
    (hnd : f.Nodup) {k : ℕ} (hk : k < f.length) :
    Kepler.Text.Reduction5.indexf zi ((nextEl f)^[k] zi) f = k := by
  have hdi : (nextEl f)^[k] zi ∈ f :=
    Kepler.Text.TameSpine.memPowerNextEl hzi k
  have hp : (@nextEl Dart instBEqOfDecidableEq f)^[k] zi = (nextEl f)^[k] zi :=
    (Kepler.Text.Reduction5.iterateInstEq f zi k).symm
  exact Kepler.Text.MoreLemma2Island1.nextElnIndexf hzi hdi hnd hp hk

/-- **W1-2b（B1-B4+B6）：非严格计数**——
`indexf zi yi f ≤ (parts L r).toFinset.card`（= `sizel (core L r)`）。
f-弧内部点的单点 atom（B2）经 `Finset.card_image_of_injOn` 计数（B3），
排除 `zi` 所在 part（B4）后基数收口（B6）。 -/
theorem indexfZLtSizelYtranLe (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {i : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf2 : ¬ finalList L (rtrans L N r x (i + 1)))
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) :
    indexf (ztrans L N r x i) (ytrans L N r x (i + 1)) f
      ≤ (parts L r).toFinset.card := by
  set zi := ztrans L N r x i with hzi
  set yi := ytrans L N r x (i + 1) with hyi
  set n := indexf zi yi f with hn
  show n ≤ (parts L r).toFinset.card
  have hziF : zi ∈ f := by
    have h := Kepler.Text.TameSpine.ztranMeFChain L hL hgn haq hm i
    rwa [hfind] at h
  have hyiF : yi ∈ f := Kepler.Text.MoreLemma2a23.ytranMeF L hL hm hfind.symm (i + 1)
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
  have hnlt : n < f.length := indexfLtSizel hziF hyiF
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · rw [hn0]
    exact Nat.zero_le _
  · -- 像集 T
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
    -- B4：zi 的 part 不在 T 中
    have hunL : ∀ l ∈ L, l.Nodup :=
      (Kepler.Text.TameSpine.simpleHypermapUniq L hL hgn).mp hm.1.simple
    have hnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
    have hziR : zi ∈ r :=
      pnxvwfs2 L hL hgn haq i (Kepler.Text.Reduction5.finalListInduct i hf2) hm
    obtain ⟨pz, hpz, hzipz⟩ :=
      Kepler.Text.MoreLemma2Naming.partsMemExists L hnd hziR
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
    have hsub : (Finset.range (n - 1)).image φ
        ⊆ (parts L r).toFinset.erase pz := by
      intro q hq
      have hqP : q ∈ (parts L r).toFinset := by
        obtain ⟨k, hk, hkφ⟩ := Finset.mem_image.mp hq
        rw [← hkφ]
        exact hmem k hk
      refine Finset.mem_erase.mpr ⟨?_, hqP⟩
      intro hqp
      exact hpzT (hqp ▸ hq)
    have hcard : ((Finset.range (n - 1)).image φ).card = n - 1 := by
      rw [Finset.card_image_of_injOn hinj]
      simp
    have hpzM : pz ∈ (parts L r).toFinset := List.mem_toFinset.mpr hpz
    have hcle := Finset.card_le_card hsub
    rw [hcard, Finset.card_erase_of_mem hpzM] at hcle
    have hPpos : 0 < (parts L r).toFinset.card := Finset.card_pos.mpr ⟨pz, hpzM⟩
    omega

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期标准三，零 sorryAx） -/
#print axioms Kepler.Text.Reduction5.indexfZLtSizelYtranLe
