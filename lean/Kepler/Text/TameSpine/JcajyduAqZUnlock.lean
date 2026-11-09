/-
  Kepler.Text.TameSpine.JcajyduAqZUnlock — 裁决 (b1)+(b2) 首批（z 侧解锁）：

  ① b2（hzface 干净桥）：face↔findFaceDarts 轨道桥 + zMemFindFaceDarts
     （引擎 hypY_hypZ_mem_face + hypYL/hypZLz + cong）；② b1：hqymrtx
     证明体逐行复刻（入口 IsMarked → IsSplitCondition+SFlagged+hedge，
     三处消费点全换干净件）→ hypZMemDartsOfSplit → zMemRtransClean（干净
     z ∈ r，绕开 TameList16:1095 单点）；③ E3 槽供给 hyneSupply（现成）。
     公理账见 recon_hqymrtx_axioms*.log（两轮 RC=0）；hunL 沿既有链作
     诚实前提参。纪律：零 sorry/admit/native_decide/axiom；主仓零写入。
-/
import Kepler.Text.TameSpine.TameList17
import Kepler.Text.TameSpine.JcajyduAqTowerBase

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

/-! ## §1 b2：face ↔ findFaceDarts 桥（零债） -/

/-- **faceMap 轨道保面内成员性**：`d ∈ findFaceDarts L x → (faceMap^k) d ∈
findFaceDarts L x`——归纳步 = `faceMap_hypermapOfList`（faceMap d = fList d）
+ `findFaceDarts_congr_of_mem`（同面等表）+ `nextEl_mem_of_mem`（面内后继
封闭）。 -/
theorem faceMapPowMemFaceDarts {L : fgraph ℕ} (hL : GoodList L) (x : ℕ × ℕ)
    (hxx : x ∈ listOfDarts L) :
    ∀ (k : ℕ) {d : ℕ × ℕ}, d ∈ findFaceDarts L x →
      ((hypermapOfList L hL).faceMap ^ k) d ∈ findFaceDarts L x := by
  intro k
  induction k with
  | zero => intro d hd; simpa using hd
  | succ k ih =>
    intro d hd
    have hdk : ((hypermapOfList L hL).faceMap ^ k) d ∈ findFaceDarts L x := ih hd
    have hdkD : ((hypermapOfList L hL).faceMap ^ k) d ∈ listOfDarts L :=
      mem_darts_of_mem_findFace L hdk
    rw [pow_succ', Equiv.Perm.mul_apply]
    have hFd : (hypermapOfList L hL).faceMap (((hypermapOfList L hL).faceMap ^ k) d)
        = fList L (((hypermapOfList L hL).faceMap ^ k) d) :=
      faceMap_hypermapOfList L hL (List.mem_toFinset.mpr hdkD)
    rw [hFd]
    show nextEl (findFaceDarts L (((hypermapOfList L hL).faceMap ^ k) d))
      (((hypermapOfList L hL).faceMap ^ k) d) ∈ findFaceDarts L x
    have hcongr : findFaceDarts L (((hypermapOfList L hL).faceMap ^ k) d)
        = findFaceDarts L x :=
      findFaceDarts_congr_of_mem hL.1 hxx hdk
    rw [hcongr]
    exact nextEl_mem_of_mem hdk

/-- **face 成员 → findFaceDarts 成员**：`z ∈ H.face x → z ∈ findFaceDarts L x`
（face = faceMap 轨道集；锚点 x 自身须在 findFaceDarts L x 内）。 -/
theorem memFindFaceDartsOfMemFace {L : fgraph ℕ} (hL : GoodList L) {x z : ℕ × ℕ}
    (hxx : x ∈ findFaceDarts L x)
    (hz : z ∈ (hypermapOfList L hL).face x) : z ∈ findFaceDarts L x := by
  obtain ⟨k, hk⟩ := hz
  rw [← hk]
  exact faceMapPowMemFaceDarts hL x (mem_darts_of_mem_findFace L hxx) k hxx

/-- **b2 主件（hzface 供给）**：`lZSpine L N r x ∈ findFaceDarts L
(lYSpine L r x)`——`hypY_hypZ_mem_face`（两者同面）+ `hypYL`/`hypZLz`
transport + face→findFaceDarts + 同面等表 congr。 -/
theorem zMemFindFaceDarts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    lZSpine L N r x ∈ findFaceDarts L (lYSpine L r x) := by
  have hnext := hm.1.2.2.2.2.2.1
  have hsc := markListSplitConditionList L hL hm.1 hf
  have hyz := (hypermapOfList L hL).hypY_hypZ_mem_face
    (loopFamilyOfListSpine N) (loopOfListSpine r) x
  have hyEq : (hypermapOfList L hL).hypY (loopFamilyOfListSpine N)
      (loopOfListSpine r) x = lYSpine L r x := hypYL L hL hgn hunL hnext hsc
  have hzEq : (hypermapOfList L hL).hypZ (loopFamilyOfListSpine N)
      (loopOfListSpine r) x = lZSpine L N r x := hypZLz L hL hgn hunL hnext hsc
  have hn := hm.1.2.1
  have hrN := hm.1.2.2.1
  have hxr := hm.1.2.2.2.1
  have hxd : x ∈ listOfDarts L :=
    normalListListOfDarts hn x (List.mem_flatten.mpr ⟨r, hrN, hxr⟩)
  have hxx : x ∈ findFaceDarts L x := (dart_in_face L x).mpr hxd
  have hzx : lZSpine L N r x ∈ findFaceDarts L x := by
    refine memFindFaceDartsOfMemFace hL hxx ?_
    rw [← hzEq]; exact hyz.2
  have hyx : lYSpine L r x ∈ findFaceDarts L x := by
    refine memFindFaceDartsOfMemFace hL hxx ?_
    rw [← hyEq]; exact hyz.1
  have hcongr : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
    findFaceDarts_congr_of_mem hL.1 hxd hyx
  rw [hcongr]
  exact hzx

end Kepler.Text.TameSpine

/-! ## §2 b1：hqymrtx 证明体拆分条件级复刻

底本 = Hypermap.lean:10505 `hqymrtx`（270 行平面性论证），逐行抄录；
三处 IsMarked 消费点替换：
- `split_marked_loop hmark hLnot` → 参数 `hsplit`（干净构造见
  `splitConditionOfMarked`）；
- `hmark.2.2.2.2.2.2.2.2 hLnot`（SFlagged）→ 参数 `hsflag`
  （由 `markListSFlagged` 标准三供给）；
- `(H.marked_dart hmark).2`（nodeMap.symm x ∈ final）→ 由参数
  `hedge`（edgeMap x ∈ final）+ `marked_dart` 的同款推导 `hH5` 重证。
-/

namespace Kepler.Text.Hypermap

/-- **hqymrtx 的拆分条件级内核**（超集：结论含 `.1` 与迭代不等式；
E3 只用 `.1`）。命名空间同底本（Kepler.Text.Hypermap），全部下级件
按 hqymrtx 同名直接解析。 -/
theorem hypZMemDartsOfSplit {α : Type*} [DecidableEq α] (H : Hypermap α)
    {NF : Set (Loop α)}
    {hnf : H.IsNormalFamily NF} {L : Loop α} {x : α}
    (hsplit : H.IsSplitCondition NF L x) (hsflag : H.SFlagged NF L x)
    (hedge : H.edgeMap x ∈ H.dartsInFinalLoops NF) :
    H.hypZ NF L x ∈ L.darts ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ H.hypM NF L x + 1 →
        H.hypZ NF L x ≠ (H.faceMap ^ k) x := by
  obtain ⟨hres, -, hL, hLnot, hx, -⟩ := id hsplit
  have hH5 : H.nodeMap.symm x ∈ H.dartsInFinalLoops NF := by
    obtain ⟨L', hL', hedL'⟩ := H.mem_dartsInFinalLoops_iff.mp hedge
    have h1 : (H.faceMap ^ 1) (H.edgeMap x) = (L'.map ^ 1) (H.edgeMap x) :=
      (H.pow_faceMap_eq_pow_map_final hL' hedL' 1)
    rw [pow_one, pow_one] at h1
    have h2 : H.nodeMap.symm x = H.faceMap (H.edgeMap x) := by
      have he : H.nodeMap⁻¹ = H.faceMap * H.edgeMap := (H.inverse_hypermap_maps).2.1
      calc H.nodeMap.symm x = H.nodeMap⁻¹ x := rfl
        _ = (H.faceMap * H.edgeMap) x := by rw [he]
        _ = H.faceMap (H.edgeMap x) := Equiv.Perm.mul_apply _ _ _
    rw [h2, h1]
    exact H.mem_dartsInFinalLoops (L'.pow_map_mem hedL' 1) hL'
  have hspec := H.hypM_spec hsplit
  have hpspec := H.hypP_spec hsplit
  have hF9 : ∀ i ≤ H.hypM NF L x + 1, (L.map ^ i) x = (H.faceMap ^ i) x := hspec.1
  have hF12 : H.hypZ NF L x ∈ dartsOfFamily NF := hpspec.2
  have hHD : H.hypY NF L x ∈ L.darts := (H.on_hypY hsplit).1
  have hiter : ∀ (f : Equiv.Perm α) (k : ℕ) (w : α), (f ^ (k + 1)) w = f ((f ^ k) w) :=
    fun f k w => by rw [pow_succ', Equiv.Perm.mul_apply]
  have hpow : ∀ (a b : ℕ) (w : α),
      (H.faceMap ^ a) ((H.faceMap ^ b) w) = (H.faceMap ^ (a + b)) w := by
    intro a b w
    rw [pow_add, Equiv.Perm.mul_apply]
  have hF16 : ∀ k : ℕ, 1 ≤ k → k ≤ H.hypM NF L x + 1 →
      H.hypZ NF L x ≠ (H.faceMap ^ k) x := by
    intro k hk1 hk2 hcon
    rcases Nat.eq_zero_or_pos (H.hypP NF L x) with hp0 | hp1
    · exfalso
      have hzc := H.hypM_lt_face hsplit
      have hz : (H.faceMap ^ (H.hypP NF L x + 1)) (H.hypY NF L x) = (H.faceMap ^ k) x :=
        hcon
      rw [hp0, Nat.zero_add] at hz
      have hz2 : (H.faceMap ^ (H.hypM NF L x + 2)) x = (H.faceMap ^ k) x := by
        have hy : H.hypY NF L x = (H.faceMap ^ (H.hypM NF L x + 1)) x := rfl
        calc (H.faceMap ^ (H.hypM NF L x + 2)) x
            = H.faceMap ((H.faceMap ^ (H.hypM NF L x + 1)) x) := hiter H.faceMap _ x
          _ = H.faceMap (H.hypY NF L x) := by rw [hy]
          _ = (H.faceMap ^ k) x := hz
      obtain ⟨q, hq⟩ := H.exists_mul_ncard_add_of_pow_eq_face
        (n := k) (m := H.hypM NF L x + 2) (by omega) hz2.symm
      rcases Nat.eq_zero_or_pos q with rfl | hq1
      · omega
      · have hqc : (H.face x).ncard ≤ q * (H.face x).ncard :=
          Nat.le_mul_of_pos_left _ hq1
        omega
    · exfalso
      obtain ⟨d, hd⟩ : ∃ d : ℕ, k = d + 1 := ⟨k - 1, by omega⟩
      have hz : (H.faceMap ^ (H.hypP NF L x + 1)) (H.hypY NF L x)
          = (H.faceMap ^ (d + 1)) x := by
        rw [← hd]; exact hcon
      have key : (H.faceMap ^ H.hypP NF L x) (H.hypY NF L x) = (H.faceMap ^ d) x := by
        refine H.faceMap.injective ?_
        calc H.faceMap ((H.faceMap ^ H.hypP NF L x) (H.hypY NF L x))
            = (H.faceMap ^ (H.hypP NF L x + 1)) (H.hypY NF L x) := (hiter H.faceMap _ _).symm
          _ = (H.faceMap ^ (d + 1)) x := hz
          _ = H.faceMap ((H.faceMap ^ d) x) := hiter H.faceMap d x
      exact hpspec.1 (H.hypP NF L x) hp1 (Nat.le_refl _) (by
        rw [key, ← hF9 d (by omega)]
        exact mem_dartsOfFamily hL (L.pow_map_mem hx _))
  refine ⟨?_, hF16⟩
  obtain ⟨L', hL'NF, hzdarts⟩ := hF12
  rcases eq_or_ne L' L with rfl | hne
  · exact hzdarts
  · exfalso
    have huatom : H.headOfAtom NF (H.hypZ NF L x) ∈ H.atom L' (H.hypZ NF L x) :=
      (H.headOfAtom_mem_atom hnf hL'NF hzdarts).1
    have hudarts : H.headOfAtom NF (H.hypZ NF L x) ∈ L'.darts :=
      H.mem_darts_of_mem_atom hzdarts huatom
    by_cases hL'fin : L' ∈ H.finalLoops NF
    · have hzorb : H.hypZ NF L x ∈ orbitMap H.faceMap x := by
        have hzK : H.hypZ NF L x
            = (H.faceMap ^ (H.hypP NF L x + 1 + (H.hypM NF L x + 1))) x := by
          show (H.faceMap ^ (H.hypP NF L x + 1)) (H.hypY NF L x) = _
          rw [show H.hypY NF L x = (H.faceMap ^ (H.hypM NF L x + 1)) x from rfl]
          exact hpow _ _ x
        rw [hzK]
        exact pow_apply_mem_orbitMap _ _ _
      have hsym : orbitMap H.faceMap (H.hypZ NF L x) = orbitMap H.faceMap x :=
        orbitMap_eq_of_mem H.faceMap_permutes hzorb
      have hxmem : x ∈ orbitMap H.faceMap (H.hypZ NF L x) := by
        rw [hsym]; exact mem_orbitMap_self _ _
      obtain ⟨j, hj⟩ : ∃ j : ℕ, (H.faceMap ^ j) (H.hypZ NF L x) = x := hxmem
      have hagree' := H.pow_faceMap_eq_pow_map_final hL'fin hzdarts j
      have hxL' : x ∈ L'.darts := by
        have hxeq : x = (L'.map ^ j) (H.hypZ NF L x) := hj.symm.trans hagree'
        rw [hxeq]
        exact L'.pow_map_mem hzdarts j
      exact hne (hnf.eq_of_mem_of_mem hL'NF hL hxL' hx)
    · have hL'not : L' ∉ H.finalLoops NF := hL'fin
      have hu23 : H.headOfAtom NF (H.hypZ NF L x) ∉ H.hypS NF L x := by
        intro hcon
        exact hne (hnf.eq_of_mem_of_mem hL hL'NF
          (H.hypS_subset_darts hsplit hcon) hudarts).symm
      obtain ha | hb := hsflag.2 L' hL'NF (H.hypZ NF L x) hzdarts hL'not hu23
      · obtain ⟨K, hKfin, hKmem⟩ := H.mem_dartsInFinalLoops_iff.mp ha
        have hident : H.faceMap (H.edgeMap (H.headOfAtom NF (H.hypZ NF L x)))
            = H.nodeMap.symm (H.headOfAtom NF (H.hypZ NF L x)) := by
          have he : H.nodeMap⁻¹ = H.faceMap * H.edgeMap := (H.inverse_hypermap_maps).2.1
          calc H.faceMap (H.edgeMap (H.headOfAtom NF (H.hypZ NF L x)))
              = (H.faceMap * H.edgeMap) (H.headOfAtom NF (H.hypZ NF L x)) :=
                (Equiv.Perm.mul_apply _ _ _).symm
            _ = H.nodeMap⁻¹ (H.headOfAtom NF (H.hypZ NF L x)) := by rw [he]
            _ = H.nodeMap.symm (H.headOfAtom NF (H.hypZ NF L x)) := rfl
        have hvin : H.nodeMap.symm (H.headOfAtom NF (H.hypZ NF L x))
            ∈ H.dartsInFinalLoops NF := by
          have h4 : (K.map ^ 1) (H.edgeMap (H.headOfAtom NF (H.hypZ NF L x)))
              = H.faceMap (H.edgeMap (H.headOfAtom NF (H.hypZ NF L x))) :=
            (H.pow_faceMap_eq_pow_map_final hKfin hKmem 1).symm
          rw [pow_one] at h4
          rw [← hident, ← h4]
          exact H.mem_dartsInFinalLoops (K.pow_map_mem hKmem 1) hKfin
        obtain ⟨kb, -, hkbeq⟩ := L'.exists_pow_apply hzdarts hudarts
        have hHG : H.faceContour (H.hypY NF L x) (H.hypP NF L x + 1)
            = L'.pathOf (H.hypZ NF L x) 0 := rfl
        have hH8 : H.isContour (gluePaths (H.faceContour (H.hypY NF L x))
            (L'.pathOf (H.hypZ NF L x)) (H.hypP NF L x + 1))
            (H.hypP NF L x + 1 + kb) :=
          H.isContour_gluePaths (H.isContour_faceContour _ _)
            (L'.isContour_pathOf (hnf.1 L' hL'NF).1 hzdarts kb) hHG
        have hfwayend : gluePaths (H.faceContour (H.hypY NF L x))
            (L'.pathOf (H.hypZ NF L x)) (H.hypP NF L x + 1)
            (H.hypP NF L x + 1 + kb) = H.headOfAtom NF (H.hypZ NF L x) := by
          rw [gluePaths_apply_add hHG kb]
          show (L'.map ^ kb) (H.hypZ NF L x) = H.headOfAtom NF (H.hypZ NF L x)
          exact hkbeq.symm
        obtain ⟨sway, s, hs0, hss, hscont, hssup⟩ :=
          hsflag.1 (H.nodeMap.symm (H.headOfAtom NF (H.hypZ NF L x))) hvin
            (H.nodeMap.symm x) hH5
        have hH15 : H.isContour
            (joinPaths (gluePaths (H.faceContour (H.hypY NF L x))
              (L'.pathOf (H.hypZ NF L x)) (H.hypP NF L x + 1)) sway
              (H.hypP NF L x + 1 + kb))
            (H.hypP NF L x + 1 + kb + s + 1) :=
          H.isContour_joinPaths hH8 hscont (by
            rw [hfwayend, hs0]
            exact Or.inr rfl)
        refine absurd hres.planar (H.loopSeparation L
          (joinPaths (gluePaths (H.faceContour (H.hypY NF L x))
            (L'.pathOf (H.hypZ NF L x)) (H.hypP NF L x + 1)) sway
            (H.hypP NF L x + 1 + kb)) (H.hypP NF L x + 1 + kb + s + 1)
          (hnf.1 L hL).1 (by omega) hH15 ?_ ?_ ?_ ?_ ⟨x, ?_, hx⟩)
        · rw [joinPaths_apply_le (by omega), gluePaths_apply_le (by omega)]
          exact hHD
        · rw [joinPaths_apply_le (by omega), gluePaths_apply_le (by omega)]
          show (H.faceMap ^ 1) (H.hypY NF L x) = H.faceMap (H.hypY NF L x)
          rw [pow_one]
        · intro i hi1 hi2
          rcases Nat.lt_or_ge i (H.hypP NF L x + 1 + kb + 1) with hilt | hige
          · have hin : i ≤ H.hypP NF L x + 1 + kb := by omega
            rw [joinPaths_apply_le hin]
            rcases Nat.lt_or_ge i (H.hypP NF L x + 1) with hilt2 | hige2
            · rw [gluePaths_apply_le (by omega)]
              intro hcon
              have hmem : (H.faceMap ^ i) (H.hypY NF L x) ∈ dartsOfFamily NF :=
                mem_dartsOfFamily hL hcon
              exact hpspec.1 i hi1 (by omega) hmem
            · obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = H.hypP NF L x + 1 + j :=
                ⟨i - (H.hypP NF L x + 1), by omega⟩
              rw [gluePaths_apply_add hHG j]
              intro hcon
              exact hne (hnf.eq_of_mem_of_mem hL'NF hL
                (L'.pow_map_mem hzdarts j) hcon)
          · obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = H.hypP NF L x + 1 + kb + (j + 1) :=
              ⟨i - (H.hypP NF L x + 1 + kb) - 1, by omega⟩
            rw [joinPaths_apply_add j]
            intro hcon
            have hjdfl : sway j ∈ H.dartsInFinalLoops NF := by
              have hsup : sway j ∈ ↑(Loop.pathSupport sway s) :=
                (Loop.mem_pathSupport.mpr ⟨j, by omega, rfl⟩)
              exact hssup hsup
            exact H.not_mem_dartsInFinalLoops hnf hL hLnot hcon hjdfl
        · have hxnode : H.nodeMap.symm x ∈ H.node x :=
            H.nodeMap_symm_mem_node (mem_orbitMap_self _ _)
          have hwayend : (joinPaths (gluePaths (H.faceContour (H.hypY NF L x))
              (L'.pathOf (H.hypZ NF L x)) (H.hypP NF L x + 1)) sway
              (H.hypP NF L x + 1 + kb)) (H.hypP NF L x + 1 + kb + s + 1)
              = H.nodeMap.symm x := by
            rw [show H.hypP NF L x + 1 + kb + s + 1
                = (H.hypP NF L x + 1 + kb) + (s + 1) from by omega,
              joinPaths_apply_add s]
            exact hss
          rw [hwayend,
            show H.node (H.nodeMap.symm x) = H.node x from (H.node_eq_of_mem hxnode).symm]
          exact (H.on_hypY hsplit).2.2
        · rw [show (joinPaths (gluePaths (H.faceContour (H.hypY NF L x))
              (L'.pathOf (H.hypZ NF L x)) (H.hypP NF L x + 1)) sway
              (H.hypP NF L x + 1 + kb)) (H.hypP NF L x + 1 + kb + s + 1)
              = H.nodeMap.symm x from by
              rw [show H.hypP NF L x + 1 + kb + s + 1
                = (H.hypP NF L x + 1 + kb) + (s + 1) from by omega,
                joinPaths_apply_add s]
              exact hss,
            show H.node (H.nodeMap.symm x) = H.node x from (H.node_eq_of_mem
              (H.nodeMap_symm_mem_node (mem_orbitMap_self _ _))).symm]
          exact mem_orbitMap_self _ _
      · simp only [hypS, Set.mem_image] at hb
        obtain ⟨i, hiIcc, hieu⟩ := hb
        rw [Set.mem_Icc] at hiIcc
        have hident : H.faceMap (H.edgeMap (H.headOfAtom NF (H.hypZ NF L x)))
            = H.nodeMap.symm (H.headOfAtom NF (H.hypZ NF L x)) := by
          have he : H.nodeMap⁻¹ = H.faceMap * H.edgeMap := (H.inverse_hypermap_maps).2.1
          calc H.faceMap (H.edgeMap (H.headOfAtom NF (H.hypZ NF L x)))
              = (H.faceMap * H.edgeMap) (H.headOfAtom NF (H.hypZ NF L x)) :=
                (Equiv.Perm.mul_apply _ _ _).symm
            _ = H.nodeMap⁻¹ (H.headOfAtom NF (H.hypZ NF L x)) := by rw [he]
            _ = H.nodeMap.symm (H.headOfAtom NF (H.hypZ NF L x)) := rfl
        have hu_z : H.headOfAtom NF (H.hypZ NF L x) ∈ H.node (H.hypZ NF L x) :=
          H.atom_subset_node L' (H.hypZ NF L x) huatom
        have hvnode : (L.map ^ (i + 1)) x ∈ H.node (H.hypZ NF L x) := by
          have hnu : H.node (H.headOfAtom NF (H.hypZ NF L x)) = H.node (H.hypZ NF L x) :=
            (H.node_eq_of_mem hu_z).symm
          have hval : (L.map ^ (i + 1)) x
              = H.nodeMap.symm (H.headOfAtom NF (H.hypZ NF L x)) := by
            calc (L.map ^ (i + 1)) x
                = (H.faceMap ^ (i + 1)) x := hF9 (i + 1) (by omega)
              _ = H.faceMap ((H.faceMap ^ i) x) := hiter H.faceMap i x
              _ = H.faceMap (H.edgeMap (H.headOfAtom NF (H.hypZ NF L x))) := by
                  rw [hieu]
              _ = H.nodeMap.symm (H.headOfAtom NF (H.hypZ NF L x)) := hident
          rw [hval, ← hnu]
          exact H.nodeMap_symm_mem_node (mem_orbitMap_self _ _)
        refine absurd hres.planar (H.loopSeparation L (H.faceContour (H.hypY NF L x))
          (H.hypP NF L x + 1)
          (hnf.1 L hL).1 (by omega) (H.isContour_faceContour _ _) ?_ ?_ ?_ ?_
          ⟨(L.map ^ (i + 1)) x, hvnode, L.pow_map_mem hx _⟩)
        · rw [show H.faceContour (H.hypY NF L x) 0 = H.hypY NF L x from rfl]
          exact hHD
        · show (H.faceMap ^ 1) (H.hypY NF L x) = H.faceMap (H.hypY NF L x)
          rw [pow_one]
        · intro i' hi1 hi2
          show (H.faceMap ^ i') (H.hypY NF L x) ∉ L.darts
          rcases Nat.eq_or_lt_of_le hi2 with hi' | hi'
          · rw [hi']
            intro hcon
            exact hne (hnf.eq_of_mem_of_mem hL'NF hL hzdarts hcon)
          · intro hcon
            exact hpspec.1 i' hi1 (by omega) (mem_dartsOfFamily hL hcon)
        · rw [show H.faceContour (H.hypY NF L x) 0 = H.hypY NF L x from rfl,
            show H.faceContour (H.hypY NF L x) (H.hypP NF L x + 1)
              = H.hypZ NF L x from rfl]
          exact (H.on_hypZ hsplit).1

end Kepler.Text.Hypermap

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl prevEl eList fList GoodList findFaceDarts nList
  listOfDarts)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nextEl_mem_of_mem faceMap_hypermapOfList)

/-! ## §3 干净构造与 z ∈ r（b1 落地） -/

/-- **b1 接线①：干净 IsSplitCondition 构造**（MarkedListSpineFull +
¬final → IsSplitCondition）——`split_marked_loop` 的债-free 替身。 -/
theorem splitConditionOfMarked (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    (hypermapOfList L hL).IsSplitCondition (loopFamilyOfListSpine N)
      (loopOfListSpine r) x :=
  splitConditionListSplit L hL hgn hunL (markListSplitConditionList L hL hm.1 hf)

/-- **b1 主件：干净 `z ∈ r`**（mem_ztrans_rtrans_v0 的债-free 替身）：
`lZSpine L N r x ∈ r`——`hypZMemDartsOfSplit`（b1 复刻）经 `hypZLz`
（hypZ = lZSpine）+ `inDartLoopOfList`（loop darts ↔ r）落地。 -/
theorem zMemRtransClean (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    lZSpine L N r x ∈ r := by
  have hnext := hm.1.2.2.2.2.2.1
  have hsc := markListSplitConditionList L hL hm.1 hf
  have hsplit := splitConditionListSplit L hL hgn hunL hsc
  have hsflag := markListSFlagged L hL hgn hunL hm hf
  have hedge : (hypermapOfList L hL).edgeMap x
      ∈ (hypermapOfList L hL).dartsInFinalLoops (loopFamilyOfListSpine N) :=
    markedListEdgeMapFinal hL hm.1
  have hq := Kepler.Text.Hypermap.hypZMemDartsOfSplit
    (H := hypermapOfList L hL)
    (hnf := normalListNormal hL hgn hm.1.1 hm.1.2.1)
    (NF := loopFamilyOfListSpine N) (L := loopOfListSpine r) (x := x)
    hsplit hsflag hedge
  have hzEq := hypZLz L hL hgn hunL hnext hsc
  have hzD : lZSpine L N r x ∈ (loopOfListSpine r).darts := hzEq ▸ hq.1
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hm.1.2.1 hm.1.2.2.1
  exact (inDartLoopOfList hr1 hr2 _).mp hzD

/-! ## §4 E3 槽供给（aq3Split2FLast 三槽之二） -/

/-- **hyne 槽供给**（零成本：`hqymrtx3List` 标准三现成）。 -/
theorem hyneSupply (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    lYSpine L r x ≠ lZSpine L N r x :=
  hqymrtx3List L hL hgn hunL hm hf

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三 ⊆ [propext, Classical.choice,
Quot.sound]，零 sorryAx——本批全部件零消费 TameList16:1109 债链。） -/
#print axioms Kepler.Text.TameSpine.faceMapPowMemFaceDarts
#print axioms Kepler.Text.TameSpine.memFindFaceDartsOfMemFace
#print axioms Kepler.Text.TameSpine.zMemFindFaceDarts
#print axioms Kepler.Text.Hypermap.hypZMemDartsOfSplit
#print axioms Kepler.Text.TameSpine.splitConditionOfMarked
#print axioms Kepler.Text.TameSpine.zMemRtransClean
#print axioms Kepler.Text.TameSpine.hyneSupply
