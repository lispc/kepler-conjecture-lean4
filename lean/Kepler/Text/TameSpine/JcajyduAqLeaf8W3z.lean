/-
  JcajyduAqLeaf8W3z — AQ8 波 3z：`partsSubArcRefine`（element-wise，共享引擎）。

  ┌─ 路线（HOL AQ8.hl:1047-1095 逐段；ERRATA 后重开）─────────────
  │ ① `d := HD u`；`MEM_PARTS_IMP` ⇒ `d ∈ s ⊆ r`；`partsMemExists` 取 `p ∋ d`；
  │ ② 对任意 `a ∈ u`：`a ∈ s ⊆ r`；`partsMemExists` 取 `p1 ∋ a`；
  │ ③ `partsFst` 三处（u 侧 / p 侧 / p1 侧）⇒ `p1.head!.1 = a.1 = d.1 = p.head!.1`；
  │ ④ **r-side 单射**（`uniq (core L r)`，旧 quotient `hm.1.2.2.2.2.1` +
  │    `nodup_map_iff_inj_on`）⇒ `p1 = p` ⇒ `a ∈ p`；
  │ ⑤ `FST (HD u) = FST (HD p)` 由 `partsFst` 两次。
  └────────────────────────────────────────────────────────────────

  ┌─ ERRATA（撤回 W3x 的「wrap 支 containment 假」）────────────────
  │ 跨接缝的 part 会要求两个同 head-FST 的 r-part（`partsFst` 把 part 内
  │ 全元素钉成同 FST），撞 r-side 单射 ⇒ 不可能。containment 对任意
  │ `s ⊆ r` 成立（只要 r-side 单射在）。`partsSubArcRefine` **可证**。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件 `aq8w3z_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W3yVI
import Kepler.Text.TameSpine.JcajyduBetwnMap

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)

/-- **子弧 parts 细化（element-wise，ERRATA 后重开）**：
`u ∈ parts L SND`、`u` 的元素全在 `r`（`hur`）⇒ 存在 `p ∈ parts L r`
包含 `u` 全部元素且 `FST (HD u) = FST (HD p)`。

`partsSubArcRefine` 的 element-wise 形——按 HOL `AQ8.hl:1047-1095` 五步，
核心是 **r-side 单射**（旧 quotient）把「每个元素所在的 r-part」合并成同一个 `p`。 -/
theorem aq8w3z_partsSubArcRefine (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (h1 : aq1Concl L hL) (h2 : aq2Concl L hL) (h3 : aq3Concl L hL)
    (h4 : aq4Concl L hL) (h5 : aq5Concl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hsN : ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
        ++ [lYSpine L r x]) ++ between (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (lZSpine L N r x) ∈ ntransSpine L N r x 1)
    {u : List (ℕ × ℕ)}
    (hu : u ∈ partsSpine L (([lZSpine L N r x] ++ between r (lZSpine L N r x)
        (lYSpine L r x) ++ [lYSpine L r x]) ++ between
        (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)))
    (hur : ∀ a ∈ u, a ∈ r) :
    ∃ p ∈ partsSpine L r, (∀ a ∈ u, a ∈ p) ∧ (u.head!).1 = (p.head!).1 := by
  have hnN : NormalListSpine hL (ntransSpine L N r x 1) :=
    aqs_aqNormalList L hL h1 h2 h3 h4 h5 hgn hm
  obtain ⟨hndS, hneS⟩ := normalListUniqNonnil hnN hsN
  have hnR : NormalListSpine hL N := hm.1.2.1
  have hrN : r ∈ N := hm.1.2.2.1
  obtain ⟨hrnd, hrne⟩ := normalListUniqNonnil hnR hrN
  have hune : u ≠ [] := partsAllNonnil L hndS hneS u hu
  have hup : u.head! ∈ u := List.head!_mem_self hune
  -- ① d = HD u ∈ r，取 p ∋ d
  have hdS : u.head! ∈ ([lZSpine L N r x] ++ between r (lZSpine L N r x)
      (lYSpine L r x) ++ [lYSpine L r x]) ++ between
      (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x) :=
    memPartsImp L hndS hneS hu _ hup
  have hdr : u.head! ∈ r := hur _ hup
  obtain ⟨p, hp, hdp⟩ := partsMemExists L hrnd hdr
  -- r-side 单射
  have hq : (partsSpine L r).map (fun q => q.head!.1) ∈ quotientListSpine L N := by
    show _ ∈ coreListSpine (N.map (partsSpine L))
    exact List.mem_map.mpr ⟨partsSpine L r, List.mem_map.mpr ⟨r, hrN, rfl⟩, rfl⟩
  have hcoreNodup : ((partsSpine L r).map (fun q => q.head!.1)).Nodup :=
    (hm.1.2.2.2.2.1).1 _ hq
  have hinj : ∀ q ∈ partsSpine L r, ∀ q' ∈ partsSpine L r,
      (q.head!).1 = (q'.head!).1 → q = q' :=
    (List.nodup_map_iff_inj_on (uniqParts L hrnd hrne)).mp hcoreNodup
  refine ⟨p, hp, ?_, ?_⟩
  · -- ②③④ containment
    intro a ha
    have har : a ∈ r := hur a ha
    obtain ⟨p1, hp1, hap1⟩ := partsMemExists L hrnd har
    have hfst1 : a.1 = (p1.head!).1 := partsFst L hL hnR hrN hp1 hap1
    have hfstu : a.1 = (u.head!).1 := partsFst L hL hnN hsN hu ha
    have hfstp : (u.head!).1 = (p.head!).1 := partsFst L hL hnR hrN hp hdp
    have heq : (p1.head!).1 = (p.head!).1 := by rw [← hfst1, hfstu, hfstp]
    have hpp : p1 = p := hinj p1 hp1 p hp heq
    rw [hpp] at hap1
    exact hap1
  · -- ⑤ FST 相等
    exact (partsFst L hL hnN hsN hu hup).trans (partsFst L hL hnR hrN hp hdp)

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：⊆ 标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq8w3z_partsSubArcRefine
