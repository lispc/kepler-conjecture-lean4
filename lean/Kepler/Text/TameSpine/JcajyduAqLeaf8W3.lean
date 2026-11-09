/-
  JcajyduAqLeaf8W3 — AQ8 波 3a：snd 巨头（`uniq_snd_split_normal_parts`，
  AQ8.hl:530-1356，827 行）的**上游闭环 + 通用引擎**。

  ┌─ 本波范围（先报后做；W3 单波 >450 已按令拆分）─────────────────
  │ W3 目标形（单件，827 HOL）：
  │   `(coreSpine L (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
  │      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2).Nodup`
  │ 依赖普查（HOL 侧 27 个 helper token 逐一核 Lean 库）结论：
  │   **只缺 1 件** = `betwn_not_in_fst_rtrans`（AQ1.hl:1316，23 行）。
  │   其余 26 token 全部已在库（见 §0 表），含此前疑缺的
  │   `uniq_snd_split_norm` → `hsndClean`（JcajyduAqSnd:188）、
  │   `betwn_not_in_rtrans` → `betwnNotInRtrans`（:136）、
  │   `indexf_in_rtrans_suc_not_rtrans_new2_v0` → `indexfInRtransSucNotRtransNew2`（:117）、
  │   `AQ_normal_list` → `aqs_aqNormalList`（W1a:113，五槽条件形）。
  │ ⇒ 本波 W3a = 上游闭环，两件：
  │   ① aq8w3_betwnNotInFstRtrans   AQ1.hl:1316（23 行）—— 唯一缺件
  │   ② aq8w3_yNextNeFListEList     AQ8.hl:924-943（20 行）—— 巨头的
  │      「y 不是新面的末元」引擎（两条分支各消费一次）
  └────────────────────────────────────────────────────────────────

  ┌─ 依赖普查明细（HOL token ↦ Lean 载体）───────────────────────
  │ parts_uniq_nonnil→partsUniqNonnil / parts_fst→partsFst /
  │ parts_darts→partsDarts / parts_mem_exists→partsMemExists /
  │ uniq_parts→uniqParts / parts_last_inj→partsLastInj /
  │ parts_flatten→partsFlatten / parts_cat→partsCat /
  │ next_el_parts_unlast→nextElPartsUnlast / parts_next_unlast→partsNextUnlast /
  │ normal_list_parts_next_last→normalListPartsNextLast /
  │ MEM_HD→memHd / MEM_LAST→memLast / MEM_PARTS_IMP→memPartsImp /
  │ uniq_imp_inj→uniqImpInj / uniq_map→List.nodup_map_iff_inj_on /
  │ uniq_sublist_unique→uniqSublistUnique / uniq_append_betwn→uniqAppendBetwn /
  │ uniq_betwn→uniqBetwn / next_cat_betwn_same→nextCatBetwnSame /
  │ next_el_cat1→nextElCat1 / next_el_cat_last1→nextElCatLast1 /
  │ betwn_mem→betwnMem / F_LIST_INJ→fListInjDarts /
  │ is_restricted_e_list_nondeg→isRestrictedEListNondeg /
  │ good_list_e_list→goodListEList / uniq_find_face→findFaceDarts_nodup /
  │ mem_find_face_imp_faces_eq→aq10_memFindFaceImpFacesEq /
  │ f_list_power_next_el→fListPowerNextEl / Seq2.next_prev_id→nextElPrevElUniq /
  │ HD_BETWN2→hdBetwn / mem_imp_not_nil→memImpNotNil /
  │ last_parts_y_not_cat→lastPartsYNotCat / snd_mem_rtran1→sndMemRtran1 /
  │ uniq_flatten_uniq→uniqFlattenUniq / PPLHULJ_v0→pplhuljV0 /
  │ ytrans/rtrans/ztrans 三族 → zMemRtransClean/ytransMemRtrans/hyneSupply、
  │ marked_list_of_dart→markedListOfDart、memYtransListOfDarts、
  │ fst_mem_rtran1（W2b）——全部在库、标准三。
  └────────────────────────────────────────────────────────────────

  ┌─ W3 拆分表（估值，供续接）────────────────────────────────────
  │ W3a（本波）：上游闭环 2 件（43 HOL → 约 60-90 Lean）✔
  │ W3b：CASE 1 块（`betwn (findFace L y) y z = []` 支；HOL 约 320 行）
  │      内含引擎：parts 的 FST∘HD 包含（GSUBGOAL#1）/ 提 finer part
  │      （#3）/ map Last 单射（#4）/ 面内 (FST∘HD) 单射（#8）——估 450-600，
  │      须再拆 W3b-i（#1+#3）/ W3b-ii（#4+#8）。
  │ W3c：CASE 2 块（同形再走一遍，HOL 约 380 行）+ 总装（cat_uniq +
  │      W2bE 两件）——估 500-650。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件 `aq8w3_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W2bE
import Kepler.Text.TameSpine.JcajyduAqSnd
import Kepler.Text.TameSpine.JcajyduAqLeaf8W1a
import Kepler.Text.TameSpine.JcajyduAqSplit1D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)

/-! ## §1 `betwn_not_in_fst_rtrans`（AQ1.hl:1316，W3 唯一缺件） -/

/-- **HOL `betwn_not_in_fst_rtrans`**（AQ1.hl:1316）：
`MEM d (betwn f (ytrans 0) (ztrans 0)) ∧ find_face L x = f ⇒
~(MEM (FST d) (map FST r))`——窗口 darts 的首点不进 `r` 的首点表。

HOL 证体只一步：`betwn_not_in_fst_faltten`（= Lean `windowFstNotMemNFlatten`，
Split1D:87）把首点排除从 `flatten N` 推到 `r`（`MEM r N`，marked_list 合取）。
本件按具体窗口 `findFaceDarts L x` 实例（HOL 的 `f` 参数即此实例的别名）。 -/
theorem aq8w3_betwnNotInFstRtrans (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {d : ℕ × ℕ} (hd : d ∈ between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)) :
    d.1 ∉ r.map Prod.fst := by
  intro hmem
  -- 窗口面 = l'y 所在面（`mem_find_face_imp_faces_eq`）
  have hpp := pplhuljV0 L hL hgn hunL hm hf
  have hface : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
    aq10_memFindFaceImpFacesEq hL.1 hpp.1
  have hd' : d ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x) := by
    rw [hface]
    exact hd
  obtain ⟨a, ha, hafst⟩ := List.mem_map.mp hmem
  exact windowFstNotMemNFlatten L hL hgn hunL hm hf hd'
    (List.mem_map.mpr ⟨a, List.mem_flatten.mpr ⟨r, hm.1.2.2.1, ha⟩, hafst⟩)

/-! ## §2 巨头的「y 非新面末元」引擎（AQ8.hl:924-943） -/

/-- **HOL `~(next_el f y = f_list L (e_list y))`**（AQ8.hl:924，20 行）：
`f = find_face L y` 时 `next_el f y = f_list L y`（定义式），若与
`f_list L (e_list y)` 相等则 `F_LIST_INJ` 给 `y = e_list y`，撞 edge 非退化。
（HOL 证体 = `f_list_power_next_el` 一步 + `F_LIST_INJ` + e 非退化。） -/
theorem aq8w3_yNextNeFListEList (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    nextEl (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      ≠ fList L (eList (lYSpine L r x)) := by
  have hy : lYSpine L r x ∈ listOfDarts L := memYtransListOfDarts L hL hgn hm hf
  have he : eList (lYSpine L r x) ∈ listOfDarts L := goodListEList hL hy
  intro h
  exact absurd ((fListInjDarts L hL hy he).mp h).symm
    (isRestrictedEListNondeg hL hm.1.1 hy)

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：两件全 ⊆ 标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq8w3_betwnNotInFstRtrans
#print axioms Kepler.Text.TameSpine.aq8w3_yNextNeFListEList
