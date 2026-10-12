/-
  Kepler.Text.TameSpine.TameList3 — B1 Tame_list 地基批 3：indexf / split_at / betwn 家族
  （tamespine-port-plan §4 批次表 B1 行，计划现位于 `docs/projects/tamespine-port-plan.md`；
  接续批 2 = TameList2.lean :23-1466 general list processing 块，commit a964c47d）。

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353，
  `text_formalization/tame/tame_list.hl:1469-2934`——indexf 定义起、`unadj`
  new_recursive_definition（:2936，hideDups/nextVertices 新定义块）之前的全部
  循环索引与切分机器；批 2 报告指路的 indexf/split_at/betwn 家族整块）：

  - `indexf` 定义 :1469 与其基础件 :1473-1690（空表/越界 junk、≤/</refl/
    零点单射性/antisym(+wlog)/cond 三段形、add_left/add_right/add_sum）；
  - sizel 基础两件 :1497/:1692（sizel0、sizel_gt_1）；
  - rotate 群 :1714-1756（`rot n` ↦ `List.rotate n`，复用批 2 idxOfRotateOne）；
  - next_el↔indexf 往返 :1758-1918（indexf1/next_el_indexf/next_eln_indexf/
    indexf_n，HOL POWER ↦ `Function.iterate`）；
  - nextElem/rcons/rot 群 :1919-2034（`rcons` ↦ `l ++ [a]`）；
  - nextVertex/vertices_set2 桥 :2027-2064（:2036 fgraph_makeFaceFinal 已由
    批 2 fgraphMakeFaceFinal 覆盖，跳过记账）；
  - split_at_rec 家族 :2065-2305（mem_fst/snd、acc 群、antirefl/antisym、
    hd、take/drop 刻画）；
  - betwn 家族 :2306-2918（betwn_mem、mem_drop/take_index、take/drop 交换律、
    betwn_take_drop 显式形、size_betwn、not_betwn1/2、indexl_betwn、
    indexf_betwn(_eq)、betwn_cases、indexf_add_betwn、next_el_refl、
    indexf_prev）；
  - option 杂件 :2920（:2928 some_the 与批 2 theSome 重复，跳过记账）。

  载体折算（沿批 1/2 约定）：`sizel` ↦ `List.length`、`indexl` ↦ `List.idxOf`
  （越界 junk = length，TameLp 已审计与 HOL indexl 约定一致）、`next_el` ↦
  `Kepler.Assembly.nextEl`、`nextElem` ↦ `Kepler.Graphs.nextElem`、
  `nextVertex` ↦ `Face.nextVertex`、`split_at_rec`/`split_at` ↦
  `Kepler.Graphs.splitAtRec`/`splitAt`、`betwn` ↦ `Kepler.Graphs.between`、
  `take`/`dropl` ↦ `List.take`/`List.drop`、`uniq` ↦ `List.Nodup`、
  `rot n` ↦ `List.rotate n`、`rcons s a` ↦ `s ++ [a]`、`POWER n` ↦
  `Function.iterate n`、`HD` ↦ `List.head!`（配 `[Inhabited α]` 载体伪参）。

  批内记账：
  - **Isabelle 车道同构件**（ListAuxLemmas 先行，本批以 HOL 原句桥引落地）：
    fst/snd_split_at_acc(:2202/:2100) = splitAtRec_eq_append 的分量形；
    betwn_mem(:2306) = inbetween_inset；split_at 的 between 分解用 between_def。
  - **诚实收窄/强化记账**：
    - fst/snd_split_at_take/drop(:2257/:2273/:2285/:2294)：HOL 的 take/drop
      刻画按 Seq2.index_take/index_drop_le 语义在 `u ∈ f` 下叙述；Lean 载体
      `idxOf` 的越界约定（= length）使无前提形亦成立（`u ∉ f` 时 splitAtRec
      退化为 `(b ++ f, [])`，与 take length/drop length 逐字一致）——本批按
      无前提一般形落地，为诚实强化；
    - betwn_take_drop(:2433) 的第一段取值 `PRE (indexl v f - indexl u f)` 按
      `indexl v f - (indexl u f + 1)` 逐字换算（Nat 减法，defeq）；
    - mem_take_index(:2378)：Mathlib `List.mem_take_iff_idxOf_lt` 无 Nodup
      即真，本批桥引（HOL 原句 uniq 前提冗余，签名按原句携带、记账）；
    - vertices_set2_makeFaceFinal(:2056)：HOL 断言 set_of_list (vertices_graph)
      层相等；Lean 侧直接落列表等式 `(makeFaceFinal f g).vertices = g.vertices`
      （集合形为逐点推论，无 junk 语义损失）；
    - :1919 nextElem_nonmem_rcons 的 HOL 量化有笔误（`a` 自由），本批补
      `∀ a` 全称化；
    - :1919/:2087 前身 nextElemOfNotMem/nextElemNonmemRcons：HOL nextElem 按
      Leibniz 等式递归，载体 BEq 须配 LawfulBEq 方可保陈述为真（否则伪 BEq
      可在 `x ∉ s` 下误命中），本批按载体约定补 `[LawfulBEq α]`——诚实强化；
    - betwn_cases(:2744) 在 HOL 中先于 indexf_betwn_eq(:2799) 且不依赖后者，
      本批按原序以 betwn_take_drop + take/drop 位置算术直证（前稿经
      indexfBetwnEq 桥引与 indexf_betwn_eq 成环，已理顺）；
    - :2501 betwn_hd 在 HOL 源中整段注释（未证），按源跳过；
    - :2928 some_the 与 tame_list.hl:33 重复且批 2 theSome 已落地（getD 默认值
      约定吸收 `the` 的部分性），跳过。
  - **NEEDS（战术位记账）**：indexf_rot/indexfRotn 的 rotate 位移计算依赖
    `idxOf` 在 `rotate 1` 下的显式位移，本批以批 2 idxOfRotateOne（非 head 位）
    + head 位特例辅件 idxOfHeadRotateOne/idxOfHead 闭合，无 sorry、无外部债；
    其余各件均为纯直译，零 NEEDS。

  红线遵守：本模块零 sorry、零既有文件触碰、零 git 写操作。
-/
import Kepler.Assembly
import Kepler.Text.TameSpine.TameList2

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl)
open Kepler.Graphs (splitAtRec splitAt between nextElem makeFaceFinal between_def
  inbetween_inset splitAt_in_fst splitAtRec_eq_append nextElem_cons nextElem_cons_nil)

variable {α : Type*}

/-! ### §0 载体：HOL `indexf`（tame_list.hl:1469）

HOL 原文：`indexf (x:A) y s = if (MEM x s /\ MEM y s) then
(indexl y s + (sizel s - indexl x s)) MOD sizel s else sizel s`。
折算：`indexl` ↦ `List.idxOf`、`sizel` ↦ `List.length`（junk 约定一致）。 -/

/-- HOL `indexf`（tame_list.hl:1469）逐句镜像。 -/
def indexf [BEq α] [LawfulBEq α] (x y : α) (s : List α) : ℕ :=
  if x ∈ s ∧ y ∈ s then (s.idxOf y + (s.length - s.idxOf x)) % s.length else s.length

/-- 辅件（Seq.index_mem 的 idxOf 形）。 -/
private theorem idxOfMem [BEq α] [LawfulBEq α] {s : List α} {x : α} (hx : x ∈ s) :
    s.idxOf x < s.length :=
  List.idxOf_lt_length_iff.mpr hx

/-- 辅件：`(j + (n - i)) % n = 0` 且 `i, j < n` 蕴含 `j = i`
（indexf 零点的位置单射性核心，tame_list.hl:1542 的算术骨架）。 -/
private theorem modAddSubEqZero {n i j : ℕ} (hi : i < n) (hj : j < n)
    (h : (j + (n - i)) % n = 0) : j = i := by
  rcases Nat.lt_or_ge j i with hlt | hge
  · have hsum : j + (n - i) < n := by omega
    rw [Nat.mod_eq_of_lt hsum] at h
    omega
  · have hsplit : j + (n - i) = n + (j - i) := by omega
    rw [hsplit, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : j - i < n)] at h
    omega

/-! ### §1 indexf 基础件（tame_list.hl:1473-1690） -/

/-- HOL `indexf0` 第一件（tame_list.hl:1473 `indexf x y [] = 0`）。 -/
theorem indexfEmpty [BEq α] [LawfulBEq α] (x y : α) : indexf x y ([] : List α) = 0 := by
  simp [indexf]

/-- HOL `indexf_mem1`（tame_list.hl:1481 `~MEM x s ==> indexf x y s = sizel s`）。 -/
theorem indexfOfNotMemLeft [BEq α] [LawfulBEq α] {x y : α} {s : List α} (h : x ∉ s) :
    indexf x y s = s.length := by
  simp [indexf, h]

/-- HOL `indexf2`（tame_list.hl:1489 `~MEM y s ==> indexf x y s = sizel s`）。 -/
theorem indexfOfNotMemRight [BEq α] [LawfulBEq α] {x y : α} {s : List α} (h : y ∉ s) :
    indexf x y s = s.length := by
  simp [indexf, h]

/-- HOL `sizel0`（tame_list.hl:1497
`sizel s = 0 <=> ~(?x. MEM x s)`；`sizel` ↦ `List.length`）。 -/
theorem sizelZeroIff {s : List α} : s.length = 0 ↔ ∀ x, x ∉ s := by
  constructor
  · intro h x hx
    rw [List.length_eq_zero_iff.mp h] at hx
    simpa using hx
  · intro h
    cases s with
    | nil => rfl
    | cons a t => exact absurd List.mem_cons_self (h a)

/-- HOL `indexf_le_sizel`（tame_list.hl:1506 `indexf x y s <= sizel s`）。 -/
theorem indexfLeSizel [BEq α] [LawfulBEq α] (x y : α) (s : List α) :
    indexf x y s ≤ s.length := by
  rw [indexf]
  split
  · rename_i hm
    have hx : x ∈ s := hm.1
    by_cases h0 : s.length = 0
    · exact absurd hx (sizelZeroIff.mp h0 x)
    · exact Nat.le_of_lt (Nat.mod_lt _ (by omega))
  · exact Nat.le_refl _

/-- HOL `indexf_lt_sizel`（tame_list.hl:1518
`MEM x s /\ MEM y s ==> indexf x y s < sizel s`）。 -/
theorem indexfLtSizel [BEq α] [LawfulBEq α] {x y : α} {s : List α}
    (hx : x ∈ s) (hy : y ∈ s) : indexf x y s < s.length := by
  have h0 : 0 < s.length := by
    by_contra hc
    exact absurd hx (sizelZeroIff.mp (by omega) x)
  rw [indexf, if_pos ⟨hx, hy⟩]
  exact Nat.mod_lt _ h0

/-- HOL `indexf_refl`（tame_list.hl:1530 `MEM x s ==> indexf x x s = 0`）。 -/
theorem indexfRefl [BEq α] [LawfulBEq α] {x : α} {s : List α} (hx : x ∈ s) :
    indexf x x s = 0 := by
  have hi := idxOfMem hx
  have heq : s.idxOf x + (s.length - s.idxOf x) = s.length := by omega
  rw [indexf, if_pos ⟨hx, hx⟩, heq, Nat.mod_self]

/-- HOL 第二个 `indexf0`（tame_list.hl:1542
`MEM x s /\ MEM y s /\ indexf x y s = 0 ==> (x = y)`；HOL 两件同名，
Lean 按 indexfEmpty/indexfZeroEq 分名）。 -/
theorem indexfZeroEq [BEq α] [LawfulBEq α] {x y : α} {s : List α}
    (hx : x ∈ s) (hy : y ∈ s) (h0 : indexf x y s = 0) : x = y := by
  have hi := idxOfMem hx
  have hj := idxOfMem hy
  rw [indexf, if_pos ⟨hx, hy⟩] at h0
  have hpos : s.idxOf y = s.idxOf x := modAddSubEqZero hi hj h0
  exact (idxUniq hy hx hpos).symm

/-- HOL `indexf_antisym_wlog`（tame_list.hl:1576
`MEM x s /\ MEM y s /\ ~(x = y) /\ indexl x s < indexl y s
==> indexf x y s + indexf y x s = sizel s`）。 -/
theorem indexfAntisymWlog [BEq α] [LawfulBEq α] {x y : α} {s : List α}
    (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) (hlt : s.idxOf x < s.idxOf y) :
    indexf x y s + indexf y x s = s.length := by
  have hi := idxOfMem hx
  have hj := idxOfMem hy
  have e1 : (s.idxOf y + (s.length - s.idxOf x)) % s.length = s.idxOf y - s.idxOf x := by
    have h1 : s.idxOf y + (s.length - s.idxOf x) = s.length + (s.idxOf y - s.idxOf x) := by
      omega
    rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have e2 : (s.idxOf x + (s.length - s.idxOf y)) % s.length
      = s.idxOf x + (s.length - s.idxOf y) :=
    Nat.mod_eq_of_lt (by omega)
  rw [indexf, indexf, if_pos ⟨hx, hy⟩, if_pos ⟨hy, hx⟩, e1, e2]
  omega

/-- HOL `indexf_antisym`（tame_list.hl:1601
`MEM x s /\ MEM y s /\ ~(x = y) ==> indexf x y s + indexf y x s = sizel s`）。 -/
theorem indexfAntisym [BEq α] [LawfulBEq α] {x y : α} {s : List α}
    (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
    indexf x y s + indexf y x s = s.length := by
  rcases Nat.lt_trichotomy (s.idxOf x) (s.idxOf y) with h | h | h
  · exact indexfAntisymWlog hx hy hne h
  · exact absurd (idxUniq hx hy h) hne
  · linarith [indexfAntisymWlog hy hx (fun e => hne e.symm) h]

/-- HOL `indexf_cond`（tame_list.hl:1616
`MEM x s /\ MEM y s ==> indexf x y s = if (indexl x s <= indexl y s)
then indexl y s - indexl x s else indexl y s + (sizel s - indexl x s)`）。 -/
theorem indexfCond [BEq α] [LawfulBEq α] {x y : α} {s : List α} (hx : x ∈ s) (hy : y ∈ s) :
    indexf x y s =
      if s.idxOf x ≤ s.idxOf y then s.idxOf y - s.idxOf x
      else s.idxOf y + (s.length - s.idxOf x) := by
  have hi := idxOfMem hx
  have hj := idxOfMem hy
  rw [indexf, if_pos ⟨hx, hy⟩]
  split
  · rename_i hle
    have h1 : s.idxOf y + (s.length - s.idxOf x) = s.length + (s.idxOf y - s.idxOf x) := by
      omega
    rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- HOL `indexf_add_left`（tame_list.hl:1638
`MEM x s /\ MEM y s /\ MEM z s /\ indexf x y s <= indexf x z s
==> indexf x y s + indexf y z s = indexf x z s`）。 -/
theorem indexfAddLeft [BEq α] [LawfulBEq α] {x y z : α} {s : List α}
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) (h : indexf x y s ≤ indexf x z s) :
    indexf x y s + indexf y z s = indexf x z s := by
  have hi := idxOfMem hx
  have hj := idxOfMem hy
  have hk := idxOfMem hz
  rw [indexfCond hx hy, indexfCond hx hz] at h
  rw [indexfCond hx hy, indexfCond hy hz, indexfCond hx hz]
  split at h <;> split at h <;> (repeat' split) <;> omega

/-- HOL `indexf_add_right`（tame_list.hl:1656
`MEM x s /\ MEM y s /\ MEM z s /\ indexf y z s <= indexf x z s
==> indexf x y s + indexf y z s = indexf x z s`）。 -/
theorem indexfAddRight [BEq α] [LawfulBEq α] {x y z : α} {s : List α}
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) (h : indexf y z s ≤ indexf x z s) :
    indexf x y s + indexf y z s = indexf x z s := by
  have hi := idxOfMem hx
  have hj := idxOfMem hy
  have hk := idxOfMem hz
  rw [indexfCond hy hz, indexfCond hx hz] at h
  rw [indexfCond hx hy, indexfCond hy hz, indexfCond hx hz]
  split at h <;> split at h <;> (repeat' split) <;> omega

/-- HOL `indexf_add_sum`（tame_list.hl:1674
`MEM x s /\ MEM y s /\ MEM z s /\ indexf x y s + indexf y z s < sizel s
==> indexf x y s + indexf y z s = indexf x z s`）。 -/
theorem indexfAddSum [BEq α] [LawfulBEq α] {x y z : α} {s : List α}
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) (h : indexf x y s + indexf y z s < s.length) :
    indexf x y s + indexf y z s = indexf x z s := by
  have hi := idxOfMem hx
  have hj := idxOfMem hy
  have hk := idxOfMem hz
  rw [indexfCond hx hy, indexfCond hy hz] at h
  rw [indexfCond hx hy, indexfCond hy hz, indexfCond hx hz]
  split at h <;> split at h <;> (repeat' split) <;> omega

/-- HOL `sizel_gt_1`（tame_list.hl:1692
`MEM x s /\ MEM y s /\ ~(x = y) ==> 1 < sizel s`）。 -/
theorem sizelGt1 [BEq α] [LawfulBEq α] {x y : α} {s : List α}
    (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) : 1 < s.length := by
  have hij : s.idxOf x ≠ s.idxOf y := fun e => hne (idxUniq hx hy e)
  have hi := idxOfMem hx
  have hj := idxOfMem hy
  omega

/-! ### §2 indexf 与 rotate（tame_list.hl:1714-1756）

`rot 1`/`rot n` ↦ `List.rotate 1`/`List.rotate n`；`idxOf` 的 rotate 1 位移
由批 2 idxOfRotateOne（无 Nodup 一般形，非 head 位）与 head 位特例辅件给出。 -/

/-- 辅件：head 的 idxOf 为 0（Seq2.index_head 的 idxOf 形）。 -/
private theorem idxOfHead [Inhabited α] [BEq α] [LawfulBEq α] {x : α} {s : List α}
    (hx : x ∈ s) (hhead : x = s.head!) : s.idxOf x = 0 := by
  cases s with
  | nil => cases hx
  | cons a t =>
    rw [List.head!_cons] at hhead
    subst hhead
    simp

/-- 辅件（Seq 层 `indexl (HD s) (rot 1 s) = sizel s - 1` 的 idxOf 形）：
Nodup 列表 rotate 1 后 head 落在末位。 -/
private theorem idxOfHeadRotateOne [Inhabited α] [BEq α] [LawfulBEq α] {x : α} {s : List α}
    (hnd : s.Nodup) (hx : x ∈ s) (hhead : x = s.head!) :
    (s.rotate 1).idxOf x = s.length - 1 := by
  cases s with
  | nil => cases hx
  | cons a t =>
    rw [List.head!_cons] at hhead
    subst hhead
    have hna : x ∉ t := (List.nodup_cons.mp hnd).1
    rw [List.rotate_cons_succ, List.rotate_zero, List.idxOf_append_of_notMem hna]
    simp

/-- HOL `indexf_rot`（tame_list.hl:1714
`MEM x s /\ MEM y s /\ uniq s ==> indexf x y s = indexf x y (rot 1 s)`）。 -/
theorem indexfRot [Inhabited α] [BEq α] [LawfulBEq α] {x y : α} {s : List α}
    (hx : x ∈ s) (hy : y ∈ s) (hnd : s.Nodup) :
    indexf x y s = indexf x y (s.rotate 1) := by
  by_cases hxy : x = y
  · subst hxy
    rw [indexfRefl hx, indexfRefl (List.mem_rotate.mpr hx)]
  · have hx1 : x ∈ s.rotate 1 := List.mem_rotate.mpr hx
    have hy1 : y ∈ s.rotate 1 := List.mem_rotate.mpr hy
    have hn1 : (s.rotate 1).length = s.length := List.length_rotate s 1
    have hi := idxOfMem hx
    have hj := idxOfMem hy
    have hi1 : (s.rotate 1).idxOf x < s.length := by rw [← hn1]; exact idxOfMem hx1
    have hj1 : (s.rotate 1).idxOf y < s.length := by rw [← hn1]; exact idxOfMem hy1
    rw [indexfCond hx hy, indexfCond hx1 hy1]
    by_cases hxh : x = s.head!
    · have hyh : y ≠ s.head! := fun e => hxy (hxh.trans e.symm)
      have hdx : (s.rotate 1).idxOf x = s.length - 1 := idxOfHeadRotateOne hnd hx hxh
      have hdy : (s.rotate 1).idxOf y + 1 = s.idxOf y := idxOfRotateOne hy hyh
      have hix : s.idxOf x = 0 := idxOfHead hx hxh
      split <;> split <;> omega
    · by_cases hyh : y = s.head!
      · have hdx : (s.rotate 1).idxOf x + 1 = s.idxOf x := idxOfRotateOne hx hxh
        have hdy : (s.rotate 1).idxOf y = s.length - 1 := idxOfHeadRotateOne hnd hy hyh
        have hinz : s.idxOf x ≠ 0 := by
          intro e; exact hxh (idxZero hx e)
        have hiy : s.idxOf y = 0 := idxOfHead hy hyh
        split <;> split <;> omega
      · have hdx : (s.rotate 1).idxOf x + 1 = s.idxOf x := idxOfRotateOne hx hxh
        have hdy : (s.rotate 1).idxOf y + 1 = s.idxOf y := idxOfRotateOne hy hyh
        split <;> split <;> omega

/-- HOL `indexf_rotn`（tame_list.hl:1738
`MEM x s /\ MEM y s /\ uniq s /\ n <= sizel s
==> indexf x y s = indexf x y (rot n s)`）。 -/
theorem indexfRotn [Inhabited α] [BEq α] [LawfulBEq α] {n : ℕ} {x y : α} {s : List α}
    (hx : x ∈ s) (hy : y ∈ s) (hnd : s.Nodup) (hle : n ≤ s.length) :
    indexf x y s = indexf x y (s.rotate n) := by
  induction n with
  | zero => rw [List.rotate_zero]
  | succ m ih =>
    have hmle : m ≤ s.length := Nat.le_trans (Nat.le_succ m) hle
    have h0 : indexf x y s = indexf x y (s.rotate m) := ih hmle
    have h1 : s.rotate (m + 1) = (s.rotate m).rotate 1 :=
      (List.rotate_rotate s m 1).symm
    rw [h0, h1]
    exact indexfRot (List.mem_rotate.mpr hx) (List.mem_rotate.mpr hy)
      (List.nodup_rotate.mpr hnd)

/-! ### §3 next_el ↔ indexf 往返（tame_list.hl:1758-1918）

`next_el` ↦ `Kepler.Assembly.nextEl`；HOL POWER ↦ `Function.iterate`。 -/

/-- 辅件：`next_el` 在非末位的取值形（Seq2.next_el 展开的一半）。 -/
private theorem nextElOfLt [BEq α] {s : List α} {x : α} (h : s.idxOf x + 1 < s.length) :
    nextEl s x = s.getD (s.idxOf x + 1) x :=
  if_neg (by omega : ¬(s.idxOf x = s.length - 1))

/-- 辅件：`next_el` 在末位的取值形。 -/
private theorem nextElOfLast [BEq α] {s : List α} {x : α} (h : s.idxOf x = s.length - 1) :
    nextEl s x = s.headD x :=
  if_pos h

/-- 辅件：`next_el` 不出表（Seq.mem_nth 链的起点）。 -/
private theorem memNextEl [BEq α] [LawfulBEq α] {s : List α} {x : α} (hx : x ∈ s) :
    nextEl s x ∈ s := by
  have hi := idxOfMem hx
  by_cases hlast : s.idxOf x = s.length - 1
  · rw [nextElOfLast hlast]
    cases s with
    | nil => cases hx
    | cons a t =>
      simp only [List.headD_cons]
      exact List.mem_cons_self
  · rw [nextElOfLt (by omega), List.getD_eq_getElem _ _ (by omega)]
    exact List.mem_iff_getElem.mpr ⟨s.idxOf x + 1, by omega, rfl⟩

/-- 辅件：`next_el` 的迭代不出表（Seq2.next_el_power 的成员半边）。 -/
private theorem memNextElIterate [BEq α] [LawfulBEq α] {s : List α} {x : α} (hx : x ∈ s) :
    ∀ m : ℕ, (nextEl s)^[m] x ∈ s := by
  intro m
  induction m with
  | zero => exact hx
  | succ m ih => rw [Function.iterate_succ_apply']; exact memNextEl ih

/-- 辅件：cons 表的成员首项（mem_cons_self 的显式化）。 -/
private theorem memConsSelf {a : α} {t : List α} : a ∈ a :: t := List.mem_cons_self

/-- HOL `indexf1`（tame_list.hl:1758
`MEM x s /\ MEM y s /\ uniq s /\ indexf x y s = 1 ==> next_el s x = y`）。 -/
theorem indexfOne [BEq α] [LawfulBEq α] {x y : α} {s : List α}
    (hx : x ∈ s) (hy : y ∈ s) (hnd : s.Nodup) (h1 : indexf x y s = 1) :
    nextEl s x = y := by
  have hi := idxOfMem hx
  have hj := idxOfMem hy
  rw [indexfCond hx hy] at h1
  by_cases hlt : s.idxOf x + 1 < s.length
  · rw [nextElOfLt hlt]
    split at h1
    · have hj' : s.idxOf y = s.idxOf x + 1 := by omega
      rw [← hj', List.getD_eq_getElem _ _ hj]
      exact List.getElem_idxOf hj
    · exfalso; omega
  · have hlast : s.idxOf x = s.length - 1 := by omega
    rw [nextElOfLast hlast]
    obtain ⟨a, t, rfl⟩ :=
      List.exists_cons_of_ne_nil
        (show s ≠ [] by intro hc; subst hc; exact List.not_mem_nil hx)
    split at h1
    · exfalso; omega
    · simp only [List.headD_cons]
      have hj0 : (a :: t).idxOf y = 0 := by omega
      have ha0 : (a :: t).idxOf a = 0 := by simp
      exact idxUniq memConsSelf hy (ha0.trans hj0.symm)

/-- HOL `next_el_indexf`（tame_list.hl:1796
`MEM x s /\ MEM y s /\ uniq s /\ next_el s x = y /\ 1 < sizel s
==> indexf x y s = 1`）。 -/
theorem nextElIndexf [BEq α] [LawfulBEq α] {x y : α} {s : List α}
    (hx : x ∈ s) (hy : y ∈ s) (hnd : s.Nodup) (hny : nextEl s x = y)
    (hlt : 1 < s.length) : indexf x y s = 1 := by
  have hi := idxOfMem hx
  by_cases hlt2 : s.idxOf x + 1 < s.length
  · rw [nextElOfLt hlt2, List.getD_eq_getElem _ _ hlt2] at hny
    have hj : s.idxOf y = s.idxOf x + 1 := by
      have hidx := List.Nodup.idxOf_getElem hnd (s.idxOf x + 1) hlt2
      rw [← hny]
      exact hidx
    rw [indexfCond hx hy, if_pos (by omega)]
    omega
  · have hlast : s.idxOf x = s.length - 1 := by omega
    rw [nextElOfLast hlast] at hny
    obtain ⟨a, t, rfl⟩ :=
      List.exists_cons_of_ne_nil
        (show s ≠ [] by intro hc; subst hc; exact List.not_mem_nil hx)
    simp only [List.headD_cons] at hny
    have hj : (a :: t).idxOf y = 0 := by rw [← hny]; simp
    have hnle : ¬((a :: t).idxOf x ≤ (a :: t).idxOf y) := by omega
    rw [indexfCond hx hy, if_neg hnle]
    omega

/-- HOL `next_eln_indexf`（tame_list.hl:1840
`MEM x s /\ MEM y s /\ uniq s /\ (next_el s POWER n) x = y /\ n < sizel s
==> indexf x y s = n`）。 -/
theorem nextElnIndexf [BEq α] [LawfulBEq α] {m : ℕ} {x y : α} {s : List α}
    (hx : x ∈ s) (hy : y ∈ s) (hnd : s.Nodup) (hp : (nextEl s)^[m] x = y)
    (hlt : m < s.length) : indexf x y s = m := by
  have key : ∀ (k : ℕ) (x' y' : α), x' ∈ s → y' ∈ s → (nextEl s)^[k] x' = y' →
      k < s.length → indexf x' y' s = k := by
    intro k
    induction k with
    | zero =>
      intro x' y' hx' hy' hp _
      rw [Function.iterate_zero_apply] at hp
      subst hp
      exact indexfRefl hy'
    | succ k ih =>
      intro x' y' hx' hy' hp hlt'
      rw [Function.iterate_succ_apply'] at hp
      have hk : k < s.length := by omega
      have hym : (nextEl s)^[k] x' ∈ s := memNextElIterate hx' k
      have him : indexf x' ((nextEl s)^[k] x') s = k := ih x' _ hx' hym rfl hk
      have h1yn : indexf ((nextEl s)^[k] x') y' s = 1 :=
        nextElIndexf hym hy' hnd hp (by omega)
      have hsum := indexfAddSum hx' hym hy' (by omega)
      omega
  exact key m x y hx hy hp hlt

/-- HOL `indexf_n`（tame_list.hl:1876
`MEM x s /\ MEM y s /\ uniq s ==> ((next_el s) POWER (indexf x y s)) x = y`）。 -/
theorem indexfN [BEq α] [LawfulBEq α] {x y : α} {s : List α} (hx : x ∈ s) (hy : y ∈ s)
    (hnd : s.Nodup) : (nextEl s)^[indexf x y s] x = y := by
  have hlt := indexfLtSizel hx hy
  have key : ∀ m : ℕ, indexf x y s = m → (nextEl s)^[m] x = y := by
    intro m
    induction m with
    | zero =>
      intro h0
      have hxy : x = y := indexfZeroEq hx hy h0
      subst hxy
      rw [Function.iterate_zero_apply]
    | succ m ih =>
      intro hm
      have hmlt : m < s.length := by omega
      have hym : (nextEl s)^[m] x ∈ s := memNextElIterate hx m
      have him : indexf x ((nextEl s)^[m] x) s = m := nextElnIndexf hx hym hnd rfl hmlt
      have hle : indexf x ((nextEl s)^[m] x) s ≤ indexf x y s := by omega
      have hadd := indexfAddLeft hx hym hy hle
      rw [him, hm] at hadd
      have h1 : indexf ((nextEl s)^[m] x) y s = 1 := by omega
      have hny := indexfOne hym hy hnd h1
      rw [Function.iterate_succ_apply', hny]
  exact key _ rfl

/-! ### §4 nextElem / rcons / rot / nextVertex（tame_list.hl:1919-2064） -/

/-- 辅件：`nextElem` 的缺元退化形（nextElem 递归的补题）。 -/
private theorem nextElemOfNotMem [BEq α] [LawfulBEq α] {s : List α} {b x : α} (h : x ∉ s) :
    nextElem s b x = b := by
  induction s with
  | nil => rfl
  | cons a t ih =>
    have hxa : ¬((x == a) = true) := by
      intro hc
      rw [beq_iff_eq] at hc
      exact h (by rw [← hc]; exact memConsSelf)
    rw [nextElem_cons, if_neg hxa]
    exact ih (fun hm => h (List.mem_cons_of_mem _ hm))

/-- HOL `nextElem_nonmem_rcons`（tame_list.hl:1919
`~MEM x s ==> nextElem (rcons s a) u x = u`；HOL 量化笔误（`a` 自由）已按
`∀ a` 全称化记账；`rcons` ↦ `l ++ [a]`）。 -/
theorem nextElemNonmemRcons [BEq α] [LawfulBEq α] {s : List α} {x a u : α} (h : x ∉ s) :
    nextElem (s ++ [a]) u x = u := by
  induction s with
  | nil =>
    rw [List.nil_append, nextElem_cons_nil]
    split <;> rfl
  | cons b t ih =>
    rw [List.cons_append, nextElem_cons]
    have hxb : ¬((x == b) = true) := by
      intro hc
      rw [beq_iff_eq] at hc
      exact h (by rw [← hc]; exact memConsSelf)
    rw [if_neg hxb]
    exact ih (fun hm => h (List.mem_cons_of_mem _ hm))

/-- 辅件（Seq2.next_el_alt 的 nextElem 形）：`x ∈ s` 时 `nextElem s b x`
由位置 `idxOf x s` 逐点刻画——批内 nextElem 机器的枢纽。 -/
private theorem nextElemEqGetD [Inhabited α] [BEq α] [LawfulBEq α] {s : List α} {b x : α}
    (hx : x ∈ s) :
    nextElem s b x =
      if s.idxOf x + 1 < s.length then s.getD (s.idxOf x + 1) x else b := by
  induction s with
  | nil => cases hx
  | cons a t ih =>
    by_cases hxa : x = a
    · have h0 : (a :: t).idxOf x = 0 := by simp [hxa]
      rw [h0, nextElem_cons, if_pos (by simp [hxa])]
      cases t with
      | nil => simp
      | cons a' t' => simp
    · have hxt : x ∈ t := by
        rcases List.mem_cons.mp hx with he | he
        · exact absurd he hxa
        · exact he
      have hne : ¬((x == a) = true) := by
        intro hc
        rw [beq_iff_eq] at hc
        exact hxa hc
      have hio : (a :: t).idxOf x = t.idxOf x + 1 := List.idxOf_cons_ne t (Ne.symm hxa)
      rw [hio, nextElem_cons, if_neg hne, ih hxt, List.length_cons]
      by_cases hlt : t.idxOf x + 1 < t.length
      · rw [if_pos hlt, if_pos (by omega), List.getD_cons_succ]
      · rw [if_neg hlt, if_neg (by omega)]

/-- HOL `nextElem_rcons`（tame_list.hl:1932
`MEM x s ==> nextElem s h x = nextElem (rcons s h) u x`）。 -/
theorem nextElemRcons [Inhabited α] [BEq α] [LawfulBEq α] {s : List α} {a x u : α}
    (hmem : x ∈ s) : nextElem s a x = nextElem (s ++ [a]) u x := by
  have hi := idxOfMem hmem
  rw [nextElemEqGetD hmem, nextElemEqGetD (by simp [hmem] : x ∈ s ++ [a]),
    List.idxOf_append_of_mem hmem]
  have hlen : (s ++ [a]).length = s.length + 1 := by simp
  have hlt2 : s.idxOf x + 1 < (s ++ [a]).length := by omega
  by_cases hlt : s.idxOf x + 1 < s.length
  · rw [if_pos hlt2, if_pos hlt, List.getD_eq_getElem _ _ hlt2,
      List.getD_eq_getElem _ _ hlt]
    simp [hlt]
  · rw [if_neg hlt, if_pos hlt2]
    have hlast : s.idxOf x + 1 = s.length := by omega
    have h3 : s.length < (s ++ [a]).length := by simp
    have h4 : (s ++ [a]).getD s.length x = [a][0] := by
      rw [List.getD_eq_getElem _ _ h3, List.getElem_append h3]
      simp
    rw [hlast, h4]
    simp

/-- HOL `nextElem_rot`（tame_list.hl:1959
`MEM x s /\ ~(x = HD s) ==>
nextElem s (HD s) x = nextElem (rot 1 s) (HD (rot 1 s)) x`）。 -/
theorem nextElemRot [Inhabited α] [BEq α] [LawfulBEq α] {s : List α} {x : α}
    (hx : x ∈ s) (hne : x ≠ s.head!) :
    nextElem s s.head! x = nextElem (s.rotate 1) (s.rotate 1).head! x := by
  cases s with
  | nil => cases hx
  | cons a t =>
    have hne' : x ≠ a := by simpa using hne
    have hxt : x ∈ t := by
      rcases List.mem_cons.mp hx with he | he
      · exact absurd he hne'
      · exact he
    have hna : ¬((x == a) = true) := by
      intro hc
      rw [beq_iff_eq] at hc
      exact hne' hc
    rw [List.head!_cons, List.rotate_cons_succ, List.rotate_zero, nextElem_cons,
      if_neg hna]
    exact nextElemRcons hxt

/-- HOL `nextElem_next_el`（tame_list.hl:2019
`MEM x s ==> nextElem s (HD s) x = next_el s x`）。 -/
theorem nextElemNextElSpine [Inhabited α] [BEq α] [LawfulBEq α] {s : List α} {x : α}
    (hx : x ∈ s) : nextElem s s.head! x = nextEl s x := by
  have hi := idxOfMem hx
  rw [nextElemEqGetD hx]
  by_cases hlt : s.idxOf x + 1 < s.length
  · rw [if_pos hlt, nextElOfLt hlt, List.getD_eq_getElem _ _ hlt]
  · have hlast : s.idxOf x = s.length - 1 := by omega
    rw [if_neg (by omega), nextElOfLast hlast]
    cases s with
    | nil => cases hx
    | cons a t => rfl

/-- HOL `index_nextElem_next_el`（tame_list.hl:1974
`MEM x s /\ indexl x s = n ==> nextElem s (HD s) x = next_el s x`；
n 在载体层不出现（nextElem_next_el :2019 即足），按原句签名携带记账）。 -/
theorem indexNextElemNextEl [Inhabited α] [BEq α] [LawfulBEq α] {s : List α} {x : α}
    (hx : x ∈ s) (n : ℕ) (hn : s.idxOf x = n) : nextElem s s.head! x = nextEl s x :=
  nextElemNextElSpine hx

/-- HOL `nextVertex_next_el`（tame_list.hl:2027
`MEM x (FST f) ==> nextVertex f x = next_el (FST f) x`；
`nextVertex` ↦ `Face.nextVertex`，即 `nextElem vertices (HD vertices)`）。 -/
theorem nextVertexNextEl {f : Kepler.Graphs.Face} {x : Kepler.Graphs.Vertex}
    (hx : x ∈ f.vertices) : f.nextVertex x = nextEl f.vertices x :=
  nextElemNextElSpine hx

/-- HOL `vertices_set2_makeFaceFinal`（tame_list.hl:2056
`vertices_set2 (makeFaceFinal f' g) = vertices_set2 g`；
诚实强化：Lean 侧直接落列表等式——`vertices` 仅依赖 `countVertices`，
而 makeFaceFinal 保该字段。记账见文件头。 -/
theorem verticesSet2MakeFaceFinal (f : Kepler.Graphs.Face) (g : Kepler.Graphs.Graph) :
    (makeFaceFinal f g).vertices = g.vertices := rfl

/-! ### §5 split_at_rec 家族（tame_list.hl:2065-2305） -/

/-- 辅件：`split_at_rec` 在命中位的展开（`a == u` 为真）。 -/
private theorem splitAtRecSelf [BEq α] [LawfulBEq α] {u : α} {b f : List α} :
    splitAtRec u b (u :: f) = (b, f) := by
  rw [splitAtRec, if_pos (beq_self_eq_true u)]

/-- 辅件：`split_at_rec` 在非命中位的展开。 -/
private theorem splitAtRecNe [BEq α] [LawfulBEq α] {a u : α} {b f : List α}
    (h : ¬(a = u)) : splitAtRec u b (a :: f) = splitAtRec u (b ++ [a]) f := by
  rw [splitAtRec, if_neg (by
    intro hc
    rw [beq_iff_eq] at hc
    exact h hc)]

/-- HOL `split_at_mem_fst`（tame_list.hl:2065
`MEM v (FST (split_at_rec u b f)) ==> MEM v f \/ MEM v b`）。 -/
theorem splitAtRecMemFst [BEq α] [LawfulBEq α] {f : List α} {u v : α} {b : List α}
    (h : v ∈ (splitAtRec u b f).1) : v ∈ f ∨ v ∈ b := by
  revert h
  induction f generalizing b with
  | nil => intro h; exact Or.inr h
  | cons a t ih =>
    intro h
    by_cases ha : a = u
    · rw [ha] at h
      rw [splitAtRecSelf] at h
      exact Or.inr h
    · rw [splitAtRecNe ha] at h
      rcases ih (b := b ++ [a]) h with h' | h'
      · exact Or.inl (List.mem_cons_of_mem _ h')
      · rcases List.mem_append.mp h' with hm | hm
        · exact Or.inr hm
        · exact Or.inl (by rw [List.mem_singleton.mp hm]; exact List.mem_cons_self)

/-- HOL `snd_split_at_acc`（tame_list.hl:2100
`SND (split_at_rec u b f) = SND (split_at_rec u [] f)`）。
与 ListAuxLemmas.splitAtRec_eq_append 同构（Isabelle 车道先行件），记账。 -/
theorem sndSplitAtAcc [BEq α] [LawfulBEq α] (f : List α) (u : α) (b : List α) :
    (splitAtRec u b f).2 = (splitAtRec u [] f).2 := by
  induction f generalizing b with
  | nil => rfl
  | cons a t ih =>
    by_cases ha : a = u
    · subst ha
      simp only [splitAtRecSelf]
    · rw [splitAtRecNe ha, splitAtRecNe ha, List.nil_append,
        ih (b := b ++ [a]), ih (b := [a])]

/-- 辅件：`snd_split_at_acc` 后的 `b = []` 特形（split_at_mem_snd 的归纳载体）。 -/
private theorem memSndSplitAtRecNil [BEq α] [LawfulBEq α] {f : List α} {u v : α} :
    v ∈ (splitAtRec u [] f).2 → v ∈ f := by
  induction f with
  | nil => intro h; simp [splitAtRec] at h
  | cons a t ih =>
    intro h
    by_cases ha : a = u
    · rw [ha, splitAtRecSelf] at h
      exact List.mem_cons_of_mem _ h
    · rw [splitAtRecNe ha, List.nil_append] at h
      rw [sndSplitAtAcc t u [a]] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- HOL `split_at_mem_snd`（tame_list.hl:2135
`MEM v (SND (split_at_rec u b f)) ==> MEM v f`）。 -/
theorem splitAtRecMemSnd [BEq α] [LawfulBEq α] {f : List α} {u v : α} {b : List α}
    (h : v ∈ (splitAtRec u b f).2) : v ∈ f := by
  rw [sndSplitAtAcc f u b] at h
  exact memSndSplitAtRecNil h

/-- HOL `split_at_acc_fst`（tame_list.hl:2152
`MEM v b ==> MEM v (FST (split_at_rec u b f))`）。 -/
theorem splitAtRecAccFst [BEq α] [LawfulBEq α] {f : List α} {u v : α} {b : List α}
    (hv : v ∈ b) : v ∈ (splitAtRec u b f).1 := by
  induction f generalizing b with
  | nil => simpa [splitAtRec] using hv
  | cons a t ih =>
    by_cases ha : a = u
    · rw [ha, splitAtRecSelf]
      simpa using hv
    · rw [splitAtRecNe ha]
      exact ih (b := b ++ [a]) (by simp [hv])

/-- HOL `split_at_both`（tame_list.hl:2164
`MEM v f /\ (v = u ==> MEM v b) ==>
MEM v (FST (split_at_rec u b f)) \/ MEM v (SND (split_at_rec u b f))`）。 -/
theorem splitAtRecBoth [BEq α] [LawfulBEq α] {f : List α} {u v : α} {b : List α}
    (hv : v ∈ f) (h : v = u → v ∈ b) :
    v ∈ (splitAtRec u b f).1 ∨ v ∈ (splitAtRec u b f).2 := by
  revert h
  induction f generalizing b with
  | nil => intro h; cases hv
  | cons a t ih =>
    intro h
    by_cases ha : a = u
    · rw [ha] at hv ⊢
      rw [splitAtRecSelf]
      rcases List.mem_cons.mp hv with he | hvt
      · exact Or.inl (h he)
      · exact Or.inr hvt
    · rw [splitAtRecNe ha]
      rcases List.mem_cons.mp hv with he | hvt
      · exact Or.inl (splitAtRecAccFst (u := u) (b := b ++ [a]) (f := t)
          (by simp [he]))
      · exact ih (b := b ++ [a]) hvt (fun he => List.mem_append.mpr (Or.inl (h he)))

/-- HOL `fst_split_at_acc`（tame_list.hl:2202
`APPEND b (FST (split_at_rec u [] f)) = FST (split_at_rec u b f)`）。
与 ListAuxLemmas.splitAtRec_eq_append 同构（Isabelle 车道先行件），记账。 -/
theorem fstSplitAtAcc [BEq α] [LawfulBEq α] (f : List α) (u : α) (b : List α) :
    b ++ (splitAtRec u [] f).1 = (splitAtRec u b f).1 := by
  have h := splitAtRec_eq_append (c := u) (bs := b) (vs := f)
  rw [h]
  rfl

/-- HOL `split_at_fst_antirefl`（tame_list.hl:2215
`MEM u (FST (split_at_rec u b f)) ==> MEM u b`）。 -/
theorem splitAtRecFstAntirefl [BEq α] [LawfulBEq α] {f : List α} {u : α} {b : List α}
    (h : u ∈ (splitAtRec u b f).1) : u ∈ b := by
  induction f generalizing b with
  | nil => simpa [splitAtRec] using h
  | cons a t ih =>
    by_cases ha : a = u
    · rw [ha, splitAtRecSelf] at h
      simpa using h
    · rw [splitAtRecNe ha] at h
      have h' := ih (b := b ++ [a]) h
      rcases List.mem_append.mp h' with hm | hm
      · exact hm
      · exact absurd (List.mem_singleton.mp hm).symm ha

/-- HOL `split_at_snd_antirefl`（tame_list.hl:2226
`uniq f ==> ~(MEM u (SND (split_at_rec u b f)))`）。 -/
theorem splitAtRecSndAntirefl [BEq α] [LawfulBEq α] {f : List α} {u : α} {b : List α}
    (hnd : f.Nodup) : u ∉ (splitAtRec u b f).2 := by
  induction f generalizing b with
  | nil => simp [splitAtRec]
  | cons a t ih =>
    by_cases ha : a = u
    · subst ha
      intro hm
      rw [splitAtRecSelf] at hm
      exact (List.nodup_cons.mp hnd).1 hm
    · rw [splitAtRecNe ha]
      intro hm
      exact ih (b := b ++ [a]) (List.nodup_cons.mp hnd).2 hm

/-- HOL `snd_split_at_hd`（tame_list.hl:2249
`~(f = []) ==> SND (split_at_rec (HD f) b f) = TL f`）。 -/
theorem sndSplitAtHd [Inhabited α] [BEq α] [LawfulBEq α] {f : List α} {b : List α}
    (hf : f ≠ []) : (splitAtRec f.head! b f).2 = f.tail := by
  cases f with
  | nil => exact absurd rfl hf
  | cons a t =>
    show (splitAtRec a b (a :: t)).2 = t
    rw [splitAtRecSelf]

/-- HOL `fst_split_at_take`（tame_list.hl:2257
`FST (split_at_rec u b f) = APPEND b (take (indexl u f) f)`；
无前提一般形——诚实强化记账见文件头。 -/
theorem fstSplitAtTake [BEq α] [LawfulBEq α] (f : List α) (u : α) (b : List α) :
    (splitAtRec u b f).1 = b ++ f.take (f.idxOf u) := by
  induction f generalizing b with
  | nil => simp [splitAtRec]
  | cons a t ih =>
    by_cases ha : a = u
    · rw [ha]
      have hio : (u :: t).idxOf u = 0 := by simp
      rw [splitAtRecSelf, hio, List.take_zero, List.append_nil]
    · have hau : ¬(a == u) := by
        intro hc
        rw [beq_iff_eq] at hc
        exact ha hc
      have hio : (a :: t).idxOf u = t.idxOf u + 1 := by simp [ha]
      rw [splitAtRecNe ha, hio, ih (b := b ++ [a]), List.take_cons, List.append_assoc]
      <;> first | rfl | omega

/-- HOL `snd_split_at_drop`（tame_list.hl:2273
`SND (split_at_rec u b f) = dropl (SUC (indexl u f)) f`；
无前提一般形——诚实强化记账见文件头。 -/
theorem sndSplitAtDrop [BEq α] [LawfulBEq α] (f : List α) (u : α) (b : List α) :
    (splitAtRec u b f).2 = f.drop (f.idxOf u + 1) := by
  induction f generalizing b with
  | nil => simp [splitAtRec]
  | cons a t ih =>
    by_cases ha : a = u
    · rw [ha]
      have hio : (u :: t).idxOf u = 0 := by simp
      rw [splitAtRecSelf, hio]
      rfl
    · have hio : (a :: t).idxOf u = t.idxOf u + 1 := by simp [ha]
      rw [splitAtRecNe ha, hio, ih (b := b ++ [a]), List.drop_cons]
      <;> first | rfl | omega

/-- HOL `split_at_take_drop`（tame_list.hl:2285
`split_at_rec u b f = (APPEND b (take (indexl u f) f), dropl (SUC (indexl u f)) f)`）。 -/
theorem splitAtRecTakeDropPair [BEq α] [LawfulBEq α] (f : List α) (u : α) (b : List α) :
    splitAtRec u b f = (b ++ f.take (f.idxOf u), f.drop (f.idxOf u + 1)) :=
  Prod.ext (fstSplitAtTake f u b) (sndSplitAtDrop f u b)

/-- HOL `split_at_nil_take_drop`（tame_list.hl:2294
`split_at_rec u [] f = (take (indexl u f) f, dropl (SUC (indexl u f)) f)`）。 -/
theorem splitAtNilTakeDropPair [BEq α] [LawfulBEq α] (f : List α) (u : α) :
    splitAtRec u [] f = (f.take (f.idxOf u), f.drop (f.idxOf u + 1)) := by
  rw [splitAtRecTakeDropPair]
  rfl

/-- HOL `split_at` 层的 `split_at_mem_fst` 特形（b = []）。 -/
theorem splitAtMemFst [BEq α] [LawfulBEq α] {v u : α} {f : List α}
    (h : v ∈ (splitAt u f).1) : v ∈ f := by
  have h' := splitAtRecMemFst (u := u) (b := ([] : List α)) h
  rcases h' with h' | h'
  · exact h'
  · cases h'

/-! ### §6 take / drop 核心件（tame_list.hl:2326-2562） -/

/-- HOL `not_take_drop`（tame_list.hl:2723
`uniq s ==> ~(MEM x (take k s) /\ MEM x (dropl k s))`；提前至本节供
mem_drop_index 使用——HOL 用 Seq2.mem_imp_not_uniq_cat 承担同职责）。 -/
theorem notTakeDrop [BEq α] [LawfulBEq α] {s : List α} {x : α} {k : ℕ} (hnd : s.Nodup) :
    ¬(x ∈ s.take k ∧ x ∈ s.drop k) := by
  rintro ⟨h1, h2⟩
  have hs : x ∈ s := List.mem_of_mem_take h1
  have hi := idxOfMem hs
  have h1' : s.idxOf x < k := (List.mem_take_iff_idxOf_lt hs).mp h1
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp h2
  rw [List.getElem_drop] at he
  have hidx := List.Nodup.getElem_inj_iff hnd |>.mp
    ((List.getElem_idxOf hi).trans he.symm)
  omega

/-- HOL `mem_drop_index`（tame_list.hl:2326
`uniq s /\ MEM v s ==> (MEM v (dropl k s) <=> k <= indexl v s)`）。 -/
theorem memDropIndex [BEq α] [LawfulBEq α] {s : List α} {v : α} {k : ℕ}
    (hnd : s.Nodup) (hv : v ∈ s) : v ∈ s.drop k ↔ k ≤ s.idxOf v := by
  constructor
  · intro h
    by_contra hle
    have ht : v ∈ s.take k := (List.mem_take_iff_idxOf_lt hv).mpr (by omega)
    exact notTakeDrop hnd ⟨ht, h⟩
  · intro hle
    have hta : s = s.take k ++ s.drop k := (List.take_append_drop k s).symm
    have hvs : v ∈ s := hv
    rw [hta] at hv
    rcases List.mem_append.mp hv with ht | hd
    · exact absurd ((List.mem_take_iff_idxOf_lt hvs).mp ht) (by omega)
    · exact hd

/-- HOL `mem_take_index`（tame_list.hl:2378
`uniq s /\ MEM v s ==> (MEM v (take k s) <=> indexl v s < k)`）。
Mathlib `List.mem_take_iff_idxOf_lt` 无 Nodup 即真——前提冗余记账。 -/
theorem memTakeIndex [BEq α] [LawfulBEq α] {s : List α} {v : α} {k : ℕ}
    (hv : v ∈ s) : v ∈ s.take k ↔ s.idxOf v < k :=
  List.mem_take_iff_idxOf_lt hv

/-- HOL `take_take`（tame_list.hl:2409 `i <= j ==> take i (take j s) = take i s`）。 -/
theorem takeTake {s : List α} {i j : ℕ} (h : i ≤ j) :
    (s.take j).take i = s.take i := by
  rw [List.take_take, Nat.min_eq_left h]

/-- HOL `drop_drop`（tame_list.hl:2424
`dropl i (dropl j s) = dropl (i+j) s`）。 -/
theorem dropDrop (s : List α) (i j : ℕ) : (s.drop j).drop i = s.drop (i + j) := by
  rw [List.drop_drop, Nat.add_comm]

/-- HOL `drop_take_commute`（tame_list.hl:2465
`k <= n ==> dropl k (take n s) = take (n-k) (dropl k s)`）。 -/
theorem dropTakeCommute {s : List α} {k n : ℕ} (h : k ≤ n) :
    (s.take n).drop k = (s.drop k).take (n - k) :=
  List.drop_take

/-- HOL `take_drop_commute`（tame_list.hl:2490
`take n (dropl k s) = dropl k (take (n+k) s)`）。 -/
theorem takeDropCommute (s : List α) (k n : ℕ) :
    (s.drop k).take n = (s.take (n + k)).drop k := by
  symm
  rw [dropTakeCommute (by omega), Nat.add_sub_cancel]

/-- HOL `uniq_take`（tame_list.hl:2564 `uniq s ==> uniq (take k s)`）。 -/
theorem uniqTake {s : List α} {k : ℕ} (hnd : s.Nodup) : (s.take k).Nodup :=
  (List.take_sublist k s).nodup hnd

/-- HOL `uniq_drop`（tame_list.hl:2554 `uniq s ==> uniq (dropl k s)`）。 -/
theorem uniqDrop {s : List α} {k : ℕ} (hnd : s.Nodup) : (s.drop k).Nodup :=
  (List.drop_sublist k s).nodup hnd

/-- HOL `size_take_le`（tame_list.hl:2369 `sizel (take k s) <= sizel s`）。 -/
theorem sizeTakeLe (s : List α) (k : ℕ) : (s.take k).length ≤ s.length :=
  List.length_take_le' k s

/-- 辅件（Seq2.index_take 的 Nodup 形）：Nodup 列表前段的 idxOf 不变。 -/
private theorem idxOfTake [BEq α] [LawfulBEq α] {s : List α} {v : α} {i : ℕ}
    (hnd : s.Nodup) (hv : v ∈ s) (h : s.idxOf v < i) :
    (s.take i).idxOf v = s.idxOf v := by
  have hmem : v ∈ s.take i := (List.mem_take_iff_idxOf_lt hv).mpr h
  have hpl : (s.take i).idxOf v < (s.take i).length := List.idxOf_lt_length_iff.mpr hmem
  have h1 : (s.take i)[(s.take i).idxOf v] = v := List.getElem_idxOf hpl
  rw [List.getElem_take (j := i)] at h1
  exact List.Nodup.getElem_inj_iff hnd |>.mp
    (h1.trans (List.getElem_idxOf (idxOfMem hv)).symm)

/-- 辅件（Seq2.index_drop_le 的 Nodup 形）：Nodup 列表后段的 idxOf 平移。 -/
private theorem idxOfDrop [BEq α] [LawfulBEq α] {s : List α} {v : α} {k : ℕ}
    (hnd : s.Nodup) (hv : v ∈ s) (h : k ≤ s.idxOf v) :
    (s.drop k).idxOf v = s.idxOf v - k := by
  have hd : v ∈ s.drop k := (memDropIndex hnd hv).mpr h
  have hpl : (s.drop k).idxOf v < (s.drop k).length := List.idxOf_lt_length_iff.mpr hd
  have h1 : (s.drop k)[(s.drop k).idxOf v] = v := List.getElem_idxOf hpl
  rw [List.getElem_drop] at h1
  have heq := List.Nodup.getElem_inj_iff hnd |>.mp
    (h1.trans (List.getElem_idxOf (idxOfMem hv)).symm)
  omega

/-- HOL `split_at_snd_antisym`（tame_list.hl:2238
`uniq f /\ MEM v (SND (split_at_rec u b f)) /\ MEM u (SND (split_at_rec v b f))
==> F`；在 take/drop 刻画就绪后落位）。 -/
theorem splitAtRecSndAntisym [BEq α] [LawfulBEq α] {f : List α} {u v : α} {b : List α}
    (hnd : f.Nodup) (hv : v ∈ (splitAtRec u b f).2) (hu : u ∈ (splitAtRec v b f).2) :
    False := by
  have hvf : v ∈ f := splitAtRecMemSnd hv
  have huf : u ∈ f := splitAtRecMemSnd hu
  rw [sndSplitAtDrop f u b] at hv
  rw [sndSplitAtDrop f v b] at hu
  have h1 := (memDropIndex hnd hvf).mp hv
  have h2 := (memDropIndex hnd huf).mp hu
  omega

/-- HOL `take_or_drop`（tame_list.hl:2734
`uniq s /\ MEM x s ==> (MEM x (take k s) \/ MEM x (dropl k s))`；
cat_take_drop 成员半边）。 -/
theorem takeOrDrop [BEq α] [LawfulBEq α] {s : List α} {x : α} {k : ℕ}
    (hv : x ∈ s) : x ∈ s.take k ∨ x ∈ s.drop k := by
  have hta : s = s.take k ++ s.drop k := (List.take_append_drop k s).symm
  rw [hta] at hv
  exact List.mem_append.mp hv

/-! ### §7 betwn 家族（tame_list.hl:2306-2918） -/

/-- HOL `betwn_mem`（tame_list.hl:2306 `MEM w (betwn f u v) ==> MEM w f`）。
与 ListAuxLemmas.inbetween_inset 同构（Isabelle 车道先行件），桥引记账。 -/
theorem betwnMem [BEq α] [LawfulBEq α] {f : List α} {u v w : α} (h : w ∈ between f u v) :
    w ∈ f :=
  inbetween_inset h

/-- HOL `betwn_take_drop`（tame_list.hl:2433
`MEM v f /\ uniq f ==> betwn f u v =
if (indexl u f < indexl v f) then take (PRE (indexl v f - indexl u f))
(dropl (SUC (indexl u f)) f) else APPEND (dropl (SUC (indexl u f)) f)
(take (indexl v f) f)`；PRE (j - i) 按 j - (i + 1) 逐字换算，记账见文件头）。 -/
theorem betwnTakeDrop [BEq α] [LawfulBEq α] {f : List α} {u v : α}
    (hnd : f.Nodup) (hv : v ∈ f) :
    between f u v =
      if f.idxOf u < f.idxOf v then
        (f.drop (f.idxOf u + 1)).take (f.idxOf v - (f.idxOf u + 1))
      else f.drop (f.idxOf u + 1) ++ f.take (f.idxOf v) := by
  have hnd1 : (f.drop (f.idxOf u + 1)).Nodup := uniqDrop hnd
  have hnd2 : (f.take (f.idxOf u)).Nodup := uniqTake hnd
  rw [between_def]
  simp only [splitAt]
  rw [fstSplitAtTake f u [], sndSplitAtDrop f u [], List.nil_append]
  split
  · rename_i hc
    have hmem : v ∈ f.drop (f.idxOf u + 1) := List.contains_iff_mem.mp hc
    have hij : f.idxOf u < f.idxOf v := by
      have := (memDropIndex hnd hv).mp hmem
      omega
    rw [if_pos hij, fstSplitAtTake (f.drop (f.idxOf u + 1)) v [], List.nil_append,
      idxOfDrop hnd hv (by omega)]
  · rename_i hc
    have hnc : v ∉ f.drop (f.idxOf u + 1) := by
      intro hm
      exact hc (List.contains_iff_mem.mpr hm)
    have hij : ¬(f.idxOf u < f.idxOf v) := by
      intro hl
      exact hnc ((memDropIndex hnd hv).mpr (by omega))
    rw [if_neg hij, fstSplitAtTake (f.take (f.idxOf u)) v [], List.nil_append]
    rcases Nat.lt_trichotomy (f.idxOf v) (f.idxOf u) with hji | heq | hij'
    · have hmem2 : v ∈ f.take (f.idxOf u) := (memTakeIndex hv).mpr (by omega)
      rw [idxOfTake hnd hv (by omega), takeTake (by omega)]
    · have hnt : v ∉ f.take (f.idxOf u) := by
        intro ht
        have := (memTakeIndex hv).mp ht
        omega
      have hidxT : (f.take (f.idxOf u)).idxOf v = (f.take (f.idxOf u)).length :=
        List.idxOf_eq_length_iff.mpr hnt
      have hlenT : (f.take (f.idxOf u)).length = f.idxOf u := by
        rw [List.length_take]
        exact Nat.min_eq_left List.idxOf_le_length
      rw [hidxT, hlenT, takeTake (Nat.le_refl (f.idxOf u)), ← heq]
    · exact absurd hij' hij

/-- HOL `size_betwn`（tame_list.hl:2520
`uniq s /\ MEM x s /\ MEM y s /\ ~(x = y) ==>
sizel (betwn s x y) = PRE (indexf x y s)`）。 -/
theorem sizeBetwn [BEq α] [LawfulBEq α] {s : List α} {x y : α}
    (hnd : s.Nodup) (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
    (between s x y).length = indexf x y s - 1 := by
  have hi := idxOfMem hx
  have hj := idxOfMem hy
  rw [betwnTakeDrop hnd hy, indexfCond hx hy]
  split
  · rename_i hc
    rw [if_pos (Nat.le_of_lt hc), List.length_take, List.length_drop]
    omega
  · rename_i hc
    have hne' : s.idxOf x ≠ s.idxOf y := fun e => hne (idxUniq hx hy e)
    have hnle : ¬(s.idxOf x ≤ s.idxOf y) := by omega
    rw [if_neg hnle, List.length_append, List.length_drop, List.length_take]
    omega

/-- HOL `not_betwn1`（tame_list.hl:2574
`uniq s /\ MEM z s ==> ~(MEM x (betwn s x z))`）。 -/
theorem notBetwn1 [BEq α] [LawfulBEq α] {s : List α} {x z : α}
    (hnd : s.Nodup) (hz : z ∈ s) : x ∉ between s x z := by
  rw [betwnTakeDrop hnd hz]
  split
  · intro hm
    have hd : x ∈ s.drop (s.idxOf x + 1) := List.mem_of_mem_take hm
    have hx : x ∈ s := List.mem_of_mem_drop hd
    have := (memDropIndex hnd hx).mp hd
    omega
  · intro hm
    rcases List.mem_append.mp hm with h1 | h2
    · have hx : x ∈ s := List.mem_of_mem_drop h1
      have := (memDropIndex hnd hx).mp h1
      omega
    · have hx : x ∈ s := List.mem_of_mem_take h2
      have := (memTakeIndex hx).mp h2
      omega

/-- HOL `not_betwn2`（tame_list.hl:2600 `uniq s ==> ~(MEM z (betwn s x z))`）。 -/
theorem notBetwn2 [BEq α] [LawfulBEq α] {s : List α} {x z : α} (hnd : s.Nodup) :
    z ∉ between s x z := by
  by_cases hz : z ∈ s
  · rw [betwnTakeDrop hnd hz]
    split
    · intro hm
      have hdz : z ∈ s.drop (s.idxOf x + 1) := List.mem_of_mem_take hm
      have hik : s.idxOf x + 1 ≤ s.idxOf z := (memDropIndex hnd hz).mp hdz
      have hidx := idxOfDrop hnd hz hik
      have hlt := (memTakeIndex hdz).mp hm
      omega
    · intro hm
      rcases List.mem_append.mp hm with h1 | h2
      · have hik : s.idxOf x + 1 ≤ s.idxOf z := (memDropIndex hnd hz).mp h1
        have hij : ¬(s.idxOf x < s.idxOf z) := by
          rename_i hc
          intro hl
          exact hc hl
        omega
      · have hj := idxOfMem hz
        have := (memTakeIndex hz).mp h2
        omega
  · intro hm
    rw [between_def] at hm
    simp only [splitAt] at hm
    rw [fstSplitAtTake s x [], sndSplitAtDrop s x [], List.nil_append] at hm
    rw [if_neg (by
      intro hc
      exact hz (List.mem_of_mem_drop (List.contains_iff_mem.mp hc)))] at hm
    rcases List.mem_append.mp hm with h1 | h2
    · exact hz (List.mem_of_mem_drop h1)
    · exact hz (List.mem_of_mem_take (splitAt_in_fst h2))

/-- HOL `indexl_betwn`（tame_list.hl:2631
`uniq s /\ MEM x s /\ MEM z s /\ MEM y (betwn s x z)
==> SUC (indexl y (betwn s x z)) = indexf x y s`）。 -/
theorem indexlBetwn [BEq α] [LawfulBEq α] {s : List α} {x y z : α}
    (hnd : s.Nodup) (hx : x ∈ s) (hz : z ∈ s) (hy : y ∈ between s x z) :
    (between s x z).idxOf y + 1 = indexf x y s := by
  have hys : y ∈ s := betwnMem hy
  have hj := idxOfMem hys
  have hxb := idxOfMem hx
  have hxy : x ≠ y := by
    intro e
    exact notBetwn1 hnd hz (e ▸ hy)
  by_cases hij : s.idxOf x < s.idxOf z
  · rw [betwnTakeDrop hnd hz, if_pos hij] at hy ⊢
    have hd : y ∈ s.drop (s.idxOf x + 1) := List.mem_of_mem_take hy
    have hik : s.idxOf x + 1 ≤ s.idxOf y := (memDropIndex hnd hys).mp hd
    have hidx := idxOfDrop hnd hys hik
    have hlt3 := (memTakeIndex hd).mp hy
    have hlt2 : (s.drop (s.idxOf x + 1)).idxOf y < s.idxOf z - (s.idxOf x + 1) := by omega
    have hnle : s.idxOf x ≤ s.idxOf y := by omega
    rw [idxOfTake (uniqDrop hnd) hd hlt2, hidx, indexfCond hx hys, if_pos hnle]
    omega
  · rw [betwnTakeDrop hnd hz, if_neg hij] at hy ⊢
    have hnd1 : (s.drop (s.idxOf x + 1)).Nodup := uniqDrop hnd
    by_cases hyd : y ∈ s.drop (s.idxOf x + 1)
    · have hik : s.idxOf x + 1 ≤ s.idxOf y := (memDropIndex hnd hys).mp hyd
      have hidx := idxOfDrop hnd hys hik
      have hnle : s.idxOf x ≤ s.idxOf y := by omega
      rw [List.idxOf_append_of_mem hyd, hidx, indexfCond hx hys, if_pos hnle]
      omega
    · have hik : s.idxOf y ≤ s.idxOf x := by
        by_contra hcc
        exact hyd ((memDropIndex hnd hys).mpr (by omega))
      have hki : s.idxOf y ≠ s.idxOf x := by
        intro e
        have h2 : y = x := idxUniq hys hx e
        exact hxy h2.symm
      rcases List.mem_append.mp hy with ht | ht
      · exact absurd ht hyd
      · have hij2 : s.idxOf y < s.idxOf z := (memTakeIndex hys).mp ht
        have hpf : (s.take (s.idxOf z)).idxOf y = s.idxOf y := idxOfTake hnd hys hij2
        have hnle : ¬(s.idxOf x ≤ s.idxOf y) := fun hle =>
          hki (Nat.le_antisymm hik hle)
        rw [List.idxOf_append_of_notMem hyd, List.length_drop,
          hpf, indexfCond hx hys, if_neg hnle]
        omega

/-- HOL `indexf_betwn`（tame_list.hl:2704
`~(x = z) /\ uniq s /\ MEM x s /\ MEM z s /\ MEM y (betwn s x z)
==> 0 < indexf x y s /\ indexf x y s < indexf x z s`）。 -/
theorem indexfBetwn [BEq α] [LawfulBEq α] {s : List α} {x y z : α}
    (hne : x ≠ z) (hnd : s.Nodup) (hx : x ∈ s) (hz : z ∈ s) (hy : y ∈ between s x z) :
    0 < indexf x y s ∧ indexf x y s < indexf x z s := by
  have h1 := indexlBetwn hnd hx hz hy
  have hb : (between s x z).idxOf y < (between s x z).length :=
    List.idxOf_lt_length_iff.mpr hy
  have h2 : indexf x z s = (between s x z).length + 1 := by
    have := sizeBetwn hnd hx hz hne
    omega
  exact ⟨by omega, by omega⟩

/-- HOL `betwn_cases`（tame_list.hl:2744
`~(x = z) /\ uniq s /\ MEM x s /\ MEM y s /\ MEM z s ==>
(y = x) \/ (y = z) \/ (MEM y (betwn s x z)) \/ MEM y (betwn s z x)`）。
按 HOL 原证次序（先于 indexf_betwn_eq）以 betwn_take_drop + take/drop 位置
算术直证；前稿经 indexfBetwnEq 桥引与 indexf_betwn_eq 成环，已按原序理顺。 -/
theorem betwnCases [BEq α] [LawfulBEq α] {s : List α} {x y z : α}
    (hne : x ≠ z) (hnd : s.Nodup) (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) :
    y = x ∨ y = z ∨ y ∈ between s x z ∨ y ∈ between s z x := by
  by_cases hyx : y = x
  · exact Or.inl hyx
  by_cases hyz : y = z
  · exact Or.inr (Or.inl hyz)
  have hij : s.idxOf x ≠ s.idxOf z := fun e => hne (idxUniq hx hz e)
  rcases Nat.lt_trichotomy (s.idxOf x) (s.idxOf z) with hlt | heq | hgt
  · rw [betwnTakeDrop hnd hz, if_pos hlt, betwnTakeDrop hnd hx, if_neg (by omega)]
    rcases Nat.lt_trichotomy (s.idxOf y) (s.idxOf x) with hjx | hjx | hjx
    · exact Or.inr (Or.inr (Or.inr
        (List.mem_append.mpr (Or.inr ((memTakeIndex hy).mpr (by omega))))))
    · exact absurd (idxUniq hy hx hjx) hyx
    · have hd : y ∈ s.drop (s.idxOf x + 1) := (memDropIndex hnd hy).mpr (by omega)
      rcases Nat.lt_trichotomy (s.idxOf y) (s.idxOf z) with hjz | hjz | hjz
      · refine Or.inr (Or.inr (Or.inl ?_))
        have hidx : (s.drop (s.idxOf x + 1)).idxOf y
            = s.idxOf y - (s.idxOf x + 1) := idxOfDrop hnd hy (by omega)
        exact (memTakeIndex hd).mpr (by omega)
      · exact absurd (idxUniq hy hz hjz) hyz
      · exact Or.inr (Or.inr (Or.inr
          (List.mem_append.mpr (Or.inl ((memDropIndex hnd hy).mpr (by omega))))))
  · exact absurd (idxUniq hx hz heq) hne
  · rw [betwnTakeDrop hnd hz, if_neg (by omega), betwnTakeDrop hnd hx, if_pos hgt]
    rcases Nat.lt_trichotomy (s.idxOf y) (s.idxOf z) with hjz | hjz | hjz
    · exact Or.inr (Or.inr (Or.inl
        (List.mem_append.mpr (Or.inr ((memTakeIndex hy).mpr (by omega))))))
    · exact absurd (idxUniq hy hz hjz) hyz
    · have hd : y ∈ s.drop (s.idxOf z + 1) := (memDropIndex hnd hy).mpr (by omega)
      rcases Nat.lt_trichotomy (s.idxOf y) (s.idxOf x) with hjx | hjx | hjx
      · refine Or.inr (Or.inr (Or.inr ?_))
        have hidx : (s.drop (s.idxOf z + 1)).idxOf y
            = s.idxOf y - (s.idxOf z + 1) := idxOfDrop hnd hy (by omega)
        exact (memTakeIndex hd).mpr (by omega)
      · exact absurd (idxUniq hy hx hjx) hyx
      · exact Or.inr (Or.inr (Or.inl
          (List.mem_append.mpr (Or.inl ((memDropIndex hnd hy).mpr (by omega))))))

/-- HOL `indexf_betwn_eq`（tame_list.hl:2799
`~(x = z) /\ uniq s /\ MEM x s /\ MEM z s ==> (MEM y (betwn s x z) <=>
0 < indexf x y s /\ indexf x y s < indexf x z s)`）。 -/
theorem indexfBetwnEq [BEq α] [LawfulBEq α] {s : List α} {x y z : α}
    (hne : x ≠ z) (hnd : s.Nodup) (hx : x ∈ s) (hz : z ∈ s) :
    y ∈ between s x z ↔ 0 < indexf x y s ∧ indexf x y s < indexf x z s := by
  constructor
  · exact indexfBetwn hne hnd hx hz
  · rintro ⟨hpos, hlt⟩
    have hys : y ∈ s := by
      by_contra hny
      have h1 := indexfOfNotMemRight (x := x) hny
      have h2 := indexfLtSizel hx hz
      omega
    rcases betwnCases hne hnd hx hys hz with e | e | hm | hm
    · subst e
      rw [indexfRefl hx] at hpos
      exact absurd hpos (by omega)
    · subst e
      exact absurd hlt (by omega)
    · exact hm
    · exfalso
      have hxy : x ≠ y := by
        intro e
        rw [e] at hpos
        exact absurd (indexfRefl hys) (by omega)
      have hzy : z ≠ y := by
        intro e
        rw [e] at hlt
        omega
      have hyx := indexfBetwn (Ne.symm hne) hnd hz hx hm
      have e1 := indexfAntisym hx hys hxy
      have e2 := indexfAntisym hx hz hne
      have e3 := indexfAntisym hz hys hzy
      have hle2 : indexf z y s ≤ indexf z x s := by omega
      have e4 := indexfAddLeft hz hys hx hle2
      have hn := indexfLtSizel hx hys
      omega

/-- HOL `indexf_add_betwn`（tame_list.hl:2842
`~(x = z) /\ uniq s /\ MEM x s /\ MEM y (betwn s x z) /\ MEM z s
==> indexf x y s + indexf y z s = indexf x z s`）。 -/
theorem indexfAddBetwn [BEq α] [LawfulBEq α] {s : List α} {x y z : α}
    (hne : x ≠ z) (hnd : s.Nodup) (hx : x ∈ s) (hy : y ∈ between s x z) (hz : z ∈ s) :
    indexf x y s + indexf y z s = indexf x z s := by
  have hy' := indexfBetwn hne hnd hx hz hy
  have hys : y ∈ s := betwnMem hy
  exact indexfAddLeft hx hys hz (by omega)

/-! ### §8 next_el 反射 / indexf_prev / option 杂件（tame_list.hl:2859-2934） -/

/-- HOL `next_el_refl`（tame_list.hl:2859
`MEM x s /\ next_el s x = x /\ uniq s ==> s = [x]`）。 -/
theorem nextElRefl [BEq α] [LawfulBEq α] {s : List α} {x : α}
    (hx : x ∈ s) (h : nextEl s x = x) (hnd : s.Nodup) : s = [x] := by
  have hi := idxOfMem hx
  by_cases hlt : s.idxOf x + 1 < s.length
  · rw [nextElOfLt hlt, List.getD_eq_getElem _ _ hlt] at h
    have h2 : s[s.idxOf x] = s[s.idxOf x + 1] := (List.getElem_idxOf hi).trans h.symm
    have := List.Nodup.getElem_inj_iff hnd |>.mp h2
    omega
  · have hlast : s.idxOf x = s.length - 1 := by omega
    rw [nextElOfLast hlast] at h
    obtain ⟨a, t, rfl⟩ :=
      List.exists_cons_of_ne_nil
        (show s ≠ [] by intro hc; subst hc; exact List.not_mem_nil hx)
    rw [List.headD_cons] at h
    subst h
    have h0 : (a :: t).idxOf a = 0 := by simp
    have hlen1 : (a :: t).length = t.length + 1 := rfl
    have hlt1 : t.length = 0 := by omega
    cases t with
    | nil => rfl
    | cons a' t' => simp at hlt1

/-- HOL `indexf_prev`（FWDDPHY，tame_list.hl:2895
`MEM x s /\ MEM y s /\ uniq s /\ next_el s x = y
==> indexf y x s = sizel s - 1`）。 -/
theorem indexfPrev [BEq α] [LawfulBEq α] {s : List α} {x y : α}
    (hx : x ∈ s) (hy : y ∈ s) (hnd : s.Nodup) (h : nextEl s x = y) :
    indexf y x s = s.length - 1 := by
  by_cases hxy : x = y
  · subst hxy
    have hs := nextElRefl hx h hnd
    have hlen : s.length = 1 := by rw [hs]; simp
    rw [indexfRefl hx]
    omega
  · have h1lt := sizelGt1 hx hy hxy
    have e1 := indexfAntisym hx hy hxy
    have h1 := nextElIndexf hx hy hnd h h1lt
    omega

/-- HOL `not_some_none`（tame_list.hl:2920 `~(SOME x = NONE)`）。 -/
theorem notSomeNone (x : α) : ¬(Option.some x = Option.none) := by
  rintro ⟨⟩

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；预期标准三 `[propext, Classical.choice, Quot.sound]`）：
#print axioms Kepler.Text.TameSpine.indexfAntisym
#print axioms Kepler.Text.TameSpine.indexfN
#print axioms Kepler.Text.TameSpine.betwnTakeDrop
#print axioms Kepler.Text.TameSpine.betwnCases
-/
