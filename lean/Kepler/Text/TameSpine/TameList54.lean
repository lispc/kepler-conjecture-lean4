/-
  Kepler.Text.TameSpine.TameList54 — B1 Tame_list 地基批 54：
  unadj/rotate_to 面（tamespine-port-plan §4 批次表 B1 行；接续批 53 =
  TameList53.lean，批 53 终点 = HOL :13581；本批起点 = HOL :13582
  `unadj_alt`。行号均按主仓 reference/flyspeck（commit 1ce0353）实测；
  批 53 头注预记 :13582/:13615/:13623/:13639 四锚点与实测一致，零偏移。

  槽面侦察裁定（批 53 头注预记面的对拍结论）：

  - **unadj alt 面语义对拍（开工先核，命中）**：`unadj`（tame_defs2.hl:656
    `unadj [] = T /\ unadj (h::t) = if t = [] then T else
    ~(h = HD t) /\ unadj t`）批 4 已按「空表/单元素表为 True、长表首二相异」
    三支递归落 TameList4 `Unadj`（TameList4.lean:99），与 HOL 条件式逐点
    等价（HD 的 junk 值由 t = [] 分支挡死，批 4 头注既档）——alt 面
    `unadj_alt` :13582 直接在 `Unadj` 载体上落 Iff，零新 def、零收窄。
  - **rotate_to 载体侦察裁定（tame_defs 系开工先核，命中）**：
    - `split_at_rec`/`split_at`（tame_defs.hl:328/:333）在册：
      `Kepler.Graphs.splitAtRec`/`splitAt`（Graphs/ListAux.lean:16/:22，
      Isabelle ListAux.thy 同源逐句镜像，批 3 betwn 载体面既档；
      `List.splitAt`（Nat 下标版）同名异面——开面全限定消费）；
    - `rotate_to`（tame_defs.hl:346 `rotate_to (vs:A list) v = v ::
      APPEND (SND (split_at v vs)) (FST (split_at v vs))`）不在册，本批
      新落 `rotateTo`（逐句镜像，SND/FST ↦ .2/.1）；hd_rotate_to/
      mem_rotate_to 在该载体上定义性直落（头元恒为 v，HD/MEM junk 面
      由 cons 结构封死）。
  - **next_el 载体在册（批 1 既档）**：`next_el`（seq2-compiled.hl:24）↦
    `Kepler.Assembly.nextEl`（GoodListDefs.lean:44）；本件核心槽 =
    TameLp `nextEl_eq_getD`（TameLp.lean:3602）+ `idxOf_getElem`
    （TameLp.lean:3577，Nodup 下标单射）+ `getD_eq_getElem_of_lt`
    （TameLp.lean:3526）；HOL 证体 COND_CASES 两支（indexl = size-1 的
    headl 支 vs nth 支）在 Lean 由 `Nat.mod_eq_of_lt` 免 split 直落
    （SUC i < sizel 时 index+1 < length 恒成立）——机制简化记档，
    非语义损失。
  - **dropl 载体在册**：`dropl`（jHOLLight/Examples/seq.vhl:728
    `dropl n [] = [] /\ dropl 0 s = s /\ dropl (SUC n) (x::s) = dropl n s`）
    ↦ core `List.drop`（递归逐字同构，零新 def）。drop 家族四件：
    `drop_eq_nil` :13657 ↦ mathlib `List.drop_eq_nil_iff` 逐字同语句
    零镜像直投；`el_drop` 核槽 = mathlib `List.getElem_drop`
    （`(drop i xs)[j] = xs[i + j]`，HOL `j + i` 序经 Nat.add_comm 换装）；
    `hd_drop`/`tl_drop` 非空支 `HD`/`TL` ↦ `head!`/`tail`（批 11/12
    既档，junk 面由非空前提封死）。
  - **EL/HD 约定既档**：`EL` ↦ `getElem`（real-getElem 面，前提内联），
    ∀ 辖域面见新雷区第二条；`HD` ↦ `head!`（批 11/12）。

  新雷区（本批实测记档）：
  - **`List.getElem_head!` 不在册**（head!↔getElem 桥缺，mathlib 无
    head!_eq_getElem 系）——`hd_drop` 走私件 `head!EqGetElemZero`
    （cases 一发：nil 支 absurd、cons 支 rfl，批 8 `getElem!Eq` 换形器
    同体例）；
  - **∀ 辖域内 getElem 下标证槽的具名 binder 雷**：语句形
    `∀ i, i + 1 < l.length → l[i] ≠ l[i+1]` 的匿名箭头域不入 getElem
    槽 elaboration 语境（`failed to prove index is valid` 实测两例）；
    具名 binder 形 `∀ i, (hi : i + 1 < l.length) → l[i] ≠ l[i+1]`
    elaboration 直通（下标证经语境 hoist + get_elem_tactic 免写）——
    unadj_alt 按具名 binder 形落（打印形与 HOL 逐句同构，语义零差）；
  - **omega 拒复合 length 原子目标的独立事实槽**：`0 + 1 <
    (a::b::u).length` 槽仅给 `(a::b::u).length = (b::u).length + 1`
    不够（需 length ≥ 2 的独立事实），先立 `… = u.length + 2 := rfl`
    型独立 hlen 再 omega（批 52/53「omega 不吃 List.length」雷的
    复合面延伸——rw [hL] 换装后 omega 吃纯 Nat）；
  - **`getElem_cons_succ` 双发逐阶换装**：复合下标 `j+1+1` 一发 rw 只换
    首现实例（i := j），`j+1` 与 `j+1+1` 各一发（第二发命中原复合下标，
    `j` 为变元不匹配 `i+1` 模式故首发不误伤）；
  - **getElem 下标槽内 rw-motive 雷（批 53「getElem rw-motive 走免重写」
    雷的 add 换装面）**：`rw [Nat.add_zero]`/`rw [Nat.add_comm]` 打不进
    `xs[i+0]`/`xs[i+j]` 的下标槽（下标证例依赖被换下标，motive 不型正；
    `cases Nat.add_comm` 的 Eq.rec 泛化同样败——依赖证例内嵌 goal 项
    不可 revert），按报错处方走 simp：`i + 0` 位 defeq + 证明无关性
    rfl 直落；`i + j`↔`j + i` 非 defeq 走 `simp only [Nat.add_comm]`
    （simp 换下标证例随装）。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:13582-:13702，八件）：

  §1 unadj alt 面：`unadj_alt` :13582 `!vs. unadj vs = (!i. SUC i <
  sizel vs ==> ~(EL i vs = EL (SUC i) vs))` ↦ unadjAlt（真证；vs 归纳 +
  尾表分流——空/单表支 length 换装 omega 免 split，长表支 zero/succ
  下标分流，getElem_cons_succ 双发换装 + ih 回喂）。

  §2 rotate_to 章（定义层 + 二件）：`rotate_to` 定义层（tame_defs.hl:346）
  ↦ rotateTo（本批唯一新 def，逐句镜像；载体裁定如上）；`hd_rotate_to`
  :13615 ↦ hdRotateTo（定义性 rfl）；`mem_rotate_to` :13639 ↦
  memRotateTo（mem_cons_self 直投）。

  §3 next_el 下标章：`next_el_el` :13623 `!xs i. uniq xs /\ SUC i <
  sizel xs ==> next_el xs (EL i xs) = EL (SUC i) xs` ↦ nextElEl（真证；
  三槽机制如上对拍落地）。

  §4 drop 家族：`tl_drop` :13647 ↦ tlDrop（nil 支 absurd + cons 支定义性
  rfl）；`drop_eq_nil` :13657 ↦ dropEqNil（零镜像直投）；`hd_drop`
  :13671 ↦ hdDrop（head!EqGetElemZero 换装 + getElem_drop + add_zero）；
  `el_drop` :13687 ↦ elDrop（getElem_drop + Nat.add_comm）。

  诚实记账：八件全真证（unadjAlt/hdRotateTo/nextElEl/memRotateTo/
  tlDrop/dropEqNil/hdDrop/elDrop），零 sorry、零止损件、零记账债；
  drop_eq_nil 零镜像直投记档如上（非止损件）；rotateTo 为本批唯一新 def
  （rotate_to 定义层不在册，逐句镜像如上，非止损）。范围决策：批 54 射程
  收口至 :13702（unadj alt 面 + rotate_to 章 + next_el 下标章 + drop
  家族，自然边界——下一件 :13703 `inj_on_union` 起为 inj_on/UNION
  集合面新章）。
  红线遵守：零既有文件触碰、零 git 写操作。
  批 55 接续点：HOL :13703 `inj_on_union`（:13703-:13728，inj_on/UNION
  集合面开章——不相交两族分片拼接 `inj_on f (s ∪ t)` + 逐点 f = fs/ft
  双方程，证体 SET_TAC/ASM_MESON_TAC 面）；其后 :13730 `inj_on_union3`
  （三族版，经 inj_on_union 两步复合）、:13763 `INJ_inj_on`（批 2
  inj_on_INJ 对偶面，`Set.InjOn` 即唯一载体，大概率零镜像跳过）、
  :13772 `set_of_list_iota_alt`、:13780 `uniq_bij_map`；inj_on 载体 =
  `Set.InjOn` 批 2 既档，UNION/INTER 面 core+mathlib 在册性开工先核。
-/

import Kepler.Text.TameSpine.TameList53

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl)
open Kepler.Text.TameLp (nextEl_eq_getD getD_eq_getElem_of_lt idxOf_getElem)
open Kepler.Graphs (splitAt)

variable {α : Type*}

/-! ### §1 unadj alt 面（tame_list.hl:13582） -/

/-- **HOL `unadj_alt`**（tame_list.hl:13582 `!vs. unadj vs = (!i. SUC i <
sizel vs ==> ~(EL i vs = EL (SUC i) vs))`）。载体 = 批 4 `Unadj`
（三支递归 = HOL 条件式逐点等价，TameList4.lean:99）。证体：vs 归纳 +
尾表分流——空/单表支 length 换装 omega 免 split（HOL arith
`~(SUC i < 0)`/`~(SUC i < 1)` 支）；长表支 zero/succ 下标分流
（zero 支 = 首二相异，succ 支 getElem_cons_succ 双发换装 + ih 回喂，
即 HOL EL/TL 机制的 Lean 形）。 -/
theorem unadjAlt (vs : List α) :
    Unadj vs ↔ ∀ i, (hi : i + 1 < vs.length) → vs[i] ≠ vs[i + 1] := by
  induction vs with
  | nil =>
    simp only [Unadj]
    constructor
    · intro _ i hi
      rw [List.length_nil] at hi
      omega
    · intro _
      trivial
  | cons a t ih =>
    cases t with
    | nil =>
      simp only [Unadj]
      constructor
      · intro _ i hi
        rw [List.length_cons, List.length_nil] at hi
        omega
      · intro _
        trivial
    | cons b u =>
      have hM : (b :: u).length = u.length + 1 := rfl
      have hL : (a :: b :: u).length = u.length + 2 := rfl
      simp only [Unadj]
      constructor
      · rintro ⟨hab, hrec⟩ i hi
        cases i with
        | zero => exact hab
        | succ j =>
          have hlt : j + 1 < (b :: u).length := by rw [hM]; omega
          have h := ih.mp hrec j hlt
          rw [List.getElem_cons_succ, List.getElem_cons_succ]
          exact h
      · intro h
        refine ⟨?_, ?_⟩
        · have h0 := h 0 (by rw [hL]; omega)
          exact h0
        · refine ih.mpr fun j hj => ?_
          rw [hM] at hj
          have h1 := h (j + 1) (by rw [hL]; omega)
          rw [List.getElem_cons_succ, List.getElem_cons_succ] at h1
          exact h1

/-! ### §2 rotate_to 章（tame_defs.hl:346；tame_list.hl:13615/:13639） -/

/-- HOL `rotate_to`（tame_defs.hl:346
`rotate_to (vs:A list) v = v :: (APPEND (SND (split_at v vs))
(FST (split_at v vs)))`）逐句镜像（`split_at` ↦ `Kepler.Graphs.splitAt`
批 3 载体既档，SND/FST ↦ `.2`/`.1`；头元恒为 v、尾段 = 首遇 v 处的
后缀 ++ 前缀）。 -/
def rotateTo [BEq α] (vs : List α) (v : α) : List α :=
  v :: ((splitAt v vs).2 ++ (splitAt v vs).1)

/-- **HOL `hd_rotate_to`**（tame_list.hl:13615 `!vs v. HD (rotate_to vs v)
= v`）。定义性直落（rotate_to 头元恒为 v，HD junk 面由 cons 结构封死）。 -/
theorem hdRotateTo [BEq α] [Inhabited α] (vs : List α) (v : α) :
    (rotateTo vs v).head! = v := rfl

/-- **HOL `mem_rotate_to`**（tame_list.hl:13639 `!vs v. MEM v (rotate_to
vs v)`）。头元成员直投。 -/
theorem memRotateTo [BEq α] (vs : List α) (v : α) : v ∈ rotateTo vs v :=
  List.mem_cons_self

/-! ### §3 next_el 下标章（tame_list.hl:13623） -/

/-- **HOL `next_el_el`**（tame_list.hl:13623 `!xs i. uniq xs /\ SUC i <
sizel xs ==> next_el xs (EL i xs) = EL (SUC i) xs`）。证体（三槽机制）：
nextEl_eq_getD（next_el_alt 换装）+ idxOf_getElem（Nodup 下标单射定位，
即 HOL index_el 槽）+ Nat.mod_eq_of_lt（SUC i < sizel 时 index+1 免
mod 折算）+ getD_eq_getElem_of_lt（nth 槽）；HOL COND_CASES 两支
（indexl = size-1 的 headl 支在 `SUC i < sizel` 下矛盾）由 mod 换装
免 split 直落。 -/
theorem nextElEl [BEq α] [LawfulBEq α] [DecidableEq α] {xs : List α}
    (hnd : xs.Nodup) {i : ℕ} (hi : i + 1 < xs.length) :
    nextEl xs xs[i] = xs[i + 1] := by
  have hilt : i < xs.length := by omega
  have hmem : xs[i] ∈ xs := List.getElem_mem hilt
  rw [nextEl_eq_getD hmem, idxOf_getElem hnd hilt, Nat.mod_eq_of_lt hi]
  exact getD_eq_getElem_of_lt hi _

/-! ### §4 drop 家族（tame_list.hl:13647-:13702） -/

/-- **HOL `tl_drop`**（tame_list.hl:13647 `!xs. ~(xs = []) ==> TL xs =
dropl 1 xs`）。nil 支 absurd 反证 + cons 支定义性 rfl（`tail`/`drop 1`
在 cons 上同归约）。 -/
theorem tlDrop {xs : List α} (hne : xs ≠ []) : xs.tail = xs.drop 1 := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons a t => rfl

/-- **HOL `drop_eq_nil`**（tame_list.hl:13657 `!s i. dropl i s = [] <=>
sizel s <= i`）。mathlib `List.drop_eq_nil_iff` 逐字同语句零镜像直投。 -/
theorem dropEqNil (s : List α) (i : ℕ) : s.drop i = [] ↔ s.length ≤ i :=
  List.drop_eq_nil_iff

/-- 私件：非空表 `head!` 与零位 getElem 换形器（`List.getElem_head!`
不在册实测记档；批 8 `getElem!Eq` 换形器同体例）。 -/
private theorem head!EqGetElemZero [Inhabited α] {l : List α}
    (h : 0 < l.length) : l.head! = l[0] := by
  cases l with
  | nil => simp at h
  | cons a t => rfl

/-- **HOL `hd_drop`**（tame_list.hl:13671 `!xs i. i < sizel xs ==>
HD (dropl i xs) = EL i xs`）。证体：length_drop 界槽封非空 + 换形器 +
getElem_drop（j = 0）；尾段 `i + 0` 位 defeq + 证明无关性 rfl 收口
（rw-motive 雷区：add_zero 打不进 getElem 下标槽，见新雷区记档）；
HOL num_CASES 两支由 length_drop 免 split 直落（机制简化记档）。 -/
theorem hdDrop [Inhabited α] {xs : List α} {i : ℕ} (hi : i < xs.length) :
    (xs.drop i).head! = xs[i] := by
  have hpos : 0 < (xs.drop i).length := by rw [List.length_drop]; omega
  rw [head!EqGetElemZero hpos, List.getElem_drop]
  rfl

/-- **HOL `el_drop`**（tame_list.hl:13687 `!xs i j. i + j < sizel xs ==>
EL j (dropl i xs) = EL (j+i) xs`）。mathlib `List.getElem_drop`
（`(drop i xs)[j] = xs[i + j]`）+ `simp only [Nat.add_comm]`（rw-motive
雷区：rw [Nat.add_comm]/cases Eq.rec 均打不进 getElem 下标槽——前者
motive 不型正、后者依赖证例内嵌 goal 项不可 revert；simp only 按报错
处方吃下标证例换装，HOL `j + i` 序经此换装）。 -/
theorem elDrop {xs : List α} {i j : ℕ} (h : i + j < xs.length) :
    (xs.drop i)[j]'(by rw [List.length_drop]; omega) = xs[j + i] := by
  rw [List.getElem_drop]
  simp only [Nat.add_comm]

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；八件正文 + 消费链槽全绿零 sorryAx——
#print axioms Kepler.Text.TameSpine.unadjAlt
#print axioms Kepler.Text.TameSpine.hdRotateTo
#print axioms Kepler.Text.TameSpine.nextElEl
#print axioms Kepler.Text.TameSpine.memRotateTo
#print axioms Kepler.Text.TameSpine.tlDrop
#print axioms Kepler.Text.TameSpine.dropEqNil
#print axioms Kepler.Text.TameSpine.hdDrop
#print axioms Kepler.Text.TameSpine.elDrop
-/
