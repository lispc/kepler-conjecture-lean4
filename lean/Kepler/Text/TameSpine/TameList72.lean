/-
  Kepler.Text.TameSpine.TameList72 — B3 D 链第十三批：DANGEYJ 章末收章
  （HOL 对账段：DANGEYJ.hl :739-:949；接续批 71 = TameList71.lean 642 行，
  md5 403ac5b12b818c39d2b9c3c1e7e87e0d）。本批 = split_normal_list 情形分裂
  + DANGEYJ 主定理；终点 = :949 文件末（DANGEYJ 章收官）。

  ┌─ 本批战绩小结 ────────────────────────────────────────────────
  │ 落点：18 声明（3 公开 = SPLIT_NORMAL_LIST_CASES +
  │ DANGEYJ_concl（def）+ DANGEYJ；15 枚 §0-§3 私有辅件），零 sorry、
  │ 零 axiom 声明；`lake build Kepler.Text.TameSpine.TameList72`
  │ 9504 jobs 全绿（clone /tmp/p4t21，单发串行、零旗标、零 -K，
  │ 模块重建 6.74s，rc=0，零本模块 linter 警告）。
  │ axiom 探针 3/3 全零 sorryAx 且 = [propext, Classical.choice,
  │ Quot.sound] 标准三；快照 t72_axiom_audit.log 全文。
  │
  │ §0 between 索引/覆盖桥（15 私件）：between_of_not_mem_right /
  │ mem_cons_splitAt_append（split_at 前缀覆盖）/ idxOf_getElem_self /
  │ idxOf_headD / idxOf_getD_succ / nextEl_eq_headD_of_idx /
  │ nextEl_eq_getD_of_idx / mem_between_iff_idx（betwnTakeDrop 的
  │ if-区间刻画）/ betwn_succ_subset（弧首段 = next_el）/
  │ betwn_next_subset（右端点后继只多出 v）/ mem_between_of_nextEl
  │ （紧邻端点回绕弧覆盖）/ betwn_or_betwn_cover（f1++f2 ⊇ r 的
  │ 四情形覆盖）/ mem_replaceSpine_of_ne（MEM3_replace）/
  │ mem_replaceSpine_of_mem（MEM2_replace）/ DANGEYJ_step。
  │ §1 SPLIT_NORMAL_LIST_CASES（:739）：覆盖内核 + split_normal_list
  │ 展开（FST = REVERSE new1 ++ f1、SND = f2 ++ new2）收口。
  │ §2 DANGEYJ_concl / DANGEYJ（:813-:949）：j 归纳、i 全称；归纳步
  │ 经 finalListSpine 真支不动点 / 假支 replaceSpine 成员分裂 +
  │ SPLIT_NORMAL_LIST_CASES 收；终点即 DANGEYJ.hl :949 文件末，
  │ 本章收官。
  └──────────────────────────────────────────────────────────────

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353，
  text_formalization/tame/DANGEYJ.hl :739-:949）：
  - `SPLIT_NORMAL_LIST_CASES`（:739）：`MEM x r /\ uniq r ==>
    MEM x (FST (split_normal_list L r f ram1 ram2)) \/
    MEM x (SND (split_normal_list L r f ram1 ram2))`；
  - `DANGEYJ_concl` / `DANGEYJ`（:813-:949）：
    `transform_assumption_v2 L /\ good_list L /\ good_list_nodes L /\
    marked_list L N r x /\ i <= j ==>
    set_of_list (flatten (ntrans L N r x i)) SUBSET
    set_of_list (flatten (ntrans L N r x j))`。

  载体折算（沿批 17/69/71 约定）：`split_normal_list` ↦
  `splitNormalListSpine`（TameList17 在册，tame_defs2.hl:167-180 逐句镜像，
  本批零重定义）；`ntrans`/`rtrans`/`transform_list` ↦ `ntransSpine`/
  `rtransSpine`/`transformListSpine`（TameList17）；`set_of_list` ↦
  `setOfListSpine`（TameList11）；`transform_assumption_v2 L` ↦
  `transformAssumptionSpine L hL`；`good_list L` ↦ `GoodList L`（证人 hL
  显式入参，批 69 约定）；`good_list_nodes L` ↦ `GoodListNodesTl L hL`；
  `marked_list L N r x` ↦ `MarkedListSpineFull hL N r x`（批 13 全量九合取，
  与 HOL 定义同面，零收窄）；AQIUNPP3 ↦ TameList17 `aqiunpp3` 直引。

  诚实记账（证明路线偏离，非语句失真）：
  - `SPLIT_NORMAL_LIST_CASES`：HOL 走 `next_el_outside`/`next_el_refl`/
    `not_in_mem_betwn`/`in_uniq_betwn`/`HD_BETWN1`/`BETWN_TWO_MEM` 的
    逐分支 MEM 推导；本批改证其集合内核「`FST` 前缀 `f1` 与 `SND` 前缀
    `f2` 的并覆盖 `r`」（`betwn_or_betwn_cover`），再经 `++` 成员分裂收口。
    两侧陈述均逐字对应 HOL；覆盖证明只用 `between` 的索引刻画
    （`betwnTakeDrop` + `idxOf` 算术），不消费 `next_el_outside`。HOL 证明
    中被消费的 `betwn_cases`/`betwn_nil`/`set_between_id` 等本批照常消费。
  - `DANGEYJ`：HOL 归纳步按 `final_list` 真假两分支 + `MEM_replace` 族收；
    本批同构（`finalListSpine` 真支 `ntrans` 不动点，假支经
    `replaceSpine` 成员三引理 `mem_replaceSpine_of_ne`/`_of_mem` +
    `SPLIT_NORMAL_LIST_CASES`）。归纳序与 HOL 一致（对 j 归纳，i 全称）。
  - `transform_assumption_v2`/`good_list`/`good_list_nodes` 的 Lean 载体均为
    显式证明参（hL/hta/hgn），`DANGEYJ_concl` 的 ∀ 量化仅对 N r x i j；
    与 TameList17 `aqiunpp3` 的载体约定同款。

  新雷区（本批实测记档，编号承批 71 的 #194）：
  - #195 `Function.iterate_succ_apply` = `f^[n+1] a = f^[n] (f a)`，
    `Function.iterate_succ_apply'` = `f (f^[n] a)`；在
    `ntrans (j+1) = FST ((transform_list)^[j+1] (N,r))` 上必须用
    **带撇**版，否则得到 `f^[j] (f (N,r))` 的错嵌套（本批 hnt 实测；
    批 17 用不带撇版成立是因为其换装点在 `transform_list_pair` 之后）。
  - #196 `betwn_or_betwn_cover` 的结论是 `x ∈ F1 ++ F2`（成员命题，非析取）；
    接 `rcases` 前必须 `List.mem_append.mp`，否则 rcases 会去拆 `List.Mem`
    归纳本身，第二支绑定名报 "Unknown identifier"（本批 SPLIT 实测）。
  - #197 `TameLp.nextEl_mem_of_mem` 所在 section 带 `[DecidableEq α]`
    （TameLp.lean:3524），泛型 `[BEq] [LawfulBEq]` 私件引用它须补
    `[DecidableEq α]`（本批 betwn_succ_subset/betwn_next_subset/
    betwn_or_betwn_cover 三件实测）。
  - #198 `rw [if_pos hlt]` 后 RHS 已是合取时不可再按析取模式
    `rintro (⟨_,_⟩ | ⟨_,_⟩)`/`rcases ... | ...`；误用报伪指数级
    "Dependent elimination failed … List.findIdx.go … at case Nat.le.refl"
    （本批 mem_between_iff_idx 直进支实测）。按该支实际连接词拆。
  - #199 `next_el` 回绕分支的指标桥免对 `s` 做 `cases`（`hpos : 0 < s.length`
    依赖 `s` 会触发 dependent elimination 失败）：走
    `List.idxOf_eq_zero_iff_head_eq hsne` + `List.headD_eq_head?`，
    再对 `s.head?` 分情形；"none" 引理名是 `List.head?_eq_none_iff`
    （无 `head?_eq_none`）。
  - #200 `List.getElem_drop` 正向是 `(l.drop n)[i] → l[n+i]`；要把
    `s[m+j]` 形态换成 drop 形须 `rw [← List.getElem_drop]`
    （本批 mem_between_iff_idx 的 hdrop 实测）。
  - #201 DANGEYJ 归纳步 `replaceSpine R [sp.2] M` 的 α 是
    `List (ℕ×ℕ)`（R/sp 都是面表）：`MEM2_replace` 引用时第二前提是
    `sp.2 ∈ [sp.2]`（`by simp`），而 `w ∈ sp.2` 只用于最后
    `List.mem_flatten` 取 `l = sp.2`；两者不可混用（本批实测）。

  批 73 接续点（精确）：DANGEYJ.hl :949 文件末（`end;;`）已收章，
  下一章 = PWSSRAT.hl（759 行）。首件 = `min_not_eq_imp_eq`（:50）；
  :22 `AQIUNPP3_concl` / :28 `HQYMRTX1_list` 只是陈述重绑（对应
  TameList17 `aqiunpp3` / `hqymrtx1List`，零重证）。PWSSRAT 主要消费
  本批 DANGEYJ + 批 17 的 l'/ntrans/rtrans/marked 桥。
-/
import Kepler.Text.TameSpine.TameList71

/-! # DANGEYJ.hl §8-§9：split_normal_list 情形分裂 + DANGEYJ 主定理

HOL 对账：`DANGEYJ.hl:739-:949`（2 定理）。 -/

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl prevEl findFaceDarts GoodList)
open Kepler.Graphs (fgraph between splitAt splitAt_ram splitAt_no_ram
  splitAt_in_fst splitAt_in_snd between_of_splitAt set_between_id)
open Kepler.Text.TameLp (nextEl_mem_of_mem GoodListNodesTl)

variable {α : Type*}

/-! ### §0 私有辅件：between 的覆盖/索引桥

本批 `SPLIT_NORMAL_LIST_CASES` 改用覆盖路线：`split_normal_list` 的两个
输出分量分别以 `f1 = [next_el ram1] ++ betwn r next_el ram1 ram2 ++ [ram2]`、
`f2 = [next_el ram2] ++ betwn r next_el ram2 ram1 ++ [ram1]` 为（前缀/后缀）
段；只要 `f1 ++ f2` 覆盖 `r`，`x ∈ r` 必落其一。覆盖的四种情形：
`ram1 ∉ r`（`f2` 全覆）/ `ram2 ∉ r`（`f1` 全覆）/ 二者皆在（经
`betwnCases` 把环切成 `[next ram1 .. ram2]` 与 `[next ram2 .. ram1]` 两段，
端点用 `betwnNil`/`set_between_id` 特判）。 -/

/-- 私件：`v ∉ s ==> between s u v = SND (split_at u s) ++ FST (split_at u s)`
（`betwn` 的「右端点不在表中」退化形）。 -/
private theorem between_of_not_mem_right [BEq α] [LawfulBEq α] {s : List α}
    {u v : α} (hv : v ∉ s) :
    between s u v = (splitAt u s).2 ++ (splitAt u s).1 := by
  set P := (splitAt u s).1 with hPdef
  set S := (splitAt u s).2 with hSdef
  have hPS : splitAt u s = (P, S) := by rw [hPdef, hSdef]
  have hS : v ∉ S := by rw [hSdef]; exact fun h => hv (splitAt_in_snd h)
  have hP : v ∉ P := by rw [hPdef]; exact fun h => hv (splitAt_in_fst h)
  rw [between_of_splitAt hPS, if_neg (mt List.contains_iff_mem.mp hS),
    splitAt_no_ram hP]

/-- 私件：任意 `(P,S) = split_at u s` 下，`s` 的成员都落在
`[u] ++ (S ++ P) ++ [w]`（`split_at u s` 的变体：`u ∈ s` 时
`s = P ++ u :: S`，否则 `s = P ++ S`）。 -/
private theorem mem_cons_splitAt_append [BEq α] [LawfulBEq α] {s : List α}
    {u w x : α} (hx : x ∈ s) :
    x ∈ [u] ++ ((splitAt u s).2 ++ (splitAt u s).1) ++ [w] := by
  by_cases hu : u ∈ s
  · set P := (splitAt u s).1 with hPdef
    set S := (splitAt u s).2 with hSdef
    have hram : s = P ++ u :: S := by
      rw [hPdef, hSdef]
      exact splitAt_ram hu
    rw [hram] at hx
    simp only [List.mem_append, List.mem_cons] at hx ⊢
    tauto
  · rw [splitAt_no_ram hu]
    simp only [List.nil_append, List.mem_append, List.mem_cons]
    tauto

/-- 私件：`s[i]` 在无重表 `s` 中的下标就是 `i`。 -/
private theorem idxOf_getElem_self [BEq α] [LawfulBEq α] {s : List α}
    (hnd : s.Nodup) {i : ℕ} (hi : i < s.length) :
    s.idxOf (s[i]'hi) = i := by
  have hmem : s[i] ∈ s := List.getElem_mem hi
  have hlt : s.idxOf (s[i]'hi) < s.length := List.idxOf_lt_length_iff.mpr hmem
  exact (List.Nodup.getElem_inj_iff hnd).mp (List.getElem_idxOf hlt)

/-- 私件：无重表表头元素的下标为 0（`next_el` 回绕分支的指标桥）。 -/
private theorem idxOf_headD [BEq α] [LawfulBEq α] {s : List α} (_hnd : s.Nodup)
    {u : α} (hu : u ∈ s) : s.idxOf (s.headD u) = 0 := by
  have hsne : s ≠ [] := List.ne_nil_of_mem hu
  rw [List.idxOf_eq_zero_iff_head_eq hsne, List.headD_eq_head?]
  cases h : s.head? with
  | none => exact absurd (List.head?_eq_none_iff.mp h) hsne
  | some a =>
    have hh : s.head hsne = a := by
      rw [List.head?_eq_some_head hsne] at h
      exact Option.some.inj h
    simpa using hh

/-- 私件：无重表 `getD (i+1)` 落在界内时下标即 `i+1`（`next_el` 直进分支）。 -/
private theorem idxOf_getD_succ [BEq α] [LawfulBEq α] {s : List α} (hnd : s.Nodup)
    {u : α} {i : ℕ} (hi : i + 1 < s.length) :
    s.idxOf (s.getD (i + 1) u) = i + 1 := by
  rw [List.getD_eq_getElem s u hi]
  exact idxOf_getElem_self hnd hi

/-- 私件：`next_el` 的最后元素回绕分支。 -/
private theorem nextEl_eq_headD_of_idx [BEq α] {s : List α} {u : α}
    (h : s.idxOf u = s.length - 1) : nextEl s u = s.headD u := by
  unfold nextEl
  rw [if_pos h]

/-- 私件：`next_el` 的直进分支。 -/
private theorem nextEl_eq_getD_of_idx [BEq α] {s : List α} {u : α}
    (h : ¬ s.idxOf u = s.length - 1) : nextEl s u = s.getD (s.idxOf u + 1) u := by
  unfold nextEl
  rw [if_neg h]

/-- 私件：`between` 成员的无重索引刻画（`betwnTakeDrop` 的两分支换成
`idxOf` 区间：直进支 `iu < ix < iv`，回绕支 `iu < ix ∨ ix < iv`）。 -/
private theorem mem_between_iff_idx [BEq α] [LawfulBEq α] {s : List α}
    (hnd : s.Nodup) {u v x : α} (hu : u ∈ s) (hv : v ∈ s) (hx : x ∈ s) :
    x ∈ between s u v ↔
      (if s.idxOf u < s.idxOf v then
        (s.idxOf u < s.idxOf x ∧ s.idxOf x < s.idxOf v)
      else (s.idxOf u < s.idxOf x ∨ s.idxOf x < s.idxOf v)) := by
  have hidx_lt : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hx
  have hidx_u : s.idxOf u < s.length := List.idxOf_lt_length_iff.mpr hu
  have hidx_v : s.idxOf v < s.length := List.idxOf_lt_length_iff.mpr hv
  have hdrop : ∀ {m : ℕ}, x ∈ s.drop m → s.idxOf x = (s.drop m).idxOf x + m := by
    intro m hm
    have hlt : (s.drop m).idxOf x < (s.drop m).length :=
      List.idxOf_lt_length_iff.mpr hm
    have h1 : (s.drop m)[(s.drop m).idxOf x] = x := List.getElem_idxOf hlt
    have hlen : (s.drop m).length = s.length - m := List.length_drop
    have h2 : s[m + (s.drop m).idxOf x] = x := by
      rw [← List.getElem_drop]
      exact h1
    have h3 : s[s.idxOf x] = x := List.getElem_idxOf hidx_lt
    have hinj := (List.Nodup.getElem_inj_iff hnd).mp (h3.trans h2.symm)
    omega
  rw [betwnTakeDrop hnd hv]
  by_cases hlt : s.idxOf u < s.idxOf v
  · rw [if_pos hlt, if_pos hlt]
    constructor
    · intro h
      have hd : x ∈ s.drop (s.idxOf u + 1) := List.mem_of_mem_take h
      have hk : (s.drop (s.idxOf u + 1)).idxOf x
          < s.idxOf v - (s.idxOf u + 1) :=
        (List.mem_take_iff_idxOf_lt (l := s.drop (s.idxOf u + 1)) (a := x) hd).mp h
      have hidx := hdrop hd
      omega
    · intro h
      obtain ⟨h1, h2⟩ := h
      have hd : x ∈ s.drop (s.idxOf u + 1) :=
        (memDropIndex hnd hx).mpr (by omega)
      have hidx := hdrop hd
      exact (List.mem_take_iff_idxOf_lt
        (l := s.drop (s.idxOf u + 1)) (a := x) hd).mpr (by omega)
  · rw [if_neg hlt, if_neg hlt]
    rw [List.mem_append, memDropIndex hnd hx, List.mem_take_iff_idxOf_lt hx]
    constructor
    · rintro (h | h)
      · exact Or.inl (by omega)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl (by omega)
      · exact Or.inr h

/-- 私件：`x ∈ betwn s u v ==> x ∈ [next_el s u] ++ betwn s next_el s u v`
（集合内核：去掉首端点 `u` 后，弧的第一段就是 `next_el u`）。 -/
private theorem betwn_succ_subset [BEq α] [LawfulBEq α] [DecidableEq α] {s : List α}
    (hnd : s.Nodup) {u v : α} (hu : u ∈ s) (hv : v ∈ s) :
    between s u v ⊆ [nextEl s u] ++ between s (nextEl s u) v := by
  intro x hx
  have hx' : x ∈ s := betwnMem hx
  have hw : nextEl s u ∈ s := nextEl_mem_of_mem hu
  have hxu : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hx'
  have hvu : s.idxOf v < s.length := List.idxOf_lt_length_iff.mpr hv
  have huu : s.idxOf u < s.length := List.idxOf_lt_length_iff.mpr hu
  by_cases hxw : x = nextEl s u
  · exact List.mem_append_left _ (by simp [hxw])
  · refine List.mem_append_right _ ?_
    have hne : s.idxOf x ≠ s.idxOf (nextEl s u) := fun h =>
      hxw ((List.idxOf_inj hx').mp h)
    rw [mem_between_iff_idx hnd hu hv hx'] at hx
    rw [mem_between_iff_idx hnd hw hv hx']
    by_cases hlast : s.idxOf u = s.length - 1
    · have hwidx : s.idxOf (nextEl s u) = 0 := by
        rw [nextEl_eq_headD_of_idx hlast]
        exact idxOf_headD hnd hu
      rw [hwidx]
      have hne0 : s.idxOf x ≠ 0 := by rwa [hwidx] at hne
      rw [if_neg (by omega)] at hx
      rcases hx with h | h
      · omega
      · rw [if_pos (by omega)]
        exact ⟨by omega, h⟩
    · have hwidx : s.idxOf (nextEl s u) = s.idxOf u + 1 := by
        rw [nextEl_eq_getD_of_idx hlast]
        exact idxOf_getD_succ hnd (i := s.idxOf u) (by omega)
      rw [hwidx]
      have hne1 : s.idxOf x ≠ s.idxOf u + 1 := by rwa [hwidx] at hne
      by_cases huv : s.idxOf u < s.idxOf v
      · rw [if_pos huv] at hx
        rcases hx with ⟨h1, h2⟩
        by_cases hnext_lt : s.idxOf u + 1 < s.idxOf v
        · rw [if_pos hnext_lt]
          exact ⟨by omega, h2⟩
        · rw [if_neg hnext_lt]
          exact Or.inr h2
      · rw [if_neg huv] at hx
        rw [if_neg (by omega)]
        rcases hx with h | h
        · exact Or.inl (by omega)
        · exact Or.inr h

/-- 私件：`next_el` 右端点前移——`betwn s u (next_el s v) ⊆ betwn s u v ++ [v]`
（集合内核：右端点换成其后继时，多出的唯一元素是 `v` 本身）。 -/
private theorem betwn_next_subset [BEq α] [LawfulBEq α] [DecidableEq α] {s : List α}
    (hnd : s.Nodup) {u v : α} (hu : u ∈ s) (hv : v ∈ s) (huv : u ≠ v) :
    between s u (nextEl s v) ⊆ between s u v ++ [v] := by
  intro x hxw
  have hx : x ∈ s := betwnMem hxw
  have hw : nextEl s v ∈ s := nextEl_mem_of_mem hv
  have hxu : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hx
  have hvu : s.idxOf v < s.length := List.idxOf_lt_length_iff.mpr hv
  have huu : s.idxOf u < s.length := List.idxOf_lt_length_iff.mpr hu
  have hne_uv : s.idxOf u ≠ s.idxOf v := fun h => huv ((List.idxOf_inj hu).mp h)
  by_cases hxv : x = v
  · exact List.mem_append_right _ (by simp [hxv])
  · refine List.mem_append_left _ ?_
    have hne : s.idxOf x ≠ s.idxOf v := fun h =>
      hxv ((List.idxOf_inj hx).mp h)
    rw [mem_between_iff_idx hnd hu hw hx] at hxw
    rw [mem_between_iff_idx hnd hu hv hx]
    by_cases hlast : s.idxOf v = s.length - 1
    · have hwidx : s.idxOf (nextEl s v) = 0 := by
        rw [nextEl_eq_headD_of_idx hlast]
        exact idxOf_headD hnd hv
      rw [hwidx] at hxw
      rw [if_neg (by omega)] at hxw
      by_cases hlt : s.idxOf u < s.idxOf v
      · rw [if_pos hlt]
        rcases hxw with h | h
        · exact ⟨h, by omega⟩
        · omega
      · rw [if_neg hlt]
        rcases hxw with h | h
        · exact Or.inl h
        · omega
    · have hwidx : s.idxOf (nextEl s v) = s.idxOf v + 1 := by
        rw [nextEl_eq_getD_of_idx hlast]
        exact idxOf_getD_succ hnd (i := s.idxOf v) (by omega)
      rw [hwidx] at hxw
      by_cases hlt : s.idxOf u < s.idxOf v
      · rw [if_pos (by omega)] at hxw
        rw [if_pos hlt]
        rcases hxw with ⟨h1, h2⟩
        omega
      · rw [if_neg (by omega)] at hxw
        rw [if_neg hlt]
        rcases hxw with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)

/-- 私件：`u = next_el s v`（`v` 紧邻 `u` 之前）时，`s` 中除端点外的元素
都落在 `betwn s u v`（回绕弧覆盖全表；`betwnNil` 排除反向弧）。 -/
private theorem mem_between_of_nextEl [BEq α] [LawfulBEq α] {s : List α}
    (hnd : s.Nodup) {u v x : α} (hu : u ∈ s) (hv : v ∈ s) (huv : u ≠ v)
    (hnext : u = nextEl s v) (hx : x ∈ s) (hxu : x ≠ u) (hxv : x ≠ v) :
    x ∈ between s u v := by
  rcases betwnCases (s := s) (x := u) (y := x) (z := v) huv hnd hu hx hv with
    h | h | h | h
  · exact absurd h hxu
  · exact absurd h hxv
  · exact h
  · have hnil : between s v u = [] :=
      (betwnNil hnd (Ne.symm huv) hv hu).mpr hnext
    rw [hnil] at h
    exact absurd h (by simp)

/-- 私件：`f1 ++ f2` 覆盖 `r`，其中
`f1 = [next_el r ram1] ++ betwn r next_el r ram1 ram2 ++ [ram2]`，
`f2 = [next_el r ram2] ++ betwn r next_el r ram2 ram1 ++ [ram1]`
（`SPLIT_NORMAL_LIST_CASES` 的集合内核）。 -/
private theorem betwn_or_betwn_cover [BEq α] [LawfulBEq α] [DecidableEq α] {s : List α}
    (hnd : s.Nodup) (ram1 ram2 : α) {x : α} (hx : x ∈ s) :
    x ∈ (([nextEl s ram1] ++ between s (nextEl s ram1) ram2) ++ [ram2]) ++
        (([nextEl s ram2] ++ between s (nextEl s ram2) ram1) ++ [ram1]) := by
  by_cases h1 : ram1 ∈ s
  · by_cases h2 : ram2 ∈ s
    · -- 两端点皆在环上：把环按 next_el 切成两段
      have ha : nextEl s ram1 ∈ s := nextEl_mem_of_mem h1
      have hb : nextEl s ram2 ∈ s := nextEl_mem_of_mem h2
      by_cases h12 : ram1 = ram2
      · -- ram1 = ram2：f1 覆盖全表（a = next ram1 的闭弧到其前驱 ram1）
        have h21 : ram2 = ram1 := h12.symm
        subst ram2
        by_cases hxa : x = nextEl s ram1
        · exact List.mem_append_left
            (([nextEl s ram1] ++ between s (nextEl s ram1) ram1) ++ [ram1])
            (List.mem_append_left [ram1]
              (List.mem_append_left (between s (nextEl s ram1) ram1)
                (by simp [hxa])))
        · by_cases hxr : x = ram1
          · exact List.mem_append_left
              (([nextEl s ram1] ++ between s (nextEl s ram1) ram1) ++ [ram1])
              (List.mem_append_right
                ([nextEl s ram1] ++ between s (nextEl s ram1) ram1)
                (by simp [hxr]))
          · have huv : nextEl s ram1 ≠ ram1 := by
              intro h
              have hs : s = [ram1] := nextElRefl h1 h hnd
              rw [hs] at hx
              exact hxr (by simpa using hx)
            have hbet : x ∈ between s (nextEl s ram1) ram1 :=
              mem_between_of_nextEl hnd ha h1 huv rfl hx hxa hxr
            exact List.mem_append_left
              (([nextEl s ram1] ++ between s (nextEl s ram1) ram1) ++ [ram1])
              (List.mem_append_left [ram1]
                (List.mem_append_right [nextEl s ram1] hbet))
      · by_cases ha2 : nextEl s ram1 = ram2
        · -- next ram1 = ram2：f1 的闭弧退化为 [ram2] ++ betwn ram2 ram2 ++ [ram2]
          by_cases hxa : x = nextEl s ram1
          · exact List.mem_append_left
              (([nextEl s ram2] ++ between s (nextEl s ram2) ram1) ++ [ram1])
              (List.mem_append_left [ram2]
                (List.mem_append_left (between s (nextEl s ram1) ram2)
                  (by simp [hxa])))
          · have hxr2 : x ≠ ram2 := by rwa [ha2] at hxa
            have hbet : x ∈ between s (nextEl s ram1) ram2 := by
              rw [ha2]
              exact (set_between_id hnd h2).mpr ⟨hx, hxr2⟩
            exact List.mem_append_left
              (([nextEl s ram2] ++ between s (nextEl s ram2) ram1) ++ [ram1])
              (List.mem_append_left [ram2]
                (List.mem_append_right [nextEl s ram1] hbet))
        · -- 主情形：betwnCases 把环切成 [a..ram2] 与 [ram2..a]
          rcases betwnCases (s := s) (x := nextEl s ram1) (y := x) (z := ram2)
            ha2 hnd ha hx h2 with hxa | hxr2 | hbet | hbet2
          · exact List.mem_append_left
              (([nextEl s ram2] ++ between s (nextEl s ram2) ram1) ++ [ram1])
              (List.mem_append_left [ram2]
                (List.mem_append_left (between s (nextEl s ram1) ram2)
                  (by simp [hxa])))
          · exact List.mem_append_left
              (([nextEl s ram2] ++ between s (nextEl s ram2) ram1) ++ [ram1])
              (List.mem_append_right
                ([nextEl s ram1] ++ between s (nextEl s ram1) ram2)
                (by simp [hxr2]))
          · exact List.mem_append_left
              (([nextEl s ram2] ++ between s (nextEl s ram2) ram1) ++ [ram1])
              (List.mem_append_left [ram2]
                (List.mem_append_right [nextEl s ram1] hbet))
          · -- x 落在反向弧 [ram2 .. next ram1]：先转成 betwn ram2 ram1，再切 b 段
            have hstep1 : x ∈ between s ram2 ram1 ++ [ram1] :=
              betwn_next_subset (s := s) hnd h2 h1 (Ne.symm h12) hbet2
            rcases List.mem_append.mp hstep1 with h | h
            · have hstep2 : x ∈ [nextEl s ram2] ++ between s (nextEl s ram2) ram1 :=
                betwn_succ_subset (s := s) hnd h2 h1 h
              exact List.mem_append_right
                (([nextEl s ram1] ++ between s (nextEl s ram1) ram2) ++ [ram2])
                (List.mem_append_left [ram1] hstep2)
            · exact List.mem_append_right
                (([nextEl s ram1] ++ between s (nextEl s ram1) ram2) ++ [ram2])
                (List.mem_append_right
                  ([nextEl s ram2] ++ between s (nextEl s ram2) ram1)
                  (by simp [h]))
    · -- ram2 ∉ s：f1 前缀覆盖全表
      have hbetween : between s (nextEl s ram1) ram2 =
          (splitAt (nextEl s ram1) s).2 ++ (splitAt (nextEl s ram1) s).1 :=
        between_of_not_mem_right h2
      have hcover : x ∈ ([nextEl s ram1] ++
          ((splitAt (nextEl s ram1) s).2 ++ (splitAt (nextEl s ram1) s).1))
          ++ [ram2] := mem_cons_splitAt_append hx
      rw [← hbetween] at hcover
      exact List.mem_append_left
        (([nextEl s ram2] ++ between s (nextEl s ram2) ram1) ++ [ram1])
        hcover
  · -- ram1 ∉ s：f2 前缀覆盖全表
    have hbetween : between s (nextEl s ram2) ram1 =
        (splitAt (nextEl s ram2) s).2 ++ (splitAt (nextEl s ram2) s).1 :=
      between_of_not_mem_right h1
    have hcover : x ∈ ([nextEl s ram2] ++
        ((splitAt (nextEl s ram2) s).2 ++ (splitAt (nextEl s ram2) s).1))
        ++ [ram1] := mem_cons_splitAt_append hx
    rw [← hbetween] at hcover
    exact List.mem_append_right
      (([nextEl s ram1] ++ between s (nextEl s ram1) ram2) ++ [ram2])
      hcover

/-! ### §1 SPLIT_NORMAL_LIST_CASES（DANGEYJ.hl:739-:811） -/

/-- **HOL `SPLIT_NORMAL_LIST_CASES`**（DANGEYJ.hl:739）：
`MEM x r /\ uniq r ==>
MEM x (FST (split_normal_list L r f ram1 ram2)) \/
MEM x (SND (split_normal_list L r f ram1 ram2))`。
经 `betwn_or_betwn_cover`（f1/f2 覆盖 r）与 `split_normal_list` 定义展开
（FST = `REVERSE new1 ++ f1`、SND = `f2 ++ new2`）收口。 -/
theorem SPLIT_NORMAL_LIST_CASES {L : fgraph ℕ} {r f : List (ℕ × ℕ)}
    {ram1 ram2 x : ℕ × ℕ} (hx : x ∈ r) (hnd : r.Nodup) :
    x ∈ (splitNormalListSpine L r f ram1 ram2).1 ∨
      x ∈ (splitNormalListSpine L r f ram1 ram2).2 := by
  have hcover := List.mem_append.mp
    (betwn_or_betwn_cover (s := r) hnd ram1 ram2 hx)
  rcases hcover with hmc | hmc
  · left
    unfold splitNormalListSpine
    exact List.mem_append_right _ hmc
  · right
    unfold splitNormalListSpine
    exact List.mem_append_left _ hmc

/-! ### §2 replaceSpine 成员引理（HOL `MEM2_replace`/`MEM3_replace`，tame_list.hl:546-:598）

DANGEYJ 归纳步在 `final_list = F` 支把 `ntrans (j+1)` 展开成
`replace r [SND split] N ++ [FST split]`；结论中面表成员的两种去向正对应
HOL 的 `MEM3_replace`（未命中元素原样保留）与 `MEM2_replace`
（命中元素被新表段替换）。 -/

/-- 私件（HOL `MEM3_replace`，tame_list.hl:583）：替换点未命中时成员原样保留。 -/
private theorem mem_replaceSpine_of_ne [DecidableEq α] {z x : α} {ys xs : List α}
    (hx : x ∈ xs) (hne : x ≠ z) : x ∈ replaceSpine z ys xs := by
  induction xs with
  | nil => exact absurd hx (by simp)
  | cons a t ih =>
    rw [replaceSpine]
    by_cases haz : a = z
    · rw [if_pos haz]
      rcases List.mem_cons.mp hx with h | h
      · subst h
        exact absurd haz hne

      · exact List.mem_append_right _ h
    · rw [if_neg haz]
      rcases List.mem_cons.mp hx with h | h
      · subst h
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

/-- 私件（HOL `MEM2_replace`，tame_list.hl:566）：命中元素被替换段吸收。 -/
private theorem mem_replaceSpine_of_mem [DecidableEq α] {z x : α} {ys xs : List α}
    (hz : z ∈ xs) (hx : x ∈ ys) : x ∈ replaceSpine z ys xs := by
  induction xs with
  | nil => exact absurd hz (by simp)
  | cons a t ih =>
    rw [replaceSpine]
    by_cases haz : a = z
    · rw [if_pos haz]
      exact List.mem_append_left _ hx
    · rw [if_neg haz]
      rcases List.mem_cons.mp hz with h | h
      · exact absurd h.symm haz
      · exact List.mem_cons_of_mem _ (ih h)

/-! ### §3 DANGEYJ_concl / DANGEYJ（DANGEYJ.hl:813-:949） -/

/-- HOL `DANGEYJ_concl`（DANGEYJ.hl:813-:819）的 Lean 载体形：
`transform_assumption_v2 L /\ good_list L /\ good_list_nodes L /\
marked_list L N r x /\ i <= j ==>
set_of_list (flatten (ntrans L N r x i)) SUBSET
set_of_list (flatten (ntrans L N r x j))`。
`transform_assumption_v2`/`good_list_nodes` 的证明参（hta/hgn）与
`good_list` 的证人（hL）按批 17/69 载体约定显式入参。 -/
def DANGEYJ_concl (L : fgraph ℕ) (hL : GoodList L)
    (_hta : transformAssumptionSpine L hL) (_hgn : GoodListNodesTl L hL) : Prop :=
  ∀ (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ)) (x : ℕ × ℕ) (i j : ℕ),
    MarkedListSpineFull hL N r x → i ≤ j →
      setOfListSpine (ntransSpine L N r x i).flatten ⊆
        setOfListSpine (ntransSpine L N r x j).flatten

/-- 私件：DANGEYJ 的归纳步 `ntrans j ⊆ ntrans (j+1)`。
`finalListSpine` 真支 `transform_list` 不动；假支
`ntrans (j+1) = replace R [SND split] M ++ [FST split]`，对 `M` 的每个面表
`l`：`l = R` 时用 `SPLIT_NORMAL_LIST_CASES` 分流（FST 段走 `[FST split]`，
SND 段走 `MEM2_replace`），`l ≠ R` 时走 `MEM3_replace`。 -/
private theorem DANGEYJ_step (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (j : ℕ) :
    setOfListSpine (ntransSpine L N r x j).flatten ⊆
      setOfListSpine (ntransSpine L N r x (j + 1)).flatten := by
  classical
  let M := ntransSpine L N r x j
  let R := rtransSpine L N r x j
  have hmj : MarkedListSpineFull hL M R x := aqiunpp3 L hL j hta hgn hm
  have hn : NormalListSpine hL M := hmj.1.2.1
  have hRM : R ∈ M := hmj.1.2.2.1
  let y := lYSpine L R x
  let z := lZSpine L M R x
  let ram2 := prevEl R z
  let fs := findFaceDarts L y
  let sp := splitNormalListSpine L R fs y ram2
  have hnt : ntransSpine L N r x (j + 1) = (transformListSpine L x (M, R)).1 := by
    show ((transformListSpine L x)^[j + 1] (N, r)).1 = _
    rw [Function.iterate_succ_apply']
    rfl
  have htr : transformListSpine L x (M, R) =
      (if finalListSpine L R then (M, R)
       else (replaceSpine R [sp.2] M ++ [sp.1], sp.2)) := rfl
  by_cases hf : finalListSpine L R
  · rw [hnt, htr, if_pos hf]
  · rw [hnt, htr, if_neg hf]
    intro w hw
    rw [setOfListSpine_mem] at hw ⊢
    rw [List.mem_flatten] at hw ⊢
    obtain ⟨l, hl, hwl⟩ := hw
    by_cases hlR : l = R
    · subst l
      have hRnd : R.Nodup := (List.nodup_flatten.mp hn.1).1 R hRM
      have hsp := SPLIT_NORMAL_LIST_CASES (L := L) (r := R) (f := fs)
        (ram1 := y) (ram2 := ram2) (x := w) hwl hRnd
      rcases hsp with hs | hs
      · refine ⟨sp.1, ?_, hs⟩
        exact List.mem_append_right (replaceSpine R [sp.2] M) (by simp)
      · refine ⟨sp.2, ?_, hs⟩
        exact List.mem_append_left [sp.1]
          (mem_replaceSpine_of_mem (x := sp.2) hRM (by simp))
    · refine ⟨l, ?_, hwl⟩
      exact List.mem_append_left [sp.1] (mem_replaceSpine_of_ne hl hlR)

/-- **HOL `DANGEYJ`**（DANGEYJ.hl:821-:949）：
`transform_assumption_v2 L /\ good_list L /\ good_list_nodes L /\
marked_list L N r x /\ i <= j ==>
set_of_list (flatten (ntrans L N r x i)) SUBSET
set_of_list (flatten (ntrans L N r x j))`。
对 `j` 归纳、`i` 全称（HOL `INDUCT_TAC` 同序）：基 `i = 0` 自反；
步 `i ≤ j` 走归纳假设 + `DANGEYJ_step`，`i = j+1` 自反。 -/
theorem DANGEYJ (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL) :
    DANGEYJ_concl L hL hta hgn := by
  intro N r x i j hm hij
  have key : ∀ j i : ℕ, i ≤ j →
      setOfListSpine (ntransSpine L N r x i).flatten ⊆
        setOfListSpine (ntransSpine L N r x j).flatten := by
    intro j
    induction j with
    | zero =>
      intro i hi
      have hi0 : i = 0 := Nat.le_zero.mp hi
      subst hi0
      intro w hw
      exact hw
    | succ k ih =>
      intro i hi
      rcases Nat.eq_or_lt_of_le hi with heq | hlt
      · subst heq
        intro w hw
        exact hw
      · intro w hw
        exact DANGEYJ_step L hL hta hgn hm k (ih i (Nat.lt_succ_iff.mp hlt) hw)
  exact key j i hij

end Kepler.Text.TameSpine
