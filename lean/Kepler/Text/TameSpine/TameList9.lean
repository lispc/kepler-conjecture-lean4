/-
  Kepler.Text.TameSpine.TameList9 — B1 Tame_list 地基批 9：next_el_cat 族 +
  LAST/HD 词典 + partition_into_atom0r 块（tamespine-port-plan §4 批次表 B1 行；
  接续批 8 = TameList8.lean，HOL :4706-:5579 已由批 8 落，本批从
  `next_el_cat_sym` :5580 起）。

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353，
  text_formalization/tame/tame_list.hl:5580-:6356）：

  - next_el_cat 族 :5580-:5695（`next_el_cat_sym`/`indexl_last`/`indexl_LAST`/
    `next_el_cat1`/`next_el_cat2`/`cat_eq_nil`/`next_el_cat_last2`/
    `next_el_cat_last1`，外加消费点载体件 `Seq2.next_el_last`）；
  - LAST/HD 词典 :5696-:6006（`LAST_find_list`/`find_list_uniq`/
    `next_el_flatten_unlast`/`HD_flatten`/`next_el_flatten_last_hd`/`HD_take`/
    `cat_to`/`next_el_flatten_last`/`rev1`/`LAST_rev`/`cat_from`/`LAST_cat`/
    `HD_rev`/`FORALL_REV_THM`）；
  - partition_into_atom0r 块 :6007-:6356（`partition_into_atom0r_cases`/`partsr`/
    `LISTR_INDUCT`/`LAST_rcons`/`partition_into_atom0r_pure`/`parts_pure`/
    `eqseq_cat2`/`partition_into_atom0r_cons_acc`/`partition_into_atom0r_cat`/
    `parts_cat`/`parts_cases`/`size_induct`/`parts_induct_lemma`/
    `parts_flatten`）。`parts_flatten`（HOL 全书 105 处消费）是本批 capstone，
    在此自然边界收批；`parts_all_nonnil` :6358 起留给批 10（与 `size_induct`
    机械同款）。

  诚实记账（本批跳过/合并/桥引件）：
  - `indexl_last` :5591 与 `indexl_LAST` :5605 在 `LAST/HD ↦ getLast!/head!`
    载体下同形（`last x s` 的 junk 元 x 被默认值吸收），合并为一枚
    `idxOfGetLast`（消费侧全部携带非空 + nodup 折算）；
  - `cat_eq_nil` :5657：本版无 Mathlib `List.append_eq_nil` 名，以载体件
    `catEqNil` 落地；
  - `rev1` :5930 = Mathlib `List.reverse_singleton` 桥引（零移植）；
  - `LAST_rev` :5938/`HD_rev` :5988/`LAST_cat` :5977：Kepler.Graphs.GraphProps
    `getLast!_reverse`/FaceDivisionProps1 `getLast!_append_right` 有孪生，但
    本模块 import 闭包不含 Graphs（批 8 先例：消费定理出现时再桥引），就地
    重推导（`getLast?_reverse`/`head?_reverse`/`getLast?_append_of_ne_nil`
    桥引，各 1-2 行）；
  - `HD_take` :5852 = `List.take_cons` + `head!_cons` 载体件；
  - `FORALL_REV_THM` :5999 = `List.reverse_reverse` 桥引；
  - `partition_into_atom0r`（tame_defs2.hl:123-125）定义层本批补齐为
    `partitionIntoAtom0r`（批 7 的 `partitionIntoAtom` = 其 `acc = []` 特形，
    `partsr` 逐字：`partsSpine L r = partitionIntoAtom0r (fun d => fList L
    (eList d)) [] r`，rfl）；
  - 批 8 私件 `getElemCon`/`nextElOfNotMem'`/`findListSpineHit` 为 private 不
    跨文件可见，本批 §0 同证重推导（批 7→8 惯例）。

  续批（B1 批 9 续二线，前任限额中止后续作；修伤 + 续接批 10 前段）：
  - 修伤：前任遗留 11 处编译错误全清（partitionIntoAtom0rCat 两分支的
    if-链解构/hun'-索引搬运/partsCases 的 push_neg 形状/partsFlatten 幽灵
    if_pos 等，逐处根因见交付报告）；
  - **误植修正**：头注原把 `next_el_flatten_last` :5895 列入镜像清单但正文
    缺席——本批 §4 以 `nextElFlattenLast` 补齐（MEM r s 版，非 HD 特形；
    next_el_parts_last 的直接上游）；
  - 续接 :6357-:6560 纯列表簇：`parts_all_nonnil`/`parts_uniq`/`parts_nonnil`/
    `parts_uniq_nonnil`/`parts_next_unlast`/`parts_next_last`/
    `next_el_parts_unlast`/`next_el_parts_last`/`quotient_all_uniq`/
    `quotient_all_nonnil`/`indexl_next_el`（size_induct 四连 + 直取件）；
  - 续接 :6617-:6740 hypermap 桥簇：`f_list_fst_snd`（zip-环结构，免 uniq）、
    `parts_node_inverse_power`/`parts_in_node`/`parts_fst`/`parts_darts`
    （经 inverseNodeMapList + indexl_next_el + nodeMap 保 FST 迭代不变量；
    parts_last_as_fst_hd :6744 起留批 11）；
  - 复用件：批 8 `inverseNodeMapList`/`indexHd0` 公开直引；批 5
    `uniqFlattenUniq`/`normalListListOfDarts`、批 6 `normalListUniqNonnil`
    同命名空间直引；TameLp `findFaceDarts_ex_of_self`/`fList_prev_inverse`/
    `la7_length_listPairs` 公开直引；
  - `quotient_all_uniq` = MarkedListSpine 第 5 合取块首项直取（批 7 载体
    记账：marked_list 定义层前 7 块镜像，结论零收窄）。

  载体折算（沿批 1-8 约定）：
  - `cat s t` ↦ `s ++ t`、`uniq` ↦ `List.Nodup`、`sizel` ↦ `List.length`；
  - `LAST`/`HD` ↦ `List.getLast!`/`List.head!`（junk 按默认值吸收，消费侧
    携带非空折算）；`rcons t h` ↦ `t ++ [h]`、`flatten` ↦ `List.flatten`、
    `rev` ↦ `List.reverse`、`all P s` ↦ `∀ q ∈ s, P q`；
  - `indexl` ↦ `List.idxOf`、`find_list` ↦ `findListSpine`（批 7）、
    `parts` ↦ `partsSpine`（批 7）、`next_el` ↦ `nextEl`（Assembly）；
  - `f_list L o e_list` ↦ `fun d => fList L (eList d)`。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git 写操作。
-/

import Kepler.Text.TameSpine.TameList8

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl eList fList prevEl GoodList listPairs listOfDarts
  findFaceDarts nList)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (nextEl_eq_getD getD_eq_getElem_of_lt getElem_idxOf
   idxOf_getElem getLastD_eq_getElem_last nextEl_mem_of_mem prevEl_mem_of_mem
   dart_in_face fList_prev_inverse findFaceDarts_ex_of_self la7_length_listPairs
   headD_eq_getD_zero hypermapOfList mem_darts_of_mem_findFace getD_next
   nodeMap_hypermapOfList)

/-! ### §0 next_el/flatten 私有引擎（批 8 私件同证重推导 + 载体小件） -/

/-- 同表两下标相等则取元相等（proof-irrelevant getElem 换形器）。 -/
private theorem getElemCon {l : List (ℕ × ℕ)} {a b : ℕ} (ha : a < l.length)
    (hb : b < l.length) (hab : a = b) : l[a]'ha = l[b]'hb := by
  subst hab; rfl

/-- 表外 `next_el` 恒等（junk 支；非空表版，批 8 私件同证重推导）。 -/
private theorem nextElOfNotMem' {s : List (ℕ × ℕ)} (hne : s ≠ []) {x : ℕ × ℕ}
    (hx : x ∉ s) : nextEl s x = x := by
  have hidx : s.idxOf x = s.length := List.idxOf_eq_length hx
  have hpos : 0 < s.length := List.length_pos_of_ne_nil hne
  show (if s.idxOf x = s.length - 1 then s.headD x
    else s.getD (s.idxOf x + 1) x) = x
  rw [if_neg (by omega : ¬(s.idxOf x = s.length - 1)), hidx,
    List.getD_eq_default s x (by omega)]

/-- 表外 `next_el` 恒等（junk 支；含空表）。 -/
private theorem nextElOfNotMem {s : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hx : x ∉ s) : nextEl s x = x := by
  cases s with
  | nil => rfl
  | cons a l => exact nextElOfNotMem' (by simp) hx

/-- 非空表 `getLast!` 的 getElem? 换形器（proof-free 形，避开 rw motive 陷阱）。 -/
private theorem getLast!EqGet {l : List (ℕ × ℕ)} (hpos : 0 < l.length) :
    l.getLast! = (l[l.length - 1]? : Option (ℕ × ℕ)).getD default := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?]

/-- `l[len-1]` 与 `getLast!` 的项级换形器（calc 收尾用）。 -/
private theorem getElemLastGetLast! {l : List (ℕ × ℕ)} (hpos : 0 < l.length) :
    l[l.length - 1]'(by omega) = l.getLast! := by
  rw [getLast!EqGet hpos, List.getElem?_eq_getElem (by omega)]
  rfl

/-- 非空表 `getLast!` 成员（junk 吸收后的 `LAST`-成员载体件）。 -/
private theorem getLastMem {l : List (ℕ × ℕ)} (h : l ≠ []) : l.getLast! ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t =>
    rw [List.getLast!_cons_eq_getLastD]
    exact List.getLastD_mem_cons

/-- **HOL `indexl_last`/`indexl_LAST`**（tame_list.hl:5591-:5611，两陈述在
getLast! 载体下同形，合并记账见头注）
`uniq s /\ ~(s = []) ==> indexl (LAST s) s = sizel s - 1`。 -/
theorem idxOfGetLast {s : List (ℕ × ℕ)} (hun : s.Nodup) (hne : s ≠ []) :
    s.idxOf s.getLast! = s.length - 1 := by
  have hpos : 0 < s.length := List.length_pos_of_ne_nil hne
  have h1 : (s[s.length - 1]? : Option (ℕ × ℕ)).getD default =
      s[s.length - 1]'(by omega) := by
    rw [List.getElem?_eq_getElem (by omega)]
    rfl
  rw [getLast!EqGet hpos, h1, idxOf_getElem hun (by omega)]

/-- **HOL `Seq2.next_el_last`**（seq2 载体件；tame_list.hl:5816/:5841 消费：
`LAST s` 是 `next_el s` 的不动点。） -/
theorem nextElLast {s : List (ℕ × ℕ)} (hun : s.Nodup) (hne : s ≠ []) :
    nextEl s s.getLast! = s.head! := by
  have hpos : 0 < s.length := List.length_pos_of_ne_nil hne
  have hm : (s.length - 1 + 1) % s.length = 0 := by
    have h1 : s.length - 1 + 1 = s.length := by omega
    rw [h1, Nat.mod_self]
  rw [nextEl_eq_getD (getLastMem hne), idxOfGetLast hun hne, hm,
    getD_eq_getElem_of_lt hpos]
  cases s with
  | nil => simp at hne
  | cons a l => rfl

/-- **HOL `cat_eq_nil`**（tame_list.hl:5657-:5663）
`cat s t = [] <=> (s = [] /\ t = [])`（本版无 `List.append_eq_nil` 名）。 -/
theorem catEqNil {s t : List (ℕ × ℕ)} : s ++ t = [] ↔ s = [] ∧ t = [] := by
  constructor
  · intro h
    have hl : (s ++ t).length = 0 := congrArg List.length h
    rw [List.length_append] at hl
    exact ⟨List.eq_nil_of_length_eq_zero (by omega),
      List.eq_nil_of_length_eq_zero (by omega)⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    rfl

/-- nodup 拼接表两段同元矛盾（cat_sym/词典块共用）。 -/
private theorem nodupAppendDisjoint {s t : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hnd : (s ++ t).Nodup) (hs : x ∈ s) (ht : x ∈ t) : False := by
  have hi : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hs
  have hj : t.idxOf x < t.length := List.idxOf_lt_length_iff.mpr ht
  have h1 : (s ++ t)[s.idxOf x]'(by rw [List.length_append]; omega) = x :=
    (List.getElem_append_left hi).trans (getElem_idxOf hs)
  have h2 : (s ++ t)[s.length + t.idxOf x]'(by rw [List.length_append]; omega) = x :=
    (List.getElem_append_right (Nat.le_add_right s.length (t.idxOf x))).trans
      (((getElemCon (show s.length + t.idxOf x - s.length < t.length by omega) hj
        (show s.length + t.idxOf x - s.length = t.idxOf x by omega)).trans
        (getElem_idxOf ht) : _))
  have h3 := (hnd.getElem_inj_iff
    (hi := (by rw [List.length_append]; omega :
      s.length + t.idxOf x < (s ++ t).length))
    (hj := (by rw [List.length_append]; omega :
      s.idxOf x < (s ++ t).length))).mp (h2.trans h1.symm)
  omega

/-! ### §1 next_el_cat 族（tame_list.hl:5580-:5695） -/

/-- **HOL `next_el_cat1`**（tame_list.hl:5613-:5646）
`uniq s /\ MEM x s /\ ~(x = LAST s) ==> next_el (cat s t) x = next_el s x`
——`idxOf_append_of_mem` + 双侧 `getD`-`getElem` 归一。 -/
theorem nextElCat1 {s t : List (ℕ × ℕ)} (hsn : s.Nodup) {x : ℕ × ℕ}
    (hx : x ∈ s) (hx2 : x ≠ s.getLast!) :
    nextEl (s ++ t) x = nextEl s x := by
  have hpos : 0 < s.length := List.length_pos_of_mem hx
  have hidx : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hx
  have hlast : s.idxOf x ≠ s.length - 1 := by
    intro hc
    refine hx2 ?_
    have heq : s[s.idxOf x]'hidx = s[s.length - 1]'(by omega) :=
      getElemCon hidx (by omega) hc
    calc x = s[s.idxOf x]'hidx := (getElem_idxOf hx).symm
      _ = s[s.length - 1]'(by omega) := heq
      _ = s.getLast! := getElemLastGetLast! hpos
  have hj1 : s.idxOf x + 1 < s.length := by omega
  rw [nextEl_eq_getD (List.mem_append.mpr (Or.inl hx)), nextEl_eq_getD hx,
    List.idxOf_append_of_mem hx,
    Nat.mod_eq_of_lt (show s.idxOf x + 1 < (s ++ t).length from by
      rw [List.length_append]; omega),
    getD_eq_getElem_of_lt (show s.idxOf x + 1 < (s ++ t).length from by
      rw [List.length_append]; omega),
    Nat.mod_eq_of_lt hj1,
    getD_eq_getElem_of_lt hj1, List.getElem_append_left hj1]

/-- **HOL `next_el_cat_last1`**（tame_list.hl:5683-:5694）
`uniq (cat s t) /\ ~(t = []) /\ ~(s = []) ==> next_el (cat s t) (LAST s) = HD t`
——`idxOf_append_of_mem` + 末位 wrap。 -/
theorem nextElCatLast1 {s t : List (ℕ × ℕ)} (hnd : (s ++ t).Nodup)
    (hs : s ≠ []) (ht : t ≠ []) :
    nextEl (s ++ t) s.getLast! = t.head! := by
  have hpos : 0 < s.length := List.length_pos_of_ne_nil hs
  have htl : 0 < t.length := List.length_pos_of_ne_nil ht
  have hsn : s.Nodup := List.Sublist.nodup (List.sublist_append_left s t) hnd
  rw [nextEl_eq_getD (List.mem_append.mpr (Or.inl (getLastMem hs))),
    List.idxOf_append_of_mem (getLastMem hs), idxOfGetLast hsn hs,
    show s.length - 1 + 1 = s.length from by omega,
    Nat.mod_eq_of_lt (show s.length < (s ++ t).length from by
      rw [List.length_append]; omega),
    getD_eq_getElem_of_lt (show s.length < (s ++ t).length from by
      rw [List.length_append]; omega)]
  exact (List.getElem_append_right (Nat.le_refl s.length)).trans
    (((getElemCon (show s.length - s.length < t.length by omega) htl
      (Nat.sub_self s.length)).trans
      (by cases t with
        | nil => exact absurd rfl ht
        | cons a l => rfl) : _))

/-- **HOL `next_el_cat2`**（tame_list.hl:5648-:5655）
`uniq (cat s t) /\ MEM x t /\ ~(x = LAST t) ==> next_el (cat s t) x = next_el t x`
——`idxOf_append_of_notMem` + nodup 拆位（不经过 cat_sym，避免循环）。 -/
theorem nextElCat2 {s t : List (ℕ × ℕ)} (hnd : (s ++ t).Nodup) {x : ℕ × ℕ}
    (hx : x ∈ t) (hx2 : x ≠ t.getLast!) :
    nextEl (s ++ t) x = nextEl t x := by
  have htl : 0 < t.length := List.length_pos_of_mem hx
  have htn : t.Nodup := List.Sublist.nodup (List.sublist_append_right s t) hnd
  have hsout : x ∉ s := fun hc => nodupAppendDisjoint hnd hc hx
  have hidx : t.idxOf x < t.length := List.idxOf_lt_length_iff.mpr hx
  have hj1 : t.idxOf x + 1 < t.length := by
    have hx2' : t.idxOf x ≠ t.length - 1 := by
      intro hc
      refine hx2 ?_
      have heq : t[t.idxOf x]'hidx = t[t.length - 1]'(by omega) :=
        getElemCon hidx (by omega) hc
      calc x = t[t.idxOf x]'hidx := (getElem_idxOf hx).symm
        _ = t[t.length - 1]'(by omega) := heq
        _ = t.getLast! := getElemLastGetLast! htl
    omega
  rw [nextEl_eq_getD (List.mem_append.mpr (Or.inr hx)), nextEl_eq_getD hx,
    List.idxOf_append_of_notMem hsout,
    show (s.length + t.idxOf x) + 1 = s.length + (t.idxOf x + 1) from by omega,
    Nat.mod_eq_of_lt (show s.length + (t.idxOf x + 1) < (s ++ t).length from by
      rw [List.length_append]; omega),
    getD_eq_getElem_of_lt (show s.length + (t.idxOf x + 1) < (s ++ t).length from by
      rw [List.length_append]; omega),
    Nat.mod_eq_of_lt hj1,
    getD_eq_getElem_of_lt hj1]
  exact (List.getElem_append_right
      (show s.length ≤ s.length + (t.idxOf x + 1) by omega)).trans
    (getElemCon (show s.length + (t.idxOf x + 1) - s.length < t.length by omega) hj1
      (show s.length + (t.idxOf x + 1) - s.length = t.idxOf x + 1 by omega))

/-- **HOL `next_el_cat_sym`**（tame_list.hl:5580-:5589）
`!s t. uniq (cat s t) ==> next_el (cat s t) = next_el (cat t s)`
——逐点分类（普通成员/末位/表外）；末位支双侧下标 wrap
（避开 omega-in-rw-arg：末位支长度事实全部走 `Nat.lt_add_of_pos_right` 等
显式 Nat 件）。 -/
theorem nextElCatSym {s t : List (ℕ × ℕ)} (hnd : (s ++ t).Nodup) :
    nextEl (s ++ t) = nextEl (t ++ s) := by
  have hnd2 : (t ++ s).Nodup :=
    List.Perm.nodup (List.perm_append_comm (l₁ := s) (l₂ := t)) hnd
  refine funext fun x => ?_
  by_cases hx : x ∈ s ++ t
  · rcases List.mem_append.mp hx with hxs | hxt
    · by_cases hxt' : x ∈ t
      · exact (nodupAppendDisjoint hnd hxs hxt').elim
      · have hs : s ≠ [] := List.ne_nil_of_mem hxs
        have hspos : 0 < s.length := List.length_pos_of_ne_nil hs
        have hsn : s.Nodup := List.Sublist.nodup (List.sublist_append_left s t) hnd
        by_cases hx2 : x = s.getLast!
        · -- 末位支：LHS = HD t；RHS 下标 wrap 同值
          by_cases ht0 : t = []
          · rw [ht0, List.append_nil, List.nil_append, hx2, nextElLast hsn hs]
          · have ht : t ≠ [] := ht0
            have htl : 0 < t.length := List.length_pos_of_ne_nil ht
            have hsout : s.getLast! ∉ t := by
              rw [← hx2]; exact hxt'
            rw [hx2, nextElCatLast1 hnd hs ht,
              nextEl_eq_getD (List.mem_append.mpr (Or.inr (getLastMem hs))),
              List.idxOf_append_of_notMem hsout, idxOfGetLast hsn hs,
              show t.length + (s.length - 1) + 1 = (t ++ s).length from by
                rw [List.length_append, Nat.add_assoc,
                  Nat.sub_one_add_one (by omega : s.length ≠ 0)],
              Nat.mod_self,
              getD_eq_getElem_of_lt (by
                rw [List.length_append]
                exact Nat.add_pos_right _ hspos),
              List.getElem_append_left htl]
            cases t with
            | nil => exact absurd rfl ht
            | cons a l => rfl
        · have htn : t.Nodup :=
            List.Sublist.nodup (List.sublist_append_right s t) hnd
          rw [nextElCat1 hsn hxs hx2, nextElCat2 hnd2 hxs hx2]
    · by_cases hxs' : x ∈ s
      · exact (nodupAppendDisjoint hnd hxs' hxt).elim
      · have ht : t ≠ [] := List.ne_nil_of_mem hxt
        have htn : t.Nodup :=
          List.Sublist.nodup (List.sublist_append_right s t) hnd
        by_cases hx2 : x = t.getLast!
        · -- 末位支（镜像）：LHS = HD s；RHS 经 t 段下标 wrap 同值
          by_cases hs0 : s = []
          · rw [hs0, List.nil_append, List.append_nil, hx2, nextElLast htn ht]
          · have hs : s ≠ [] := hs0
            have hsl : 0 < s.length := List.length_pos_of_ne_nil hs
            have htl : 0 < t.length := List.length_pos_of_ne_nil ht
            have hsout : t.getLast! ∉ s := by
              rw [← hx2]; exact hxs'
            have hlt : t.length < (t ++ s).length := by
              rw [List.length_append]
              exact Nat.lt_add_of_pos_right hsl
            have hidx : (t ++ s).idxOf t.getLast! + 1 = t.length := by
              rw [List.idxOf_append_of_mem (getLastMem ht), idxOfGetLast htn ht,
                Nat.sub_one_add_one (by omega : t.length ≠ 0)]
            have hrhs : nextEl (t ++ s) x = s[0]'hsl := by
              rw [hx2, nextEl_eq_getD (List.mem_append.mpr (Or.inl (getLastMem ht))),
                hidx, Nat.mod_eq_of_lt hlt, getD_eq_getElem_of_lt hlt]
              exact (List.getElem_append_right (Nat.le_refl t.length)).trans
                (getElemCon (by rw [Nat.sub_self]; exact hsl) hsl
                  (Nat.sub_self t.length))
            have hlhs : nextEl (s ++ t) x = s[0]'hsl := by
              rw [hx2, nextEl_eq_getD (List.mem_append.mpr (Or.inr (getLastMem ht))),
                List.idxOf_append_of_notMem hsout, idxOfGetLast htn ht,
                show s.length + (t.length - 1) + 1 = (s ++ t).length from by
                  rw [List.length_append, Nat.add_assoc,
                    Nat.sub_one_add_one (by omega : t.length ≠ 0)],
                Nat.mod_self,
                getD_eq_getElem_of_lt (by
                  rw [List.length_append]
                  exact Nat.add_pos_right _ htl),
                List.getElem_append_left hsl]
            rw [hlhs, hrhs]
        · rw [nextElCat2 hnd hxt hx2, nextElCat1 htn hxt hx2]
  · have hx2 : x ∉ t ++ s := by
      intro hc
      rcases List.mem_append.mp hc with h | h
      · exact hx (List.mem_append.mpr (Or.inr h))
      · exact hx (List.mem_append.mpr (Or.inl h))
    rw [nextElOfNotMem hx, nextElOfNotMem hx2]

/-- **HOL `next_el_cat_last2`**（tame_list.hl:5665-:5681）
`uniq (cat s t) /\ ~(t = []) /\ ~(s = []) ==> next_el (cat s t) (LAST t) = HD s`
——cat_sym + cat_last1 换位。 -/
theorem nextElCatLast2 {s t : List (ℕ × ℕ)} (hnd : (s ++ t).Nodup)
    (hs : s ≠ []) (ht : t ≠ []) :
    nextEl (s ++ t) t.getLast! = s.head! := by
  have hnd2 : (t ++ s).Nodup :=
    List.Perm.nodup (List.perm_append_comm (l₁ := s) (l₂ := t)) hnd
  rw [nextElCatSym hnd]
  exact nextElCatLast1 hnd2 ht hs

/-! ### §2 LAST/HD 词典 + flatten 块（tame_list.hl:5696-:6006；
为依赖序把词典小块前置，flatten 群随后，HOL 行号逐件对账） -/

/-- **HOL `LAST_cat`**（tame_list.hl:5977-:5986）
`~(v = []) ==> LAST (cat u v) = LAST v`。 -/
theorem lastCat {u v : List (ℕ × ℕ)} (hv : v ≠ []) :
    (u ++ v).getLast! = v.getLast! := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_append_of_ne_nil _ hv,
    List.getLast!_eq_getLast?_getD]

/-- **HOL `HD_take`**（tame_list.hl:5852-:5863）
`~(i = 0) /\ ~(s = []) ==> HD (take i s) = HD s`。 -/
theorem hdTake {s : List (ℕ × ℕ)} {i : ℕ} (hi : i ≠ 0) (hs : s ≠ []) :
    (s.take i).head! = s.head! := by
  cases i with
  | zero => exact absurd rfl hi
  | succ n =>
    cases s with
    | nil => exact absurd rfl hs
    | cons a l => rfl

/-- **HOL `rev1`**（tame_list.hl:5930-:5936）`rev [h] = [h]`
（= Mathlib `List.reverse_singleton` 桥引）。 -/
theorem rev1 (h : ℕ × ℕ) : [h].reverse = [h] :=
  List.reverse_singleton

/-- **HOL `LAST_rev`**（tame_list.hl:5938-:5957）
`~(t = []) ==> LAST (rev t) = HD t`（junk 载体下实际无条件成立，记账见头注）。 -/
theorem lastRev (t : List (ℕ × ℕ)) : t.reverse.getLast! = t.head! := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_reverse,
    ← List.head!_eq_head?_getD]

/-- **HOL `HD_rev`**（tame_list.hl:5988-:5997）
`~(t = []) ==> HD (rev t) = LAST t`（同上无条件）。 -/
theorem hdRev (t : List (ℕ × ℕ)) : t.reverse.head! = t.getLast! := by
  rw [List.head!_eq_head?_getD, List.head?_reverse, ← List.getLast!_eq_getLast?_getD]

/-- **HOL `FORALL_REV_THM`**（tame_list.hl:5999-:6005）
`(!r. f (rev r)) <=> (!r. f r)`。 -/
theorem forallRevThm {f : List (ℕ × ℕ) → Prop} :
    (∀ r : List (ℕ × ℕ), f r.reverse) ↔ ∀ r : List (ℕ × ℕ), f r := by
  constructor
  · intro h r
    have := h r.reverse
    rwa [List.reverse_reverse] at this
  · exact fun h r => h r.reverse

/-- **HOL `cat_to`**（tame_list.hl:5865-:5893）
`MEM x s ==> (?a b. s = cat a b /\ x = HD b /\ ~(b = []))`。 -/
theorem catTo {x : ℕ × ℕ} {s : List (ℕ × ℕ)} (hx : x ∈ s) :
    ∃ a b : List (ℕ × ℕ), s = a ++ b ∧ b.head! = x ∧ b ≠ [] := by
  obtain ⟨a, b, hab⟩ := List.append_of_mem hx
  exact ⟨a, x :: b, hab, rfl, by simp⟩

/-- **HOL `LAST_rcons`**（tame_list.hl:6046-:6052，:5959 cat_from 消费前置）
`LAST (rcons t h) = h`。 -/
theorem lastRcons (t : List (ℕ × ℕ)) (h : ℕ × ℕ) :
    (t ++ [h]).getLast! = h := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_append_of_ne_nil _ (by simp)]
  simp

/-- **HOL `cat_from`**（tame_list.hl:5959-:5975）
`MEM x s ==> (?a b. s = cat a b /\ x = LAST a /\ ~(a = []))`。 -/
theorem catFrom {x : ℕ × ℕ} {s : List (ℕ × ℕ)} (hx : x ∈ s) :
    ∃ a b : List (ℕ × ℕ), s = a ++ b ∧ a.getLast! = x ∧ a ≠ [] := by
  obtain ⟨a, b, hab⟩ := List.append_of_mem (List.mem_reverse.mpr hx)
  have key : (a ++ x :: b).reverse = (b.reverse ++ [x]) ++ a.reverse := by
    rw [List.reverse_append, List.reverse_cons]
  rw [← hab, List.reverse_reverse] at key
  exact ⟨b.reverse ++ [x], a.reverse, key, lastRcons b.reverse x, by simp⟩

/-- **HOL `HD_flatten`**（tame_list.hl:5786-:5801）
`~(flatten t = []) /\ ~(HD t = []) ==> HD (flatten t) = HD (HD t)`。 -/
theorem hdFlatten {L : List (List (ℕ × ℕ))} (hne : L.flatten ≠ [])
    (hh : L.head! ≠ []) : L.flatten.head! = L.head!.head! := by
  cases L with
  | nil => exact absurd (by rfl : ([] : List (List (ℕ × ℕ))).flatten = []) hne
  | cons h t =>
    have hh' : h ≠ [] := hh
    rw [List.flatten_cons, List.head!_append _ hh']
    rfl

/-- **HOL `next_el_flatten_last_hd`**（tame_list.hl:5803-:5850）
`uniq (flatten s) /\ all (\r. ~(r = [])) s /\ r = HD s /\ ~(s = []) ==>
  next_el (flatten s) (LAST r) = HD (next_el s r)`。 -/
theorem nextElFlattenLastHd {L : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    (hun : L.flatten.Nodup) (hn : ∀ q ∈ L, q ≠ []) (hr : r = L.head!)
    (hL : L ≠ []) :
    nextEl L.flatten r.getLast! = (nextEl L r).head! := by
  cases L with
  | nil => exact absurd rfl hL
  | cons hh0 t =>
    have hr' : r = hh0 := hr
    subst hr'
    have hh : r ≠ [] := hn r (List.mem_cons_self ..)
    by_cases ht0 : t = []
    · subst ht0
      rw [List.flatten_cons, List.flatten_nil, List.append_nil] at hun
      rw [List.flatten_cons, List.flatten_nil, List.append_nil, nextElLast hun hh]
      have hrhs : nextEl [r] r = r := by
        rw [nextEl_eq_getD (List.mem_cons_self ..), List.idxOf_cons_self]
        have h1 : (0 + 1) % [r].length = 0 := by
          rw [show [r].length = 1 from rfl]
        rw [h1, getD_eq_getElem_of_lt (List.length_pos_of_ne_nil (by simp))]
        rfl
      rw [hrhs]
    · have ht : t ≠ [] := ht0
      have htl : 0 < t.length := List.length_pos_of_ne_nil ht
      have htf : t.flatten ≠ [] := by
        cases t with
        | nil => exact absurd rfl ht
        | cons q u =>
          have hq : q ≠ [] := hn q
            (List.mem_cons_of_mem _ (List.mem_cons_self (a := q)))
          have hd : q.getLast! ∈ (q :: u).flatten := by
            rw [List.flatten_cons]
            exact List.mem_append.mpr (Or.inl (getLastMem hq))
          exact List.ne_nil_of_mem hd
      have htnn : t.head! ≠ [] := hn t.head!
        (List.mem_cons_of_mem _ (List.head!_mem_self ht))
      have hrhs : nextEl (r :: t) r = t.head! := by
        rw [nextEl_eq_getD (List.mem_cons_self ..), List.idxOf_cons_self,
          show (0 + 1) % (r :: t).length = 1 from Nat.mod_eq_of_lt
            (by rw [List.length_cons]; omega),
          getD_eq_getElem_of_lt (by rw [List.length_cons]; omega),
          List.getElem_cons_succ]
        cases t with
        | nil => exact absurd rfl ht
        | cons a l => rfl
      rw [List.flatten_cons] at hun
      rw [List.flatten_cons, nextElCatLast1 hun hh htf, hdFlatten htf htnn, hrhs]

/-- **HOL `LISTR_INDUCT`** 的 flatten-双块矛盾载体：
`d` 同属 dart-list 首块与尾段 flatten 时破坏 nodup。 -/
private theorem nodupAppendFlattenContra {h : List (ℕ × ℕ)}
    {t : List (List (ℕ × ℕ))} {d : ℕ × ℕ}
    (hun : (h ++ t.flatten).Nodup) (hd : d ∈ h) (hdt : d ∈ t.flatten) : False := by
  have hi : h.idxOf d < h.length := List.idxOf_lt_length_iff.mpr hd
  have hj : t.flatten.idxOf d < t.flatten.length := List.idxOf_lt_length_iff.mpr hdt
  have h1 : (h ++ t.flatten)[h.idxOf d]'(by rw [List.length_append]; omega) = d :=
    (List.getElem_append_left hi).trans (getElem_idxOf hd)
  have h2 : (h ++ t.flatten)[h.length + t.flatten.idxOf d]'(
      by rw [List.length_append]; omega) = d :=
    (List.getElem_append_right (Nat.le_add_right h.length (t.flatten.idxOf d))).trans
      ((getElemCon
        (show h.length + t.flatten.idxOf d - h.length < t.flatten.length by omega)
        hj
        (show h.length + t.flatten.idxOf d - h.length = t.flatten.idxOf d by omega)).trans
        (getElem_idxOf hdt))
  have h3 := (hun.getElem_inj_iff
    (hi := (by rw [List.length_append]; omega :
      h.length + t.flatten.idxOf d < (h ++ t.flatten).length))
    (hj := (by rw [List.length_append]; omega :
      h.idxOf d < (h ++ t.flatten).length))).mp (h2.trans h1.symm)
  omega

/-- flatten nodup 时同一 dart 不能分属两个成员表。 -/
private theorem flattenNodupMemUnique {L : List (List (ℕ × ℕ))} {x : ℕ × ℕ}
    {r b : List (ℕ × ℕ)}
    (hun : L.flatten.Nodup) (hr : r ∈ L) (hb : b ∈ L) (hxr : x ∈ r) (hxb : x ∈ b) :
    r = b := by
  induction L generalizing r b with
  | nil => cases hr
  | cons c t ih =>
    rw [List.flatten_cons] at hun
    rcases List.mem_cons.mp hr with hr' | hr'
    · subst hr'
      rcases List.mem_cons.mp hb with hb' | hb'
      · exact hb'.symm
      · exact (nodupAppendFlattenContra hun hxr
          (List.mem_flatten.mpr ⟨b, hb', hxb⟩)).elim
    · rcases List.mem_cons.mp hb with hb' | hb'
      · subst hb'
        exact (nodupAppendFlattenContra hun hxb
          (List.mem_flatten.mpr ⟨r, hr', hxr⟩)).elim
      · exact ih
          (List.Sublist.nodup (List.sublist_append_right c t.flatten) hun) hr' hb' hxr hxb

/-- **HOL `mem_find_list`** 命中半向的合并载体件（批 8 §1 私件同证重推导）：
`x ∈ flatten N` 时 `findListSpine N x` 命中且 ∈ N。 -/
private theorem findListSpineHit {N : List (List (ℕ × ℕ))} {x : ℕ × ℕ}
    (hx : x ∈ N.flatten) : findListSpine N x ∈ N ∧ x ∈ findListSpine N x := by
  induction N with
  | nil => exact absurd hx (by simp)
  | cons h t ih =>
    rw [List.flatten_cons, List.mem_append] at hx
    by_cases hmem : x ∈ h
    · have hf : (h :: t).find? (fun r => decide (x ∈ r)) = some h := by
        rw [List.find?_cons, decide_eq_true hmem]
      simp only [findListSpine, hf, Option.getD_some]
      exact ⟨List.mem_cons_self .., decide_eq_true_eq.mp (decide_eq_true hmem)⟩
    · have hp : decide (x ∈ h) = false := decide_eq_false hmem
      have hf : (h :: t).find? (fun r => decide (x ∈ r))
          = t.find? (fun r => decide (x ∈ r)) := by
        rw [List.find?_cons, hp]
      obtain ⟨hm1, hm2⟩ := ih (by
        rcases hx with hxl | hxr
        · exact absurd hxl hmem
        · exact hxr)
      simp only [findListSpine, hf]
      exact ⟨List.mem_cons_of_mem _ hm1, hm2⟩

/-- **HOL `find_list_uniq`**（tame_list.hl:5731-:5750）
`uniq (flatten L) /\ MEM x s /\ MEM s L ==> find_list L x = s`。 -/
theorem findListUniq {L : List (List (ℕ × ℕ))} {s : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hun : L.flatten.Nodup) (hxs : x ∈ s) (hs : s ∈ L) : findListSpine L x = s := by
  obtain ⟨h1, h2⟩ := findListSpineHit (List.mem_flatten.mpr ⟨s, hs, hxs⟩)
  exact flattenNodupMemUnique hun h1 hs h2 hxs

/-- **HOL `LAST_find_list`**（tame_list.hl:5696-:5729）
`x = LAST (flatten s) /\ ~(flatten s = []) /\ uniq (flatten s) ==>
  LAST (find_list s x) = x`。 -/
theorem lastFindList {N : List (List (ℕ × ℕ))} {x : ℕ × ℕ}
    (hx : x = N.flatten.getLast!) (hne : N.flatten ≠ []) (hun : N.flatten.Nodup) :
    (findListSpine N x).getLast! = x := by
  induction N with
  | nil => exact absurd (by rfl : ([] : List (List (ℕ × ℕ))).flatten = []) hne
  | cons h t ih =>
    rw [List.flatten_cons] at hx hne hun
    by_cases hxh : x ∈ h
    · have hf : (h :: t).find? (fun r => decide (x ∈ r)) = some h := by
        rw [List.find?_cons, decide_eq_true hxh]
      simp only [findListSpine, hf, Option.getD_some]
      by_cases ht0 : t.flatten = []
      · rw [ht0, List.append_nil] at hx
        exact hx.symm
      · have hxf : x ∈ t.flatten := by
          rw [hx, lastCat ht0]
          exact getLastMem ht0
        exact (nodupAppendFlattenContra hun hxh hxf).elim
    · have hp : decide (x ∈ h) = false := decide_eq_false hxh
      have hf : (h :: t).find? (fun r => decide (x ∈ r))
          = t.find? (fun r => decide (x ∈ r)) := by
        rw [List.find?_cons, hp]
      simp only [findListSpine, hf]
      have htfne : t.flatten ≠ [] := by
        intro hc
        have hh : h ≠ [] := by
          intro h0
          rw [h0, hc, List.append_nil] at hne
          exact hne rfl
        rw [hc, List.append_nil] at hx
        have hmem : x ∈ h := by rw [hx]; exact getLastMem hh
        exact hxh hmem
      have hun' : t.flatten.Nodup :=
        List.Sublist.nodup (List.sublist_append_right h t.flatten) hun
      have hx' : x = t.flatten.getLast! := by
        rw [hx, lastCat htfne]
      exact ih hx' htfne hun'


/-- **HOL** 词典推论：`x = LAST (flatten L)` 时含 `x` 的成员表以 `x` 收尾
（flattenLastMem = lastFindList + findListUniq 推论）。 -/
private theorem flattenLastMem {L : List (List (ℕ × ℕ))} (hun : L.flatten.Nodup)
    (hne : L.flatten ≠ []) {x : ℕ × ℕ} {r : List (ℕ × ℕ)} (hr : r ∈ L) (hxr : x ∈ r)
    (hx : x = L.flatten.getLast!) : x = r.getLast! := by
  have hfl : findListSpine L x = r := findListUniq hun hxr hr
  have hlast := lastFindList hx hne hun
  rw [hfl] at hlast
  exact hlast.symm

/-- **HOL `next_el_flatten_unlast`**（tame_list.hl:5752-:5784）
`uniq (flatten s) /\ MEM x r /\ MEM r s /\ ~(x = LAST r) ==>
  next_el (flatten s) x = next_el r x`
——对 `L` 归纳：`r = HD L` 走 cat1；`r ∈ TL` 走 cat2（x ≠ LAST (flatten TL) 由
flattenLastMem + findListUniq 从 x ≠ LAST r 推出）。 -/
theorem nextElFlattenUnlast {L : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hun : L.flatten.Nodup) (hxr : x ∈ r) (hr : r ∈ L)
    (hx2 : x ≠ r.getLast!) : nextEl L.flatten x = nextEl r x := by
  induction L with
  | nil => cases hr
  | cons h t ih =>
    rw [List.flatten_cons] at hun
    rw [List.flatten_cons]
    rcases List.mem_cons.mp hr with heq | hmem
    · rw [heq] at hxr hx2 ⊢
      have hsn : h.Nodup :=
        List.Sublist.nodup (List.sublist_append_left h t.flatten) hun
      exact nextElCat1 hsn hxr hx2
    · have hxf : x ∈ t.flatten := List.mem_flatten.mpr ⟨r, hmem, hxr⟩
      have htfne : t.flatten ≠ [] := List.ne_nil_of_mem hxf
      have hx2' : x ≠ t.flatten.getLast! := by
        intro hc
        refine hx2 ?_
        exact flattenLastMem
          (List.Sublist.nodup (List.sublist_append_right h t.flatten) hun) htfne
          hmem hxr hc
      rw [nextElCat2 hun
        (List.mem_flatten.mpr ⟨r, hmem, hxr⟩) hx2']
      exact ih
        (List.Sublist.nodup (List.sublist_append_right h t.flatten) hun) hmem


/-! ### §3 partition_into_atom0r 块（tame_list.hl:6007-:6356） -/

/-- HOL `partition_into_atom0r`（tame_defs2.hl:123-125）逐句镜像：
`partition_into_atom0r n acc r = partition_into_atom0 n acc (rev r)`。
批 7 的 `partitionIntoAtom` 是其 `acc = []` 特形（`partsr` 逐字，rfl）。 -/
def partitionIntoAtom0r (n : ℕ × ℕ → ℕ × ℕ) (acc : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) : List (List (ℕ × ℕ)) :=
  partitionIntoAtom0 n acc r.reverse

/-- **HOL `partition_into_atom0r_cases`**（tame_list.hl:6007-:6020）
nil 方程 + rcons（`rcons rs r` ↦ `rs ++ [r]`）方程。 -/
theorem partitionIntoAtom0rCases (n : ℕ × ℕ → ℕ × ℕ)
    (acc : List (List (ℕ × ℕ))) (rs : List (ℕ × ℕ)) (r : ℕ × ℕ) :
    partitionIntoAtom0r n acc [] = acc ∧
    partitionIntoAtom0r n acc (rs ++ [r]) =
      (if acc = [] then partitionIntoAtom0r n [[r]] rs
       else if n r = acc.head!.head! then
         partitionIntoAtom0r n ((r :: acc.head!) :: acc.tail) rs
       else partitionIntoAtom0r n ([r] :: acc) rs) := by
  constructor
  · rfl
  · have hrev : ∀ rs : List (ℕ × ℕ), (rs ++ [r]).reverse = r :: rs.reverse := by
      intro rs
      induction rs with
      | nil => rfl
      | cons a t iha =>
        rw [List.cons_append, List.reverse_cons, iha, List.cons_append,
          List.reverse_cons]
    show partitionIntoAtom0 n acc ((rs ++ [r]).reverse) = _
    rw [hrev rs, partitionIntoAtom0]
    simp only [partitionIntoAtom0r]

/-- **HOL `LISTR_INDUCT`**（tame_list.hl:6030-:6040）右归纳原理
（`rcons` 归纳经 `reverse` 双向搬运）。 -/
theorem listrInduct {motive : List (ℕ × ℕ) → Prop} (h0 : motive [])
    (hstep : ∀ (h : ℕ × ℕ) (t : List (ℕ × ℕ)), motive t → motive (t ++ [h]))
    (r : List (ℕ × ℕ)) : motive r := by
  have key : ∀ l : List (ℕ × ℕ), motive l.reverse := by
    intro l
    induction l with
    | nil => simpa using h0
    | cons h t ih =>
      rw [List.reverse_cons]
      exact hstep h t.reverse ih
  have hr2 : r = r.reverse.reverse := (List.reverse_reverse r).symm
  rw [hr2]
  exact key r.reverse

/-- **HOL `partition_into_atom0r_pure`**（tame_list.hl:6054-:6109）
`~(r = []) /\ uniq r /\ (!x. MEM x r ==> x = LAST r \/ next_el r x = n x) ==>
  partition_into_atom0r n a r =
    if (a = [] \/ ~(n (LAST r) = HD (HD a))) then r :: a
    else (cat r (HD a)) :: TL a`
（右归纳；归纳假设对累加器 a 全称量化——merge 分支的 acc 依赖它）。 -/
theorem partitionIntoAtom0rPure (n : ℕ × ℕ → ℕ × ℕ) (a : List (List (ℕ × ℕ)))
    {r : List (ℕ × ℕ)} (hne : r ≠ []) (hun : r.Nodup)
    (hp : ∀ x ∈ r, x = r.getLast! ∨ nextEl r x = n x) :
    partitionIntoAtom0r n a r =
      if a = [] ∨ n r.getLast! ≠ a.head!.head! then r :: a
      else (r ++ a.head!) :: a.tail := by
  refine listrInduct (motive := fun w => w ≠ [] → w.Nodup →
    (∀ x ∈ w, x = w.getLast! ∨ nextEl w x = n x) →
    ∀ a' : List (List (ℕ × ℕ)), partitionIntoAtom0r n a' w =
      if a' = [] ∨ n w.getLast! ≠ a'.head!.head! then w :: a'
      else (w ++ a'.head!) :: a'.tail)
    (fun hne0 _ => absurd rfl hne0) ?_ r hne hun hp a
  intro h t ih hne hun hp
  have hlast : (t ++ [h]).getLast! = h := lastRcons t h
  have hlen : (t ++ [h]).length = t.length + 1 := by
    rw [List.length_append, List.length_singleton]
  have htn : t.Nodup := List.Sublist.nodup (List.sublist_append_left t [h]) hun
  have hhh : h ∉ t := by
    intro hc
    have hi : t.idxOf h < t.length := List.idxOf_lt_length_iff.mpr hc
    have h1 : (t ++ [h])[t.idxOf h]'(by rw [hlen]; omega) = h :=
      (List.getElem_append_left hi).trans (getElem_idxOf hc)
    have h2 : (t ++ [h])[t.length]'(by rw [hlen]; omega) = h :=
      ((List.getElem_append_right (Nat.le_refl t.length)).trans
        (getElemCon
          (show t.length - t.length < [h].length by
            rw [Nat.sub_self]; exact List.length_pos_of_ne_nil (by simp))
          (List.length_pos_of_ne_nil (by simp)) (Nat.sub_self t.length))).trans
        (by cases h <;> rfl)
    have h3 := (hun.getElem_inj_iff
      (hi := (by rw [hlen]; omega : t.idxOf h < (t ++ [h]).length))
      (hj := (by rw [hlen]; omega : t.length < (t ++ [h]).length))).mp
      (h1.trans h2.symm)
    omega
  have hpT : ∀ x ∈ t, x = t.getLast! ∨ nextEl t x = n x := by
    intro x hx
    rcases hp x (List.mem_append.mpr (Or.inl hx)) with h1 | h1
    · have hxh : x = h := h1.trans hlast
      have hxh2 : h ∈ t := by rw [← hxh]; exact hx
      exact absurd hxh2 hhh
    · by_cases hx2 : x = t.getLast!
      · exact Or.inl hx2
      · exact Or.inr (by rw [← nextElCat1 htn hx hx2]; exact h1)
  by_cases ht0 : t = []
  · subst ht0
    intro a'
    rw [(partitionIntoAtom0rCases n a' [] h).2, List.nil_append,
      show ([h] : List (ℕ × ℕ)).getLast! = h from rfl]
    have hpio : ∀ b : List (List (ℕ × ℕ)), partitionIntoAtom0r n b [] = b :=
      fun b => rfl
    by_cases ha0 : a' = []
    · rw [if_pos ha0, if_pos (Or.inl ha0), ha0, hpio]
    · rw [if_neg ha0]
      by_cases hn0 : n h = a'.head!.head!
      · rw [if_pos hn0,
          if_neg (fun hor => hor.elim (fun hc => ha0 hc) (fun hc => absurd hn0 hc)),
          hpio]
        rfl
      · rw [if_neg hn0, if_pos (Or.inr hn0), hpio]
  · have htne : t ≠ [] := ht0
    have hnkey : n t.getLast! = h := by
      have hm : t.getLast! ∈ t ++ [h] :=
        List.mem_append.mpr (Or.inl (getLastMem htne))
      rcases hp t.getLast! hm with h1 | h1
      · have hxh : t.getLast! = h := h1.trans hlast
        have hxh2 : h ∈ t := by rw [← hxh]; exact getLastMem htne
        exact absurd hxh2 hhh
      · rw [← h1, nextElCatLast1 hun htne (by simp)]
        rfl
    intro a'
    rw [(partitionIntoAtom0rCases n a' t h).2, hlast]
    by_cases ha0 : a' = []
    · rw [if_pos ha0, if_pos (Or.inl ha0)]
      rw [ih htne htn hpT [[h]], if_neg (by rw [hnkey]; simp [List.head!_cons])]
      simp only [List.head!_cons, List.tail_cons]
      rw [ha0]
    · rw [if_neg ha0]
      by_cases hn0 : n h = a'.head!.head!
      · rw [if_pos hn0,
          if_neg (fun hor => hor.elim (fun hc => ha0 hc) (fun hc => absurd hn0 hc)),
          ih htne htn hpT ((h :: a'.head!) :: a'.tail),
          if_neg (by rw [hnkey]; simp [List.head!_cons])]
        simp only [List.head!_cons, List.tail_cons] at *
        first | rfl | simp [List.cons_append] | simp
      · rw [if_neg hn0, if_pos (Or.inr hn0),
          ih htne htn hpT ([h] :: a'), if_neg (by rw [hnkey]; simp [List.head!_cons])]
        simp only [List.head!_cons, List.tail_cons] at *


/-- **HOL `parts_pure`**（tame_list.hl:6111-:6122）
`~(r = []) /\ uniq r /\ (!x. MEM x r ==> x = LAST r \/ next_el r x = f_list L (e_list x))
  ==> parts L r = [r]`。 -/
theorem partsPure (L : fgraph ℕ) {r : List (ℕ × ℕ)} (hne : r ≠ []) (hun : r.Nodup)
    (hp : ∀ x ∈ r, x = r.getLast! ∨ nextEl r x = fList L (eList x)) :
    partsSpine L r = [r] := by
  show partitionIntoAtom0r (fun d => fList L (eList d)) [] r = [r]
  rw [partitionIntoAtom0rPure (fun d => fList L (eList d)) [] hne hun hp]
  simp

/-- **HOL `eqseq_cat2`**（tame_list.hl:6124-:6141）
`sizel s3 = sizel s4 ==> (cat s1 s3 = cat s2 s4 <=> s1 = s2 /\ s3 = s4)`。 -/
theorem eqseqCat2 {s1 s2 s3 s4 : List (ℕ × ℕ)} (h : s3.length = s4.length) :
    s1 ++ s3 = s2 ++ s4 ↔ s1 = s2 ∧ s3 = s4 := by
  constructor
  · intro he
    have hl : (s1 ++ s3).length = (s2 ++ s4).length := by rw [he]
    simp only [List.length_append] at hl
    have h12 : s1.length = s2.length := by omega
    exact List.append_inj he h12
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

/-- **HOL `partition_into_atom0r_cons_acc`**（tame_list.hl:6143-:6162）
`partition_into_atom0r n (a0::a) r = cat (partition_into_atom0r n [a0] r) a`。 -/
theorem partitionIntoAtom0rConsAcc (n : ℕ × ℕ → ℕ × ℕ) (r : List (ℕ × ℕ))
    (a0 : List (ℕ × ℕ)) (a : List (List (ℕ × ℕ))) :
    partitionIntoAtom0r n (a0 :: a) r = partitionIntoAtom0r n [a0] r ++ a := by
  refine listrInduct (motive := fun w => ∀ a0 : List (ℕ × ℕ), ∀ a : List (List (ℕ × ℕ)),
    partitionIntoAtom0r n (a0 :: a) w = partitionIntoAtom0r n [a0] w ++ a)
    (fun a0 a => rfl) ?_ r a0 a
  intro h t ih a0 a
  rw [(partitionIntoAtom0rCases n (a0 :: a) t h).2,
      (partitionIntoAtom0rCases n [a0] t h).2]
  simp only [List.head!_cons, List.tail_cons]
  by_cases hn0 : n h = a0.head!
  · rw [if_pos hn0, if_pos hn0, ih (h :: a0) a]
    simp only [show (a0 :: a = []) ↔ [a0] = [] from by simp]
    rfl
  · rw [if_neg hn0, if_neg hn0, if_neg (List.cons_ne_nil a0 a),
      if_neg (List.cons_ne_nil a0 []), ih [h] (a0 :: a), ih [h] [a0],
      List.append_assoc]
    simp only [List.cons_append, List.nil_append]

/-- **HOL `size_induct`**（tame_list.hl:6296-:6313）长度强归纳。 -/
theorem sizeInduct {P : List (ℕ × ℕ) → Prop}
    (H : ∀ i : ℕ, (∀ r : List (ℕ × ℕ), r.length < i → P r) →
      ∀ r : List (ℕ × ℕ), r.length = i → P r) (r : List (ℕ × ℕ)) : P r := by
  have key : ∀ n : ℕ, ∀ q : List (ℕ × ℕ), q.length ≤ n → P q := by
    intro n
    induction n with
    | zero =>
      intro q hq
      exact H 0 (fun r' hr' => absurd hr' (by omega)) q (by omega)
    | succ m ih =>
      intro q hq
      rcases Nat.lt_or_ge q.length (m + 1) with hlt | hge
      · exact ih q (by omega)
      · exact H (m + 1) (fun r' hr' => ih r' (by omega)) q (by omega)
  exact key r.length r (Nat.le_refl _)

/-- **HOL `parts_induct_lemma`**（tame_list.hl:6315-:6332）
`uniq r /\ r = cat u v /\ ~(u = []) /\ ~(v = []) ==>
  sizel u < sizel r /\ sizel v < sizel r /\ uniq u /\ uniq v`。 -/
theorem partsInductLemma {r u v : List (ℕ × ℕ)} (hun : r.Nodup) (hruv : r = u ++ v)
    (hu : u ≠ []) (hv : v ≠ []) :
    u.length < r.length ∧ v.length < r.length ∧ u.Nodup ∧ v.Nodup := by
  have hlen : r.length = u.length + v.length := by rw [hruv, List.length_append]
  have hup : 0 < u.length := List.length_pos_of_ne_nil hu
  have hvp : 0 < v.length := List.length_pos_of_ne_nil hv
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [hruv] at hun
    exact (List.nodup_append.mp hun).1
  · rw [hruv] at hun
    exact (List.nodup_append.mp hun).2.1


/-- 非空表的 `getLast!`-分解：`l = l' ++ [l.getLast!]`。 -/
private theorem existsAppendGetLast! {l : List (ℕ × ℕ)} (hne : l ≠ []) :
    ∃ l' : List (ℕ × ℕ), l = l' ++ [l.getLast!] := by
  cases l with
  | nil => exact absurd rfl hne
  | cons x t =>
    cases t with
    | nil => exact ⟨[], rfl⟩
    | cons y s =>
      obtain ⟨w, hw⟩ := existsAppendGetLast! (l := y :: s) (by simp)
      refine ⟨x :: w, ?_⟩
      nth_rewrite 1 [hw]
      rfl

/-- **HOL `partition_into_atom0r_cat`**（tame_list.hl:6164-:6251）
分裂引理：`r = cat u v`、`x = LAST u`、`next_el r x ≠ n x` 时
`partition_into_atom0r n a r = cat (partition_into_atom0r n [] u) (partition_into_atom0r n a v)`。 -/
theorem partitionIntoAtom0rCat (n : ℕ × ℕ → ℕ × ℕ) {r u v : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (a : List (List (ℕ × ℕ))) (hxr : x ∈ r) (hne : nextEl r x ≠ n x)
    (hruv : r = u ++ v) (hx : u.getLast! = x) (hu : u ≠ []) (hv : v ≠ [])
    (hun : r.Nodup) :
    partitionIntoAtom0r n a r = partitionIntoAtom0r n [] u ++ partitionIntoAtom0r n a v := by
  refine listrInduct (motive := fun w => ∀ u' v' x' a', x' ∈ w → nextEl w x' ≠ n x' →
    w = u' ++ v' → u'.getLast! = x' → u' ≠ [] → v' ≠ [] → w.Nodup →
    partitionIntoAtom0r n a' w =
      partitionIntoAtom0r n [] u' ++ partitionIntoAtom0r n a' v')
    (fun _ _ _ _ hx => absurd hx (by simp)) ?_ r u v x a hxr hne hruv hx hu hv hun
  intro h t ih u v x a hxr hne hruv hx hu hv hun
  have hvlv : v.getLast! = h := by
    have hq1 : (t ++ [h]).getLast! = h := lastRcons t h
    have hq2 : (t ++ [h]).getLast! = v.getLast! := by rw [hruv]; exact lastCat hv
    exact hq2.symm.trans hq1
  obtain ⟨v', hv'⟩ := existsAppendGetLast! (l := v) hv
  rw [hvlv] at hv'
  have htv : t = u ++ v' := by
    have hrw : t ++ [h] = (u ++ v') ++ [h] := by rw [hruv, hv', List.append_assoc]
    have hlc : t.length + 1 = (u ++ v').length + 1 := by
      have h0 := congrArg List.length hrw
      rw [List.length_append, List.length_append] at h0
      rw [List.length_singleton] at h0
      exact h0
    have hlen : t.length = (u ++ v').length := by omega
    exact (List.append_inj hrw hlen).1
  have hun' : t.Nodup := List.Sublist.nodup (List.sublist_append_left t [h]) hun
  by_cases hv0 : v' = []
  · -- 尾段 v = [h]：t = u，u = u' ++ [x]，两侧各推一层到 u'，cons_acc 收口
    subst hv0
    have htu : t = u := by rw [htv, List.append_nil]
    obtain ⟨u', hu'⟩ := existsAppendGetLast! (l := u) hu
    rw [hx] at hu'
    have hr2 : t ++ [h] = (u' ++ [x]) ++ [h] := by rw [htu, hu']
    rw [hr2] at hxr hne hun
    have hsne : (u' ++ [x]) ++ [h] ≠ [] := List.ne_nil_of_mem hxr
    have hxmem : x ∈ u' ++ [x] := by simp
    have hxeq : x = (u' ++ [x]).getLast! :=
      hx.symm.trans (by rw [hu'])
    have hkey : nextEl ((u' ++ [x]) ++ [h]) x = h := by
      have hnotmem : x ∉ u' := by
        intro hc
        rw [List.append_assoc] at hun
        exact nodupAppendDisjoint (t := [x] ++ [h]) hun hc
          (List.mem_append.mpr (Or.inl (List.mem_cons_self (a := x))))
      have hxmem2 : x ∈ (u' ++ [x]) ++ [h] :=
        List.mem_append.mpr (Or.inl hxmem)
      have hidx : ((u' ++ [x]) ++ [h]).idxOf x = u'.length := by
        rw [List.idxOf_append_of_mem (l₁ := u' ++ [x]) hxmem,
          List.idxOf_append_of_notMem hnotmem, List.idxOf_cons_self, Nat.add_zero]
      have hlen2 : ((u' ++ [x]) ++ [h]).length = u'.length + 2 := by
        simp [List.length_append]
      have hlt : u'.length + 1 < ((u' ++ [x]) ++ [h]).length := by
        rw [hlen2]; omega
      rw [nextEl_eq_getD hxr, hidx, Nat.mod_eq_of_lt hlt,
        getD_eq_getElem_of_lt hlt]
      exact (List.getElem_append_right
          (show (u' ++ [x]).length ≤ u'.length + 1 by
            rw [List.length_append, List.length_singleton])).trans
        ((getElemCon
          (show u'.length + 1 - (u' ++ [x]).length < [h].length by
            rw [List.length_append, List.length_singleton, List.length_singleton]; omega)
          (List.length_pos_of_ne_nil (by simp))
          (show u'.length + 1 - (u' ++ [x]).length = 0 by
            rw [List.length_append, List.length_singleton]; omega)).trans
          (by cases h <;> rfl))
    rw [hkey] at hne
    have key : ∀ b : List (List (ℕ × ℕ)), b ≠ [] → b.head!.head! = h →
        partitionIntoAtom0r n b (u' ++ [x]) = partitionIntoAtom0r n [[x]] u' ++ b := by
      intro b hb1 hb2
      rw [(partitionIntoAtom0rCases n b u' x).2, if_neg hb1,
        if_neg (fun hc => hne (hc.trans hb2).symm), partitionIntoAtom0rConsAcc]
    have hrhs1 : partitionIntoAtom0r n [] (u' ++ [x]) =
        partitionIntoAtom0r n [[x]] u' := by
      rw [(partitionIntoAtom0rCases n [] u' x).2, if_pos rfl]
    rw [htu, hu', hv', (partitionIntoAtom0rCases n a (u' ++ [x]) h).2,
      (partitionIntoAtom0rCases n a [] h).2]
    have hpio : ∀ b : List (List (ℕ × ℕ)), partitionIntoAtom0r n b [] = b :=
      fun b => rfl
    by_cases ha0 : a = []
    · rw [if_pos ha0, if_pos ha0, key [[h]] (by simp) (by simp), hrhs1]
      rfl
    · rw [if_neg ha0]
      by_cases hnh : n h = a.head!.head!
      · rw [if_pos hnh, if_neg ha0, if_pos hnh,
          key ((h :: a.head!) :: a.tail) (by simp) (by simp), hrhs1]
        rfl
      · rw [if_neg hnh, if_neg ha0, if_neg hnh,
          key ([h] :: a) (by simp) (by simp), hrhs1]
        rfl
  · -- 尾段 v' ≠ []：对 t 用归纳假设，三分支镜像
    have hv'ne : v' ≠ [] := hv0
    have hxu : x ∈ u := by rw [← hx]; exact getLastMem hu
    have hxr' : x ∈ t := by
      rw [htv]; exact List.mem_append.mpr (Or.inl hxu)
    have hne1 : nextEl (u ++ v) x = v.head! := by
      rw [← hx]; exact nextElCatLast1 (by rw [← hruv]; exact hun) hu hv
    have hun2 : (u ++ v').Nodup := by rw [← htv]; exact hun'
    have hne2 : nextEl (u ++ v') x = v'.head! := by
      rw [← hx]; exact nextElCatLast1 hun2 hu hv'ne
    have hhd : (v' ++ [h]).head! = v'.head! := by
      cases v' with
      | nil => exact absurd rfl hv'ne
      | cons y s => rfl
    have hne' : nextEl t x ≠ n x := by
      rw [htv, hne2]
      rw [hruv, hne1, hv'] at hne
      intro hc
      exact hne (hhd.trans hc)
    rw [hv', (partitionIntoAtom0rCases n a t h).2,
      (partitionIntoAtom0rCases n a v' h).2,
      ih u v' x [[h]] hxr' hne' htv hx hu hv'ne hun',
      ih u v' x ((h :: a.head!) :: a.tail) hxr' hne' htv hx hu hv'ne hun',
      ih u v' x ([h] :: a) hxr' hne' htv hx hu hv'ne hun']
    by_cases ha0 : a = []
    · rw [if_pos ha0, if_pos ha0]
    · by_cases hnh : n h = a.head!.head!
      · rw [if_neg ha0, if_neg ha0, if_pos hnh, if_pos hnh]
      · rw [if_neg ha0, if_neg ha0, if_neg hnh, if_neg hnh]

/-- **HOL `parts_cat`**（tame_list.hl:6253-:6271）
`parts L r = cat (parts L u) (parts L v)`（分裂条件下）。 -/
theorem partsCat (L : fgraph ℕ) {r u v : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hruv : r = u ++ v) (hx : u.getLast! = x) (hu : u ≠ []) (hv : v ≠ [])
    (hne : nextEl r x ≠ fList L (eList x)) (hun : r.Nodup) :
    partsSpine L r = partsSpine L u ++ partsSpine L v := by
  have hxr : x ∈ r := by
    rw [hruv]
    exact List.mem_append.mpr (Or.inl (by rw [← hx]; exact getLastMem hu))
  show partitionIntoAtom0r (fun d => fList L (eList d)) [] r =
    partitionIntoAtom0r (fun d => fList L (eList d)) [] u ++
      partitionIntoAtom0r (fun d => fList L (eList d)) [] v
  rw [partitionIntoAtom0rCat (fun d => fList L (eList d)) [] hxr hne hruv hx hu hv
    hun]

/-- **HOL `parts_cases`**（tame_list.hl:6273-:6294）
n-封闭性或分裂二择一。 -/
theorem partsCases (n : ℕ × ℕ → ℕ × ℕ) (r : List (ℕ × ℕ)) :
    (∀ x ∈ r, x = r.getLast! ∨ nextEl r x = n x) ∨
      ∃ u v : List (ℕ × ℕ), ∃ x : ℕ × ℕ, r = u ++ v ∧ u.getLast! = x ∧ u ≠ [] ∧
        v ≠ [] ∧ nextEl r x ≠ n x := by
  by_contra hc
  push_neg at hc
  obtain ⟨hc1, hc2⟩ := hc
  obtain ⟨x, hxr, hx1, hx2⟩ := hc1
  obtain ⟨a, b, hab, hba, hane⟩ := catFrom hxr
  have hbne : b ≠ [] := by
    intro hc0
    rw [hc0, List.append_nil] at hab
    rw [hab] at hx1
    exact hx1 hba.symm
  exact absurd (hc2 a b x hab hba hane hbne) hx2

/-- **HOL `parts_flatten`**（tame_list.hl:6334-:6356，全书 105 处消费的 capstone）
`uniq r /\ ~(r = []) ==> flatten (parts L r) = r`。 -/
theorem partsFlatten (L : fgraph ℕ) {r : List (ℕ × ℕ)} (hun : r.Nodup)
    (hne : r ≠ []) : (partsSpine L r).flatten = r := by
  refine sizeInduct (P := fun w => w.Nodup → w ≠ [] → (partsSpine L w).flatten = w)
    ?_ r hun hne
  intro i IH r hr
  intro hun hne
  rcases partsCases (fun d => fList L (eList d)) r with hp | ⟨u, v, x, hruv, hx, hu, hv, hne2⟩
  · rw [partsPure L hne hun hp, List.flatten_cons, List.flatten_nil,
      List.append_nil]
  · have hilm := partsInductLemma hun hruv hu hv
    have hxr : x ∈ r := by
      rw [hruv]
      exact List.mem_append.mpr (Or.inl (by rw [← hx]; exact getLastMem hu))
    have hkey := partsCat L hruv hx hu hv hne2 hun
    rw [hkey, List.flatten_append]
    rw [IH u (by omega) hilm.2.2.1 (List.ne_nil_of_mem (getLastMem hu)),
      IH v (by omega) hilm.2.2.2 hv]
    exact hruv.symm

/-! ### §4 parts 群续 + 词典缺口补（tame_list.hl:5895 与 :6357-:6600） -/

/-- 同表非空 `l[0]` 与 `l.head!` 的项级换形器。 -/
private theorem getElem0Head! {α : Type*} [Inhabited α] {l : List α}
    (h : 0 < l.length) : l[0]'h = l.head! := by
  cases l with
  | nil => exact absurd h (by simp)
  | cons a t => rfl

/-- 同表非空 `getD 0` 的 `head!`-换形器。 -/
private theorem getD0EqHead! {α : Type*} [Inhabited α] [BEq α] [LawfulBEq α]
    [DecidableEq α] {l : List α} (h : 0 < l.length) :
    l.getD 0 default = l.head! := by
  rw [getD_eq_getElem_of_lt h default, getElem0Head! h]

/-- 左段非空时 `getD 0` 穿过拼接（默认元任意）。 -/
private theorem getD0_append {α : Type*} [Inhabited α] [BEq α] [LawfulBEq α]
    [DecidableEq α] {l₁ l₂ : List α} (h : l₁ ≠ []) (d : α) :
    (l₁ ++ l₂).getD 0 d = l₁.getD 0 d := by
  have h2 : 0 < l₁.length := List.length_pos_of_ne_nil h
  have h1 : 0 < (l₁ ++ l₂).length := by rw [List.length_append]; omega
  rw [getD_eq_getElem_of_lt h1 d, getD_eq_getElem_of_lt h2 d,
    List.getElem_append_left h2]

/-- 成员全非空且非空表的 flatten 非空。 -/
private theorem flatten_ne_nil {L : List (List (ℕ × ℕ))} (hn : ∀ q ∈ L, q ≠ [])
    (hne : L ≠ []) : L.flatten ≠ [] := by
  cases L with
  | nil => exact absurd rfl hne
  | cons q t =>
    have hq : q ≠ [] := hn q (List.mem_cons_self ..)
    intro hc
    rw [List.flatten_cons, catEqNil] at hc
    exact hq hc.1

/-- flatten-nodup 且成员全非空时 `L` 自身 nodup。 -/
private theorem nodupOfFlattenNodup {L : List (List (ℕ × ℕ))} (hun : L.flatten.Nodup)
    (hn : ∀ q ∈ L, q ≠ []) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons q t ih =>
    rw [List.flatten_cons] at hun
    rw [List.nodup_cons]
    refine ⟨?_, ih (List.Sublist.nodup (List.sublist_append_right q t.flatten) hun)
      (fun x hx => hn x (List.mem_cons_of_mem _ hx))⟩
    intro hc
    cases q with
    | nil => exact hn [] (List.mem_cons_self ..) rfl
    | cons y s =>
      have hy : y ∈ y :: s := List.mem_cons_self ..
      exact nodupAppendFlattenContra hun hy (List.mem_flatten.mpr ⟨y :: s, hc, hy⟩)

/-- **HOL `next_el_flatten_last`**（tame_list.hl:5895-:5928；批 9 头注把本件列入
镜像清单但正文缺席，本件按对账补齐）`uniq (flatten s) /\ all nonnil s /\
MEM r s ==> next_el (flatten s) (LAST r) = HD (next_el s r)`。 -/
theorem nextElFlattenLast {L : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    (hun : L.flatten.Nodup) (hn : ∀ q ∈ L, q ≠ []) (hr : r ∈ L) :
    nextEl L.flatten r.getLast! = (nextEl L r).head! := by
  have hr0 : r ≠ [] := hn r hr
  have hLn : L.Nodup := nodupOfFlattenNodup hun hn
  obtain ⟨a, b, hab⟩ := List.append_of_mem hr
  rw [hab] at hLn hun ⊢
  have hfl : (a ++ r :: b).flatten = (a.flatten ++ r) ++ b.flatten := by
    rw [List.flatten_append, List.flatten_cons, List.append_assoc]
  rw [hfl] at hun ⊢
  have hra : r ∉ a := by
    intro hc
    exact ((List.nodup_append.mp hLn).2.2) r hc r
      (List.mem_cons.mpr (Or.inl rfl)) rfl
  have hSne : a.flatten ++ r ≠ [] :=
    List.ne_nil_of_mem (List.mem_append.mpr (Or.inr (getLastMem hr0)))
  have hSpos : 0 < (a.flatten ++ r).length := List.length_pos_of_ne_nil hSne
  have hSn : (a.flatten ++ r).Nodup :=
    List.Sublist.nodup (List.sublist_append_left (a.flatten ++ r) b.flatten) hun
  have hlast : r.getLast! = (a.flatten ++ r).getLast! :=
    (lastCat (u := a.flatten) hr0).symm
  have hidx : (a ++ r :: b).idxOf r = a.length := by
    rw [List.idxOf_append_of_notMem hra, List.idxOf_cons_self, Nat.add_zero]
  by_cases hb0 : b = []
  · -- b = []：r 是末位成员表，两侧均为回卷到首元的 headD/head!
    have hblen0 : b.length = 0 := by rw [hb0]; rfl
    have hrLast : (a ++ [r]).idxOf r = (a ++ [r]).length - 1 := by
      have hmem : r ∈ a ++ [r] :=
        List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      have hidx2 : (a ++ [r]).idxOf r = a.length := by
        rw [List.idxOf_append_of_notMem hra, List.idxOf_cons_self, Nat.add_zero]
      rw [hidx2, List.length_append, List.length_cons, List.length_nil]
      simp
    have hwrap : nextEl (a.flatten ++ r) (a.flatten ++ r).getLast!
        = (a.flatten ++ r).getD 0 default := by
      have hmlen : (a.flatten ++ r).length - 1 + 1 = (a.flatten ++ r).length := by omega
      rw [nextEl_eq_getD (getLastMem hSne), idxOfGetLast hSn hSne, hmlen,
        Nat.mod_self, getD_eq_getElem_of_lt hSpos (a.flatten ++ r).getLast!,
        getD_eq_getElem_of_lt hSpos default]
    have hrhs : nextEl (a ++ [r]) r = (a ++ [r]).getD 0 r := by
      show (if (a ++ [r]).idxOf r = (a ++ [r]).length - 1 then (a ++ [r]).headD r
        else (a ++ [r]).getD ((a ++ [r]).idxOf r + 1) r) = _
      rw [if_pos hrLast, headD_eq_getD_zero]
    rw [hb0, List.flatten_nil, List.append_nil, hlast, hwrap, hrhs]
    cases a with
    | nil =>
      show r.getD 0 default = r.head!
      exact getD0EqHead! (List.length_pos_of_ne_nil hr0)
    | cons c t =>
      have hcne : c ≠ [] := by
        intro hccc
        exact hn c (by simp [hab]) hccc
      have hcpos : 0 < c.length := List.length_pos_of_ne_nil hcne
      have hc0 : 0 < ((c :: t) ++ [r]).length := by
        rw [List.length_append, List.length_cons, List.length_singleton]
        omega
      show (((c :: t).flatten ++ r)).getD 0 default
        = (((c :: t) ++ [r]).getD 0 r).head!
      have hL : (((c :: t).flatten ++ r)).getD 0 default = c.head! := by
        rw [List.flatten_cons, getD0_append (l₁ := c ++ t.flatten)
          (List.ne_nil_of_mem (List.mem_append.mpr (Or.inl
            (List.head!_mem_self hcne)))) default,
          getD0_append (l₁ := c) hcne default, getD0EqHead! hcpos]
      have hR : (((c :: t) ++ [r]).getD 0 r).head! = c.head! := by
        rw [getD_eq_getElem_of_lt hc0 r, getElem0Head! hc0]
        simp
      rw [hL, hR]
  · -- b ≠ []：末位走 nextElCatLast1，下一位走 getElem
    have hbne : b ≠ [] := hb0
    have hblen : 0 < b.length := List.length_pos_of_ne_nil hbne
    have hbflne : b.flatten ≠ [] := flatten_ne_nil
      (fun q hq => hn q (by rw [hab]; exact List.mem_append.mpr (Or.inr
        (List.mem_cons_of_mem _ hq)))) hbne
    have hbh : b.head! ≠ [] := hn b.head!
      (by rw [hab]; exact List.mem_append.mpr (Or.inr
        (List.mem_cons_of_mem _ (List.head!_mem_self hbne))))
    have hlt : a.length + 1 < (a ++ r :: b).length := by
      rw [List.length_append, List.length_cons]; omega
    have hrhs : nextEl (a ++ r :: b) r = b.head! := by
      rw [nextEl_eq_getD (List.mem_append.mpr (Or.inr (List.mem_cons_self ..))),
        hidx, Nat.mod_eq_of_lt hlt, getD_eq_getElem_of_lt hlt,
        List.getElem_append_right (Nat.le_add_right a.length 1)]
      simp only [show a.length + 1 - a.length = 1 from by omega]
      cases b with
      | nil => exact absurd rfl hbne
      | cons q t => rfl
    rw [hlast, nextElCatLast1 hun hSne hbflne, hdFlatten hbflne hbh, hrhs]

/-- **HOL `parts_all_nonnil`**（tame_list.hl:6357-:6378）
`uniq r /\ ~(r = []) ==> all (\p. ~(p = [])) (parts L r)`。 -/
theorem partsAllNonnil (L : fgraph ℕ) {r : List (ℕ × ℕ)} (hun : r.Nodup)
    (hne : r ≠ []) : ∀ q ∈ partsSpine L r, q ≠ [] := by
  refine sizeInduct (P := fun w => w.Nodup → w ≠ [] → ∀ q ∈ partsSpine L w, q ≠ [])
    ?_ r hun hne
  intro i IH r hr hun hne
  rcases partsCases (fun d => fList L (eList d)) r with hp |
    ⟨u, v, x, hruv, hx, hu, hv, hne2⟩
  · rw [partsPure L hne hun hp]
    intro q hq
    rcases List.mem_singleton.mp hq with rfl
    exact hne
  · have hilm := partsInductLemma hun hruv hu hv
    rw [partsCat L hruv hx hu hv hne2 hun]
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact IH u (by omega) hilm.2.2.1 hu q hq
    · exact IH v (by omega) hilm.2.2.2 hv q hq

/-- **HOL `parts_uniq`**（tame_list.hl:6561-:6574）
`~(r = []) /\ uniq r /\ MEM p (parts L r) ==> uniq p`。 -/
theorem partsUniq (L : fgraph ℕ) {r : List (ℕ × ℕ)} (hun : r.Nodup) (hne : r ≠ []) :
    ∀ q ∈ partsSpine L r, q.Nodup := by
  refine sizeInduct (P := fun w => w.Nodup → w ≠ [] → ∀ q ∈ partsSpine L w, q.Nodup)
    ?_ r hun hne
  intro i IH r hr hun hne
  rcases partsCases (fun d => fList L (eList d)) r with hp |
    ⟨u, v, x, hruv, hx, hu, hv, hne2⟩
  · rw [partsPure L hne hun hp]
    intro q hq
    rcases List.mem_singleton.mp hq with rfl
    exact hun
  · have hilm := partsInductLemma hun hruv hu hv
    rw [partsCat L hruv hx hu hv hne2 hun]
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact IH u (by omega) hilm.2.2.1 hu q hq
    · exact IH v (by omega) hilm.2.2.2 hv q hq

/-- **HOL `parts_nonnil`**（tame_list.hl:6533-:6541）
`uniq r /\ ~(r = []) ==> ~(parts L r = [])`。 -/
theorem partsNonnil (L : fgraph ℕ) {r : List (ℕ × ℕ)} (hun : r.Nodup) (hne : r ≠ []) :
    partsSpine L r ≠ [] := by
  have h := partsFlatten L hun hne
  intro hc
  rw [hc, List.flatten_nil] at h
  exact hne h.symm

/-- **HOL `parts_uniq_nonnil`**（tame_list.hl:6576-:6598）
`normal_list L N /\ MEM r N /\ MEM p (parts L r) ==>
  uniq r /\ ~(r = []) /\ uniq p /\ ~(p = []) /\ (!x. MEM x p ==> MEM x r)`。 -/
theorem partsUniqNonnil (L : fgraph ℕ) (hL : GoodList L) {N : List (List (ℕ × ℕ))}
    {r : List (ℕ × ℕ)} (hn : NormalListSpine hL N) (hr : r ∈ N)
    {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r) :
    r.Nodup ∧ r ≠ [] ∧ p.Nodup ∧ p ≠ [] ∧ ∀ x ∈ p, x ∈ r := by
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  have hp1 : p.Nodup := partsUniq L hr1 hr2 p hp
  have hp2 : p ≠ [] := partsAllNonnil L hr1 hr2 p hp
  refine ⟨hr1, hr2, hp1, hp2, ?_⟩
  intro x hx
  have hxf : x ∈ (partsSpine L r).flatten := List.mem_flatten.mpr ⟨p, hp, hx⟩
  rw [partsFlatten L hr1 hr2] at hxf
  exact hxf

/-- **HOL `parts_next_unlast`**（tame_list.hl:6380-:6406）
`uniq r /\ ~(r = []) ==> all (\p. !x. MEM x p /\ ~(x = LAST p) ==>
  next_el p x = f_list L (e_list x)) (parts L r)`。 -/
theorem partsNextUnlast (L : fgraph ℕ) {r : List (ℕ × ℕ)} (hun : r.Nodup)
    (hne : r ≠ []) :
    ∀ p ∈ partsSpine L r, ∀ x ∈ p, x ≠ p.getLast! → nextEl p x = fList L (eList x) := by
  refine sizeInduct (P := fun w => w.Nodup → w ≠ [] →
    ∀ p ∈ partsSpine L w, ∀ x ∈ p, x ≠ p.getLast! → nextEl p x = fList L (eList x))
    ?_ r hun hne
  intro i IH r hr hun hne
  rcases partsCases (fun d => fList L (eList d)) r with hp |
    ⟨u, v, x, hruv, hx, hu, hv, hne2⟩
  · rw [partsPure L hne hun hp]
    intro p hp' x hx' hx2
    rcases List.mem_singleton.mp hp' with rfl
    rcases hp x hx' with h1 | h1
    · exact absurd h1 hx2
    · exact h1
  · have hilm := partsInductLemma hun hruv hu hv
    rw [partsCat L hruv hx hu hv hne2 hun]
    intro p hp' x hx' hx2
    rcases List.mem_append.mp hp' with hp' | hp'
    · exact IH u (by omega) hilm.2.2.1 hu p hp' x hx' hx2
    · exact IH v (by omega) hilm.2.2.2 hv p hp' x hx' hx2

/-- **HOL `parts_next_last`**（tame_list.hl:6408-:6460）
`uniq r /\ ~(r = []) ==> all (\p. !x. MEM x p /\ (x = LAST p) /\
  ~(x = LAST r) ==> ~(next_el r x = f_list L (e_list x))) (parts L r)`。 -/
theorem partsNextLast (L : fgraph ℕ) {r : List (ℕ × ℕ)} (hun : r.Nodup) (hne : r ≠ []) :
    ∀ p ∈ partsSpine L r, ∀ x ∈ p, x = p.getLast! → x ≠ r.getLast! →
      nextEl r x ≠ fList L (eList x) := by
  refine sizeInduct (P := fun w => w.Nodup → w ≠ [] →
    ∀ p ∈ partsSpine L w, ∀ x ∈ p, x = p.getLast! → x ≠ w.getLast! →
      nextEl w x ≠ fList L (eList x)) ?_ r hun hne
  intro i IH r hr hun hne
  rcases partsCases (fun d => fList L (eList d)) r with hp |
    ⟨u, v, xs, hruv, hxs, hu, hv, hne2⟩
  · rw [partsPure L hne hun hp]
    intro p hp' x hx' hx3 hx4
    rcases List.mem_singleton.mp hp' with rfl
    exact fun _ => hx4 hx3
  · have hilm := partsInductLemma hun hruv hu hv
    have hund : (u ++ v).Nodup := by rw [← hruv]; exact hun
    have hulv : u.getLast! ≠ v.getLast! :=
      (List.nodup_append.mp hund).2.2 _ (getLastMem hu) _ (getLastMem hv)
    rw [partsCat L hruv hxs hu hv hne2 hun]
    intro p hp' x hx' hx3 hx4
    rcases List.mem_append.mp hp' with hp' | hp'
    · -- p ∈ parts u：按 x 是否 LAST u 二分
      by_cases hxu : x = u.getLast!
      · -- x = LAST u = 分裂点：目标即分裂假设 hne2
        rw [hxu, hxs]
        exact hne2
      · -- x ≠ LAST u：next_el r x = next_el u x（cat1）+ IH-u
        have hxf : x ∈ u := by
          have hxpf : x ∈ (partsSpine L u).flatten := List.mem_flatten.mpr ⟨p, hp', hx'⟩
          rw [partsFlatten L hilm.2.2.1 hu] at hxpf
          exact hxpf
        rw [show nextEl r x = nextEl u x from by
          rw [hruv]; exact nextElCat1 hilm.2.2.1 hxf hxu]
        intro hc
        exact IH u (by omega) hilm.2.2.1 hu p hp' x hx' hx3 hxu hc
    · -- p ∈ parts v：x ≠ LAST v（= LAST r），next_el r x = next_el v x（cat2）+ IH-v
      have hxf : x ∈ v := by
        have hxpf : x ∈ (partsSpine L v).flatten := List.mem_flatten.mpr ⟨p, hp', hx'⟩
        rw [partsFlatten L hilm.2.2.2 hv] at hxpf
        exact hxpf
      have hx2 : x ≠ v.getLast! := by
        intro hc
        exact hx4 (by rw [hruv, lastCat hv, hc])
      rw [show nextEl r x = nextEl v x from by
        rw [hruv]; exact nextElCat2 hund hxf hx2]
      intro hc
      exact IH v (by omega) hilm.2.2.2 hv p hp' x hx' hx3 hx2 hc

/-- **HOL `next_el_parts_unlast`**（tame_list.hl:6490-:6503）
`uniq r /\ ~(r = []) /\ MEM x p /\ MEM p (parts L r) /\ ~(x = LAST p) ==>
  next_el r x = next_el p x`。 -/
theorem nextElPartsUnlast (L : fgraph ℕ) {r : List (ℕ × ℕ)} (hun : r.Nodup)
    (hne : r ≠ []) {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r) {x : ℕ × ℕ}
    (hx : x ∈ p) (hx2 : x ≠ p.getLast!) : nextEl r x = nextEl p x := by
  have hpfl : (partsSpine L r).flatten.Nodup := by
    rw [partsFlatten L hun hne]; exact hun
  rw [← partsFlatten L hun hne]
  exact nextElFlattenUnlast hpfl hx hp hx2

/-- **HOL `next_el_parts_last`**（tame_list.hl:6505-:6520）
`uniq r /\ ~(r = []) /\ MEM x p /\ MEM p (parts L r) /\ (x = LAST p) ==>
  next_el r x = HD (next_el (parts L r) p)`。 -/
theorem nextElPartsLast (L : fgraph ℕ) {r : List (ℕ × ℕ)} (hun : r.Nodup)
    (hne : r ≠ []) {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r) {x : ℕ × ℕ}
    (hx : x ∈ p) (hx2 : x = p.getLast!) :
    nextEl r x = (nextEl (partsSpine L r) p).head! := by
  have hpfl : (partsSpine L r).flatten.Nodup := by
    rw [partsFlatten L hun hne]; exact hun
  have hpn : ∀ q ∈ partsSpine L r, q ≠ [] := partsAllNonnil L hun hne
  conv_lhs => rw [← partsFlatten L hun hne]
  rw [hx2]
  exact nextElFlattenLast hpfl hpn hp

/-- **HOL `quotient_all_uniq`**（tame_list.hl:6522-:6530）
`marked_list L N r x ==> all uniq (quotient_list L N)`——MarkedListSpine
第 5 合取块首项直取（批 7 载体记账：marked_list 定义层前 7 块镜像）。 -/
theorem quotientAllUniq {L : fgraph ℕ} (hL : GoodList L) {N : List (List (ℕ × ℕ))}
    {r : List (ℕ × ℕ)} {x : ℕ × ℕ} (hm : MarkedListSpine hL N r x) :
    ∀ q ∈ quotientListSpine L N, q.Nodup := hm.2.2.2.2.1.1

/-- **HOL `quotient_all_nonnil`**（tame_list.hl:6543-:6560）
`normal_list L N ==> all (\l. ~(l = [])) (quotient_list L N)`——
quotient_list = core_list (map (parts L) N)，core 逐面 map HD-首元；
面级非空 = parts_nonnil。 -/
theorem quotientAllNonnil {L : fgraph ℕ} (hL : GoodList L) {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N) : ∀ q ∈ quotientListSpine L N, q ≠ [] := by
  intro q hq
  rw [quotientListSpine, coreListSpine, List.mem_map] at hq
  obtain ⟨y, hy, rfl⟩ := hq
  rw [List.mem_map] at hy
  obtain ⟨r, hr, rfl⟩ := hy
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  have hpne : partsSpine L r ≠ [] := partsNonnil L hr1 hr2
  intro hc
  rw [List.map_eq_nil_iff] at hc
  exact hpne hc

/-- **HOL `indexl_next_el`**（tame_list.hl:6600-:6615）
`uniq s /\ MEM x s ==> indexl (next_el s x) s =
  if indexl x s = sizel s - 1 then 0 else indexl x s + 1`。 -/
theorem indexlNextEl {s : List (ℕ × ℕ)} (hun : s.Nodup) {x : ℕ × ℕ} (hx : x ∈ s) :
    s.idxOf (nextEl s x) =
      if s.idxOf x = s.length - 1 then 0 else s.idxOf x + 1 := by
  have hpos : 0 < s.length := List.length_pos_of_mem hx
  have hidx : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hx
  show s.idxOf (if s.idxOf x = s.length - 1 then s.headD x
    else s.getD (s.idxOf x + 1) x) = _
  by_cases hlast : s.idxOf x = s.length - 1
  · rw [if_pos hlast, if_pos hlast, headD_eq_getD_zero,
      getD_eq_getElem_of_lt hpos, idxOf_getElem hun hpos]
  · have hj1 : s.idxOf x + 1 < s.length := by omega
    rw [if_neg hlast, if_neg hlast, getD_eq_getElem_of_lt hj1, idxOf_getElem hun hj1]

/-! ### §5 hypermap 桥簇（tame_list.hl:6617-:6740）——续批留待下波：f_list_fst_snd
（zip-环结构，需 listPairs 逐项 getElem 运输）、parts_node_inverse_power /
parts_in_node / parts_fst / parts_darts（经 inverseNodeMapList + indexl_next_el +
nodeMap 保 FST 迭代不变量；parts_last_as_fst_hd :6744 起亦同）。本波在 §4
纯列表簇自然边界收批（见交付报告）。 -/

end Kepler.Text.TameSpine


