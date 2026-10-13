/-
  Kepler.Text.TameSpine.TameList10 — B1 Tame_list 地基批 10：hypermap 桥簇头位重建 +
  quotient_list 块 + is_node_going 块（tamespine-port-plan §4 批次表 B1 行；
  接续批 9 = TameList9.lean，HOL :5580-:6615 已由批 9 落，本批从
  hypermap 桥簇 :6607 起）。

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353，
  text_formalization/tame/tame_list.hl:6607-:7514）：

  - 头位重建（批 9 裁剪的五枚 hypermap 桥簇，按批 9 诊断处方）：
    `f_list_fst_snd` :6702 / `parts_node_inverse_power` :6607 / `parts_in_node`
    :6665 / `parts_fst` :6687 / `parts_darts` :6722。批 9 处方逐条兑现：
    statement 位的 getElem 长度事实作显式假设绑定器传入（`p[k + idxOf x]'hlen`
    直接引用声明绑定器 hlen，不用 statement 位 (by…)）；Perm 幂应用统一写
    `((nodeMap.symm ^ n) x)`（`pow_succ'` 在根命名空间 + `Equiv.Perm.mul_apply`
    展开）；getD_next 路由经 TameLp `nextEl_eq_getD`/`getD_eq_getElem_of_lt`。
    文件内顺序按依赖重排为 f_list_fst_snd → parts_darts → parts_node_inverse_power
    → parts_in_node → parts_fst（HOL 原序 parts_fst 在 f_list_fst_snd 前，但其
    nodeMap-symm 保 FST 引擎消费 f_list 的 FST 恒等式，见 fstInvOrbit 记账）；
  - quotient_list 块 :6742-:7151：`parts_last_as_fst_hd`/`uniq_parts`/
    `parts_list_pairs`/`list_of_darts_quotient`/`mem_list_of_darts_quotient`/
    `flatten_flatten`/`normal_list_flatten_flatten`/`list_of_darts_quotient_uniq`/
    `list_of_darts_quotient_sym`/`good_list_quotient`；
  - is_node_going 块 :7152-:7514：`is_node_going_refl`/
    `normal_list_parts_next_last`/`normal_list_parts_next_last_not`/
    `is_node_going_last1`/`mem_f_list`/`inverse_node_map_list_power`/
    `next_el_parts_power`/`indexf_hd`/`hd_eq_last`/`indexl_flatten`/
    `indexf_flatten`/`is_node_going_last2_lemma`。在 :7514 自然边界收批
    （atom_* 簇 :7515 起留批 11）。

  诚实记账（本批跳过/合并/桥引件）：
  - `next_el_list_pairs`（list_hypermap-compiled.hl:316）：List_hypermap 层件
    首次有消费者，按批 8 先例落地为公开件 `nextElListPairs`（连同元素级
    zip 访问私件 `listPairsGetElem` 与免 uniq 的 FST-半版私件
    `nextElListPairsFst`；TameLp 层无同名件，未撞名）；
  - `f_list_fst_snd` 的 FST-半版不需 `all uniq L`（next-pair 首分量只由
    zip 下标决定），私件 `fListFstOfDarts` 以 MEM 前提单独落地，公开件
    `fListFstSnd` 照 HOL 原文保留 `all uniq L` 前提（SND 半版必需，下游
    镜像件消费）；
  - `fst_node_hypermap_of_list`（list_hypermap-compiled.hl:982）+ 其上游
    `n_list_ext_fst`/`fst_n_list_ext_power`：批 7 私件 `fstNList`/`fstNodeOrbit`
    是 nodeMap（正向）版，本批消费面是 nodeMap.symm 轨道（node 轨道经
    `Hypermap.exists_pow_nodeMap_symm_apply_of_mem_node` 换 symm 幂表示），
    按实际消费面以 `fstInvOrbit`（symm 版保 FST + 留 dart 集，引擎 =
    inverseNodeMapList + fListFstOfDarts + nodeMap_permutes.symm_apply_mem +
    goodListEList）落地，不复制 TameList7 私件；
  - `parts_in_node` 的 `Hypermap.lemma_power_inverse_in_node2` 支：
    Hypermap.lean:8601 `nodeMap_symm_pow_mem_node_self` 已真直引（零移植）；
  - `Seq2.next_el_inj`（seq2 层）缺席，本批 §0 补 `nextElInj`（junk 三支 +
    `indexlNextEl` 双 if 分况 + idxOf 单射）；
  - `Seq2.next_el_power` 轨道枚举：批 8 私件 `nextElStep`/`nextElIterateGetElem`
    private 不跨文件，§0 同证重推导（批 7→8→9 惯例），
    `next_el_parts_power` 以公开件 `nextElPartsPower` 落地；
  - `e_list_ext_n_f`（list_hypermap 层 `n_list ∘ f_list = e_list` 于 dart 集）：
    TameLp 公开件 `nList_fList` 直引（零移植）；
  - `find_list_uniq` 双用（r = r' 与 q₁ = q₂ 两处）：批 9 公开件
    `findListUniq` 直引；
  - `indexf_hd`/`hd_eq_last`/`indexl_flatten`/`indexf_flatten`：indexf 主机
    （TameList3 §1）已备 `indexfCond`/`indexfAddLeft`/`indexfN`，本批只补
    四枚组合件；
  - `parts_last_as_fst_hd` 证明路线较 HOL 短：第二分量经
    `normalListPartsNextLast`（其自身两分支：LAST p = LAST r 走 f_last；
    否则 loopListFOrNi 第二支被 partsNextLast 排除）直取 f_list，
    HOL 的 edge_nondeg 反证在 normalListPartsNextLastNot 内完成，
    故 hnedg 在本件陈述保留（镜像 HOL）但证明体经前件消费；
  - `all uniq L` 前提：good_list 不蕴含（单面内重复元可造非 uniq 面），照
    HOL 原文保留为显式假设 `hunL : ∀ l ∈ L, l.Nodup`。

  载体折算（沿批 1-9 约定）：
  - `cat s t` ↦ `s ++ t`、`uniq` ↦ `List.Nodup`、`sizel` ↦ `List.length`；
  - `LAST`/`HD` ↦ `List.getLast!`/`List.head!`（junk 按默认值吸收，消费侧
    携带非空折算）、`EL` ↦ `List.getElem`（长度事实显式绑定器）；
  - `indexl` ↦ `List.idxOf`、`indexf` ↦ TameList3 `indexf`、
    `parts` ↦ `partsSpine`（批 7）、`next_el` ↦ `nextEl`（Assembly）、
    `f_list L` ↦ `fList L`、`e_list` ↦ `eList`、`n_list` ↦ `nList`；
  - `hypermap_of_list L` ↦ `hypermapOfList L hL`（GoodList 证人显式入参，
    批 5 NormalListSpine 约定）、`inverse (node_map H) POWER k` ↦
    `(hypermapOfList L hL).nodeMap.symm ^ k`、`node H x` ↦
    `(hypermapOfList L hL).node x`（Kepler.Text.Hypermap.node = orbitMap）、
    `loop_of_list r` ↦ `loopOfListSpine r`（批 6）、`is_node_going` ↦
    `Hypermap.IsNodeGoing`（Hypermap.lean:6561 已真）；
  - `quotient_list`/`core_list` ↦ 批 7 `quotientListSpine`/`coreListSpine`。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git 写操作。
-/

import Kepler.Text.TameSpine.TameList9

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl eList fList prevEl GoodList listPairs listOfDarts
  findFaceDarts nList)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (nextEl_eq_getD getD_eq_getElem_of_lt getElem_idxOf
   idxOf_getElem nextEl_mem_of_mem
   dart_in_face findFaceDarts_ex_of_self la7_length_listPairs
   hypermapOfList nodeMap_hypermapOfList findFaceDarts_nodup fList_mem_darts
   nList_fList la7_eList_involutory mem_darts_of_mem_findFace)

/-! ### §0 next_el/zip 私有引擎（批 8 私件同证重推导 + 载体小件） -/

/-- 同表两下标相等则取元相等（proof-irrelevant getElem 换形器，ℕ 版）。 -/
private theorem getElemConN {α : Type*} {l : List α} {a b : ℕ} (ha : a < l.length)
    (hb : b < l.length) (hab : a = b) : l[a]'ha = l[b]'hb := by
  subst hab; rfl

/-- 同表两下标相等则取元相等（proof-irrelevant getElem 换形器）。 -/
private theorem getElemCon {l : List (ℕ × ℕ)} {a b : ℕ} (ha : a < l.length)
    (hb : b < l.length) (hab : a = b) : l[a]'ha = l[b]'hb := by
  subst hab; rfl

/-- 非空表 `getLast!` 必是成员（批 9 私件同证重推导）。 -/
private theorem getLastMem {l : List (ℕ × ℕ)} (h : l ≠ []) : l.getLast! ∈ l := by
  have hpos : 0 < l.length := List.length_pos_of_ne_nil h
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (by omega)]
  simp

/-- 表外 `next_el` 恒等（junk 支；含空表，批 8/9 私件同证重推导）。 -/
private theorem nextElOfNotMem {s : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hx : x ∉ s) : nextEl s x = x := by
  cases s with
  | nil => rfl
  | cons a l =>
    have hidx : (a :: l).idxOf x = (a :: l).length := List.idxOf_eq_length hx
    have hpos : 0 < (a :: l).length := List.length_pos_of_ne_nil (by simp)
    show (if (a :: l).idxOf x = (a :: l).length - 1 then (a :: l).headD x
      else (a :: l).getD ((a :: l).idxOf x + 1) x) = x
    rw [if_neg (by omega : ¬((a :: l).idxOf x = (a :: l).length - 1)), hidx,
      List.getD_eq_default _ x (by omega)]

/-- 单步轨道：nodup 表第 `j` 项的 `next_el` = 第 `(j+1) mod len` 项
（批 8 私件同证重推导）。 -/
private theorem nextElStep {s : List (ℕ × ℕ)} (hsn : s.Nodup) {j : ℕ}
    (hj : j < s.length) (hj1 : (j + 1) % s.length < s.length) :
    nextEl s (s[j]'hj) = s[(j + 1) % s.length]'hj1 := by
  have hpos : 0 < s.length := List.length_pos_of_mem (List.getElem_mem hj)
  rw [nextEl_eq_getD (List.getElem_mem hj), idxOf_getElem hsn hj,
    getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]

/-- 轨道枚举：nodup 表上 `next_el` 幂从第 `j` 项出发按 mod 下标走
（批 8 私件同证重推导；HOL `Seq2.next_el_power` 载体形）。 -/
private theorem nextElIterateGetElem {s : List (ℕ × ℕ)} (hsn : s.Nodup) {j : ℕ}
    (hj : j < s.length) (n : ℕ) (hjn : (j + n) % s.length < s.length) :
    (nextEl s)^[n] (s[j]'hj) = s[(j + n) % s.length]'hjn := by
  have hpos : 0 < s.length := List.length_pos_of_mem (List.getElem_mem hj)
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply]
    exact getElemCon hj hjn (by rw [Nat.add_zero, Nat.mod_eq_of_lt hj])
  | succ k ih =>
    have hjk : (j + k) % s.length < s.length := Nat.mod_lt _ hpos
    rw [Function.iterate_succ_apply', ih hjk,
      nextElStep hsn hjk (Nat.mod_lt ((j + k) % s.length + 1) hpos)]
    refine getElemCon (Nat.mod_lt _ hpos) hjn ?_
    have hmod : ((j + k) % s.length + 1) % s.length = (j + k + 1) % s.length :=
      Nat.mod_add_mod (j + k) s.length 1
    rw [hmod, Nat.add_assoc]

/-- `next_el` 单射（HOL `Seq2.next_el_inj`：uniq s 时 next_el s x = next_el s y
⟹ x = y）。junk 支三情形 + `indexlNextEl` 双 if 分况 + idxOf 单射。 -/
private theorem nextElInj {s : List (ℕ × ℕ)} (hsn : s.Nodup) {x y : ℕ × ℕ}
    (h : nextEl s x = nextEl s y) : x = y := by
  by_cases hx : x ∈ s
  · by_cases hy : y ∈ s
    · have hxi : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hx
      have hyi : s.idxOf y < s.length := List.idxOf_lt_length_iff.mpr hy
      have e1 := indexlNextEl hsn hx
      have e2 := indexlNextEl hsn hy
      rw [h] at e1
      have hxy : s.idxOf x = s.idxOf y := by
        by_cases hx1 : s.idxOf x = s.length - 1
        · by_cases hy1 : s.idxOf y = s.length - 1
          · rw [if_pos hx1] at e1
            rw [if_pos hy1] at e2
            omega
          · rw [if_pos hx1] at e1
            rw [if_neg hy1] at e2
            omega
        · by_cases hy1 : s.idxOf y = s.length - 1
          · rw [if_neg hx1] at e1
            rw [if_pos hy1] at e2
            omega
          · rw [if_neg hx1] at e1
            rw [if_neg hy1] at e2
            omega
      calc x = s[s.idxOf x]'hxi := (getElem_idxOf hx).symm
        _ = s[s.idxOf y]'hyi := getElemCon hxi hyi hxy
        _ = y := getElem_idxOf hy
    · rw [nextElOfNotMem hy] at h
      exact absurd (h ▸ nextEl_mem_of_mem hx) hy
  · by_cases hy : y ∈ s
    · rw [nextElOfNotMem hx] at h
      exact absurd (h.symm ▸ nextEl_mem_of_mem hy) hx
    · rw [nextElOfNotMem hx, nextElOfNotMem hy] at h
      exact h

/-! ### §1 hypermap 桥簇头位（tame_list.hl:6607-:6740，批 9 处方重建） -/

/-- 元素级 zip 访问：`list_pairs s` 第 `j` 项 = `(s[j], s[(j+1) mod sizel s])`
（`list_pairs` 逐项展开；长度折算经 `la7_length_listPairs`）。 -/
private theorem listPairsGetElem {s : List ℕ} {j : ℕ} (hj : j < s.length) :
    (listPairs s)[j]'(Nat.lt_of_lt_of_eq hj (la7_length_listPairs s).symm)
      = (s[j]'hj,
        s[(j + 1) % s.length]'(Nat.mod_lt (j + 1)
          (Nat.lt_of_le_of_lt (Nat.zero_le j) hj))) := by
  have hlen : (listPairs s).length = s.length := la7_length_listPairs s
  have hpos : 0 < s.length := Nat.lt_of_le_of_lt (Nat.zero_le j) hj
  have hlenDr : (s.drop 1).length = s.length - 1 := List.length_drop
  have hlenTk : (List.take 1 s).length = min 1 s.length := List.length_take
  have htot : j < ((s.drop 1) ++ List.take 1 s).length := by
    rw [List.length_append, hlenDr, hlenTk]; omega
  show (s.zip (s.drop 1 ++ List.take 1 s))[j]'(Nat.lt_of_lt_of_eq hj (la7_length_listPairs s).symm) = _
  rw [List.getElem_zip]
  by_cases hj1 : j + 1 < s.length
  · have hrot : ((s.drop 1) ++ List.take 1 s)[j] = (s.drop 1)[j] :=
      List.getElem_append_left (by rw [hlenDr]; omega) (h' := htot)
    have hdr : (s.drop 1)[j] = s[1 + j] :=
      List.getElem_drop (h := by rw [hlenDr]; omega)
    rw [hrot, hdr]
    exact congrArg (Prod.mk s[j]) (getElemConN (by omega) (Nat.mod_lt (j + 1) hpos)
      (by rw [Nat.mod_eq_of_lt hj1]; omega))
  · have jlen : j + 1 = s.length := by omega
    have hrot : ((s.drop 1) ++ List.take 1 s)[j]
        = (List.take 1 s)[j - (s.drop 1).length] :=
      List.getElem_append_right (by rw [hlenDr]; omega) (h₂ := htot)
    have h0 : j - (s.drop 1).length = 0 := by rw [hlenDr]; omega
    have htak : (List.take 1 s)[j - (s.drop 1).length] = s[0] :=
      (getElemConN (by rw [hlenTk]; omega) (by rw [hlenTk]; omega) h0).trans
        (List.getElem_take (h := by rw [hlenTk]; omega))
    rw [hrot, htak]
    exact congrArg (Prod.mk s[j]) (getElemConN hpos (Nat.mod_lt (j + 1) hpos)
      (by rw [jlen, Nat.mod_self]))

/-- **HOL `next_el_list_pairs`**（list_hypermap-compiled.hl:316）的 FST-半版
（免 uniq：next-pair 首分量只由 zip 下标决定）——`f_list_fst_snd` 的引擎。 -/
private theorem nextElListPairsFst {s : List ℕ} {x y : ℕ}
    (h : (x, y) ∈ listPairs s) :
    (nextEl (listPairs s) (x, y)).1 = y := by
  have hlen : (listPairs s).length = s.length := la7_length_listPairs s
  have hpos : 0 < (listPairs s).length := List.length_pos_of_mem h
  have hposl : 0 < s.length := by rw [← hlen]; exact hpos
  have hi : (listPairs s).idxOf (x, y) < (listPairs s).length :=
    List.idxOf_lt_length_iff.mpr h
  have hI : (listPairs s).idxOf (x, y) < s.length := by rw [← hlen]; exact hi
  have hxy : (listPairs s)[(listPairs s).idxOf (x, y)] = (x, y) := getElem_idxOf h
  have hpair := listPairsGetElem (s := s) (j := (listPairs s).idxOf (x, y)) hI
  have hys : s[((listPairs s).idxOf (x, y) + 1) % s.length]'(Nat.mod_lt _ hposl) = y :=
    congrArg Prod.snd (hpair.symm.trans hxy)
  rw [nextEl_eq_getD h, getD_eq_getElem_of_lt (Nat.mod_lt _ hpos),
    listPairsGetElem
      (j := ((listPairs s).idxOf (x, y) + 1) % (listPairs s).length)
      (Nat.lt_of_lt_of_eq (Nat.mod_lt _ hpos) (la7_length_listPairs s))]
  have hAB : ((listPairs s).idxOf (x, y) + 1) % (listPairs s).length
      = ((listPairs s).idxOf (x, y) + 1) % s.length := by rw [hlen]
  have hA : s[((listPairs s).idxOf (x, y) + 1) % (listPairs s).length]'(
      Nat.lt_of_lt_of_eq (Nat.mod_lt _ hpos) (la7_length_listPairs s)) = y :=
    (getElemConN (Nat.lt_of_lt_of_eq (Nat.mod_lt _ hpos) (la7_length_listPairs s))
      (Nat.mod_lt _ hposl) hAB).symm ▸ hys
  exact hA

/-- **HOL `next_el_list_pairs`**（list_hypermap-compiled.hl:316）
`uniq s /\ MEM (x,y) (list_pairs s) ==> next_el (list_pairs s) (x,y) = (y, next_el s y)`
——面内 zip 环上 `next_el` 逐项（List_hypermap 层件首次有消费者；
SND 半版需 uniq s 定位 y 的下标）。 -/
theorem nextElListPairs {s : List ℕ} (hsn : s.Nodup) {x y : ℕ}
    (h : (x, y) ∈ listPairs s) :
    nextEl (listPairs s) (x, y) = (y, nextEl s y) := by
  have hlen : (listPairs s).length = s.length := la7_length_listPairs s
  have hpos : 0 < (listPairs s).length := List.length_pos_of_mem h
  have hposl : 0 < s.length := by rw [← hlen]; exact hpos
  have hi : (listPairs s).idxOf (x, y) < (listPairs s).length :=
    List.idxOf_lt_length_iff.mpr h
  have hI : (listPairs s).idxOf (x, y) < s.length := by rw [← hlen]; exact hi
  have hxy : (listPairs s)[(listPairs s).idxOf (x, y)] = (x, y) := getElem_idxOf h
  have hpair := listPairsGetElem (s := s) (j := (listPairs s).idxOf (x, y)) hI
  have hys : s[((listPairs s).idxOf (x, y) + 1) % s.length]'(Nat.mod_lt _ hposl) = y :=
    congrArg Prod.snd (hpair.symm.trans hxy)
  have hmemY : y ∈ s := hys ▸ List.getElem_mem (Nat.mod_lt _ hposl)
  have hidxY : s.idxOf y = ((listPairs s).idxOf (x, y) + 1) % s.length := by
    have h9 := idxOf_getElem hsn
      (i := ((listPairs s).idxOf (x, y) + 1) % s.length) (Nat.mod_lt _ hposl)
    rw [hys] at h9
    exact h9
  have hnext : nextEl s y =
      s[(((listPairs s).idxOf (x, y) + 1) % s.length + 1) % s.length]'(Nat.mod_lt _ hposl) := by
    rw [nextEl_eq_getD hmemY, hidxY, getD_eq_getElem_of_lt (Nat.mod_lt _ hposl)]
  rw [nextEl_eq_getD h, getD_eq_getElem_of_lt (Nat.mod_lt _ hpos),
    listPairsGetElem
      (j := ((listPairs s).idxOf (x, y) + 1) % (listPairs s).length)
      (Nat.lt_of_lt_of_eq (Nat.mod_lt _ hpos) (la7_length_listPairs s))]
  have hCD : (((listPairs s).idxOf (x, y) + 1) % (listPairs s).length + 1) % s.length
      = (((listPairs s).idxOf (x, y) + 1) % s.length + 1) % s.length := by
    rw [hlen]
  have hAB : ((listPairs s).idxOf (x, y) + 1) % (listPairs s).length
      = ((listPairs s).idxOf (x, y) + 1) % s.length := by rw [hlen]
  have e1 : s[((listPairs s).idxOf (x, y) + 1) % (listPairs s).length]'(
      Nat.lt_of_lt_of_eq (Nat.mod_lt _ hpos) (la7_length_listPairs s)) = y :=
    (getElemConN (Nat.lt_of_lt_of_eq (Nat.mod_lt _ hpos) (la7_length_listPairs s))
      (Nat.mod_lt _ hposl) hAB).symm ▸ hys
  have e2 : s[(((listPairs s).idxOf (x, y) + 1) % (listPairs s).length + 1) % s.length]'(
      Nat.mod_lt _ hposl) = nextEl s y :=
    (getElemConN (Nat.mod_lt _ hposl) (Nat.mod_lt _ hposl) hCD).trans hnext.symm
  rw [e1, e2]

/-- **HOL `f_list_fst_snd`**（tame_list.hl:6702-:6720）的引擎半版：
`MEM x (list_of_darts L) ==> FST (f_list L x) = SND x`（免 `all uniq L`）。 -/
private theorem fListFstOfDarts (L : fgraph ℕ) {x : ℕ × ℕ}
    (hx : x ∈ listOfDarts L) : (fList L x).1 = x.2 := by
  obtain ⟨l, _, hff, hxl⟩ := findFaceDarts_ex_of_self (dart_in_face L x |>.mpr hx)
  show (nextEl (findFaceDarts L x) x).1 = x.2
  rw [hff]
  exact nextElListPairsFst hxl

/-- **HOL `f_list_fst_snd`**（tame_list.hl:6702-:6720）
`all uniq L /\ MEM x (list_of_darts L) ==> FST (f_list L x) = SND x`
——FST 半版免 uniq（`fListFstOfDarts`），`all uniq L` 为 HOL 原文前提
（SND 半版必需，下游镜像件消费）。 -/
theorem fListFstSnd (L : fgraph ℕ) (hunL : ∀ l ∈ L, l.Nodup) {x : ℕ × ℕ}
    (hx : x ∈ listOfDarts L) : (fList L x).1 = x.2 :=
  fListFstOfDarts L hx

/-- **HOL `parts_darts`**（tame_list.hl:6722-:6740）
`MEM x p /\ MEM p (parts L r) /\ MEM r N /\ normal_list L N ==> MEM x (list_of_darts L)`
——`parts_flatten` + `normal_list_list_of_darts`。 -/
theorem partsDarts (L : fgraph ℕ) {hL : GoodList L} {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N) {r : List (ℕ × ℕ)} (hr : r ∈ N)
    {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r) {x : ℕ × ℕ} (hx : x ∈ p) :
    x ∈ listOfDarts L := by
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  have hxP : x ∈ (partsSpine L r).flatten := List.mem_flatten.mpr ⟨p, hp, hx⟩
  rw [partsFlatten L hr1 hr2] at hxP
  exact normalListListOfDarts hn x (List.mem_flatten.mpr ⟨r, hr, hxP⟩)

/-- **HOL `parts_node_inverse_power`**（tame_list.hl:6607-:6663）
`normal_list L N /\ good_list L /\ MEM r N /\ MEM p (parts L r) /\
  MEM x p /\ k + indexl x p < sizel p ==>`
`((inverse (node_map (hypermap_of_list L))) POWER k) x = EL (k + indexl x p) p`
——k 归纳：归纳步在 `y = EL (k + indexl x p) p` 处用 `parts_next_unlast`
（y ≠ LAST p 由 nodup 下标算术）+ `inverse_node_map_list` + `indexl_next_el`。 -/
theorem partsNodeInversePower (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N) {r : List (ℕ × ℕ)}
    (hr : r ∈ N) {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r) (k : ℕ)
    {x : ℕ × ℕ} (hx : x ∈ p) (hlen : k + p.idxOf x < p.length) :
    (((hypermapOfList L hL).nodeMap.symm ^ k) x) = p[k + p.idxOf x]'(by omega) := by
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  have hpun : p.Nodup := partsUniq L hr1 hr2 p hp
  have hpne : p ≠ [] := partsAllNonnil L hr1 hr2 p hp
  have hpos : 0 < p.length := List.length_pos_of_ne_nil hpne
  have hlast : p.idxOf p.getLast! = p.length - 1 := idxOfGetLast hpun hpne
  have hpn := partsNextUnlast L hr1 hr2
  have key : ∀ k : ℕ, ∀ z ∈ p, ∀ hl : k + p.idxOf z < p.length,
      (((hypermapOfList L hL).nodeMap.symm ^ k) z) = p[k + p.idxOf z]'hl := by
    intro k
    induction k with
    | zero =>
      intro z hz hl
      rw [pow_zero, Equiv.Perm.one_apply]
      exact (getElem_idxOf hz).symm.trans
        (getElemCon (List.idxOf_lt_length_iff.mpr hz) hl (Nat.zero_add _).symm)
    | succ k ih =>
      intro z hz h
      have hk : k + p.idxOf z < p.length := by omega
      have hIH := ih z hz hk
      have hy : p[k + p.idxOf z]'hk ∈ p := List.getElem_mem hk
      have hidx : p.idxOf (p[k + p.idxOf z]'hk) = k + p.idxOf z := idxOf_getElem hpun hk
      have hynl : p[k + p.idxOf z]'hk ≠ p.getLast! := by
        intro hc
        rw [hc] at hidx
        omega
      have hD : p[k + p.idxOf z]'hk ∈ listOfDarts L := partsDarts L hn hr hp hy
      have hstep : (((hypermapOfList L hL).nodeMap.symm ^ (k + 1)) z)
          = fList L (eList (p[k + p.idxOf z]'hk)) := by
        rw [pow_succ', Equiv.Perm.mul_apply, hIH, inverseNodeMapList hL hD]
      have hnext : nextEl p (p[k + p.idxOf z]'hk)
          = p[k + 1 + p.idxOf z]'(by omega) := by
        rw [nextEl_eq_getD hy, hidx, getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]
        have him : (k + p.idxOf z + 1) % p.length = k + p.idxOf z + 1 :=
          Nat.mod_eq_of_lt (by omega)
        exact getElemCon (Nat.mod_lt _ hpos) (by omega)
          (show (k + p.idxOf z + 1) % p.length = k + 1 + p.idxOf z from by
            rw [him]; omega)
      rw [hstep, ← hpn p hp (p[k + p.idxOf z]'hk) hy hynl, hnext]
  exact key k x hx hlen

/-- **HOL `parts_in_node`**（tame_list.hl:6665-:6685）
`normal_list L N /\ good_list L /\ MEM r N /\ MEM p (parts L r) /\ MEM x p ==>
  x IN node (hypermap_of_list L) (HD p)`
——`parts_node_inverse_power` 在 k = indexl x p、起点 HD p 处（index_hd0 归零），
落地经 `Hypermap.nodeMap_symm_pow_mem_node_self`（HOL
lemma_power_inverse_in_node2 的已真镜像）。 -/
theorem partsInNode (L : fgraph ℕ) (hL : GoodList L) {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N) {r : List (ℕ × ℕ)} (hr : r ∈ N)
    {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r) {x : ℕ × ℕ} (hx : x ∈ p) :
    x ∈ (hypermapOfList L hL).node p.head! := by
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  have hpne : p ≠ [] := partsAllNonnil L hr1 hr2 p hp
  have h0 : p.idxOf p.head! = 0 := indexHd0 hpne
  have hx0 : p.idxOf x < p.length := List.idxOf_lt_length_iff.mpr hx
  have hpow := partsNodeInversePower L hL hn hr hp (p.idxOf x)
    (x := p.head!) (List.head!_mem_self hpne) (by omega)
  have hmem := Kepler.Text.Hypermap.nodeMap_symm_pow_mem_node_self
    (hypermapOfList L hL) p.head! (p.idxOf x)
  rw [hpow] at hmem
  have hxx : p[p.idxOf x + p.idxOf p.head!]'(by omega) = p[p.idxOf x]'hx0 := by
    refine getElemCon _ _ ?_
    rw [h0]
    omega
  rw [hxx, getElem_idxOf hx] at hmem
  exact hmem

/-- nodeMap-symm 轨道引擎：幂保 FST 且留 dart 集（HOL `fst_n_list_ext_power`
的 symm 版载体；引擎 = `inverse_node_map_list` + `fListFstOfDarts` +
`nodeMap_permutes.symm_apply_mem` + `goodListEList`）。 -/
private theorem fstInvOrbit {L : fgraph ℕ} (hL : GoodList L) {x : ℕ × ℕ}
    (hx : x ∈ (hypermapOfList L hL).darts) :
    ∀ n : ℕ, (((hypermapOfList L hL).nodeMap.symm ^ n) x).1 = x.1
      ∧ ((hypermapOfList L hL).nodeMap.symm ^ n) x ∈ (hypermapOfList L hL).darts := by
  intro n
  induction n with
  | zero => exact ⟨rfl, hx⟩
  | succ k ih =>
    obtain ⟨hfst, hmem⟩ := ih
    have hD : ((hypermapOfList L hL).nodeMap.symm ^ k) x ∈ listOfDarts L :=
      List.mem_toFinset.mp hmem
    have hED : eList (((hypermapOfList L hL).nodeMap.symm ^ k) x) ∈ listOfDarts L :=
      goodListEList hL hD
    have hfst2 : ((((hypermapOfList L hL).nodeMap.symm ^ (k + 1)) x).1) = x.1 := by
      rw [pow_succ', Equiv.Perm.mul_apply, inverseNodeMapList hL hD,
        fListFstOfDarts L hED]
      exact hfst
    have hmem2 : (((hypermapOfList L hL).nodeMap.symm ^ (k + 1)) x)
        ∈ (hypermapOfList L hL).darts := by
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact (hypermapOfList L hL).nodeMap_permutes.symm_apply_mem hmem
    exact ⟨hfst2, hmem2⟩

/-- **HOL `parts_fst`**（tame_list.hl:6687-:6700）
`normal_list L N /\ good_list L /\ MEM r N /\ MEM p (parts L r) /\ MEM x p ==>
  FST x = FST (HD p)`——`parts_in_node` + node 轨道的 symm 幂表示
（`Hypermap.exists_pow_nodeMap_symm_apply_of_mem_node`）+ nodeMap-symm 轨道保 FST。 -/
theorem partsFst (L : fgraph ℕ) (hL : GoodList L) {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N) {r : List (ℕ × ℕ)} (hr : r ∈ N)
    {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r) {x : ℕ × ℕ} (hx : x ∈ p) :
    x.1 = p.head!.1 := by
  have hnode := partsInNode L hL hn hr hp hx
  obtain ⟨n, _, hn'⟩ :=
    Kepler.Text.Hypermap.exists_pow_nodeMap_symm_apply_of_mem_node _ hnode
  have hpne : p ≠ [] := partsAllNonnil L (normalListUniqNonnil hn hr).1
    (normalListUniqNonnil hn hr).2 p hp
  have hd : p.head! ∈ (hypermapOfList L hL).darts :=
    List.mem_toFinset.mpr (partsDarts L hn hr hp (List.head!_mem_self hpne))
  rw [hn']
  exact (fstInvOrbit hL hd n).1

/-! ### §2 quotient_list 块（tame_list.hl:6742-:7151） -/

/-- **HOL `normal_list_parts_next_last`**（tame_list.hl:7180-:7206）
`normal_list L N /\ MEM r N /\ MEM p (parts L r) ==> next_el r (LAST p) = f_list L (LAST p)`
——LAST p = LAST r 支走 f_last（normal_list 第三合取项）；否则 loopListFOrNi
第二支被 parts_next_last 排除。本件较 HOL 原序（:7180）前置（parts_last_as_fst_hd
依赖，见头注）。 -/
theorem normalListPartsNextLast (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N) {r : List (ℕ × ℕ)}
    (hr : r ∈ N) {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r) :
    nextEl r p.getLast! = fList L p.getLast! := by
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  have hflast : fLastSpine L r := hn.2.2.1 r hr
  have hloop : loopListSpine L r := hn.2.2.2.1 r hr
  by_cases hlast : p.getLast! = r.getLast!
  · rw [hlast]
    exact hflast
  · have hlastP : p.getLast! ∈ p := getLastMem (partsAllNonnil L hr1 hr2 p hp)
    have hlastR : p.getLast! ∈ r := (partsUniqNonnil L hL hn hr hp).2.2.2.2 p.getLast! hlastP
    rcases loopListFOrNi hloop hlastR with h1 | h1
    · exact h1
    · exact absurd h1 (partsNextLast L hr1 hr2 p hp p.getLast! hlastP rfl hlast)

/-- **HOL `normal_list_parts_next_last_not`**（tame_list.hl:7208-:7222）
`good_list L /\ normal_list L N /\ MEM r N /\ MEM p (parts L r) /\
  is_edge_nondegenerate (hypermap_of_list L) ==>
  ~(next_el r (LAST p) = f_list L (e_list (LAST p)))`——前件 + edge_nondeg。 -/
theorem normalListPartsNextLastNot (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate) {r : List (ℕ × ℕ)}
    (hr : r ∈ N) {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r) :
    nextEl r p.getLast! ≠ fList L (eList p.getLast!) := by
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  have hpne : p ≠ [] := partsAllNonnil L hr1 hr2 p hp
  have hD : p.getLast! ∈ listOfDarts L := partsDarts L hn hr hp (getLastMem hpne)
  rw [normalListPartsNextLast L hL hn hr hp]
  exact edgeNondegFXorNi hL hnedg hD

/-- **HOL `parts_last_as_fst_hd`**（tame_list.hl:6742-:6807）
`normal_list L N /\ is_edge_nondegenerate (hypermap_of_list L) /\ good_list L /\
  all uniq L /\ MEM r N /\ MEM p (parts L r) /\ p' = next_el (parts L r) p ==>
  (FST (HD p), FST (HD p')) = LAST p`
——首分量 = parts_fst 于 LAST p；次分量经 next_el_parts_last +
normal_list_parts_next_last + f_list_fst_snd。 -/
theorem partsLastAsFstHd (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate) (hunL : ∀ l ∈ L, l.Nodup)
    {r : List (ℕ × ℕ)} (hr : r ∈ N) {p p' : List (ℕ × ℕ)}
    (hp : p ∈ partsSpine L r) (hp' : p' = nextEl (partsSpine L r) p) :
    (p.head!.1, p'.head!.1) = p.getLast! := by
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  have hpne : p ≠ [] := partsAllNonnil L hr1 hr2 p hp
  have hlastP : p.getLast! ∈ p := getLastMem hpne
  subst hp'
  have hpair : (p.head!.1, (nextEl (partsSpine L r) p).head!.1)
      = (p.getLast!.1, p.getLast!.2) := by
    congr 1
    · exact (partsFst L hL hn hr hp hlastP).symm
    · rw [← nextElPartsLast L hr1 hr2 hp hlastP rfl,
        normalListPartsNextLast L hL hn hr hp]
      exact fListFstOfDarts L (partsDarts L hn hr hp hlastP)
  rw [hpair]

/-- 辅助：flatten-nodup + 成员全非空 ⟹ 表自身 nodup（批 9 私件
`nodupOfFlattenNodup` 同证重推导，供 uniqParts 使用）。 -/
private theorem nodupOfFlattenNodup10 {L : List (List (ℕ × ℕ))} (hun : L.flatten.Nodup)
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
      have hy : y ∈ (y :: s) := List.mem_cons_self ..
      have hy2 : y ∈ t.flatten := List.mem_flatten.mpr ⟨y :: s, hc, hy⟩
      exact (List.nodup_append.mp hun).2.2 y hy y hy2 rfl

/-- **HOL `uniq_parts`**（tame_list.hl:6809-:6820）
`uniq r /\ ~(r = []) ==> uniq (parts L r)`——flatten-nodup（= r）+
成员全非空（nodupOfFlattenNodup10）。 -/
theorem uniqParts (L : fgraph ℕ) {r : List (ℕ × ℕ)} (hun : r.Nodup) (hne : r ≠ []) :
    (partsSpine L r).Nodup := by
  have hfl : (partsSpine L r).flatten.Nodup := by
    rw [partsFlatten L hun hne]; exact hun
  exact nodupOfFlattenNodup10 hfl (partsAllNonnil L hun hne)

/-- **HOL `parts_list_pairs`**（tame_list.hl:6822-:6884）
`normal_list L N /\ is_edge_nondegenerate (hypermap_of_list L) /\ good_list L /\
  MEM r N /\ all uniq L ==>`
`list_pairs (MAP (\x. FST (HD x)) (parts L r)) = MAP LAST (parts L r)`
——ext_get 逐项：第 i 项 = (FST (HD p_i), FST (HD p_{i+1})) = LAST p_i，
其中 p_{i+1} = next_el (parts) p_i（nodup 下标），恒等式即 parts_last_as_fst_hd。 -/
theorem partsListPairs (L : fgraph ℕ) (hL : GoodList L) {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N) (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup) {r : List (ℕ × ℕ)} (hr : r ∈ N) :
    listPairs ((partsSpine L r).map (fun q => q.head!.1))
      = (partsSpine L r).map (fun q => q.getLast!) := by
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  have hPsne : (partsSpine L r) ≠ [] := partsNonnil L hr1 hr2
  have hPsn : (partsSpine L r).Nodup := uniqParts L hr1 hr2
  have hPspos : 0 < (partsSpine L r).length := List.length_pos_of_ne_nil hPsne
  have hXlen : ((partsSpine L r).map (fun q => q.head!.1)).length
      = (partsSpine L r).length := List.length_map _
  have hXlen2 : (listPairs ((partsSpine L r).map (fun q => q.head!.1))).length
      = (partsSpine L r).length := by rw [la7_length_listPairs, hXlen]
  have hMlen : ((partsSpine L r).map (fun q => q.getLast!)).length
      = (partsSpine L r).length := List.length_map _
  refine List.ext_get ?_ (fun i h1 h2 => ?_)
  · rw [hXlen2, hMlen]
  · have hj : i < ((partsSpine L r).map (fun q => q.head!.1)).length := by
      rw [hXlen]; exact hXlen2 ▸ h1
    show (listPairs ((partsSpine L r).map (fun q => q.head!.1)))[i]'h1
      = ((partsSpine L r).map (fun q => q.getLast!))[i]'h2
    have hAB : (i + 1) % ((partsSpine L r).map (fun q => q.head!.1)).length
        = (i + 1) % (partsSpine L r).length := by rw [hXlen]
    have hsecond : ((partsSpine L r).map (fun q => q.head!.1))[(i + 1) %
        ((partsSpine L r).map (fun q => q.head!.1)).length]'(Nat.mod_lt (i + 1)
          (Nat.lt_of_le_of_lt (Nat.zero_le i) hj))
        = ((partsSpine L r).map (fun q => q.head!.1))[(i + 1) % (partsSpine L r).length]'(
            Nat.lt_of_lt_of_eq (Nat.mod_lt (i + 1) hPspos) hXlen.symm) :=
      getElemConN _ _ hAB
    have hiP : i < (partsSpine L r).length := hXlen ▸ hj
    have hpMem : (partsSpine L r)[i]'hiP ∈ partsSpine L r := List.getElem_mem hiP
    have hnext : nextEl (partsSpine L r) ((partsSpine L r)[i]'hiP)
        = (partsSpine L r)[(i + 1) % (partsSpine L r).length]'(Nat.mod_lt (i + 1)
            hPspos) := by
      rw [nextEl_eq_getD hpMem, idxOf_getElem hPsn hiP,
        getD_eq_getElem_of_lt (Nat.mod_lt _ hPspos)]
    simp only [List.getElem_map,
      listPairsGetElem (s := (partsSpine L r).map (fun q => q.head!.1)) (j := i) hj,
      hsecond, List.getElem_map (f := fun (q : List (ℕ × ℕ)) => (q.head!).1), ← hnext]
    exact partsLastAsFstHd L hL hn hnedg hunL hr hpMem rfl

/-- **HOL `list_of_darts_quotient`**（tame_list.hl:6886-:6911）
`normal_list L N /\ is_edge_nondegenerate (hypermap_of_list L) /\ good_list L /\
  all uniq L ==>`
`list_of_darts (quotient_list L N) = MAP LAST (flatten (MAP (parts L) N))`
——逐元素 parts_list_pairs + MAP_eq + flatten-map 交换。 -/
theorem listOfDartsQuotient (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate) (hunL : ∀ l ∈ L, l.Nodup) :
    listOfDarts (quotientListSpine L N)
      = ((N.map (partsSpine L)).flatten).map (fun q => q.getLast!) := by
  show (((quotientListSpine L N).map listPairs)).flatten = _
  rw [quotientListSpine, coreListSpine, List.map_map, List.map_flatten]
  refine congrArg List.flatten (List.map_congr_left fun f hf => ?_)
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hf
  exact partsListPairs L hL hn hnedg hunL hr

/-- **HOL `mem_list_of_darts_quotient`**（tame_list.hl:6913-:6928）
`... ==> (MEM d (list_of_darts (quotient_list L N)) <=>
  (?p r. MEM p (parts L r) /\ MEM r N /\ d = LAST p))`——前件展开。 -/
theorem memListOfDartsQuotient (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate) (hunL : ∀ l ∈ L, l.Nodup)
    (d : ℕ × ℕ) :
    d ∈ listOfDarts (quotientListSpine L N) ↔
      ∃ p : List (ℕ × ℕ), ∃ r : List (ℕ × ℕ),
        p ∈ partsSpine L r ∧ r ∈ N ∧ d = p.getLast! := by
  rw [listOfDartsQuotient L hL hn hnedg hunL, List.mem_map]
  constructor
  · rintro ⟨q, hq, hd⟩
    obtain ⟨p', hp', hqp'⟩ := List.mem_flatten.mp hq
    obtain ⟨r, hrN, rfl⟩ := List.mem_map.mp hp'
    exact ⟨q, r, hqp', hrN, hd.symm⟩
  · rintro ⟨p, r, hp, hrN, rfl⟩
    refine ⟨p, List.mem_flatten.mpr ⟨partsSpine L r,
      List.mem_map.mpr ⟨r, hrN, rfl⟩, hp⟩, rfl⟩

/-- **HOL `flatten_flatten`**（tame_list.hl:6930-:6939）
`flatten (MAP flatten s) = flatten (flatten s)`。 -/
theorem flattenFlatten (s : List (List (List (ℕ × ℕ)))) :
    (s.map (fun t => t.flatten)).flatten = s.flatten.flatten := by
  induction s with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.flatten_cons, List.flatten_append]
    rw [ih]

/-- **HOL `normal_list_flatten_flatten`**（tame_list.hl:6941-:6961）
`normal_list L N ==> flatten (flatten (MAP (parts L) N)) = flatten N`
——逐元素 parts_flatten（flatten_flatten 交换 + 逐面归纳；归纳假设取
尾表限制版 NormalListSpine：前四合取项可限制，第五项不被本件消费）。 -/
theorem normalListFlattenFlatten (L : fgraph ℕ) {hL : GoodList L}
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N) :
    ((N.map (partsSpine L)).map (fun t => t.flatten)).flatten = N.flatten := by
  rw [flattenFlatten]
  have hmain : ∀ Ts : List (List (ℕ × ℕ)), (∀ s ∈ Ts, s ∈ N) →
      (((Ts.map (partsSpine L)).flatten).flatten) = Ts.flatten := by
    intro Ts
    induction Ts with
    | nil => intro _; rfl
    | cons a t ih =>
      intro hmem
      obtain ⟨ha1, ha2⟩ := normalListUniqNonnil hn (hmem a (List.mem_cons_self ..))
      rw [List.map_cons, List.flatten_cons, List.flatten_append,
        partsFlatten L ha1 ha2, ih (fun s hs => hmem s (List.mem_cons_of_mem _ hs)),
        List.flatten_cons]
  rw [hmain N (fun _ hs => hs)]

/-- **HOL `list_of_darts_quotient_uniq`**（tame_list.hl:6963-:7020）
`... ==> uniq (list_of_darts (quotient_list L N))`——LAST 在 parts-flatten 上单射
（find_list_uniq 双用：跨面 r = r\' 与面内 q₁ = q₂）+ 逐面不相交归纳
（归纳只消费 normal_list 前三合取项的限制版，第五项不参与）。 -/
theorem listOfDartsQuotientUniq (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate) (hunL : ∀ l ∈ L, l.Nodup) :
    (listOfDarts (quotientListSpine L N)).Nodup := by
  rw [listOfDartsQuotient L hL hn hnedg hunL]
  have hFl : ((N.map (partsSpine L)).flatten).Nodup := by
    have key : ∀ Ts : List (List (ℕ × ℕ)), (∀ s ∈ Ts, s ∈ N) →
        (∀ s ∈ Ts, s ≠ []) → Ts.flatten.Nodup →
        ((Ts.map (partsSpine L)).flatten).Nodup := by
      intro Ts
      induction Ts with
      | nil => intro _ _ _; simp
      | cons a t ih =>
        intro hmem hnn hflat
        have hmemT : ∀ s ∈ t, s ∈ N := fun s hs => hmem s (List.mem_cons_of_mem _ hs)
        have hnnT : ∀ s ∈ t, s ≠ [] := fun s hs => hnn s (List.mem_cons_of_mem _ hs)
        have hflatT : t.flatten.Nodup :=
          List.Sublist.nodup (List.sublist_append_right a t.flatten) hflat
        obtain ⟨ha1, ha2⟩ := normalListUniqNonnil hn
          (hmem a (List.mem_cons_self ..))
        have hNfc : (a ++ t.flatten).Nodup := by
          rw [← List.flatten_cons]; exact hflat
        obtain ⟨haNod, -, hdisj⟩ := List.nodup_append.mp hNfc
        rw [List.map_cons, List.flatten_cons, List.nodup_append]
        refine ⟨?_, ih hmemT hnnT hflatT, ?_⟩
        · exact nodupOfFlattenNodup10
            (by rw [partsFlatten L haNod (hnn a (List.mem_cons_self ..))]; exact haNod)
            (partsAllNonnil L haNod (hnn a (List.mem_cons_self ..)))
        · intro z1 hz1 z2 hz2 hEq
          obtain ⟨r', hr't, hzr'⟩ := List.mem_flatten.mp hz2
          obtain ⟨r', hr'tN, rfl⟩ := List.mem_map.mp hr't
          obtain ⟨hr1', hr2'⟩ := normalListUniqNonnil hn (hmemT r' hr'tN)
          have hq₂ne : z2 ≠ [] := partsAllNonnil L hr1' hr2' _ hzr'
          have hzr : z2.getLast! ∈ r' :=
            (partsUniqNonnil L hL hn (hmemT r' hr'tN) hzr').2.2.2.2 _
              (getLastMem hq₂ne)
          have hlastEq : z1.getLast! = z2.getLast! := congrArg List.getLast! hEq
          have haMem : a ∈ N := hmem a (List.mem_cons_self ..)
          obtain ⟨ha1, ha2⟩ := normalListUniqNonnil hn haMem
          have hz1ne : z1 ≠ [] := partsAllNonnil L ha1 ha2 _ hz1
          have hz1' : z1.getLast! ∈ a :=
            (partsUniqNonnil L hL hn haMem hz1).2.2.2.2 _ (getLastMem hz1ne)
          have hz2' : z1.getLast! ∈ t.flatten :=
            List.mem_flatten.mpr ⟨r', hr'tN, hlastEq ▸ hzr⟩
          exact hdisj z1.getLast! hz1' z1.getLast! hz2' rfl
    exact key N (fun s hs => hs) hn.2.1 hn.1
  -- LAST 在 parts-flatten 上单射
  refine List.Nodup.map_on (f := fun q => q.getLast!) ?_ hFl
  intro q₁ h₁ q₂ h₂ he
  obtain ⟨r₁, hr₁M, hp₁⟩ := List.mem_flatten.mp h₁
  obtain ⟨r₂, hr₂M, hp₂⟩ := List.mem_flatten.mp h₂
  obtain ⟨r₁, hr₁N, rfl⟩ := List.mem_map.mp hr₁M
  obtain ⟨r₂, hr₂N, rfl⟩ := List.mem_map.mp hr₂M
  obtain ⟨hr₁', hr₁''⟩ := normalListUniqNonnil hn hr₁N
  obtain ⟨hr₂', hr₂''⟩ := normalListUniqNonnil hn hr₂N
  have hq₁ne : q₁ ≠ [] := partsAllNonnil L hr₁' hr₁'' _ hp₁
  have hq₂ne : q₂ ≠ [] := partsAllNonnil L hr₂' hr₂'' _ hp₂
  have hd₁ : q₁.getLast! ∈ r₁ := by
    have hzf : q₁.getLast! ∈ (partsSpine L r₁).flatten :=
      List.mem_flatten.mpr ⟨q₁, hp₁, getLastMem hq₁ne⟩
    rw [partsFlatten L hr₁' hr₁''] at hzf
    exact hzf
  have hd₂ : q₂.getLast! ∈ r₂ := by
    have hzf : q₂.getLast! ∈ (partsSpine L r₂).flatten :=
      List.mem_flatten.mpr ⟨q₂, hp₂, getLastMem hq₂ne⟩
    rw [partsFlatten L hr₂' hr₂''] at hzf
    exact hzf
  have hrr : r₁ = r₂ := by
    have e1 := findListUniq hn.1 hd₁ hr₁N
    have e2 := findListUniq hn.1 hd₂ hr₂N
    rw [he] at e1
    exact e1.symm.trans e2
  subst hrr
  have hq1 : findListSpine (partsSpine L r₁) q₁.getLast! = q₁ :=
    findListUniq (by rw [partsFlatten L hr₁' hr₁'']; exact hr₁') (getLastMem hq₁ne) hp₁
  have hq2 : findListSpine (partsSpine L r₁) q₂.getLast! = q₂ :=
    findListUniq (by rw [partsFlatten L hr₁' hr₁'']; exact hr₁')
      (getLastMem hq₂ne) hp₂
  exact hq1.symm.trans ((congrArg (findListSpine (partsSpine L r₁)) he).trans hq2)

/-- **HOL `list_of_darts_quotient_sym`**（tame_list.hl:7022-:7150）
`... ==> !d. MEM d (list_of_darts (quotient_list L N)) ==>
  MEM (SND d, FST d) (list_of_darts (quotient_list L N))`——e_list 闭包：
n_list ∘ f_list = e_list（nList_fList）落于 node 轨道 ⊆ flatten N 定位所在面，
再经 parts_next_unlast + next_el 单射 + edge_nondeg 排除退化。 -/
theorem listOfDartsQuotientSym (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate) (hunL : ∀ l ∈ L, l.Nodup)
    (d : ℕ × ℕ) (hd : d ∈ listOfDarts (quotientListSpine L N)) :
    eList d ∈ listOfDarts (quotientListSpine L N) := by
  obtain ⟨p, r, hp, hrN, hde⟩ := (memListOfDartsQuotient L hL hn hnedg hunL d).mp hd
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hrN
  have hpne : p ≠ [] := partsAllNonnil L hr1 hr2 p hp
  have hlastP : p.getLast! ∈ p := getLastMem hpne
  have hlastR : p.getLast! ∈ r := (partsUniqNonnil L hL hn hrN hp).2.2.2.2 _ hlastP
  have hlastD : p.getLast! ∈ listOfDarts L := partsDarts L hn hrN hp hlastP
  -- f_list L (LAST p) ∈ r ⊆ flatten N
  have hfR : fList L p.getLast! ∈ r := by
    rw [← normalListPartsNextLast L hL hn hrN hp]
    exact nextEl_mem_of_mem hlastR
  have hfF : fList L p.getLast! ∈ N.flatten := List.mem_flatten.mpr ⟨r, hrN, hfR⟩
  -- n_list (f_list LAST p) = e_list (LAST p) 落 node 轨道 ⟹ ∈ flatten N
  have hw : fList L p.getLast! ∈ (hypermapOfList L hL).darts :=
    List.mem_toFinset.mpr (fList_mem_darts hL.1 hlastD)
  have hn1 : nList L (fList L p.getLast!)
      = (hypermapOfList L hL).nodeMap (fList L p.getLast!) :=
    (nodeMap_hypermapOfList L hL hw).symm
  have hnode : nList L (fList L p.getLast!) ∈ (hypermapOfList L hL).node
      (fList L p.getLast!) := by
    simp only [Kepler.Text.Hypermap.node, orbitMap, Set.mem_setOf_eq]
    exact ⟨1, by rw [hn1, pow_one]⟩
  have hnf : nList L (fList L p.getLast!) ∈ N.flatten :=
    hn.2.2.2.2 _ hfF hnode
  obtain ⟨r', hr'N, hd'r'⟩ := List.mem_flatten.mp hnf
  obtain ⟨hr1', hr2'⟩ := normalListUniqNonnil hn hr'N
  -- e_list d = n_list (f_list LAST p) ∈ r'
  have hde' : eList d = nList L (fList L p.getLast!) := by
    rw [hde, nList_fList hL.1 hlastD]
  have hd'r : eList d ∈ r' := hde' ▸ hd'r'
  have hd'fl : eList d ∈ (partsSpine L r').flatten := by
    rw [partsFlatten L hr1' hr2']; exact hd'r
  obtain ⟨p', hp', hd'p'⟩ := List.mem_flatten.mp hd'fl
  -- e_list d 必是 p' 的 LAST
  have h1 : eList d ≠ p'.getLast! → nextEl r' (eList d) = fList L p.getLast! := by
    intro hne
    have h11 := nextElPartsUnlast L hr1' hr2' hp' hd'p' hne
    have h12 := partsNextUnlast L hr1' hr2' p' hp' (eList d) hd'p' hne
    rw [la7_eList_involutory] at h12
    exact h11.trans (h12.trans (by rw [hde]))
  have hd'last : eList d = p'.getLast! := by
    by_contra hne
    have h1' := h1 hne
    have h2 : fList L p.getLast! ∈ r' := h1' ▸ nextEl_mem_of_mem hd'r
    have hrr : r = r' := by
      have e1 := findListUniq hn.1 hfR hrN
      have e2 := findListUniq hn.1 h2 hr'N
      exact e1.symm.trans e2
    subst hrr
    have h3 : nextEl r (eList d) = fList L p.getLast! := h1'
    have hlv : p.getLast! = eList d := by
      have hsame : nextEl r p.getLast! = nextEl r (eList d) :=
        (normalListPartsNextLast L hL hn hrN hp).trans h3.symm
      exact nextElInj hr1 hsame
    exact edgeNondegFXorNi hL hnedg hlastD
      ((congrArg (fList L) hlv).trans (congrArg (fun z => fList L (eList z)) hde))
  exact (memListOfDartsQuotient L hL hn hnedg hunL (eList d)).mpr
    ⟨p', r', hp', hr'N, hd'last⟩

/-- **HOL `good_list_quotient`**（tame_list.hl:7152-:7166）
`... ==> good_list (quotient_list L N)`——三合取项分别由
list_of_darts_quotient_uniq / quotient_all_nonnil / list_of_darts_quotient_sym。 -/
theorem goodListQuotient (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate) (hunL : ∀ l ∈ L, l.Nodup) :
    GoodList (quotientListSpine L N) :=
  ⟨listOfDartsQuotientUniq L hL hn hnedg hunL, fun l hl => quotientAllNonnil hL hn l hl,
    fun d hd => listOfDartsQuotientSym L hL hn hnedg hunL d hd⟩

/-! ### §3 is_node_going 块（tame_list.hl:7168-:7514） -/

/-- **HOL `is_node_going_refl`**（tame_list.hl:7168-:7178）
`!H L d. is_node_going H L d d`——k = 0 见证。 -/
theorem isNodeGoingRefl {α : Type*} [DecidableEq α] (Hh : Hypermap α) (lL : Loop α)
    (d : α) : Hh.IsNodeGoing lL d d :=
  ⟨0, rfl, fun i hi => by
    rw [show i = 0 from Nat.le_zero.mp hi]
    simp⟩

/-- **HOL `mem_f_list`**（tame_list.hl:7255-:7263）
`MEM d (list_of_darts L) ==> MEM (f_list L d) (list_of_darts L)`。 -/
theorem memFList (L : fgraph ℕ) {d : ℕ × ℕ} (hd : d ∈ listOfDarts L) :
    fList L d ∈ listOfDarts L :=
  mem_darts_of_mem_findFace L (nextEl_mem_of_mem (dart_in_face L d |>.mpr hd))

/-- **HOL `inverse_node_map_list_power`**（tame_list.hl:7265-:7284）
`good_list L /\ MEM d (list_of_darts L) ==>`
`(inverse (node_map (hypermap_of_list L)) POWER k) d = ((f_list L o e_list) POWER k) d`。 -/
theorem inverseNodeMapListPower (L : fgraph ℕ) (hL : GoodList L) (k : ℕ)
    {d : ℕ × ℕ} (hd : d ∈ listOfDarts L) :
    (((hypermapOfList L hL).nodeMap.symm ^ k) d)
      = ((fun z => fList L (eList z))^[k]) d := by
  induction k with
  | zero => rw [pow_zero, Equiv.Perm.one_apply, Function.iterate_zero_apply]
  | succ k ih =>
    have hmem : ((hypermapOfList L hL).nodeMap.symm ^ k) d
        ∈ (hypermapOfList L hL).darts :=
      (fstInvOrbit hL (List.mem_toFinset.mpr hd) k).2
    rw [pow_succ', Equiv.Perm.mul_apply,
      inverseNodeMapList hL (List.mem_toFinset.mp hmem), ih,
      Function.iterate_succ_apply']

/-- **HOL `next_el_parts_power`**（tame_list.hl:7286-:7322）
`uniq r /\ ~(r = []) /\ MEM x p /\ MEM p (parts L r) /\
  indexl x p + i < sizel p ==> (next_el r POWER i) x = (next_el p POWER i) x`。 -/
theorem nextElPartsPower (L : fgraph ℕ) {r : List (ℕ × ℕ)} (hun : r.Nodup)
    (hne : r ≠ []) {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r) {x : ℕ × ℕ}
    (hx : x ∈ p) (i : ℕ) (hlt : p.idxOf x + i < p.length) :
    (nextEl r)^[i] x = (nextEl p)^[i] x := by
  have hpun : p.Nodup := partsUniq L hun hne p hp
  have hpne : p ≠ [] := partsAllNonnil L hun hne p hp
  have hpos : 0 < p.length := List.length_pos_of_mem hx
  have hlast : p.idxOf p.getLast! = p.length - 1 := idxOfGetLast hpun hpne
  induction i with
  | zero => rfl
  | succ i ih =>
    have hilt : p.idxOf x + i < p.length := by omega
    have hIH := ih (by omega)
    have hxg : p[p.idxOf x]'(List.idxOf_lt_length_iff.mpr hx) = x := getElem_idxOf hx
    have hz : (nextEl p)^[i] x = p[p.idxOf x + i]'(by omega) := by
      have h1 := nextElIterateGetElem (s := p) hpun (j := p.idxOf x)
        (List.idxOf_lt_length_iff.mpr hx) i (Nat.mod_lt _ hpos)
      rw [hxg] at h1
      exact h1.trans (getElemCon (Nat.mod_lt _ hpos) (by omega)
        (Nat.mod_eq_of_lt hilt))
    have hzp : p[p.idxOf x + i]'(by omega) ∈ p := List.getElem_mem (by omega)
    have hznl : p[p.idxOf x + i]'(by omega) ≠ p.getLast! := by
      intro hc
      rw [hc] at hz
      have hzi : p.idxOf (p[p.idxOf x + i]'(by omega)) = p.idxOf x + i :=
        idxOf_getElem hpun (by omega)
      rw [hc] at hzi
      omega
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hIH, hz,
      nextElPartsUnlast L hun hne hp hzp hznl]

/-- **HOL `indexf_hd`**（tame_list.hl:7324-:7335）
`MEM d p ==> indexf (HD p) d p = indexl d p`。 -/
theorem indexfHd {p : List (ℕ × ℕ)} {d : ℕ × ℕ} (hd : d ∈ p) :
    indexf p.head! d p = p.idxOf d := by
  have hpne : p ≠ [] := List.ne_nil_of_mem hd
  have h0 : p.idxOf p.head! = 0 := indexHd0 hpne
  have hh : p.head! ∈ p := List.head!_mem_self hpne
  rw [indexfCond hh hd, h0, if_pos (Nat.zero_le (p.idxOf d))]
  omega

/-- **HOL `hd_eq_last`**（tame_list.hl:7337-:7349）
`~(x = []) /\\ uniq x /\\ HD x = LAST x ==> x = [HD x]`——cons 双层：
`LAST (a :: b :: t\') = LAST (b :: t\') ∈ b :: t\'`（getLast?_cons 折算），
与 `a ∉ b :: t\'` 矛盾。 -/
theorem hdEqLast {x : List (ℕ × ℕ)} (hne : x ≠ []) (hun : x.Nodup)
    (h : x.head! = x.getLast!) : x = [x.head!] := by
  cases x with
  | nil => exact absurd rfl hne
  | cons a t =>
    cases t with
    | nil => simp
    | cons b t' =>
      exfalso
      have hne2 : (b :: t') ≠ [] := by simp
      have hmemT : (b :: t').getLast! ∈ b :: t' := getLastMem hne2
      have hlastEq : (a :: b :: t').getLast! = (b :: t').getLast! := by
        rw [getLast!EqGetLast (by simp), List.getLast_cons hne2,
          getLast!EqGetLast hne2 |>.symm]
      rw [← hlastEq, h.symm] at hmemT
      exact (List.nodup_cons.mp hun).1 hmemT

/-- getD 中段定位：`(l ++ (p ++ c)).getD l.length default = p.head!`
（l 段长恰为偏移；getD 无证明分量，hfl 等表等式可自由穿入）。 -/
private theorem getDMidHead {α : Type*} [Inhabited α] {l p c : List α}
    (hp0 : 0 < p.length) :
    (l ++ (p ++ c)).getD l.length default = p.head! := by
  rw [List.getD_eq_getElem?_getD]
  have htot : l.length < (l ++ (p ++ c)).length := by
    rw [List.length_append, List.length_append]; omega
  rw [List.getElem?_eq_getElem htot, List.getElem_append_right (Nat.le_refl l.length)]
  have hz0 : l.length - l.length < (p ++ c).length := by
    rw [Nat.sub_self, List.length_append]
    have h2 := htot
    rw [List.length_append] at h2
    omega
  have hpc0 : 0 < (p ++ c).length := by
    rw [List.length_append]
    have h2 := htot
    rw [List.length_append] at h2
    omega
  rw [getElemConN hz0 hpc0 (Nat.sub_self l.length),
    List.getElem_append_left (as := p) (bs := c) (i := 0) hp0]
  cases p with
  | nil => exact absurd hp0 (by simp)
  | cons x t => rfl

/-- getD 中段定位（带下标）：`(l ++ (p ++ c)).getD (l.length + j) default = p[j]`。 -/
private theorem getDMidAt {α : Type*} [Inhabited α] {l p c : List α} {j : ℕ}
    (hj : j < p.length) :
    (l ++ (p ++ c)).getD (l.length + j) default = p[j]'hj := by
  rw [List.getD_eq_getElem?_getD]
  have htot : l.length + j < (l ++ (p ++ c)).length := by
    rw [List.length_append, List.length_append]; omega
  rw [List.getElem?_eq_getElem htot, List.getElem_append_right (Nat.le_add_right l.length j)]
  have hzj : l.length + j - l.length < (p ++ c).length := by
    rw [Nat.add_sub_cancel_left, List.length_append]
    have h2 := htot
    rw [List.length_append] at h2
    omega
  have hpcj : j < (p ++ c).length := by
    rw [List.length_append]
    have h2 := htot
    rw [List.length_append] at h2
    omega
  rw [getElemConN hzj hpcj (Nat.add_sub_cancel_left l.length j), Option.getD_some,
    List.getElem_append_left (as := p) (bs := c) (i := j) (h := hj) (h' := hpcj)]

/-- **HOL `indexl_flatten`**（tame_list.hl:7351-:7409）
`MEM d p /\\ MEM p r /\\ uniq (flatten r) /\\ all (\\l. ~(l = [])) r ==>
  indexl d p + indexl (HD p) (flatten r) = indexl d (flatten r)`
——cat_from 分解 + getD 中段定位（HD p 在第 len(front).flatten 项，
d 在其 + indexl d p 项；nodup 下标即位）。 -/
theorem indexlFlatten {d : ℕ × ℕ} {p : List (ℕ × ℕ)} {R : List (List (ℕ × ℕ))}
    (hd : d ∈ p) (hp : p ∈ R) (hun : R.flatten.Nodup) (hnn : ∀ q ∈ R, q ≠ []) :
    p.idxOf d + R.flatten.idxOf p.head! = R.flatten.idxOf d := by
  obtain ⟨a, b, hab⟩ := List.append_of_mem hp
  have hpne : p ≠ [] := hnn p hp
  have hpos : 0 < p.length := List.length_pos_of_ne_nil hpne
  have hfl : R.flatten = a.flatten ++ (p ++ b.flatten) := by
    rw [hab, List.flatten_append, List.flatten_cons]
  have hmem : ∀ z ∈ p, z ∈ R.flatten := fun z hz =>
    List.mem_flatten.mpr ⟨p, hp, hz⟩
  have hposH : a.flatten.length < R.flatten.length := by
    rw [hfl]
    simp only [List.length_append]
    omega
  have hj : p.idxOf d < p.length := List.idxOf_lt_length_iff.mpr hd
  have hposD : a.flatten.length + p.idxOf d < R.flatten.length := by
    rw [hfl]
    simp only [List.length_append]
    omega
  -- HD p = flatten R 的第 len(front).flatten 项（getD 形计算 + 取元回写）
  have hgetH : R.flatten[a.flatten.length]'hposH = p.head! := by
    have h1 : R.flatten.getD a.flatten.length default = p.head! := by
      rw [hfl, getDMidHead (l := a.flatten) (c := b.flatten) hpos]
    rw [← getD_eq_getElem_of_lt hposH default]
    exact h1
  have hidxH : R.flatten.idxOf p.head! = a.flatten.length := by
    have h9 := idxOf_getElem hun hposH
    rw [hgetH] at h9
    exact h9
  -- d = flatten R 的第 len(front).flatten + indexl d p 项
  have hgetD : R.flatten[a.flatten.length + p.idxOf d]'hposD = d := by
    have h1 : R.flatten.getD (a.flatten.length + p.idxOf d) default = d := by
      rw [hfl, getDMidAt (l := a.flatten) (c := b.flatten) hj]
      exact getElem_idxOf hd
    rw [← getD_eq_getElem_of_lt hposD default]
    exact h1
  have hidxD : R.flatten.idxOf d = a.flatten.length + p.idxOf d := by
    have h9 := idxOf_getElem hun hposD
    rw [hgetD] at h9
    exact h9
  omega

/-- **HOL `indexf_flatten`**（tame_list.hl:7411-:7433）
`MEM d1 p /\ MEM d2 p /\ indexl d1 p <= indexl d2 p /\ MEM p par /\
  uniq (flatten par) /\ all (\l. ~(l = [])) par ==>
  indexf d1 d2 p = indexf d1 d2 (flatten par)`
（hle 排除回卷支，两支同号相减。） -/
theorem indexfFlatten {par : List (List (ℕ × ℕ))} {p : List (ℕ × ℕ)}
    {d1 d2 : ℕ × ℕ} (hd1 : d1 ∈ p) (hd2 : d2 ∈ p) (hle : p.idxOf d1 ≤ p.idxOf d2)
    (hp : p ∈ par) (hun : par.flatten.Nodup) (hnn : ∀ q ∈ par, q ≠ []) :
    indexf d1 d2 p = indexf d1 d2 par.flatten := by
  have h1 := indexlFlatten hd1 hp hun hnn
  have h2 := indexlFlatten hd2 hp hun hnn
  have hm1 : d1 ∈ par.flatten := List.mem_flatten.mpr ⟨p, hp, hd1⟩
  have hm2 : d2 ∈ par.flatten := List.mem_flatten.mpr ⟨p, hp, hd2⟩
  rw [indexfCond hd1 hd2, indexfCond hm1 hm2, if_pos hle, if_pos (by omega)]
  omega

/-- **HOL `is_node_going_last1`**（tame_list.hl:7224-:7253）
`good_list L /\\ normal_list L N /\\ is_edge_nondegenerate (hypermap_of_list L) /\\
  all uniq L /\\ MEM p (parts L r) /\\ MEM r N ==>`
`(is_node_going (hypermap_of_list L) (loop_of_list r) (LAST p) d <=> d = LAST p)`
——←：k = 0 即 refl；k ≥ 1 取 i = 1 步，loop_map = next_el r 与
node_map.symm = f_list o e_list 结合 normal_list_parts_next_last_not 矛盾。 -/
theorem isNodeGoingLast1 (L : fgraph ℕ) (hL : GoodList L) {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N) (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup) {r : List (ℕ × ℕ)} (hr : r ∈ N)
    {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r) (d : ℕ × ℕ) :
    (hypermapOfList L hL).IsNodeGoing (loopOfListSpine r) p.getLast! d ↔ d = p.getLast! := by
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  have hpne : p ≠ [] := partsAllNonnil L hr1 hr2 p hp
  have hlastD : p.getLast! ∈ listOfDarts L := partsDarts L hn hr hp (getLastMem hpne)
  constructor
  · rintro ⟨k, hk, hgo⟩
    by_cases hk0 : k = 0
    · rw [hk0, pow_zero] at hk
      exact hk
    · exfalso
      have h1 := hgo 1 (by omega)
      rw [pow_one, pow_one, loopMapNextEl hr1 hr2, inverseNodeMapList hL hlastD] at h1
      exact normalListPartsNextLastNot L hL hn hnedg hr hp h1
  · rintro rfl
    exact isNodeGoingRefl _ _ _

/-- **HOL `is_node_going_last2_lemma`**（tame_list.hl:7435-:7513）
`good_list L /\\ normal_list L N /\\ is_edge_nondegenerate (hypermap_of_list L) /\\
  all uniq L /\\ MEM p (parts L r) /\\ MEM r N /\\ MEM d p ==>`
`is_node_going (hypermap_of_list L) (loop_of_list r) d (LAST p)`
——k = indexf d (LAST p) r（indexf_flatten 折算到 p 内 = len p - 1 - indexl d p）；
沿途每步 next_el r z = node_map.symm z = f_list (e_list z) = next_el p z
（z = EL (i + indexl d p) p，i < k 时非 LAST，parts_next_unlast + parts_node_inverse_power）。 -/
theorem isNodeGoingLast2Lemma (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate) (hunL : ∀ l ∈ L, l.Nodup)
    {r : List (ℕ × ℕ)} (hr : r ∈ N) {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r)
    {d : ℕ × ℕ} (hd : d ∈ p) :
    (hypermapOfList L hL).IsNodeGoing (loopOfListSpine r) d p.getLast! := by
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  have hpun : p.Nodup := partsUniq L hr1 hr2 p hp
  have hpne : p ≠ [] := partsAllNonnil L hr1 hr2 p hp
  have hpos : 0 < p.length := List.length_pos_of_ne_nil hpne
  have hlast : p.idxOf p.getLast! = p.length - 1 := idxOfGetLast hpun hpne
  have hx0 : p.idxOf d < p.length := List.idxOf_lt_length_iff.mpr hd
  have hleLast : p.idxOf d ≤ p.idxOf p.getLast! := by omega
  have hdR : d ∈ r := (partsUniqNonnil L hL hn hr hp).2.2.2.2 d hd
  have hlastR : p.getLast! ∈ r :=
    (partsUniqNonnil L hL hn hr hp).2.2.2.2 p.getLast! (getLastMem hpne)
  -- indexf d (LAST p) r = indexf d (LAST p) p = len p - 1 - indexl d p
  have hpartsNodup : ((partsSpine L r).flatten).Nodup := by
    rw [partsFlatten L hr1 hr2]; exact hr1
  have hpartsNonnil : ∀ q ∈ partsSpine L r, q ≠ [] := partsAllNonnil L hr1 hr2
  have hIdxEq : indexf d p.getLast! r = indexf d p.getLast! p := by
    have h9 := indexfFlatten hd (getLastMem hpne) hleLast hp hpartsNodup hpartsNonnil
    rw [partsFlatten L hr1 hr2] at h9
    exact h9.symm
  have hIdxP : indexf d p.getLast! p = p.length - 1 - p.idxOf d := by
    rw [indexfCond hd (getLastMem hpne), if_pos hleLast, hlast]
  -- loop_map 幂的 next_el 表示（Perm 幂形）
  have hloopIter : ∀ (j : ℕ) (z : ℕ × ℕ),
      ((loopOfListSpine r).map ^ j) z = (nextEl r)^[j] z := by
    intro j
    induction j with
    | zero => intro z; simp
    | succ m ih =>
      intro z
      rw [pow_succ', Equiv.Perm.mul_apply, ih, loopMapNextEl hr1 hr2,
        Function.iterate_succ_apply']
  have hgo : ∀ i : ℕ, i ≤ indexf d p.getLast! r →
      ((loopOfListSpine r).map ^ i) d
        = (((hypermapOfList L hL).nodeMap.symm) ^ i) d := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ m ih =>
      intro him
      have hgoM := ih (Nat.le_trans (Nat.le_succ m) him)
      have hmlt : m + p.idxOf d < p.length := by omega
      have hz := partsNodeInversePower L hL hn hr hp m hd hmlt
      have hzmem : p[m + p.idxOf d]'(by omega) ∈ p := List.getElem_mem (by omega)
      have hzidx : p.idxOf (p[m + p.idxOf d]'(by omega)) = m + p.idxOf d :=
        idxOf_getElem hpun (by omega)
      have hznl : p[m + p.idxOf d]'(by omega) ≠ p.getLast! := by
        intro hc
        rw [hc] at hzidx
        omega
      have hDd : d ∈ listOfDarts L := partsDarts L hn hr hp hd
      have hzL : p[m + p.idxOf d]'(by omega) ∈ listOfDarts L :=
        hz ▸ List.mem_toFinset.mp (fstInvOrbit hL (List.mem_toFinset.mpr hDd) m).2
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply, hgoM,
        loopMapNextEl hr1 hr2, hz, inverseNodeMapList hL hzL,
        ← partsNextUnlast L hr1 hr2 p hp (p[m + p.idxOf d]'(by omega)) hzmem hznl,
        nextElPartsUnlast L hr1 hr2 hp (x := p[m + p.idxOf d]'(by omega)) hzmem hznl]
  refine ⟨indexf d p.getLast! r, ?_, hgo⟩
  · rw [hloopIter]
    exact (indexfN hdR hlastR hr1).symm

end Kepler.Text.TameSpine

