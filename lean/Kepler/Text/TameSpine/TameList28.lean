/-
  Kepler.Text.TameSpine.TameList28 — B1 Tame_list 地基批 28：loop_of_list
  回路段（tamespine-port-plan §4 批次表 B1 行；接续批 27 = TameList26.lean→
  TameList27.lean，批 27 终点 = HOL :11087（pathOfLoopInj 已落）；本批起点
  = HOL :11089 `loop_of_list_path_of_loop`。行号均按主仓
  reference/flyspeck（commit 1ce0353）实测）。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:11089-:11195）——
  loop_of_list 回路段四件全落，本批零止损、零顺延（批 27 处方预记的
  「rot 一般 k 递推成本超预算可按 :11158 先行收口」未触发：next_el_rot_eq
  的一般 k 面经 getElem? 无证桥+下标模运输收口，成本在预算内）：

  主件 1：`loop_of_list_path_of_loop` :11089-:11128
  `!l d n. d IN (dart_of_loop l) /\ CARD (dart_of_loop l) = n ==>
  loop_of_list (MAP (path_of_loop l d) (iota 0 n)) = l`。

  主件 2：`loop_of_list_surj` :11130-:11158
  `!l d. d IN dart_of_loop l ==> ?r. l = loop_of_list r /\
  sizel r = CARD (dart_of_loop l) /\ uniq r /\ ~(r = []) /\ HD r = d`。

  主件 3：`loop_of_list_rot` :11160-:11169
  `!r k. uniq r ==> loop_of_list (rot k r) = loop_of_list r`。

  主件 4：`loop_of_list_surj2` :11171-:11195
  `!l d. d IN dart_of_loop l ==> ?r. loop_of_list r = l /\
  CARD (dart_of_loop l) = sizel r /\ uniq r /\ ~(r = []) /\ LAST r = d`。

  定义面侦察定论（本批零新落 def——全部载体在库，逐槽记档）：
  · `rot`（seq2 左旋）↦ Mathlib `List.rotate`（Data/List/Rotate.lean）：
    `(l.rotate n)[k] = l[(k + n) % l.length]`（`getElem_rotate`）与 HOL
    `nth_rot` 同形，左旋语义一致；`set_of_list_rot` ↦ `List.mem_rotate`
    （成员集不变）、`size_rot` ↦ `List.length_rotate`、`rot_uniq` ↦
    `List.nodup_rotate`、`rot_oversize`/nil 面 ↦ `List.rotate_eq_nil_iff`；
  · `next_el_rot_eq`（seq2.vhl:1353 `uniq s ==> next_el (rot n s) =
    next_el s`）↦ 本批 §0 私件 `nextElRotate`（一般 k）。在库仅 rotOne
    特形（`la7_idxOf_rotOne`/`_shift`，TameLp:4168/:4189），一般 k 的
    idxOf-rotate 闭式不在库——本批不走 idxOf 闭式：由「rotate 后取元
    下标平移」的 `getElem?_rotate` 无证桥 + `nodup_getElem_inj` 下标单射
    直接得 `((rotate.idxOf x) + k) % length = idxOf x`，再经
    `Nat.mod_add_mod` 平移 +1 即闭，零 idxOf 递推；
  · `nth_shift_left`（seq2.vhl:1145，`nth x0 (rot 1 s) i =
    if i = sizel s - 1 then nth x0 s 0 else nth x0 s (i + 1)`）——本批
    LAST 面不镜像其逐点分支：`getLast?_eq_getElem?` + `getElem?_rotate`
    闭式一步给 `last (rot 1 r) = r[0]`（HOL 的 take/drop 分支被
    `(k + 1) % length` 模运算吸收），`LAST_EL`/`LAST` ↦
    `List.getLast!_eq_getLast?_getD` + `List.getLast?_eq_getElem?`
    （批 9 getLast!EqGet 同链）；
  · `Seq2.card_set_of_list_uniq` ↦ Mathlib `List.toFinset_card_of_nodup`
    （`#l.toFinset = l.length`）；`set_of_list` ↦ `List.toFinset`；
  · `dart_of_loop_of_list`（Finset 等式消费面）↦ 批 6 `dartLoopOfList`
    （Set 形）经 `Finset.coe_inj` + `List.coe_toFinset` 折算 Finset
    等式（批 27 头注预记路线）；成员面 ↦ 批 6 `inDartLoopOfList`；
  · `CARD_EQ_0`（dart_of_loop 非空 ⟹ CARD ≠ 0）↦ 在库
    `Loop.card_pos.2.1`（`0 < L.card`）+ omega；
  · `HD_MAP`+`hd_iota`+`POWER_0`（HD (MAP (path_of_loop l d) iota) = d）
    ↦ 本批 §0 私件 `headDRange'MapPathOf`——`List.head!_map` 不在库，
    由 `List.range'_succ` + `head!_cons`（rfl 面）+ `Loop.pathOf` 零次幂
    直接闭（`simp [Loop.pathOf]`）；
  · `MAP_EQ_NIL` ↦ length 桥 + omega；`Seq.size_map`/`size_iota` ↦
    `List.length_map` + `List.length_range'`（批 19 记账 iota j n ↦
    List.range' j n）。

  证明层侦察定论：
  · 主件 1（:11089）HOL 证体：path_of_loop_inj 例示（证人 d、n）+
    CARD_EQ_0 + uniq（path_of_loop_uniq）+ MAP_EQ_NIL + HD_MAP +
    darts 相等（dart_of_loop_of_list 双侧 + iota 0 元 + POWER_0）+
    card_set_of_list_uniq。Lean 面：批 27 `pathOfLoopInj` 五槽直接装配
    ——darts 槽 `inDartLoopOfList` + `mem_range'` + pathOf 零次幂；
    card 槽 `dartLoopOfList` 的 Finset 折算 + `toFinset_card_of_nodup`；
    map 槽批 27 `pathOfLoopOfList`。零 Meson。
  · 主件 2（:11130）= 主件 1 的存在化：证人
    `(range' 0 L.card).map (L.pathOf d)`，五合取逐槽收口（HOL 的
    ASM_SIMP 链被批 27 三件与 §0 私件吸收）。
  · 主件 3（:11160）HOL 证体：展开 loop_of_list 后 set_of_list_rot +
    next_el_rot_eq。Lean 面：`Loop.ext`（darts 槽 = `toFinset` 相等经
    `mem_rotate`；map 槽 = `loopMapNextEl` 双例示 + §0 `nextElRotate`）。
    空表支 `List.rotate_nil` + `loopOfListSpine` junk 分支 rfl。
  · 主件 4（:11171）HOL 证体：loop_of_list_surj 回用 + 证人 rot 1 r +
    nth_shift_left 的 LAST 特形 + loop_of_list_rot 收口。Lean 面：
    `loopOfListSurj` 例示 + 证人 `r.rotate 1`（`length_rotate`/
    `nodup_rotate`/`rotate_eq_nil_iff`）+ getLast! 链（§0 记档）+
    主件 3。

  依赖面（全为在案真件，零新增债）：批 27
  pathOfLoopOfList/pathOfLoopUniq/pathOfLoopInj + 批 6
  loopOfListSpine/loopMapNextEl/dartLoopOfList/inDartLoopOfList +
  TameLp nextEl_eq_getD/getD_eq_getElem_of_lt/idxOf_getElem/
  nodup_getElem_inj + 在库 Loop card/card_pos/ext + Mathlib
  mem_rotate/nodup_rotate/length_rotate/rotate_nil/
  rotate_eq_nil_iff/getElem_rotate/getElem?_rotate/getElem?_idxOf/
  idxOf_eq_length/idxOf_lt_length_iff/length_pos_of_mem/
  length_pos_of_ne_nil/getD_eq_getElem?_getD/getElem?_eq_getElem/
  getLast!_eq_getLast?_getD/getLast?_eq_getElem?/range'_succ/
  length_range'/length_map/mem_range'/toFinset_card_of_nodup/
  coe_toFinset/Finset.coe_inj + core Nat.mod_add_mod/mod_lt/
  add_sub_cancel/mod_self。import 边：本模块 import TameList27（链式
  带全批 1-26 与 GoodGraph），零新增库依赖。

  诚实记账：本批四主件全部真证，零新 def、零止损件、零记账债。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git
  写操作。批 29 接续点：HOL :11197 `DIH2K_IMP_PRE_SIMPLE_HYP2` 起
  dih2k 蕴含段。段终墙侦察：:11197-:11203 语句
  `!H k x. dih2k H k /\ ~(k=0) /\ x IN dart H ==> ~(node_map H x IN
  face H x)`，HOL 证体单行 MESON（Hypermap.node_map_and_darts +
  Wrgcvdr_cizmrrh.DIH2K_IMP_PRE_SIMPLE_HYP 两件装配）——Lean 面
  侦察预记：`Wrgcvdr_cizmrrh.DIH2K_IMP_PRE_SIMPLE_HYP` 系跨文件依赖
  （wrgcvdr_cizmrrh 模块面），落地前须查在库是否已有对应真件；
  `node_map_and_darts`（hypermap.hl）↦ 在库 node/face 载体面（批 7
  isNormalLoopList 段已消费 mem_darts_of_isNormalFamily 一族）；其后
  :11207 `set_of_list_pairs_set_of_list = 0` 系定义桩（非定理），批 29
  起点实际主件 = :11209 `quotient_bij_face_set`。
-/

import Kepler.Text.TameSpine.TameList27

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl)
open Kepler.Text.TameLp (nextEl_eq_getD getD_eq_getElem_of_lt idxOf_getElem
  nodup_getElem_inj)

/-! ### §0 私件引擎 -/

/-- HD (MAP (path_of_loop l d) (iota 0 n)) = d 面（HOL `HD_MAP`+`hd_iota`+
`POWER_0` 合流）：`head!_map` 不在库，由 `range'_succ` + `head!_cons` +
`Loop.pathOf` 零次幂直接闭。 -/
private theorem headDRange'MapPathOf {L : Loop (ℕ × ℕ)} {d : ℕ × ℕ} {n : ℕ}
    (hn0 : n ≠ 0) : ((List.range' 0 n).map (L.pathOf d)).head! = d := by
  cases n with
  | zero => exact absurd rfl hn0
  | succ m =>
    rw [List.range'_succ]
    simp [Loop.pathOf]

/-- **HOL `Seq2.next_el_rot_eq`**（seq2.vhl:1353）一般 k 面：
`uniq s ==> next_el (rot n s) = next_el s`。在库仅 rotOne 特形
（`la7_idxOf_rotOne`，TameLp:4168），一般 k 不走 idxOf 闭式：取元下标
经 `getElem?_rotate` 无证桥 + `nodup_getElem_inj` 单射得
`(idxOf x (rotate k l) + k) % length = idxOf x l`，`Nat.mod_add_mod`
平移 +1 收口。 -/
private theorem nextElRotate {l : List (ℕ × ℕ)} (hn : l.Nodup) (k : ℕ)
    (x : ℕ × ℕ) : nextEl (l.rotate k) x = nextEl l x := by
  by_cases hx : x ∈ l
  · have hrot : x ∈ l.rotate k := List.mem_rotate.mpr hx
    have hlen : (l.rotate k).length = l.length := List.length_rotate l k
    have hpos : 0 < l.length := List.length_pos_of_mem hx
    have hpos' : 0 < (l.rotate k).length := by omega
    have hjlt : (l.rotate k).idxOf x < (l.rotate k).length :=
      List.idxOf_lt_length_iff.mpr hrot
    have hjlt' : (l.rotate k).idxOf x < l.length := by omega
    have hilt : l.idxOf x < l.length := List.idxOf_lt_length_iff.mpr hx
    -- rotate 后 x 的下标平移：(idxOf x (rotate k l) + k) % len = idxOf x l
    have hik : ((l.rotate k).idxOf x + k) % l.length = l.idxOf x := by
      have hopt : l[((l.rotate k).idxOf x + k) % l.length]? = l[l.idxOf x]? := by
        rw [List.getElem?_idxOf hx, ← List.getElem?_idxOf hrot,
          List.getElem?_rotate hjlt']
      refine nodup_getElem_inj hn (Nat.mod_lt _ hpos) hilt ?_
      exact Option.some.inj ((List.getElem?_eq_getElem (Nat.mod_lt _ hpos)).symm.trans
        (hopt.trans (List.getElem?_eq_getElem hilt)))
    have hmod : (((l.rotate k).idxOf x + 1) % l.length + k) % l.length
        = (l.idxOf x + 1) % l.length := by
      rw [Nat.mod_add_mod, show (l.rotate k).idxOf x + 1 + k
          = (l.rotate k).idxOf x + k + 1 from by omega,
        ← Nat.mod_add_mod ((l.rotate k).idxOf x + k) l.length 1, hik]
    rw [nextEl_eq_getD hrot, nextEl_eq_getD hx, hlen,
      List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_rotate (Nat.mod_lt _ hpos), hmod]
  · -- 表外 junk 恒等支（批 9 nextElOfNotMem 同证，private 不跨文件重落）
    have h1 : x ∉ l.rotate k := fun hmem => hx (List.mem_rotate.mp hmem)
    cases l with
    | nil => rfl
    | cons a t =>
      have hrl : ((a :: t).rotate k).length = t.length + 1 := by
        rw [List.length_rotate, List.length_cons]
      show (if ((a :: t).rotate k).idxOf x = ((a :: t).rotate k).length - 1
          then ((a :: t).rotate k).headD x
          else ((a :: t).rotate k).getD (((a :: t).rotate k).idxOf x + 1) x)
        = (if (a :: t).idxOf x = (a :: t).length - 1 then (a :: t).headD x
          else (a :: t).getD ((a :: t).idxOf x + 1) x)
      rw [List.idxOf_eq_length h1, List.idxOf_eq_length hx,
        if_neg (by rw [hrl]; omega : ¬(((a :: t).rotate k).length
          = ((a :: t).rotate k).length - 1)),
        if_neg (by simp only [List.length_cons]; omega :
          ¬((a :: t).length = (a :: t).length - 1)),
        List.getD_eq_default _ _ (by rw [hrl]; omega),
        List.getD_eq_default _ _ (by simp only [List.length_cons]; omega)]

/-! ### §1 loop_of_list_path_of_loop（tame_list.hl:11089-:11128） -/

/-- **HOL `loop_of_list_path_of_loop`**（tame_list.hl:11089-:11128）
`!l d n. d IN (dart_of_loop l) /\ CARD (dart_of_loop l) = n ==>
loop_of_list (MAP (path_of_loop l d) (iota 0 n)) = l`——路径定环的存在化
前站：批 27 `pathOfLoopInj` 例示（证人 d、n），darts 槽
`inDartLoopOfList` + `mem_range'` + pathOf 零次幂，card 槽
`dartLoopOfList` 的 Finset 折算（`Finset.coe_inj` + `List.coe_toFinset`）
+ `toFinset_card_of_nodup`，map 槽批 27 `pathOfLoopOfList`。 -/
theorem loopOfListPathOfLoopOfList {L : Loop (ℕ × ℕ)} {d : ℕ × ℕ} {n : ℕ}
    (hd : d ∈ L.darts) (hc : L.card = n) :
    loopOfListSpine ((List.range' 0 n).map (L.pathOf d)) = L := by
  have hpos : 0 < L.card := L.card_pos.2.1
  have hn0 : n ≠ 0 := by omega
  have hu : ((List.range' 0 n).map (L.pathOf d)).Nodup := pathOfLoopUniq hd hc
  have hlen : ((List.range' 0 n).map (L.pathOf d)).length = n := by
    rw [List.length_map, List.length_range']
  have hne : (List.range' 0 n).map (L.pathOf d) ≠ [] := by
    intro he
    have h0 : ((List.range' 0 n).map (L.pathOf d)).length = 0 := by
      rw [he]; rfl
    omega
  have hhd : d = ((List.range' 0 n).map (L.pathOf d)).head! :=
    (headDRange'MapPathOf hn0).symm
  refine pathOfLoopInj ?_ hc ?_ hd ?_
  · show (loopOfListSpine ((List.range' 0 n).map (L.pathOf d))).darts.card
      = L.card
    have hfin : (loopOfListSpine ((List.range' 0 n).map (L.pathOf d))).darts
        = ((List.range' 0 n).map (L.pathOf d)).toFinset :=
      Finset.coe_inj.mp ((dartLoopOfList hu hne).trans
        (List.coe_toFinset _).symm)
    rw [hfin, List.toFinset_card_of_nodup hu, hlen, hc]
  · rw [inDartLoopOfList hu hne]
    refine List.mem_map.mpr ⟨0,
      List.mem_range'.mpr ⟨0, Nat.pos_of_ne_zero hn0, by omega⟩, ?_⟩
    simp [Loop.pathOf]
  · have h1 : (List.range' 0
        ((List.range' 0 n).map (L.pathOf d)).length).map
        ((loopOfListSpine ((List.range' 0 n).map (L.pathOf d))).pathOf d)
        = (List.range' 0 n).map (L.pathOf d) := pathOfLoopOfList hhd hu hne
    rw [hlen] at h1
    exact h1

/-! ### §2 loop_of_list_surj（tame_list.hl:11130-:11158） -/

/-- **HOL `loop_of_list_surj`**（tame_list.hl:11130-:11158）
`!l d. d IN dart_of_loop l ==> ?r. l = loop_of_list r /\
sizel r = CARD (dart_of_loop l) /\ uniq r /\ ~(r = []) /\ HD r = d`——
环表表示的存在化：证人 = 轨道枚举 `(range' 0 L.card).map (L.pathOf d)`，
五合取由主件 1 + 批 27 两件 + §0 私件逐槽收口。 -/
theorem loopOfListSurj {L : Loop (ℕ × ℕ)} {d : ℕ × ℕ} (hd : d ∈ L.darts) :
    ∃ r : List (ℕ × ℕ), L = loopOfListSpine r ∧ r.length = L.card
      ∧ r.Nodup ∧ r ≠ [] ∧ r.head! = d := by
  have hpos : 0 < L.card := L.card_pos.2.1
  refine ⟨(List.range' 0 L.card).map (L.pathOf d), ?_, ?_, ?_, ?_, ?_⟩
  · exact (loopOfListPathOfLoopOfList hd rfl).symm
  · rw [List.length_map, List.length_range']
  · exact pathOfLoopUniq hd rfl
  · intro he
    have h0 : ((List.range' 0 L.card).map (L.pathOf d)).length = 0 := by
      rw [he, List.length_nil]
    have h1 : ((List.range' 0 L.card).map (L.pathOf d)).length = L.card := by
      rw [List.length_map, List.length_range']
    omega
  · exact headDRange'MapPathOf (by omega)

/-! ### §3 loop_of_list_rot（tame_list.hl:11160-:11169） -/

/-- **HOL `loop_of_list_rot`**（tame_list.hl:11160-:11169）
`!r k. uniq r ==> loop_of_list (rot k r) = loop_of_list r`——环表旋转
不变量：`Loop.ext` 装配，darts 槽 = `toFinset` 相等经 `mem_rotate`，
map 槽 = `loopMapNextEl` 双例示 + §0 `nextElRotate`（HOL
next_el_rot_eq 面）。空表支 junk 分支 rfl（HOL 的 set_of_list_rot 被
mem_rotate 吸收）。 -/
theorem loopOfListRot {r : List (ℕ × ℕ)} (hu : r.Nodup) (k : ℕ) :
    loopOfListSpine (r.rotate k) = loopOfListSpine r := by
  rcases r with _ | ⟨a, t⟩
  · rfl
  · have hne : a :: t ≠ [] := by simp
    have hne' : (a :: t).rotate k ≠ [] :=
      fun h => hne (List.rotate_eq_nil_iff.mp h)
    have hu' : ((a :: t).rotate k).Nodup := List.nodup_rotate.mpr hu
    refine Loop.ext ?_ ?_
    · have h1 : (↑(loopOfListSpine ((a :: t).rotate k)).darts : Set (ℕ × ℕ))
          = ((a :: t).rotate k).toFinset :=
        (dartLoopOfList hu' hne').trans (List.coe_toFinset _).symm
      have h2 : (↑(loopOfListSpine (a :: t)).darts : Set (ℕ × ℕ))
          = (a :: t).toFinset :=
        (dartLoopOfList hu hne).trans (List.coe_toFinset _).symm
      have hset : (((a :: t).rotate k).toFinset : Set (ℕ × ℕ))
          = ((a :: t).toFinset : Set (ℕ × ℕ)) := by
        ext x
        simp only [Finset.mem_coe, List.mem_toFinset, List.mem_rotate]
      exact Finset.coe_inj.mp ((h1.trans hset).trans h2.symm)
    · refine Equiv.Perm.ext fun x => ?_
      rw [loopMapNextEl hu' hne' x, loopMapNextEl hu hne x]
      exact nextElRotate hu k x

/-! ### §4 loop_of_list_surj2（tame_list.hl:11171-:11195） -/

/-- **HOL `loop_of_list_surj2`**（tame_list.hl:11171-:11195）
`!l d. d IN dart_of_loop l ==> ?r. loop_of_list r = l /\
CARD (dart_of_loop l) = sizel r /\ uniq r /\ ~(r = []) /\ LAST r = d`——
环表表示的存在化（LAST 形）：`loopOfListSurj` 例示 + 证人 `r.rotate 1`
（HOL rot 1 r），LAST (rot 1 r) = HD r = d 面由 `getLast?_eq_getElem?` +
`getElem?_rotate` 闭式一步（HOL nth_shift_left 的 take/drop 分支被模
运算吸收），尾合取主件 3 收口。 -/
theorem loopOfListSurj2 {L : Loop (ℕ × ℕ)} {d : ℕ × ℕ} (hd : d ∈ L.darts) :
    ∃ r : List (ℕ × ℕ), loopOfListSpine r = L ∧ L.card = r.length
      ∧ r.Nodup ∧ r ≠ [] ∧ r.getLast! = d := by
  obtain ⟨r, heq, hlen, hu, hne, hhead⟩ := loopOfListSurj hd
  have hpos : 0 < r.length := List.length_pos_of_ne_nil hne
  refine ⟨r.rotate 1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [loopOfListRot hu 1, heq]
  · rw [List.length_rotate]
    exact hlen.symm
  · exact List.nodup_rotate.mpr hu
  · exact fun h => hne (List.rotate_eq_nil_iff.mp h)
  · -- LAST (rot 1 r) = HD r = d（HOL nth_shift_left 特形 + LAST_EL 面）
    have hrl : (r.rotate 1).length = r.length := List.length_rotate r 1
    have h0d : r[0] = d := by
      rcases r with _ | ⟨a, t⟩
      · exact absurd rfl hne
      · simpa using hhead
    rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?, hrl,
      List.getElem?_rotate (by omega : r.length - 1 < r.length),
      Nat.sub_add_cancel (by omega : 1 ≤ r.length), Nat.mod_self,
      List.getElem?_eq_getElem hpos, h0d]
    simp

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；四主件预期标准三
[propext, Classical.choice, Quot.sound]）：
#print axioms Kepler.Text.TameSpine.loopOfListPathOfLoopOfList
#print axioms Kepler.Text.TameSpine.loopOfListSurj
#print axioms Kepler.Text.TameSpine.loopOfListRot
#print axioms Kepler.Text.TameSpine.loopOfListSurj2
-/
