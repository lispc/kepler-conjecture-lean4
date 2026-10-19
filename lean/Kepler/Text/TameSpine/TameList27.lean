/-
  Kepler.Text.TameSpine.TameList27 — B1 Tame_list 地基批 27：path 章前半
  （tamespine-port-plan §4 批次表 B1 行；接续批 26 = TameList25.lean→
  TameList26.lean，批 26 终点 = HOL :10929（isNormalNodal 已落）；本批起点
  = HOL :10930 `path_of_loop_of_list`。行号均按主仓 reference/flyspeck
  （commit 1ce0353）实测——批 26 所记 AFP 版 +3/+14 偏移系批 26 任务面
  所给行号之事，本批锚点全为主仓实测行号）。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:10930-:11087）——path 章
  前半（path_of_loop 抽象理论段）三件全落，本批零止损：

  主件 1：`path_of_loop_of_list` :10930-:10963
  `!r d. d = HD r /\ uniq r /\ ~(r = []) ==> MAP (path_of_loop (loop_of_list r)
  d) (iota 0 (sizel r)) = r`。

  主件 2：`path_of_loop_uniq` :10965-:11007
  `!l d n. CARD (dart_of_loop l) = n /\ d IN dart_of_loop l ==>
  uniq (MAP (path_of_loop l d) (iota 0 n))`。

  主件 3：`path_of_loop_inj` :11009-:11087
  `!l l' d n. CARD (dart_of_loop l) = CARD (dart_of_loop l') /\
  CARD (dart_of_loop l') = n /\ d IN dart_of_loop l /\ d IN dart_of_loop l' /\
  MAP (path_of_loop l d) (iota 0 n) = MAP (path_of_loop l' d) (iota 0 n) ==>
  l = l'`。

  定义面侦察定论（本批零新落 def——全部载体在库，逐槽记档）：
  · `path_of_loop`（hypermap.hl:6730）↦ 在库 `Loop.pathOf`
    （Hypermap.lean:5738，`(L.map ^ k) x`，POWER ↦ Perm 幂）；
  · `iota 0 (sizel r)` ↦ `List.range' 0 r.length`（批 19 记账：`iota j n ↦
    List.range' j n`）；`sizel` ↦ `List.length`；`uniq` ↦ `List.Nodup`；
    `HD` ↦ `List.head!`（批 11 记账）；`EL` ↦ getElem；
  · `next_el`（ssreflect/seq2-compiled.hl:24）↦ Assembly `nextEl`；
    逐点化后 `next_el POWER k` = `(nextEl r)^[k]`（Function.iterate）——
    批 6 `loopMapNextEl`（TameList6.lean:348）给出
    `(loopOfListSpine r).map x = nextEl r x` 逐点桥，Perm 幂面经
    `pow_succ` + `Equiv.Perm.mul_apply` 归纳搬运；
  · `Seq2.next_el_power`（seq2-compiled.hl:1818-:2026）轨道公式 head 起步
    形 = 本批 §0 私件 `nextElIterateHeadD`——批 6 同语义私件
    `nextElIterateGetD`（TameList6.lean:174，x ∈ s 一般起点 getD 形）
    private 不跨文件，沿批 19 List ℕ 面先例同体重落（(ℕ×ℕ) 面）；
  · `is_inj_list` ↦ 在库 `Loop.IsInjList`（Hypermap.lean:5981）；
    `Seq2.uniq_nthP`（seq2.vhl:280）↦ Mathlib
    `List.nodup_iff_injective_getElem`（Fin-getElem 单射形）；
  · `lemma_inj_path_of_loop`（hypermap.hl:6964）↦ 在库
    `Loop.injOrbit_iff_le_preCard`（Hypermap.lean:5929）+
    `injOrbit_iff_pairwise`（:2282）；
  · `lemma_loop_identity`（hypermap.hl:6754）↦ 在库 `Loop.ext`
    （Hypermap.lean:8302）；`lemma_dart_loop_via_path`（:7217）↦
    `Loop.darts_eq_pathSupport_pathOf`（:6141，Finset 等式形——HOL
    support_of_sequence/MEM_EXTENSION 面由在库 `Loop.pathSupport`/
    `mem_pathSupport`（:5985/:5990）承载）；`map_permutes_outside_domain`
    （hypermap.hl:4902）↦ `Loop.map_permutes`（PermutesOn 定义含 dart 外
    恒等支）；`lemma_order_loop_map`（:6802）↦ `Loop.pow_card_eq_one`
    （:5760）；`lemma_card_dart_of_loop`（:6785）↦ `Loop.card_pos`
    （:5779）；`lemma_in_dart_of_loop`（:7227）↦ 批 6 `inDartLoopOfList`
    消费面（本批未直接消费）；
  · `loop_of_list`（tame_defs2.hl:149）↦ 批 6 `loopOfListSpine`
    （TameList6.lean:313）；`dart_of_loop`/`in_dart_of_loop` ↦
    `Loop.darts`/成员（批 6 载体约定）；
  · `DIVMOD_EXIST`/`COM_POWER` 全周期分解（HOL path_of_loop_inj 中段）：
    本批不需镜像——HOL 以轨道周期化归证逐点相等，Lean 面由在库
    `Loop.exists_pow_apply`（:5821，∃k ≤ preCard 表出）短路：dart 族员
    先落 `k ≤ preCard` 段内，k+1 与 n 比大小两支（< n 走假设点化、= n
    双侧 `pow_card_eq_one` 化归到 d），无 mod 分解。

  证明层侦察定论：
  · 主件 1（:10930）HOL 证体：MAP_EQ 点化（path_of_loop 展开 +
    loop_map_next_el）后 LIST_EL_EQ 逐项（EL_MAP + el_iota + next_el_power
    + index_hd0 + MOD_LT）。Lean 面：点化步经 `loopMapNextEl` 逐点桥 +
    Perm 幂归纳；轨道步 = §0 私件；列表等式步 `List.ext_get` + 批 19
    `elIota`。零 Meson。
  · 主件 2（:10965）HOL 证体：lemma_inj_path_of_loop 例示 + uniq_nthP，
    双 0 下标挤 i = j。Lean 面：`injOrbit_iff_le_preCard` 取 preCard 窗
    （card = preCard + 1 折算 i,j < n ⇒ ≤ preCard），
    `List.nodup_iff_injective_getElem` mpr + getElem_map + elIota 一步
    点化收口。
  · 主件 3（:11009）HOL 证体两段：①darts 相等 = support_of_sequence 面
    （lemma_dart_loop_via_path + MEM_EXTENSION）；②FUN_EQ_THM 后逐点
    三分（∈ l / ∈ l' / 双外）+ 幂链。Lean 面：①↦
    `darts_eq_pathSupport_pathOf` 双例示 + preCard 折算 +
    `Finset.image_congr`；②↦ `exists_pow_apply` 段内表出 + hbr
    （m ≤ n 幂值桥：< n 走假设、= n 双侧 pow_card_eq_one）链式收口，
    双 dart 集外支 `map_permutes` 恒等；`Loop.ext` 装配。HOL 的
    lemma_loop_identity 前置改写被 `Loop.ext` 吸收，不镜像。
  · 前提折算：主件 2/3 为纯 Loop 层语句（HOL `!l d n` 泛型），Lean 面
    取 `{α} [DecidableEq α] {L L' : Loop α}` 泛型（在库 Loop 件全泛型，
    零收窄）；主件 1 是 loop_of_list 层语句，按载体折 (ℕ×ℕ) 面沿批 6
    惯例。

  依赖面（全为在案真件，零新增债）：批 6 loopOfListSpine/loopMapNextEl +
  批 19 elIota + TameLp nextEl_eq_getD/idxOf_getElem/getD_eq_getElem_of_lt +
  在库 Loop pathOf/injOrbit_iff_le_preCard/injOrbit_iff_pairwise/
  IsInjList/exists_pow_apply/darts_eq_pathSupport_pathOf/pow_card_eq_one/
  card_pos/map_permutes/ext + Assembly nextEl + Mathlib
  nodup_iff_injective_getElem/getElem_map/getElem_mem/pow_succ/
  Equiv.Perm.mul_apply。import 边：本模块 import TameList26（链式带全批
  1-25 与 GoodGraph），零新增库依赖。

  诚实记账：本批三主件全部真证，零新 def、零止损件、零记账债。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git
  写操作。批 28 接续点：HOL :11089 `loop_of_list_path_of_loop` 起
  loop_of_list 回路段（:11089-:11195 四件：loop_of_list_path_of_loop/
  loop_of_list_surj/loop_of_list_rot/loop_of_list_surj2；段终墙 =
  :11197 DIH2K_IMP_PRE_SIMPLE_HYP2 开 dih2k 蕴含段）。侦察预记：rot 两件
  需 `next_el_rot_eq`（seq2.vhl:1353）的 rotate 一般 k 面（在库仅 rotOne
  特形 la7_idxOf_rotOne，TameLp:4168，一般 k 面须自证 idxOf-rotate
  递推）与 LAST/nth_shift_left（seq2.vhl:1145）载体；回路两件依赖本批
  三件 + 批 6 dartLoopOfList（Set 形，Finset 等式须经 List.coe_toFinset
  折算）+ cardSetOfListUniq 面（List.toFinset_card_of_nodup）。
-/

import Kepler.Text.TameSpine.TameList26

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl)
open Kepler.Text.TameLp (nextEl_eq_getD getD_eq_getElem_of_lt idxOf_getElem)

/-! ### §0 私件引擎 -/

/-- **HOL `Seq2.next_el_power`**（seq2-compiled.hl:1818-:2026）head 起步形：
`uniq s ==> (next_el s POWER j) (HD s) = nth (HD s) s j`（j < sizel s，
HOL `nth x0 s j = EL j s` 形）。批 6 `nextElIterateGetD`（TameList6.lean:174，
x ∈ s 一般起点 getD 形）同语义私件不跨文件，本批按批 19 List ℕ 面先例
同体重落（(ℕ×ℕ) 面）。 -/
private theorem nextElIterateHeadD {s : List (ℕ × ℕ)} (hn : s.Nodup) :
    ∀ (j : ℕ) (hj : j < s.length), (nextEl s)^[j] s.head! = s[j]'hj := by
  intro j
  cases s with
  | nil => intro hj; exact absurd hj (Nat.not_lt_zero j)
  | cons a t =>
    induction j with
    | zero => intro _; rfl
    | succ k ih =>
      intro hj
      have hk : k < (a :: t).length := by omega
      rw [Function.iterate_succ_apply', ih hk, nextEl_eq_getD
        (List.getElem_mem hk), idxOf_getElem hn hk, Nat.mod_eq_of_lt hj,
        getD_eq_getElem_of_lt hj]

/-! ### §1 path_of_loop_of_list（tame_list.hl:10930-:10963） -/

/-- **HOL `path_of_loop_of_list`**（tame_list.hl:10930-:10963）
`!r d. d = HD r /\ uniq r /\ ~(r = []) ==> MAP (path_of_loop (loop_of_list r)
d) (iota 0 (sizel r)) = r`——从环表首元起步的路径恰为表自身：MAP_EQ 点化
（`loopMapNextEl` 逐点桥 + Perm 幂归纳）后轨道公式（§0 私件）逐项收口，
列表等式 `List.ext_get` + 批 19 `elIota`。 -/
theorem pathOfLoopOfList {r : List (ℕ × ℕ)} {d : ℕ × ℕ} (hd : d = r.head!)
    (hu : r.Nodup) (hne : r ≠ []) :
    (List.range' 0 r.length).map (Loop.pathOf (loopOfListSpine r) d) = r := by
  rcases r with _ | ⟨a, t⟩
  · exact absurd rfl hne
  · have hda : d = a := by rw [hd]; rfl
    subst hda
    have hmapIter : ∀ (k : ℕ) (x : ℕ × ℕ),
        ((loopOfListSpine (d :: t)).map ^ k) x = (nextEl (d :: t))^[k] x := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro x
        rw [pow_succ', Equiv.Perm.mul_apply, loopMapNextEl hu hne, ih x,
          Function.iterate_succ_apply']
    have orbit : ∀ (k : ℕ) (hq : k < (d :: t).length),
        Loop.pathOf (loopOfListSpine (d :: t)) d k = (d :: t)[k]'hq := by
      intro k hq
      show ((loopOfListSpine (d :: t)).map ^ k) d = _
      rw [hmapIter]
      exact nextElIterateHeadD hu k hq
    refine List.ext_get ?_ (fun i h1 h2 => ?_)
    · rw [List.length_map, List.length_range']
    · show ((List.range' 0 (d :: t).length).map
        (Loop.pathOf (loopOfListSpine (d :: t)) d))[i]'h1 = (d :: t)[i]'h2
      rw [List.getElem_map, elIota h2, Nat.zero_add]
      exact orbit i h2

/-! ### §2 path_of_loop_uniq（tame_list.hl:10965-:11007） -/

/-- **HOL `path_of_loop_uniq`**（tame_list.hl:10965-:11007）
`!l d n. CARD (dart_of_loop l) = n /\ d IN dart_of_loop l ==> uniq (MAP
(path_of_loop l d) (iota 0 n))`——环内元的轨道枚举无重：preCard 窗
`injOrbit_iff_le_preCard` + 成对形 `injOrbit_iff_pairwise` 给出下标单射，
`List.nodup_iff_injective_getElem`（HOL uniq_nthP 面）mpr 收口。 -/
theorem pathOfLoopUniq {α : Type*} [DecidableEq α] {L : Loop α} {d : α}
    {n : ℕ} (hd : d ∈ L.darts) (hc : L.card = n) :
    ((List.range' 0 n).map (L.pathOf d)).Nodup := by
  have hinj : injOrbit L.map d L.preCard :=
    (L.injOrbit_iff_le_preCard hd L.preCard).mp le_rfl
  have hpair : ∀ i j : ℕ, i ≤ L.preCard → j ≤ L.preCard →
      (L.map ^ i) d = (L.map ^ j) d → i = j :=
    (injOrbit_iff_pairwise L.map d L.preCard).mp hinj
  have hcp : n = L.preCard + 1 := by rw [← hc]; exact L.card_pos.2.2
  have hlen : ((List.range' 0 n).map (L.pathOf d)).length = n := by
    rw [List.length_map, List.length_range']
  refine List.nodup_iff_injective_getElem.mpr ?_
  intro i j hij
  simp only [] at hij
  have hi' : i.1 < n := Nat.lt_of_lt_of_eq i.2 hlen
  have hj' : j.1 < n := Nat.lt_of_lt_of_eq j.2 hlen
  rw [List.getElem_map] at hij
  rw [elIota hi'] at hij
  rw [List.getElem_map] at hij
  rw [elIota hj'] at hij
  rw [Nat.zero_add] at hij
  rw [Nat.zero_add] at hij
  exact Fin.ext (hpair i.1 j.1 (by omega) (by omega) hij)

/-! ### §3 path_of_loop_inj（tame_list.hl:11009-:11087） -/

/-- **HOL `path_of_loop_inj`**（tame_list.hl:11009-:11087）
`!l l' d n. CARD (dart_of_loop l) = CARD (dart_of_loop l') /\
CARD (dart_of_loop l') = n /\ d IN dart_of_loop l /\ d IN dart_of_loop l' /\
MAP (path_of_loop l d) (iota 0 n) = MAP (path_of_loop l' d) (iota 0 n) ==>
l = l'`——路径定环：darts 相等（`darts_eq_pathSupport_pathOf` 双例示 +
`Finset.image_congr`）后逐点三分（∈ L / ∈ L' / 双外），族员经
`exists_pow_apply` 段内表出 + m ≤ n 幂值桥（< n 走假设、= n 双侧
`pow_card_eq_one`）链式收口，双外支 `map_permutes` 恒等；`Loop.ext`
装配（HOL lemma_loop_identity 被 Loop.ext 吸收）。HOL 的 DIVMOD_EXIST/
COM_POWER 周期分解被 exists_pow_apply 的段内表出短路，不镜像。 -/
theorem pathOfLoopInj {α : Type*} [DecidableEq α] {L L' : Loop α} {d : α}
    {n : ℕ} (hc : L.card = L'.card) (hc' : L'.card = n) (hd : d ∈ L.darts)
    (hd' : d ∈ L'.darts)
    (hmap : (List.range' 0 n).map (L.pathOf d) = (List.range' 0 n).map
      (L'.pathOf d)) :
    L = L' := by
  have hcard : L.card = n := hc.trans hc'
  have hnp : n = L.preCard + 1 := by rw [← hcard]; exact L.card_pos.2.2
  have hn'p : n = L'.preCard + 1 := by rw [← hc']; exact L'.card_pos.2.2
  have hpre : L.preCard = L'.preCard := by
    show L.darts.card - 1 = L'.darts.card - 1
    rw [show L.darts.card = L.card from rfl, hc, hc',
      show L'.darts.card = L'.card from rfl, hc']
  have hpt : ∀ k : ℕ, k < n → (L.map ^ k) d = (L'.map ^ k) d := by
    intro k hk
    have e1 : ((List.range' 0 n).map (L.pathOf d))[k]'(by rw [List.length_map, List.length_range']; exact hk) = L.pathOf d (0 + k) := by
      rw [List.getElem_map, elIota hk]
    have e2 : ((List.range' 0 n).map (L'.pathOf d))[k]'(by rw [List.length_map, List.length_range']; exact hk) = L'.pathOf d (0 + k) := by
      rw [List.getElem_map, elIota hk]
    have h3 : ((List.range' 0 n).map (L.pathOf d))[k]? = ((List.range' 0 n).map (L'.pathOf d))[k]? := by
      rw [hmap]
    rw [List.getElem?_eq_getElem (by rw [List.length_map, List.length_range']; exact hk)] at h3
    rw [List.getElem?_eq_getElem (by rw [List.length_map, List.length_range']; exact hk)] at h3
    rw [e1] at h3
    rw [e2] at h3
    rw [Nat.zero_add] at h3
    exact Option.some.inj h3
  have hbr : ∀ m : ℕ, m ≤ n → (L.map ^ m) d = (L'.map ^ m) d := by
    intro m hm
    rcases Nat.lt_or_ge m n with hlt | hge
    · exact hpt m hlt
    · have hmeq : m = n := by omega
      rw [hmeq]
      have h1 : (L.map ^ n) d = d := by
        rw [← hcard, L.pow_card_eq_one, Equiv.Perm.one_apply]
      have h2 : (L'.map ^ n) d = d := by
        rw [← hc', L'.pow_card_eq_one, Equiv.Perm.one_apply]
      exact h1.trans h2.symm
  have hdarts : L.darts = L'.darts := by
    rw [L.darts_eq_pathSupport_pathOf hd, L'.darts_eq_pathSupport_pathOf hd',
      hpre]
    refine Finset.image_congr fun k hk => hpt k ?_
    have hkp : k < L'.preCard + 1 := Finset.mem_range.mp hk
    omega
  refine Loop.ext hdarts ?_
  refine Equiv.Perm.ext fun x => ?_
  by_cases hx : x ∈ L.darts
  · obtain ⟨k, hk, hxk⟩ := L.exists_pow_apply hd hx
    have hkn : k + 1 ≤ n := by omega
    have e1 : L.map x = (L.map ^ (k + 1)) d := by
      rw [hxk, pow_succ', Equiv.Perm.mul_apply]
    have e2 : (L'.map ^ (k + 1)) d = L'.map x := by
      rw [pow_succ', Equiv.Perm.mul_apply, ← hbr k (by omega), hxk]
    exact e1.trans ((hbr (k + 1) hkn).trans e2)
  · by_cases hx' : x ∈ L'.darts
    · obtain ⟨k, hk, hxk⟩ := L'.exists_pow_apply hd' hx'
      have hkn : k + 1 ≤ n := by omega
      have e1 : L'.map x = (L'.map ^ (k + 1)) d := by
        rw [hxk, pow_succ', Equiv.Perm.mul_apply]
      have e2 : (L.map ^ (k + 1)) d = L.map x := by
        rw [pow_succ', Equiv.Perm.mul_apply, ← (hbr k (by omega)).symm, hxk]
      exact (e1.trans ((hbr (k + 1) hkn).symm.trans e2)).symm
    · exact (L.map_permutes x hx).trans (L'.map_permutes x hx').symm

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；三主件预期标准三
[propext, Classical.choice, Quot.sound]）：
#print axioms Kepler.Text.TameSpine.pathOfLoopOfList
#print axioms Kepler.Text.TameSpine.pathOfLoopUniq
#print axioms Kepler.Text.TameSpine.pathOfLoopInj
-/
