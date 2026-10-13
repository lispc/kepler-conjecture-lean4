/-
  Kepler.Text.TameSpine.TameList12 — B1 Tame_list 地基批 12：MEM_EXTENSION /
  loop_of_list_inj + split_condition_list / min_num 块（tamespine-port-plan §4
  批次表 B1 行；接续批 11 = TameList11.lean，HOL :5580-:8043 已由批 9/10/11 落，
  本批从 MEM_EXTENSION :8365 起）。

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353，
  text_formalization/tame/tame_list.hl:8365-:8920）——18 枚全量：

  `MEM_EXTENSION` :8365 / `loop_of_list_inj` :8373 / `split_condition_list_split`
  :8396 / `hyp_m_min` :8445 / `min_num_power` :8513 / `f_list_ext_power_mem`
  :8570 / `f_list_ext_f_list_power` :8588 / `mem_f_list_power` :8608 /
  `hyp_m_l_m` :8624 / `split_condition_list_of_darts` :8713 / `hyp_y_l_y` :8727 /
  `hyp_p_min_num` :8748 / `darts_of_family_loop_family_of_list` :8767 /
  `marked_list_split_condition_list` :8791 / `mem_l_y_dart` :8828 /
  `hyp_p_l_p` :8844 / `hyp_z_l_z` :8884 / `hyp_q_l_q` :8908。在 :8920
  自然边界收批（contour_list 章 :8921 起属 s_flag/旗塔领土，留批 13）。

  诚实记账（本批跳过/合并/桥引件）：
  - `min_num`（Library Min 包，HOL 侧空集 junk 0）↦ 新公开载体 `minNumSpine`
    （`Set ℕ` 的 `sInf`；`Nat.sInf_mem`/`Nat.sInf_le` 给出 min_num_in /
    min_num_le 语义，`minNumSpine_eq` = `min_num_unique`）；
  - `split_condition_list`（tame_defs2.hl:673）↦ 新公开载体
    `splitConditionListSpine`（六合取逐句镜像：is_restricted / normal_list /
    MEM r N / ¬final_list / MEM d r / LAST (find_list (parts L r) d) = d）；
  - `l'm`/`l'y`/`l'p`/`l'z`（tame_defs2.hl:440-454）↦ 新公开载体
    `lMSpine`/`lYSpine`/`lPSpine`/`lZSpine`（min_num 定义逐句镜像；
    HOL `ITER n f = f POWER n` 两写法在 Lean 均为 `Function.iterate`）；
  - `l'q`（tame_defs2.hl:455-456 = hyp'q 直接回引）↦ 新公开载体 `lQSpine`：
    Lean 侧 `Hypermap.hypQ`（Hypermap.lean:10842）带 `IsMarked`/`¬finalLoops`
    证明参（HOL 的 new_specification Skolem 函数无证明参，premise 外取 junk），
    载体沿证明参显式传入折算，`hypQLq` 即定义性 rfl——语义零收窄（消费侧
    需 same premises 方可使用，与 HOL 的 is_marked 前提使用点一致）；
  - `hyp'm`/`hyp'y`/`hyp'p`/`hyp'z`（Hypermap.lean:9953/10045/10343/10394
    已真，Classical.choose 载体）零移植直引；本批把 min_num 刻画补上
    （`hypMMin`/`hypPMinNum` = HOL hyp_m_min/hyp_p_min_num 的 min_num_unique
    一段，HOL 侧 `lemma_hyp_m`/`lemma_hyp_p` 的 specification 已由
    `hypM_spec`/`hypP_spec` 承担）；
  - `f_list_ext L` ↦ `(hypermapOfList L hL).faceMap`（批 6 载体约定），
    `f_list_ext_power_mem`/`f_list_ext_f_list_power`/`mem_f_list_power`
    三件的 faceMap 幂引擎就地重写（Hypermap `faceMap_apply_mem` +
    TameLp `faceMap_hypermapOfList` 装配；`f_list_ext_f_list` 点态件
    即 `faceMap_hypermapOfList` 本身）；
  - `is_restricted → is_edge_nondegenerate`（marked_list_split_condition_list
    的 ASM_MESON）经 `Hypermap.IsRestricted.edgeNondegenerate` 直取（批 11
    headOfAtomParts 同款）；`edge_nondeg_f_xor_ni`（批 8）/`parts_next_unlast`/
    `next_el_parts_unlast`（批 9）/`parts_darts`（批 10）/`parts_flatten`/
    `find_list_uniq`（批 9）/`indexf_n`（批 3 `indexfN`）全直引零复制；
  - `hyp_m_l_m` 的发散前提（HOL ENOUGH_TO_SHOW 首合取）按 HOL 同构反证：
    indexf 轨道定位 + `Function.iterate` 算术（批 3 轨道词典直接消费）；
  - 批 10 私件 `getLastMem` 不跨文件，§0 同证重推导（批 7→8→9→10→11 惯例）。

  载体折算（沿批 1-11 约定）：
  - `parts L r` ↦ `partsSpine L r`、`find_list` ↦ `findListSpine`、
    `final_list` ↦ `finalListSpine`、`marked_list` ↦ `MarkedListSpine`（批 7）、
    `normal_list` ↦ `NormalListSpine`、`loop_of_list` ↦ `loopOfListSpine`、
    `loop_family_of_list` ↦ `loopFamilyOfListSpine`（批 5/6）、
    `set_of_list` ↦ `{x | x ∈ _}`（批 11）、`uniq` ↦ `List.Nodup`、
    `LAST`/`HD` ↦ `List.getLast!`/`List.head!`、`BIJ` ↦ `Set.BijOn`、
    `darts_of_family` ↦ `Hypermap.dartsOfFamily`、`POWER` ↦
    `Equiv.Perm ^`（faceMap/map 侧）或 `Function.iterate`（fList/next_el 侧）、
    `is_split_condition` ↦ `Hypermap.IsSplitCondition`。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git 写操作。
  批 13 接续点：HOL :8921 `contour_list_cons` 起的 contour/旗塔章
  （contour_list_cons :8921 / contour_list_is_contour :8972 /
  face_map_list_power :8994 / hyp_S_list :9015 / marked_list_empty_flagged
  :9042 起——`ContourListSpine` 载体批 8 已备；`hyp_S_list` 需本批
  `hypMLm` + faceMap 幂桥，皆已就位）。备选：dart_of 选择函数章 :8043-:8221
  （仍需 Hypermap 侧 face-CARD 与 node-BIJ 桥侦察）。
-/

import Kepler.Text.TameSpine.TameList11

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl eList fList prevEl GoodList listPairs listOfDarts
  findFaceDarts nList)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (nextEl_eq_getD getD_eq_getElem_of_lt getElem_idxOf
   idxOf_getElem nextEl_mem_of_mem
   dart_in_face findFaceDarts_ex_of_self la7_length_listPairs
   hypermapOfList nodeMap_hypermapOfList findFaceDarts_nodup fList_mem_darts
   nList_fList la7_eList_involutory mem_darts_of_mem_findFace
   la7_nextEl_map findFaceDarts_eq_of_mem findFaceDarts_some flatten_nodup_inj
   GoodListNodesTl faceMap_hypermapOfList)

/-! ### §0 min_num 载体与私有引擎 -/

/-- HOL `min_num`（Library Min；空集取 junk 0）的 `sInf` 载体。 -/
noncomputable def minNumSpine (S : Set ℕ) : ℕ := sInf S

private theorem minNumSpine_spec {S : Set ℕ} (hne : S.Nonempty) :
    minNumSpine S ∈ S ∧ ∀ k ∈ S, minNumSpine S ≤ k :=
  ⟨Nat.sInf_mem hne, fun k hk => Nat.sInf_le hk⟩

/-- HOL `min_num_unique`（min_num 由成员性 + 下界唯一刻画）。 -/
theorem minNumSpine_eq {S : Set ℕ} {m : ℕ} (hm : m ∈ S) (hmin : ∀ k ∈ S, m ≤ k) :
    minNumSpine S = m :=
  le_antisymm (Nat.sInf_le hm) (hmin _ (Nat.sInf_mem ⟨m, hm⟩))

/-- 非空表 `getLast!` 必是成员（批 10 私件同证重推导）。 -/
private theorem getLastMem {l : List (ℕ × ℕ)} (h : l ≠ []) : l.getLast! ∈ l := by
  have hpos : 0 < l.length := List.length_pos_of_ne_nil h
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (by omega)]
  simp

/-- `loop_map (loop_of_list r)` 幂的 `next_el` 幺半桥（loopMapNextEl 的幂版）。 -/
private theorem loopMapNextElIter {r : List (ℕ × ℕ)} (hn : r.Nodup) (hne : r ≠ [])
    (d : ℕ × ℕ) (i : ℕ) :
    ((loopOfListSpine r).map ^ i) d = (nextEl r)^[i] d := by
  induction i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, loopMapNextEl hn hne,
      Function.iterate_succ_apply']

/-! ### §1 定义载体（split_condition_list 与 l' 族） -/

/-- HOL `split_condition_list`（tame_defs2.hl:673-675）逐句镜像。

载体记账：`hypermap_of_list L` 的构造需 `GoodList L`，证人 `hL` 显式入参
（沿 NormalListSpine/MarkedListSpine 约定）。 -/
def splitConditionListSpine {L : fgraph ℕ} (hL : GoodList L)
    (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ)) (d : ℕ × ℕ) : Prop :=
  (hypermapOfList L hL).IsRestricted ∧
    NormalListSpine hL N ∧
    r ∈ N ∧
    ¬finalListSpine L r ∧
    d ∈ r ∧
    (findListSpine (partsSpine L r) d).getLast! = d

/-- HOL `l'm`（tame_defs2.hl:440-442）逐句镜像
（`ITER n f = f POWER n` 两写法在 Lean 均为 `Function.iterate`）。 -/
noncomputable def lMSpine (L : fgraph ℕ) (r : List (ℕ × ℕ)) (d : ℕ × ℕ) : ℕ :=
  minNumSpine {m : ℕ | (nextEl r)^[m + 2] d ≠ fList L ((nextEl r)^[m + 1] d)}

/-- HOL `l'y`（tame_defs2.hl:445-446）。 -/
noncomputable def lYSpine (L : fgraph ℕ) (r : List (ℕ × ℕ)) (d : ℕ × ℕ) : ℕ × ℕ :=
  (fList L)^[lMSpine L r d + 1] d

/-- HOL `l'p`（tame_defs2.hl:448-450）。 -/
noncomputable def lPSpine (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (d : ℕ × ℕ) : ℕ :=
  minNumSpine {p : ℕ | (fList L)^[p + 1] (lYSpine L r d) ∈ N.flatten}

/-- HOL `l'z`（tame_defs2.hl:452-454）。 -/
noncomputable def lZSpine (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (d : ℕ × ℕ) : ℕ × ℕ :=
  (fList L)^[lPSpine L N r d + 1] (lYSpine L r d)

/-- HOL `l'q`（tame_defs2.hl:455-456 = `hyp'q` 直接回引）。

载体记账：Lean 侧 `Hypermap.hypQ`（Hypermap.lean:10842）是带证明参的
`Classical.choose`，HOL 的 Skolem 函数无证明参——载体沿证明参显式传入折算，
语义零收窄（HOL 消费点均持 is_marked/¬final_loops 前提）。 -/
noncomputable def lQSpine (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))}
    (hnf : (hypermapOfList L hL).IsNormalFamily (loopFamilyOfListSpine N))
    {r : List (ℕ × ℕ)} {d : ℕ × ℕ}
    (hmark : (hypermapOfList L hL).IsMarked (loopFamilyOfListSpine N) hnf
      (loopOfListSpine r) d)
    (hLnot : loopOfListSpine r ∉ (hypermapOfList L hL).finalLoops
      (loopFamilyOfListSpine N)) : ℕ :=
  (hypermapOfList L hL).hypQ hmark hLnot

/-! ### §2 MEM_EXTENSION / loop_of_list_inj（:8365-:8395） -/

/-- **HOL `MEM_EXTENSION`**（tame_list.hl:8365）
`(a = b) ==> (!x. MEM x a <=> MEM x b)`。 -/
theorem memExtension {α : Type*} {a b : List α} (h : a = b) (x : α) :
    x ∈ a ↔ x ∈ b := by
  subst h
  exact Iff.rfl

/-- **HOL `loop_of_list_inj`**（tame_list.hl:8373-:8394）
`uniq (flatten N) /\ all (\l. ~(l = [])) N /\ MEM r N /\ MEM r' N /\
loop_of_list r = loop_of_list r' ==> r = r'`——dart 集相等（批 6
`dartLoopOfList`）给交点，再 `uniqSublistUnique`（批 6）。 -/
theorem loopOfListInj {N : List (List (ℕ × ℕ))} (hfl : N.flatten.Nodup)
    (hne : ∀ l ∈ N, l ≠ []) {r r' : List (ℕ × ℕ)} (hr : r ∈ N) (hr' : r' ∈ N)
    (heq : loopOfListSpine r = loopOfListSpine r') : r = r' := by
  have hr1 : r.Nodup := uniqFlattenUniq N hfl r hr
  have hr2 : r ≠ [] := hne r hr
  have hr1' : r'.Nodup := uniqFlattenUniq N hfl r' hr'
  have hr2' : r' ≠ [] := hne r' hr'
  have hset : {x | x ∈ r} = {x | x ∈ r'} := by
    rw [← dartLoopOfList hr1 hr2, ← dartLoopOfList hr1' hr2', heq]
  obtain ⟨x, hxr⟩ := List.exists_mem_of_ne_nil r hr2
  have hxr' : x ∈ r' := by
    have hx3 : x ∈ ({x | x ∈ r'} : Set (ℕ × ℕ)) := by rw [← hset]; exact hxr
    exact hx3
  exact uniqSublistUnique N hfl r hr r' hr' ⟨x, hxr, hxr'⟩

/-! ### §3 split_condition_list 基础件（:8396-:8745） -/

/-- **HOL `split_condition_list_split`**（tame_list.hl:8396-:8443）
`split_condition_list L N r d ==> is_split_condition (hypermap_of_list L)
(loop_family_of_list N) (loop_of_list r) d`——六合取：
IsRestricted/IsNormalFamily（批 7 normalListNormal）/家族成员/
非 final 环（批 8 finalLoopsListEq + loop_of_list_inj）/dart 成员/
headOfAtom（批 11 headOfAtomParts，p := find_list (parts L r) d）。 -/
theorem splitConditionListSplit (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {d : ℕ × ℕ}
    (h : splitConditionListSpine hL N r d) :
    (hypermapOfList L hL).IsSplitCondition (loopFamilyOfListSpine N)
      (loopOfListSpine r) d := by
  obtain ⟨hres, hn, hr, hf, hd, hlast⟩ := h
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  refine ⟨hres, normalListNormal hL hgn hres hn, ⟨r, hr, rfl⟩, ?_,
    (inDartLoopOfList hr1 hr2 d).mpr hd, ?_⟩
  · intro hcon
    obtain ⟨r', hr'N, hfr', hr'eq⟩ := finalLoopsConv hL hcon hn
    have hrr : r = r' := loopOfListInj hn.1 hn.2.1 hr hr'N hr'eq
    exact hf (hrr ▸ hfr')
  · have hflat : (partsSpine L r).flatten = r := partsFlatten L hr1 hr2
    have hmemfl : d ∈ (partsSpine L r).flatten := by rw [hflat]; exact hd
    obtain ⟨l, hlmem, hlmemd⟩ := List.mem_flatten.mp hmemfl
    have hpflnod : (partsSpine L r).flatten.Nodup := by rw [hflat]; exact hr1
    have hfeq : findListSpine (partsSpine L r) d = l :=
      findListUniq hpflnod hlmemd hlmem
    have hp : findListSpine (partsSpine L r) d ∈ partsSpine L r := by
      rw [hfeq]; exact hlmem
    have hdp : d ∈ findListSpine (partsSpine L r) d := by
      rw [hfeq]; exact hlmemd
    have hP := headOfAtomParts L hL hgn hres hn hunL hr hp hdp
    rw [hP, hlast]

/-- **HOL `split_condition_list_of_darts`**（tame_list.hl:8713-:8725）
`split_condition_list L N r d ==> MEM d (list_of_darts L)`——
normal_list_darts_of_list_mem（批 5 normalListListOfDarts）经 flatten。 -/
theorem splitConditionListOfDarts {L : fgraph ℕ} {hL : GoodList L}
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {d : ℕ × ℕ}
    (h : splitConditionListSpine hL N r d) : d ∈ listOfDarts L := by
  have hx : d ∈ N.flatten := List.mem_flatten.mpr ⟨r, h.2.2.1, h.2.2.2.2.1⟩
  exact normalListListOfDarts h.2.1 d hx

/-! ### §4 min_num 幂等引理（hyp_m_min / min_num_power / hyp_p_min_num） -/

/-- **HOL `hyp_m_min`**（tame_list.hl:8445-:8466）
`is_split_condition H NF L x ==> hyp'm H NF L x = min_num {m |
~((loop_map L POWER (SUC (SUC m))) x = (face_map H POWER (SUC (SUC m))) x)}`——
`hypM_spec` 的成员性 + 下界即 min_num_unique。 -/
theorem hypMMin {α : Type*} [DecidableEq α] (H : Hypermap α)
    {NF : Set (Loop α)} {L : Loop α} {x : α}
    (hsplit : H.IsSplitCondition NF L x) :
    H.hypM NF L x = minNumSpine {m : ℕ | (L.map ^ (m + 2)) x
      ≠ (H.faceMap ^ (m + 2)) x} := by
  refine (minNumSpine_eq ?_ ?_).symm
  · show (L.map ^ (H.hypM NF L x + 2)) x ≠ (H.faceMap ^ (H.hypM NF L x + 2)) x
    exact (H.hypM_spec hsplit).2
  · intro k hk
    by_contra hlt
    exact hk ((H.hypM_spec hsplit).1 (k + 2) (by omega))

/-- **HOL `min_num_power`**（tame_list.hl:8513-:8567）
`(?i. ~((f POWER i) x = (g POWER i) x)) ==> min_num {m |
~((g POWER (SUC m)) x = (f POWER (SUC m)) x)} = min_num {m |
~((g POWER (SUC m)) x = (f ((g POWER m) x)))}`——f∘g 与 f∘f 在前缀段重合的
极小元平移论证（HOL 同构：非退化支两集同含 0；退化支经 min 下界闭段
hall/f2 两步得成员性与最小性）。 -/
theorem minNumPower {α : Type*} {f g : α → α} {x : α}
    (h : ∃ i, f^[i] x ≠ g^[i] x) :
    minNumSpine {m : ℕ | g^[m + 1] x ≠ f^[m + 1] x}
      = minNumSpine {m : ℕ | g^[m + 1] x ≠ f (g^[m] x)} := by
  by_cases hfg : f x = g x
  · -- 退化支（HOL 主论证）：f∘g 与 f∘f 在 0..m 前缀重合
    obtain ⟨i, hi⟩ := h
    have hne0 : i ≠ 0 := by
      intro h0
      rw [h0, Function.iterate_zero_apply, Function.iterate_zero_apply] at hi
      exact hi rfl
    have hS1 : ({m : ℕ | g^[m + 1] x ≠ f^[m + 1] x}).Nonempty := by
      refine ⟨i - 1, ?_⟩
      show g^[(i - 1) + 1] x ≠ f^[(i - 1) + 1] x
      have hii : (i - 1) + 1 = i := by omega
      rw [hii]; exact Ne.symm hi
    obtain ⟨hm, hmin⟩ := minNumSpine_spec hS1
    have hall : ∀ k : ℕ, k ≤ minNumSpine {m : ℕ | g^[m + 1] x ≠ f^[m + 1] x} →
        g^[k] x = f^[k] x := by
      intro k hk
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · rw [hk0, Function.iterate_zero_apply, Function.iterate_zero_apply]
      · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk0)
        have hj' : k = j + 1 := hj
        by_contra hcon
        have hjS : j ∈ {m : ℕ | g^[m + 1] x ≠ f^[m + 1] x} := by
          show g^[j + 1] x ≠ f^[j + 1] x
          rw [← hj']; exact hcon
        have hle : minNumSpine {m : ℕ | g^[m + 1] x ≠ f^[m + 1] x} ≤ j := hmin j hjS
        omega
    have hf2 : ∀ k : ℕ, k ≤ minNumSpine {m : ℕ | g^[m + 1] x ≠ f^[m + 1] x} →
        f (g^[k] x) = f^[k + 1] x := by
      intro k hk
      rw [hall k hk]
      exact (Function.iterate_succ_apply' f k x).symm
    have hmS2 : minNumSpine {m : ℕ | g^[m + 1] x ≠ f^[m + 1] x}
        ∈ {m : ℕ | g^[m + 1] x ≠ f (g^[m] x)} := by
      show g^[minNumSpine {m : ℕ | g^[m + 1] x ≠ f^[m + 1] x} + 1] x
        ≠ f (g^[minNumSpine {m : ℕ | g^[m + 1] x ≠ f^[m + 1] x}] x)
      rw [hf2 _ (Nat.le_refl _)]
      exact hm
    have hmin2 : ∀ k ∈ {m : ℕ | g^[m + 1] x ≠ f (g^[m] x)},
        minNumSpine {m : ℕ | g^[m + 1] x ≠ f^[m + 1] x} ≤ k := by
      intro k hk
      by_contra hlt
      have hkm : k ≤ minNumSpine {m : ℕ | g^[m + 1] x ≠ f^[m + 1] x} := by omega
      have hkS1 : k ∈ {m : ℕ | g^[m + 1] x ≠ f^[m + 1] x} := by
        show g^[k + 1] x ≠ f^[k + 1] x
        rw [← hf2 k hkm]; exact hk
      exact hlt (hmin k hkS1)
    exact (minNumSpine_eq hmS2 hmin2).symm
  · -- 非退化支：f x ≠ g x ⟹ 两集同含 0
    have hfg' : f x ≠ g x := hfg
    have h01 : (0:ℕ) ∈ {m : ℕ | g^[m + 1] x ≠ f^[m + 1] x} := by
      show g^[1] x ≠ f^[1] x
      rw [Function.iterate_one, Function.iterate_one]
      intro hcon
      exact hfg' hcon.symm
    have h02 : (0:ℕ) ∈ {m : ℕ | g^[m + 1] x ≠ f (g^[m] x)} := by
      show g^[1] x ≠ f (g^[0] x)
      rw [Function.iterate_one, Function.iterate_zero_apply]
      intro hcon
      exact hfg' hcon.symm
    rw [minNumSpine_eq h01 (fun j _ => Nat.zero_le j),
      minNumSpine_eq h02 (fun j _ => Nat.zero_le j)]

/-- **HOL `hyp_p_min_num`**（tame_list.hl:8748-:8764）
`is_split_condition H NF L x ==> hyp'p H NF L x = min_num {p |
(face_map H POWER SUC p) (hyp'y H NF L x) IN darts_of_family NF}`——
`hypP_spec` 的成员性 + 下界即 min_num_unique。 -/
theorem hypPMinNum {α : Type*} [DecidableEq α] (H : Hypermap α)
    {NF : Set (Loop α)} {L : Loop α} {x : α}
    (hsplit : H.IsSplitCondition NF L x) :
    H.hypP NF L x = minNumSpine {p : ℕ | (H.faceMap ^ (p + 1))
      (H.hypY NF L x) ∈ Hypermap.dartsOfFamily NF} := by
  refine (minNumSpine_eq ?_ ?_).symm
  · show (H.faceMap ^ (H.hypP NF L x + 1)) (H.hypY NF L x)
      ∈ Hypermap.dartsOfFamily NF
    exact (H.hypP_spec hsplit).2
  · intro k hk
    by_contra hlt
    exact (H.hypP_spec hsplit).1 (k + 1) (by omega) (by omega) hk

/-! ### §5 faceMap/fList 幂桥（f_list_ext 三件，:8570-:8622） -/

/-- **HOL `f_list_ext_power_mem`**（tame_list.hl:8570-:8586）
`MEM d (list_of_darts L) /\ good_list L ==> MEM ((f_list_ext L POWER i) d)
(list_of_darts L)`——`f_list_ext L` ↦ faceMap（批 6 载体），faceMap 置换
dart 集（Hypermap `faceMap_apply_mem`）幂次保持。 -/
theorem fListExtPowerMem (L : fgraph ℕ) (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) (i : ℕ) :
    ((hypermapOfList L hL).faceMap ^ i) d ∈ listOfDarts L := by
  have hdart : d ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hd
  have hmem : ∀ j : ℕ, ((hypermapOfList L hL).faceMap ^ j) d
      ∈ (hypermapOfList L hL).darts := by
    intro j
    induction j with
    | zero => exact hdart
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact (hypermapOfList L hL).faceMap_apply_mem ih
  exact List.mem_toFinset.mp
    (show ((hypermapOfList L hL).faceMap ^ i) d
      ∈ ((listOfDarts L).toFinset : Set (ℕ × ℕ)) from hmem i)

/-- **HOL `f_list_ext_f_list_power`**（tame_list.hl:8588-:8606）
`MEM d (list_of_darts L) /\ good_list L ==> (f_list_ext L POWER i) d =
(f_list L POWER i) d`——点态桥 `faceMap_hypermapOfList`（TameLp）幂次归纳。 -/
theorem fListExtFListPower (L : fgraph ℕ) (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) (i : ℕ) :
    ((hypermapOfList L hL).faceMap ^ i) d = (fList L)^[i] d := by
  have hdart : d ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hd
  have hmem : ∀ j : ℕ, ((hypermapOfList L hL).faceMap ^ j) d
      ∈ (hypermapOfList L hL).darts := by
    intro j
    induction j with
    | zero => exact hdart
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact (hypermapOfList L hL).faceMap_apply_mem ih
  induction i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, faceMap_hypermapOfList L hL (hmem k), ih,
      Function.iterate_succ_apply']

/-- **HOL `mem_f_list_power`**（tame_list.hl:8608-:8622）
`MEM d (list_of_darts L) ==> MEM ((f_list L POWER i) d) (list_of_darts L)`——
经 f_list_ext 两件（HOL 同路；免 uniq 前提）。 -/
theorem memFListPower (L : fgraph ℕ) (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) (i : ℕ) : (fList L)^[i] d ∈ listOfDarts L := by
  rw [← fListExtFListPower L hL hd i]
  exact fListExtPowerMem L hL hd i

/-! ### §6 hyp↔l' 五桥（hyp_m_l_m / hyp_y_l_y / hyp_p_l_p / hyp_z_l_z /
hyp_q_l_q，:8624-:8919） -/

/-- **HOL `hyp_m_l_m`**（tame_list.hl:8624-:8711）
`good_list L /\ good_list_nodes L /\ all uniq L /\ next_el r d = f_list L d /\
split_condition_list L N r d ==> hyp'm (hypermap_of_list L)
(loop_family_of_list N) (loop_of_list r) d = l'm L r d`——链：hypMMin →
loop_map/face_map 幺半桥（loopMapNextElIter/fListExtFListPower）→ l'm 集的
y=next_el r d 换元 → min_num_power（发散前提由 ¬final_list 的 indexf 轨道
反证给出，HOL 同构）。 -/
theorem hypMLm (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup) {N : List (List (ℕ × ℕ))}
    {r : List (ℕ × ℕ)} {d : ℕ × ℕ} (hnext : nextEl r d = fList L d)
    (hsc : splitConditionListSpine hL N r d) :
    (hypermapOfList L hL).hypM (loopFamilyOfListSpine N) (loopOfListSpine r) d
      = lMSpine L r d := by
  obtain ⟨hres, hn, hr, hf, hd, hlast⟩ := hsc
  have hsc' : splitConditionListSpine hL N r d :=
    ⟨hres, hn, hr, hf, hd, hlast⟩
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  have hmemD : d ∈ listOfDarts L :=
    normalListListOfDarts hn d (List.mem_flatten.mpr ⟨r, hr, hd⟩)
  have hsplit := splitConditionListSplit L hL hgn hunL hsc'
  have hf' : ¬finalListSpine L r := hf
  unfold finalListSpine at hf'
  push_neg at hf'
  obtain ⟨z, hzr, hz⟩ := hf'
  have hz1 : (nextEl r)^[indexf d z r] d = z := indexfN hd hzr hr1
  have hdiv : ∃ i, (fList L)^[i] (fList L d) ≠ (nextEl r)^[i] (fList L d) := by
    by_contra hcon
    push_neg at hcon
    have hkey : fList L z = nextEl r z := by
      rcases Nat.eq_zero_or_pos (indexf d z r) with hidx | hidx
      · rw [hidx] at hz1
        simp only [Function.iterate_zero_apply] at hz1
        rw [← hz1]
        exact hnext.symm
      · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hidx)
        have e1 : z = (nextEl r)^[j + 1] d := by rw [← hz1, hj]
        have e2 : (nextEl r)^[j + 1] d = (nextEl r)^[j] (nextEl r d) :=
          Function.iterate_succ_apply (nextEl r) j d
        have e3 : (nextEl r)^[j] (nextEl r d) = (nextEl r)^[j] (fList L d) := by
          rw [hnext]
        have e4 : (nextEl r)^[j] (fList L d) = (fList L)^[j] (fList L d) :=
          (hcon j).symm
        have e5 : (fList L)^[j] (fList L d) = (fList L)^[j + 1] d :=
          (Function.iterate_succ_apply (fList L) j d).symm
        have hz' : z = (fList L)^[j + 1] d := e1.trans (e2.trans (e3.trans
          (e4.trans e5)))
        have hfz : fList L z = (fList L)^[j + 1] (fList L d) := by
          rw [hz']
          exact ((Function.iterate_succ_apply' (fList L) (j + 1) d).symm).trans
            (Function.iterate_succ_apply (fList L) (j + 1) d)
        have hgz : nextEl r z = (nextEl r)^[j + 1] (fList L d) := by
          rw [e1, ← Function.iterate_succ_apply' (nextEl r) (j + 1) d,
            Function.iterate_succ_apply (nextEl r) (j + 1) d, hnext]
        rw [hfz, hgz]
        exact hcon (j + 1)
    exact hz hkey
  have eB : {m : ℕ | ((loopOfListSpine r).map ^ (m + 2)) d
        ≠ ((hypermapOfList L hL).faceMap ^ (m + 2)) d}
      = {m : ℕ | (nextEl r)^[m + 2] d ≠ (fList L)^[m + 2] d} := by
    ext m
    simp only [Set.mem_setOf_eq]
    rw [loopMapNextElIter hr1 hr2 d (m + 2), fListExtFListPower L hL hmemD (m + 2)]
  have eC : {m : ℕ | (nextEl r)^[m + 2] d ≠ (fList L)^[m + 2] d}
      = {m : ℕ | (nextEl r)^[m + 1] (fList L d)
        ≠ (fList L)^[m + 1] (fList L d)} := by
    ext m
    simp only [Set.mem_setOf_eq]
    rw [Function.iterate_succ_apply (nextEl r) (m + 1) d,
      Function.iterate_succ_apply (fList L) (m + 1) d, hnext]
  have eE : {m : ℕ | (nextEl r)^[m + 2] d
        ≠ fList L ((nextEl r)^[m + 1] d)}
      = {m : ℕ | (nextEl r)^[m + 1] (fList L d)
        ≠ fList L ((nextEl r)^[m] (fList L d))} := by
    ext m
    simp only [Set.mem_setOf_eq]
    rw [Function.iterate_succ_apply (nextEl r) (m + 1) d,
      congrArg (fList L) (Function.iterate_succ_apply (nextEl r) m d), hnext]
  rw [hypMMin (hypermapOfList L hL) hsplit, eB, eC,
    minNumPower (f := fList L) (g := nextEl r) (x := fList L d) hdiv]
  show minNumSpine {m : ℕ | (nextEl r)^[m + 1] (fList L d)
      ≠ fList L ((nextEl r)^[m] (fList L d))}
    = minNumSpine {m : ℕ | (nextEl r)^[m + 2] d
      ≠ fList L ((nextEl r)^[m + 1] d)}
  rw [eE]

/-- **HOL `hyp_y_l_y`**（tame_list.hl:8727-:8745）
`hyp'y (hypermap_of_list L) (loop_family_of_list N) (loop_of_list r) d =
l'y L r d`——hypMLm + faceMap 幂桥（HOL 的 f_list_ext_f_list_power 段）。 -/
theorem hypYL (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup) {N : List (List (ℕ × ℕ))}
    {r : List (ℕ × ℕ)} {d : ℕ × ℕ} (hnext : nextEl r d = fList L d)
    (hsc : splitConditionListSpine hL N r d) :
    (hypermapOfList L hL).hypY (loopFamilyOfListSpine N) (loopOfListSpine r) d
      = lYSpine L r d := by
  have hmemD : d ∈ listOfDarts L := splitConditionListOfDarts hsc
  have hsplit := splitConditionListSplit L hL hgn hunL hsc
  show ((hypermapOfList L hL).faceMap ^ ((hypermapOfList L hL).hypM
      (loopFamilyOfListSpine N) (loopOfListSpine r) d + 1)) d = lYSpine L r d
  rw [hypMLm L hL hgn hunL hnext hsc]
  exact fListExtFListPower L hL hmemD _

/-- **HOL `mem_l_y_dart`**（tame_list.hl:8828-:8841）
`good_list L /\ split_condition_list L N r d ==> MEM (l'y L r d)
(list_of_darts L)`——l_y 展开 + mem_f_list_power。 -/
theorem memLYDart (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {d : ℕ × ℕ}
    (hsc : splitConditionListSpine hL N r d) :
    lYSpine L r d ∈ listOfDarts L := by
  have hmemD : d ∈ listOfDarts L := splitConditionListOfDarts hsc
  show (fList L)^[lMSpine L r d + 1] d ∈ listOfDarts L
  exact memFListPower L hL hmemD _

/-- **HOL `darts_of_family_loop_family_of_list`**（tame_list.hl:8767-:8789）
`normal_list L N ==> darts_of_family (loop_family_of_list N) =
set_of_list (flatten N)`——两向 in_dart_loop_of_list（批 6）拼接。 -/
theorem dartsOfFamilyLoopFamilyOfList (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (h : NormalListSpine hL N) :
    Hypermap.dartsOfFamily (loopFamilyOfListSpine N) = {x | x ∈ N.flatten} := by
  ext x
  constructor
  · rintro ⟨Lr, ⟨r, hr, rfl⟩, hxd⟩
    obtain ⟨hr1, hr2⟩ := normalListUniqNonnil h hr
    exact List.mem_flatten.mpr ⟨r, hr, (inDartLoopOfList hr1 hr2 x).mp hxd⟩
  · intro hx
    obtain ⟨r, hr, hxr⟩ := List.mem_flatten.mp hx
    obtain ⟨hr1, hr2⟩ := normalListUniqNonnil h hr
    exact ⟨loopOfListSpine r, ⟨r, hr, rfl⟩, (inDartLoopOfList hr1 hr2 x).mpr hxr⟩

/-- **HOL `hyp_p_l_p`**（tame_list.hl:8844-:8882）
`hyp'p (hypermap_of_list L) (loop_family_of_list N) (loop_of_list r) d =
l'p L N r d`——hypPMinNum + hypYL + faceMap 幂桥 + darts_of_family
= set_of_list (flatten N)（下一件）的集合外延。 -/
theorem hypPLp (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup) {N : List (List (ℕ × ℕ))}
    {r : List (ℕ × ℕ)} {d : ℕ × ℕ} (hnext : nextEl r d = fList L d)
    (hsc : splitConditionListSpine hL N r d) :
    (hypermapOfList L hL).hypP (loopFamilyOfListSpine N) (loopOfListSpine r) d
      = lPSpine L N r d := by
  have hn : NormalListSpine hL N := hsc.2.1
  have hmemD : d ∈ listOfDarts L := splitConditionListOfDarts hsc
  have hsplit := splitConditionListSplit L hL hgn hunL hsc
  have hY : (hypermapOfList L hL).hypY (loopFamilyOfListSpine N)
      (loopOfListSpine r) d = lYSpine L r d := hypYL L hL hgn hunL hnext hsc
  have hyD : lYSpine L r d ∈ listOfDarts L := memLYDart L hL hsc
  rw [hypPMinNum (hypermapOfList L hL) hsplit]
  show minNumSpine {p : ℕ | ((hypermapOfList L hL).faceMap ^ (p + 1))
      ((hypermapOfList L hL).hypY (loopFamilyOfListSpine N)
      (loopOfListSpine r) d) ∈ Hypermap.dartsOfFamily (loopFamilyOfListSpine N)}
    = minNumSpine {p : ℕ | (fList L)^[p + 1] (lYSpine L r d) ∈ N.flatten}
  congr 1
  ext p
  simp only [Set.mem_setOf_eq]
  rw [hY, fListExtFListPower L hL hyD (p + 1),
    dartsOfFamilyLoopFamilyOfList L hL hn]
  exact Iff.rfl

/-- **HOL `hyp_z_l_z`**（tame_list.hl:8884-:8906）
`hyp'z (hypermap_of_list L) (loop_family_of_list N) (loop_of_list r) d =
l'z L N r d`——hypPLp + hypYL + faceMap 幂桥。 -/
theorem hypZLz (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup) {N : List (List (ℕ × ℕ))}
    {r : List (ℕ × ℕ)} {d : ℕ × ℕ} (hnext : nextEl r d = fList L d)
    (hsc : splitConditionListSpine hL N r d) :
    (hypermapOfList L hL).hypZ (loopFamilyOfListSpine N) (loopOfListSpine r) d
      = lZSpine L N r d := by
  have hY : (hypermapOfList L hL).hypY (loopFamilyOfListSpine N)
      (loopOfListSpine r) d = lYSpine L r d := hypYL L hL hgn hunL hnext hsc
  have hyD : lYSpine L r d ∈ listOfDarts L := memLYDart L hL hsc
  have hP := hypPLp L hL hgn hunL hnext hsc
  show ((hypermapOfList L hL).faceMap ^ ((hypermapOfList L hL).hypP
      (loopFamilyOfListSpine N) (loopOfListSpine r) d + 1))
      ((hypermapOfList L hL).hypY (loopFamilyOfListSpine N)
      (loopOfListSpine r) d) = lZSpine L N r d
  rw [hP, hY, fListExtFListPower L hL hyD _]
  rfl

/-- **HOL `hyp_q_l_q`**（tame_list.hl:8908-:8919）
`hyp'q (hypermap_of_list L) (loop_family_of_list N) (loop_of_list r) d =
l'q L N r d`——l'q 定义即 hyp'q 回引（REWRITE_TAC[l_q]），Lean 载体下
定义性 rfl。 -/
theorem hypQLq (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))}
    (hnf : (hypermapOfList L hL).IsNormalFamily (loopFamilyOfListSpine N))
    {r : List (ℕ × ℕ)} {d : ℕ × ℕ}
    (hmark : (hypermapOfList L hL).IsMarked (loopFamilyOfListSpine N) hnf
      (loopOfListSpine r) d)
    (hLnot : loopOfListSpine r ∉ (hypermapOfList L hL).finalLoops
      (loopFamilyOfListSpine N)) :
    (hypermapOfList L hL).hypQ hmark hLnot = lQSpine L hL hnf hmark hLnot :=
  rfl

/-! ### §7 marked_list 桥（:8791-:8827） -/

/-- **HOL `marked_list_split_condition_list`**（tame_list.hl:8791-:8826）
`good_list L /\ marked_list L N r d /\ ~final_list L r ==>
split_condition_list L N r d`——前五合取直取；LAST 支反证：parts_next_unlast
（批 9）+ next_el_parts_unlast（批 9）+ edge_nondeg_f_xor_ni（批 8）。
载体记账：`MarkedListSpine` 镜像 HOL marked_list 前 7 合取块（批 7），本件
恰好只消费其中块，结论零收窄。 -/
theorem markListSplitConditionList (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {d : ℕ × ℕ}
    (hm : MarkedListSpine hL N r d) (hf : ¬finalListSpine L r) :
    splitConditionListSpine hL N r d := by
  have hres := hm.1
  have hn := hm.2.1
  have hr := hm.2.2.1
  have hd := hm.2.2.2.1
  have hnext := hm.2.2.2.2.2.1
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  have hnedg := hres.edgeNondegenerate
  have hflat : (partsSpine L r).flatten = r := partsFlatten L hr1 hr2
  have hmemfl : d ∈ (partsSpine L r).flatten := by rw [hflat]; exact hd
  obtain ⟨l, hlmem, hlmemd⟩ := List.mem_flatten.mp hmemfl
  have hpflnod : (partsSpine L r).flatten.Nodup := by rw [hflat]; exact hr1
  have hfeq : findListSpine (partsSpine L r) d = l :=
    findListUniq hpflnod hlmemd hlmem
  refine ⟨hres, hn, hr, hf, hd, ?_⟩
  by_contra hne
  have hdl : d ≠ l.getLast! := by
    rw [← hfeq]
    exact fun hcon => hne hcon.symm
  have h1 : nextEl l d = fList L (eList d) :=
    partsNextUnlast L hr1 hr2 l hlmem d hlmemd hdl
  have h2 : nextEl r d = nextEl l d :=
    nextElPartsUnlast L hr1 hr2 hlmem hlmemd hdl
  have h3 : d ∈ listOfDarts L := partsDarts L hn hr hlmem hlmemd
  have h4 : fList L d ≠ fList L (eList d) := edgeNondegFXorNi hL hnedg h3
  exact h4 ((hnext.symm.trans h2).trans h1)

end Kepler.Text.TameSpine
