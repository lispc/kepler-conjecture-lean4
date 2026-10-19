/-
  Kepler.Text.TameSpine.TameList48 — B1 Tame_list 地基批 48：
  rot 旋转章全族（tamespine-port-plan §4 批次表 B1 行；接续批 47 =
  TameList47.lean，批 47 终点 = HOL :12830；本批起点 = HOL :12831
  `rot_final_list`，章开章；随收 :12991 `ALL2_MAP2`。行号均按主仓
  reference/flyspeck（commit 1ce0353）实测。

  载体折算盘点（批 47 尾处方预记对拍面，经主仓全库 grep（含
  LocalAuto 族）+ 工具链 core v4.32.2/mathlib/batteries 三处对拍
  复核）：**两个载体决定首次进场 + 八件全真证，零新 def**：
  - `ALL2`（ssreflect ALL2 P N N' 逐位合取链）↦ `List.Forall₂`
    （mathlib Mathlib/Data/List/Forall2.lean，定义体
    Data/List/Defs；nil/cons 双构造逐字对应）——本 port 首次进场，
    在册性探针 `#check @List.Forall₂` 绿（import 闭包可达，零新增
    import）；
  - `perm_eq`（ssreflect 同重数谓词 `perm_eq s1 s2 <=>
    !x. count (pred1 x) s1 = count (pred1 x) s2`，seq2.vhl:366 起）
    ↦ core `List.Perm`（`~`；Init/Data/List/Perm.lean）——同重数
    = 同多重集，`List.Perm` 忠实镜像。批 8 TameList8.lean:383 rot
    词典块先例领土对拍：该块只立 rot 方程/成员/集合面，未触碰
    perm_eq——本批 perm_eq 载体为首次决定；
  - `rot_final_list`（:12831-:12845）↦ `rotFinalList`（真证）；
    `Seq2.next_el_rot_eq` ↦ 批 8 私件 nextElRotateFunc（private 不
    跨文件可见，雷区既档）同证重落本模块 private（批 14 getElemCon
    同款先例）；`Seq.mem_rot` ↦ core `List.mem_rotate` 纯消费；
  - `ALL2_MEM`（:12846-:12856）↦ `all2Mem`（真证，泛型
    `{α β}` 形，HOL `!P N N' r'` 全量化逐字）；
  - `ALL2_rot_flatten`（:12858-:12873）↦ `all2RotFlatten`（真证）；
    `Seq2.perm_eq0l` 面（基座 [] 情形）= `List.Perm.refl` 定义式
    吸收；`Seq2.perm_eq_cat` ↦ core `List.Perm.append`；
    `Seq.perm_eq_sym` ↦ core `List.Perm.symm`（证体内隐式）；
    `Seq2.perm_eq_rot` ↦ mathlib `List.rotate_perm`
    （Rotate.lean:156）；`Seq.flatten0`/`Seq.flatten_cons` ↦ core
    `List.flatten` 定义式/`List.flatten_cons`；
  - `rot_eq_nil`（:12875-:12880）= core `List.rotate_eq_nil_iff`
    （Rotate.lean:171）——**纯消费零镜像**（批 8 rotEqRot/
    nextElRotateFunc 证内既用同件），本批消费点直取，不设包装件；
  - `loop_list_rot`（:12883-:12894）↦ `loopListRot`（真证）；
  - `normal_list_rot`（:12896-:12943）↦ `normalListRot`（真证）；
    `normal_list` 面 = NormalListSpine 五合取（批 5）；`f_last` 槽
    = finalListFLast（批 31，tame_list.hl:11290 `final_list_f_last`
    在册件）；`normal_list_uniq_nonnil` 槽 = 批 6
    normalListUniqNonnil（tame_list.hl:4500）；`Seq2.perm_eq_uniq`
    面 ↦ core `List.Perm.nodup`；`Seq.perm_eq_mem` 面 ↦ core
    `List.Perm.mem_iff`；`Seq2.perm_eq_set_of_list_eq` 面 ↦
    `Set.ext` + `Perm.mem_iff` 换向（uniq 侧条件由 flatten-Nodup
    语境吸收——Perm 载体下集合相等无须 uniq 前提，零收窄）；
  - `all_final_list_rot`（:12945-:12960）↦ `allFinalListRot`
    （真证）；
  - `quotient_list_rot`（:12962-:12989）↦ `quotientListRot`（真证，
    private 换装槽 forall2RotMapFst 点位 induction）；`final_list_
    quotient` 换装槽 = 批 47 finalListQuotient 双侧直投；
    `Seq.map_rot` ↦ mathlib `List.map_rotate`（Rotate.lean:329）；
    `lower_case` 面（β 归）= 匿名构造子内 `rw` 收；
  - `ALL2_MAP2`（:12991-:12998）↦ `all2Map2`（真证，泛型
    `{α β}` 形）；`ALL (\a. P a (f a)) l` 面 ↦ `∀ a ∈ l, …`（批 7
    finalListSpine 同款逐点 ∀∈ 折算）。
  全库 grep（含 LocalAuto 族 + core/mathlib/batteries 三处）
  rotFinalList/all2Mem/all2RotFlatten/loopListRot/normalListRot/
  allFinalListRot/quotientListRot/all2Map2 八件名零撞车零现成载体
  ——镜像本体即本批件。私件三名（getElemCon/nextElOfNotMem'/
  nextElRotateFunc）为批 8 私件同证重落（private 模块内雷区既档：
  private 不跨文件，消费侧各自重落；批 14 getElemCon 先例），
  零新增公开私件面。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:12831-:12991）：

  件一（章开章）：`rot_final_list` :12831 `!L r r'. final_list L r /\
  uniq r /\ (?n. r' = rot n r) ==> final_list L r'` ↦ `rotFinalList`
  （真证）。final_list 定义形逐点 ∀∈（批 7 槽零展开步）+
  Seq2.next_el_rot_eq（↦ nextElRotateFunc，uniq r 支）函数等式
  rw + Seq.mem_rot（↦ List.mem_rotate）成员回喂。

  件二：`ALL2_MEM` :12846 `!P N N' r'. ALL2 P N N' /\ MEM r' N' ==>
  (?r. MEM r N /\ P r r')` ↦ `all2Mem`（真证）。Forall₂ induction
  双消（nil 支 `cases` 收矛盾；cons 支 head/tail 两向匿名构造）。

  件三：`ALL2_rot_flatten` :12858 `ALL2 rot-rel N N' ==> perm_eq
  (flatten N) (flatten N')` ↦ `all2RotFlatten`（真证）。induction
  cons 支：面级旋转 perm（`rotate_perm`）+ ih + `Perm.append` 拼接
  （flatten_cons 定义式两侧归一）。

  件四（零镜像）：`rot_eq_nil` :12875 = `List.rotate_eq_nil_iff`
  纯消费（见载体盘点）。

  件五：`loop_list_rot` :12883 `uniq r /\ loop_list L r ==>
  loop_list L (rot n r)` ↦ `loopListRot`（真证）。loop_list 定义形
  逐点 ∀∈ + nextElRotateFunc 函数等式 rw + mem_rotate 成员回喂。

  件六（章主件）：`normal_list_rot` :12896 `good_list L /\
  normal_list L N /\ all (final_list L) N /\ ALL2 rot-rel N N' ==>
  normal_list L N'` ↦ `normalListRot`（真证）。五合取逐槽：
  flatten-Nodup = all2RotFlatten + `Perm.nodup`；nonnil/f_last/
  loop_list 三槽 = all2Mem 拆证人（r ∈ N，s = rot n r）+
  rotate_eq_nil_iff 非空搬运 + finalListFLast（final_list 槽经
  rotFinalList 运输）+ loopListRot；node-SUBSET 槽 = Perm.mem_iff
  集合换装（`Set.ext` 两向同 perm）后 hnorm.5 直取。

  件七：`all_final_list_rot` :12945 ↦ `allFinalListRot`（真证）。
  all 谓词展开 ∀∈（Seq.allP 面零镜像）+ all2Mem 拆证人 +
  rotFinalList 项式直投。

  件八（章 capstone）：`quotient_list_rot` :12962 `... ==> ALL2
  rot-rel (quotient_list L N) (quotient_list L N')` ↦
  `quotientListRot`（真证）。先立 N' 侧 normal_list/all_final 两槽
  （件六/件七直投）→ finalListQuotient（批 47）双侧换装
  `quotientListSpine L N = N.map (fun r => r.map (·.1))` →
  private forall2RotMapFst induction 点位收口（cons 支
  `List.map_rotate` 一发 + 匿名构造）。

  件九：`ALL2_MAP2` :12991 `ALL2 P l (MAP f l) <=>
  ALL (\a. P a (f a)) l` ↦ `all2Map2`（真证）。List induction 双向
  Iff（正向 cases 两支；反向 cons 双构造直拼）。

  新落地载体：零（本批纯消费批 + 两载体决定记档；§0 三私件为批 8
  私件同证重落，不占新领土）。

  诚实记账：八件全真证，零新 def、零 sorry、零止损件、零记账债。
  范围决策：批 48 射程收口至 :12991（rot 章全族 + ALL2_MAP2，自然
  边界 = :13001 章后件前）；:13001 `normal_list_as_list_of_faces`
  判批 49——证体第 4 合取槽 `List_hypermap_iso.rot_hypermap_of_list_
  eq`（formal_lp/hypermap/ssreflect/list_hypermap_iso-compiled.hl
  :424）未进场，且 quotient 级 `hypermap_of_list` 在 Lean 载体下
  需 `GoodList (quotientListSpine L N')` 证人（HOL 无类型无此前提，
  载体语义缺口）——两缺口处方随批 49 接续点记档；其余随收槽均在册：
  final_list_rot = 本批 rotFinalList、list_of_darts_quotient_uniq =
  批 10 listOfDartsQuotientUniq（TameList10.lean:665）、
  List_hypermap.mem_find_face = TameLp dart_in_face、SKOLEM_THM =
  Classical choose 形、ALL2_MAP2 = 本批 all2Map2、normal_list_rot/
  all_final_list_rot = 本批件六/件七。
  红线遵守：零既有文件触碰、零 git 写操作。
  批 49 接续点：HOL :13001 `normal_list_as_list_of_faces`（两缺口
  先立：① rot_hypermap_of_list_eq 移植——槽链 find_face_rot /
  rot_list_of_darts_perm / perm_eq_set_of_list_eq + res 逐点相合
  面；② quotient 级 GoodList 证人载体或存在证人形折算；备选自然
  边界件 :13060 `normal_list_perm_eq_faces`（槽 uniq_perm_eq_map/
  uniq_flatten/uniq_list_of_faces/find_face_eq 开工先清点）与
  :13118 `fst_zip`（sizel/zip 小件））。
-/

import Kepler.Text.TameSpine.TameList47

namespace Kepler.Text.TameSpine

open Kepler.Assembly (GoodList listOfDarts nextEl)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (hypermapOfList nextEl_eq_getD getD_eq_getElem_of_lt
  getElem_idxOf)

/-! ### §0 next_el 旋转私件重落（批 8 私件同证；private 不跨文件） -/

/-- 同表两下标相等则取元相等（proof-irrelevant getElem 换形器；
批 8/14 私件同款重落）。 -/
private theorem getElemCon {α : Type*} {l : List α} {a b : ℕ} (ha : a < l.length)
    (hb : b < l.length) (hab : a = b) : l[a]'ha = l[b]'hb := by
  subst hab; rfl

/-- 表外 `next_el` 恒等（junk 支；非空表；批 8 私件同证重落）。 -/
private theorem nextElOfNotMem' {s : List (ℕ × ℕ)} (hne : s ≠ []) {x : ℕ × ℕ}
    (hx : x ∉ s) : nextEl s x = x := by
  have hidx : s.idxOf x = s.length := List.idxOf_eq_length hx
  have hpos : 0 < s.length := List.length_pos_of_ne_nil hne
  show (if s.idxOf x = s.length - 1 then s.headD x
    else s.getD (s.idxOf x + 1) x) = x
  rw [if_neg (by omega : ¬(s.idxOf x = s.length - 1)), hidx,
    List.getD_eq_default s x (by omega)]

/-- nodup 表旋转后 `next_el` 函数不变（HOL `Seq2.next_el_rot_eq`；
批 8 私件同证重落——private 雷区：模块内不可见，消费侧各自重落）。 -/
private theorem nextElRotateFunc {s : List (ℕ × ℕ)} (hsn : s.Nodup) (k : ℕ) :
    nextEl (s.rotate k) = nextEl s := by
  refine funext fun z => ?_
  by_cases hz : z ∈ s.rotate k
  · have hmem : z ∈ s := List.mem_rotate.mp hz
    have hzl : 0 < (s.rotate k).length := List.length_pos_of_mem hz
    have hsl : 0 < s.length := List.length_pos_of_mem hmem
    have hiz : (s.rotate k).idxOf z < (s.rotate k).length :=
      List.idxOf_lt_length_iff.mpr hz
    have h1 : (s.rotate k)[(s.rotate k).idxOf z]'hiz = z := getElem_idxOf hz
    rw [List.getElem_rotate s k _ hiz] at h1
    have hz2 : s[s.idxOf z]'(List.idxOf_lt_length_iff.mpr hmem) = z :=
      getElem_idxOf hmem
    have hkey : ((s.rotate k).idxOf z + k) % s.length = s.idxOf z :=
      (hsn.getElem_inj_iff (hi := Nat.mod_lt _ hsl)
        (hj := List.idxOf_lt_length_iff.mpr hmem)).mp (h1.trans hz2.symm)
    show nextEl (s.rotate k) z = nextEl s z
    rw [nextEl_eq_getD hz, nextEl_eq_getD hmem,
      getD_eq_getElem_of_lt (Nat.mod_lt _ hzl),
      getD_eq_getElem_of_lt (Nat.mod_lt _ hsl),
      List.getElem_rotate s k _ (Nat.mod_lt _ hzl)]
    have hEq : (((s.rotate k).idxOf z + 1) % (s.rotate k).length + k)
        % s.length = (s.idxOf z + 1) % s.length := by
      rw [List.length_rotate s k, Nat.mod_add_mod]
      have hass2 : (s.rotate k).idxOf z + 1 + k
          = (s.rotate k).idxOf z + k + 1 := by omega
      rw [hass2, ← Nat.mod_add_mod, hkey]
    exact getElemCon (Nat.mod_lt _ hsl) (Nat.mod_lt _ hsl) hEq
  · rcases Nat.eq_zero_or_pos s.length with h0 | hpos0
    · have hs0 : s = [] := List.length_eq_zero_iff.mp h0
      subst hs0
      show nextEl (([] : List (ℕ × ℕ)).rotate k) z = nextEl [] z
      rfl
    · have hzm : z ∉ s := fun hc => hz (List.mem_rotate.mpr hc)
      have hne : s ≠ [] := by
        intro hc
        rw [hc] at hpos0
        simp at hpos0
      have hrk : s.rotate k ≠ [] := fun hc => hne (List.rotate_eq_nil_iff.mp hc)
      rw [nextElOfNotMem' hrk hz, nextElOfNotMem' hne hzm]

/-! ### §1 rot_final_list 章开章四件（tame_list.hl:12831-:12894） -/

/-- **HOL `rot_final_list`**（tame_list.hl:12831-:12845）
`!L r r'. final_list L r /\ uniq r /\ (?n. r' = rot n r) ==>
final_list L r'`——final_list 定义形逐点 ∀∈（批 7 槽）+
Seq2.next_el_rot_eq（↦ nextElRotateFunc，§0 重落）函数等式 rw +
Seq.mem_rot（↦ core List.mem_rotate）成员回喂。 -/
theorem rotFinalList {L : fgraph ℕ} {r r' : List (ℕ × ℕ)}
    (hf : finalListSpine L r) (hun : r.Nodup) {n : ℕ}
    (hr' : r' = r.rotate n) : finalListSpine L r' := by
  rw [hr']
  intro d hd
  rw [nextElRotateFunc hun n]
  exact hf d (List.mem_rotate.mp hd)

/-- **HOL `ALL2_MEM`**（tame_list.hl:12846-:12856）
`!P N N' r'. ALL2 P N N' /\ MEM r' N' ==> (?r. MEM r N /\ P r r')`
——ALL2 载体 = `List.Forall₂`（本 port 首次进场，见头注）；Forall₂
induction 双消：nil 支成员矛盾 `cases` 收，cons 支 head/tail 两向
匿名构造。泛型 `{α β}` 形（HOL `!P N N' r'` 全量化逐字）。 -/
theorem all2Mem {α β : Type*} {P : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ P l₁ l₂ →
      ∀ b ∈ l₂, ∃ a, a ∈ l₁ ∧ P a b := by
  intro l₁ l₂ h
  induction h with
  | nil => intro b hb; cases hb
  | cons hab _ ih =>
    intro r' hr'
    cases hr' with
    | head => exact ⟨_, List.mem_cons_self .., hab⟩
    | tail _ hm =>
      obtain ⟨r, hr, hP⟩ := ih r' hm
      exact ⟨r, List.mem_cons_of_mem _ hr, hP⟩

/-- **HOL `ALL2_rot_flatten`**（tame_list.hl:12858-:12873）
`ALL2 (\f1 f2. ?n. f2 = rot n f1) N N' ==> perm_eq (flatten N)
(flatten N')`——perm_eq 载体 = core `List.Perm`（同重数忠实镜像，
见头注载体决定）；induction cons 支：面级旋转 perm
（mathlib `List.rotate_perm`）+ ih + core `List.Perm.append` 拼接
（flatten_cons 定义式两侧归一）；HOL 基座 `Seq2.perm_eq0l` 面 =
`Perm.refl` 定义式吸收。 -/
theorem all2RotFlatten {N N' : List (List (ℕ × ℕ))}
    (h : List.Forall₂ (fun f1 f2 => ∃ n, f2 = f1.rotate n) N N') :
    N.flatten.Perm N'.flatten := by
  induction h with
  | nil => exact List.Perm.refl _
  | cons hab _ ih =>
    obtain ⟨n, hn⟩ := hab
    rw [List.flatten_cons, List.flatten_cons, hn]
    exact List.Perm.append (List.rotate_perm _ n).symm ih

/-- **HOL `loop_list_rot`**（tame_list.hl:12883-:12894）
`!L r n. uniq r /\ loop_list L r ==> loop_list L (rot n r)`
——loop_list 定义形逐点 ∀∈（批 5 槽）+ nextElRotateFunc 函数等式
rw + mem_rotate 成员回喂（HOL `Seq.mem_rot` 槽）。 -/
theorem loopListRot {L : fgraph ℕ} {r : List (ℕ × ℕ)} (hun : r.Nodup)
    (hloop : loopListSpine L r) (n : ℕ) : loopListSpine L (r.rotate n) := by
  intro x hx
  rw [nextElRotateFunc hun n]
  exact hloop x (List.mem_rotate.mp hx)

/-! ### §2 normal_list_rot 章（tame_list.hl:12896-:12989） -/

/-- **HOL `normal_list_rot`**（tame_list.hl:12896-:12943）
`!L N N'. good_list L /\ normal_list L N /\ all (final_list L) N /\
ALL2 (\f1 f2. ?n. f2 = rot n f1) N N' ==> normal_list L N'`——
五合取逐槽：flatten-Nodup = all2RotFlatten + `List.Perm.nodup`
（Seq2.perm_eq_uniq 面）；nonnil/f_last/loop_list 三槽 = all2Mem
拆证人（r ∈ N、s = rot n r）+ `List.rotate_eq_nil_iff`
（HOL rot_eq_nil :12875 纯消费零镜像）非空搬运 + finalListFLast
（批 31，f_last 槽；final_list 支经 rotFinalList 运输）+
loopListRot；node-SUBSET 槽 = `Perm.mem_iff` 集合换装
（Seq2.perm_eq_set_of_list_eq 面：Perm 载体下 `Set.ext` 两向同
perm，零收窄）后 hnorm.5 直取。 -/
theorem normalListRot {L : fgraph ℕ} {hL : GoodList L}
    {N N' : List (List (ℕ × ℕ))} (hnorm : NormalListSpine hL N)
    (hfinal : ∀ r ∈ N, finalListSpine L r)
    (hall2 : List.Forall₂ (fun f1 f2 => ∃ n, f2 = f1.rotate n) N N') :
    NormalListSpine hL N' := by
  have hperm : N.flatten.Perm N'.flatten := all2RotFlatten hall2
  refine ⟨hperm.nodup hnorm.1, ?_, ?_, ?_, ?_⟩
  · intro s hs'
    obtain ⟨r, hr, ⟨n, hn⟩⟩ := all2Mem hall2 s hs'
    intro hnil
    rw [hn, List.rotate_eq_nil_iff] at hnil
    exact hnorm.2.1 r hr hnil
  · intro s hs'
    obtain ⟨r, hr, ⟨n, hn⟩⟩ := all2Mem hall2 s hs'
    obtain ⟨hun, hne⟩ := normalListUniqNonnil hnorm hr
    have hne' : r.rotate n ≠ [] := fun hc => hne (List.rotate_eq_nil_iff.mp hc)
    rw [hn]
    exact finalListFLast L hne' (rotFinalList (hfinal r hr) hun rfl)
  · intro s hs'
    obtain ⟨r, hr, ⟨n, hn⟩⟩ := all2Mem hall2 s hs'
    obtain ⟨hun, -⟩ := normalListUniqNonnil hnorm hr
    rw [hn]
    exact loopListRot hun (hnorm.2.2.2.1 r hr) n
  · intro d hd
    have hset : {d' | d' ∈ N'.flatten} = {d' | d' ∈ N.flatten} := by
      ext x
      exact hperm.mem_iff.symm
    rw [hset]
    exact hnorm.2.2.2.2 d (hperm.mem_iff.mpr hd)

/-- **HOL `all_final_list_rot`**（tame_list.hl:12945-:12960）
`!L N N'. all (final_list L) N /\ normal_list L N /\
ALL2 (\f1 f2. ?n. f2 = rot n f1) N N' ==> all (final_list L) N'`
——`all` 谓词展开 ∀∈（Seq.allP 面零镜像）+ all2Mem 拆证人 +
rotFinalList 项式直投（uniq 支 = normalListUniqNonnil 第 1 合取）。 -/
theorem allFinalListRot {L : fgraph ℕ} {hL : GoodList L}
    {N N' : List (List (ℕ × ℕ))} (hfinal : ∀ r ∈ N, finalListSpine L r)
    (hnorm : NormalListSpine hL N)
    (hall2 : List.Forall₂ (fun f1 f2 => ∃ n, f2 = f1.rotate n) N N') :
    ∀ r ∈ N', finalListSpine L r := by
  intro r' hr'
  obtain ⟨r, hr, ⟨n, hn⟩⟩ := all2Mem hall2 r' hr'
  obtain ⟨hun, -⟩ := normalListUniqNonnil hnorm hr
  rw [hn]
  exact rotFinalList (hfinal r hr) hun rfl

/-- quotient_list_rot 点位 induction 私槽：ALL2 rot-rel 经 FST-双层
map 保持（HOL 证体尾段 LIST_INDUCT 双消 + `Seq.map_rot` 面；
mathlib `List.map_rotate` 一发 + 匿名构造；induction 目标独立无
依赖假设——revert 雷区免疫形）。 -/
private theorem forall2RotMapFst {N N' : List (List (ℕ × ℕ))}
    (h : List.Forall₂ (fun f1 f2 => ∃ n, f2 = f1.rotate n) N N') :
    List.Forall₂ (fun f1 f2 => ∃ n, f2 = f1.rotate n)
      (N.map (fun r => r.map (fun x => x.1)))
      (N'.map (fun r => r.map (fun x => x.1))) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hab _ ih =>
    obtain ⟨n, hn⟩ := hab
    refine List.Forall₂.cons ⟨n, ?_⟩ ih
    simp only [hn, List.map_rotate]

/-- **HOL `quotient_list_rot`**（tame_list.hl:12962-:12989，章
capstone）`!L N N'. good_list L /\ normal_list L N /\
is_edge_nondegenerate (hypermap_of_list L) /\ all (final_list L) N /\
ALL2 (\f1 f2. ?n. f2 = rot n f1) N N' ==> ALL2 (\f1 f2. ?n.
f2 = rot n f1) (quotient_list L N) (quotient_list L N')`——先立 N'
侧 normal_list/all_final 两槽（normalListRot/allFinalListRot 直投，
HOL 证体头段 CONJ_TAC 块）→ finalListQuotient（批 47）双侧换装
`quotientListSpine L N = N.map (fun r => r.map (·.1))`（HOL
`GMATCH_SIMP_TAC final_list_quotient` 槽）→ forall2RotMapFst 点位
induction 收口。 -/
theorem quotientListRot {L : fgraph ℕ} {hL : GoodList L}
    {N N' : List (List (ℕ × ℕ))} (hnorm : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hfinal : ∀ r ∈ N, finalListSpine L r)
    (hall2 : List.Forall₂ (fun f1 f2 => ∃ n, f2 = f1.rotate n) N N') :
    List.Forall₂ (fun f1 f2 => ∃ n, f2 = f1.rotate n)
      (quotientListSpine L N) (quotientListSpine L N') := by
  have hnorm' : NormalListSpine hL N' := normalListRot hnorm hfinal hall2
  have hfinal' : ∀ r ∈ N', finalListSpine L r := allFinalListRot hfinal hnorm hall2
  rw [finalListQuotient hnedg hnorm hfinal, finalListQuotient hnedg hnorm' hfinal']
  exact forall2RotMapFst hall2

/-! ### §3 ALL2_MAP2（tame_list.hl:12991-:12998） -/

/-- **HOL `ALL2_MAP2`**（tame_list.hl:12991-:12998）
`!P f l. ALL2 P l (MAP f l) <=> ALL (\a. P a (f a)) l`——List
induction 双向 Iff：正向 cases 两支（head 直取 / tail 回喂 ih）；
反向 cons 双构造直拼；`ALL (\a. P a (f a)) l` 面 ↦ `∀ a ∈ l, …`
（批 7 finalListSpine 同款逐点 ∀∈ 折算，Seq.all 面零镜像）。 -/
theorem all2Map2 {α β : Type*} {P : α → β → Prop} (f : α → β) (l : List α) :
    List.Forall₂ P l (l.map f) ↔ ∀ a ∈ l, P a (f a) := by
  induction l with
  | nil =>
    refine Iff.intro ?_ ?_
    · intro _ a ha
      cases ha
    · intro _
      exact List.Forall₂.nil
  | cons a t ih =>
    rw [List.map_cons]
    refine Iff.intro ?_ ?_
    · intro h
      cases h with
      | cons h1 h2 =>
        intro x hx
        cases hx with
        | head => exact h1
        | tail _ hm => exact ih.mp h2 x hm
    · intro h
      refine List.Forall₂.cons (h a List.mem_cons_self ..) ?_
      exact ih.mpr fun x hx => h x (List.mem_cons_of_mem _ hx)

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；八件正文 + 批 47 槽 finalListQuotient
预期零 sorryAx——探针九行全绿：八件仅 propext/Classical.choice/
Quot.sound 标准三轴，all2Mem/all2Map2 零公理；forall2RotMapFst 为
private 探针不可外引，其消费链经 quotientListRot 轴面旁证零 sorry）：
#print axioms Kepler.Text.TameSpine.rotFinalList
#print axioms Kepler.Text.TameSpine.all2Mem
#print axioms Kepler.Text.TameSpine.all2RotFlatten
#print axioms Kepler.Text.TameSpine.loopListRot
#print axioms Kepler.Text.TameSpine.normalListRot
#print axioms Kepler.Text.TameSpine.allFinalListRot
#print axioms Kepler.Text.TameSpine.quotientListRot
#print axioms Kepler.Text.TameSpine.all2Map2
#print axioms Kepler.Text.TameSpine.finalListQuotient
-/
