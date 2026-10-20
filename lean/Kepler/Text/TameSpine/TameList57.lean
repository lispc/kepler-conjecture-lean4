/-
  Kepler.Text.TameSpine.TameList57 — B1 Tame_list 地基批 57：
  inj_on_list_of_faces / inj_on_list_of_darts 章收口（tamespine-port-plan §4
  批次表 B1 行；接续批 56 = TameList56.lean，批 56 终点 = HOL :13942
  （size_flatten_le）；本批起点 = HOL :13944 `inj_on_list_of_faces`。
  行号均按主仓 reference/flyspeck（commit 1ce0353）实测；批 56 尾注预记
  :13944/:13959 两锚点与实测一致，零偏移。

  载体侦察裁定（批 56 尾注预记面的对拍结论）：

  - **map_list_pairs 载体既档**（批 56 预记「开工先核」命中）：HOL
    :1037 `map_list_pairs`（`!phi x. list_pairs (MAP phi x) = MAP
    (\u. phi (FST u),phi (SND u)) (list_pairs x)`）批 2 记账为
    「TameLp la7 先行已覆盖」，实测在册 `TameLp.la7_listPairs_map`
    （TameLp.lean:4522，{α β} 泛化形；RHS 以 `Prod.map phi phi` 书写，
    与 `(fun u => (phi u.1, phi u.2))` 面 defeq 直投——批 2
    la7_listOfDarts_map 同槽先例）；同族 :1053 `map_list_of_darts`
    实测在册 `TameLp.la7_listOfDarts_map`（TameLp.lean:4529，fgraph ℕ/
    ℕ→ℕ 具体层）。
  - **inj_on 前提冗余记档**：HOL inj_on_list_of_faces/inj_on_list_of_darts
    的 `inj_on phi (elements_of_list L)` 前提在 HOL 证体中即未消费
    （:13950-:13955 全程 list_of_faces/MAP_o/MAP_EQ/map_list_pairs 机制
    链，无 inj_on 触点；:13959 对偶面 AP_TERM 后 GMATCH 的也是
    inj_on_list_of_faces 本体）——载体 map_list_pairs 无条件。两件 Lean
    镜像按语句逐字保留前提（elements_of_list ↦ TameLp.elementsOfList
    批 5 既档、inj_on ↦ Set.InjOn 批 2 既档、ℕ→ℕ 具体层按 TameList1/25
    体例）而证体零消费。
  - **list_of_faces 载体既档**：`list_of_faces L = MAP list_pairs L`
    （list_hypermap.vhl:36）↦ 批 31 `listOfFaces`（TameList31.lean:100，
    fgraph ℕ 面）；list_of_darts ↦ Assembly `listOfDarts`
    （GoodListDefs.lean:38，批 2 载体）。两载体均 ℕ 冻结，故章主体
    `phi` 落 ℕ→ℕ 具体层（批 1 la7_mapGoodList 同例）。

  新雷区（本批实测记档）：
  - **双 map_map 同目标需双实例显式钉参**：章主体两翼各是一次
    `(map g l).map f` 嵌套（LHS `map list_pairs (map (map phi) L)`、RHS
    `map (map ·) (map list_pairs L)`）——`rw [List.map_map]` 裸写只吃
    左翼首个实例化（rw 一次遍历定实例），须 `List.map_map (g := ...)
    (f := ...)` 具名钉参各发一发（la7_listOfDarts_map 批 2 单发形在本
    章不适用：彼处 RHS 带 flatten 墙无嵌套 map）；钉参后 map_congr_left
    逐点槽对 `Function.comp` 应用面走 defeq 展开（comp 定义式 + β +
    Prod.map 结构 η，批 2 同槽）。
  - **iterate 双发逐阶的 congrArg 桥**：final_list_power_fn 归纳步在
    `iterate_succ_apply'` 双发后目标两侧轨道点不同侧
    （`fList L ((fList L)^[i] d)` vs `nextEl r ((nextEl r)^[i] d)`），
    hf 槽（finalListSpine 逐点）只对 `(nextEl r)^[i] d ∈ r` 侧成立
    ——先 `congrArg (fList L) ih` 把左轨换装到右轨点再 `.trans` 喂 hf
    （直接 `hf _` 会把 ih 当定义性相等误用，非 rfl 面）。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:13944-:14054，八件）：

  §1 主件：`inj_on_list_of_faces` :13944-:13956 ↦ injOnListOfFaces（真证；
    REWRITE[list_of_faces] ↦ listOfFaces 定义形 show 展开；GSYM MAP_o +
    o_THM 面 ↦ List.map_map 双实例具名钉参（新雷区一）；MAP_EQ 面 ↦
    List.map_congr_left，逐点槽 = la7_listPairs_map phi l 直投）；
    `inj_on_list_of_darts` :13959-:13971 ↦ injOnListOfDarts（真证；HOL
    list_of_darts_alt + MAP_flatten + AP_TERM + inj_on_list_of_faces
    四步被 la7_listOfDarts_map 一发吸收——机制简化记档非语义损失，
    语句含冗余前提逐字保留）。
  §2 边界随收三件：`tl_eq_nil` :13997-:14004 ↦ tl_eqNil（cases 两层——
    HOL CONS_HD_TL/CONS_11 两发同构；cons 支 tail/head! 走 rfl 定义式
    归一 show，TL ↦ List.tail、HD ↦ head!（批 52/11 载体））；
    `final_list_power_fn` :14016-:14033 ↦ finalListPowerFn（i 归纳 +
    iterate 零支 rfl + iterate_succ_apply' 双发逐阶（新雷区二）；
    final_list ↦ 批 7 finalListSpine 定义形；f_list ↦ Assembly fList
    （GoodListDefs.lean:62）；next_el ↦ 批 2 nextEl；POWER ↦
    Function.iterate（批 12/56 载体）；Seq.allP 面 ↦ ∀∈ 体例；
    Seq2.mem_next_el 槽（HOL :14031）= nextEl_mem_of_mem
    （TameLp.lean:3614）迭代化私件 nextElIterateMem）；`size2_cons`
    :14036-:14054 ↦ size2Cons（cases 三层——HOL list_CASES 逐层同构；
    nil/单件支 simp at h 收 False，超长支 length_cons simp only +
    omega 尾墙，恰长支 ⟨a,b,rfl⟩ 直投）。
  §3 记档不落三件：`maxn_MAX` :13974（ssreflect maxn = MAX 库内部同义
    词，Lean 唯一载体 max——批 2 :305 minn_MIN 同面先例）；
    `minimal_min_num` :13983（minimal = min_num 同面同先例）；
    `MEM_TL` :14007（core `List.mem_of_mem_tail`
    （Init/Data/List/Lemmas.lean:1018）逐字同语句且空表支 junk 安全
    ——Lean 形免 `~(s=[])` 前提：`MEM x (TL [])` 恒 False）。

  诚实记账：五件落件全真证（injOnListOfFaces/injOnListOfDarts/tl_eqNil/
  finalListPowerFn/size2Cons，含私件 nextElIterateMem），零 sorry、零
  止损件、零记账债；新 def 零枚。
  范围决策：批 57 射程收口至 :14054（inj_on 章两件 + 边界随收三件 +
  记档不落三件——自然边界：下一件 :14057 `list_pairs_core` 起为
  normal_list/core/parts 新章）。
  红线遵守：零既有文件触碰、零 git 写操作。
  批 58 接续点：HOL :14057 `list_pairs_core`
  `!L N r. normal_list L N /\ is_edge_nondegenerate (hypermap_of_list L)
  /\ good_list L /\ MEM r N /\ all uniq L ==> list_pairs (core L r) =
  MAP LAST (parts L r)`（依赖 `core` 载体与 :13926 前已档
  `parts_list_pairs`——开工先核两载体在册性；其后续件序列
  :14078 `list_pairs_parts`（若有）按射程收口）。
-/

import Kepler.Text.TameSpine.TameList56

namespace Kepler.Text.TameSpine

open Kepler.Assembly (listPairs listOfDarts nextEl fList)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (elementsOfList la7_listPairs_map la7_listOfDarts_map
  nextEl_mem_of_mem)

/-! ### §1 inj_on 章（tame_list.hl:13944/:13959） -/

/-- **HOL `inj_on_list_of_faces`**（tame_list.hl:13944-:13956
`!L phi. inj_on phi (elements_of_list L) ==> list_of_faces (MAP (MAP phi) L) =
MAP (MAP (\u. phi (FST u),phi (SND u))) (list_of_faces L)`）。
证体：list_of_faces 定义形 show 展开（HOL REWRITE[List_hypermap.list_of_faces]）；
GSYM MAP_o + o_THM 面 ↦ List.map_map 双实例具名钉参（LHS/RHS 各一发，
新雷区一）；MAP_EQ 面 ↦ List.map_congr_left，逐点槽 = la7_listPairs_map
（tame_list.hl:1037 map_list_pairs，批 2 既档）直投。inj_on 前提 HOL
证体即未消费（冗余前提逐字保留，载体裁定记档）。 -/
theorem injOnListOfFaces (L : fgraph ℕ) (phi : ℕ → ℕ)
    (_hinj : Set.InjOn phi (elementsOfList L)) :
    listOfFaces (L.map (List.map phi))
      = (listOfFaces L).map (fun l => l.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))) := by
  show (L.map (List.map phi)).map listPairs
      = (L.map listPairs).map (fun l => l.map (fun u : ℕ × ℕ => (phi u.1, phi u.2)))
  rw [List.map_map (g := listPairs) (f := List.map phi),
    List.map_map (g := fun l => l.map (fun u : ℕ × ℕ => (phi u.1, phi u.2)))
      (f := listPairs) (l := L)]
  exact List.map_congr_left (fun l _ => la7_listPairs_map phi l)

/-- **HOL `inj_on_list_of_darts`**（tame_list.hl:13959-:13971
`!L phi. inj_on phi (elements_of_list L) ==> list_of_darts (MAP (MAP phi) L) =
(MAP (\u. phi (FST u),phi(SND u)) (list_of_darts L))`）。
HOL 证体四步（list_of_darts_alt + MAP_flatten + AP_TERM_TAC +
inj_on_list_of_faces）被 TameLp la7_listOfDarts_map（:4529，即
tame_list.hl:1053 map_list_of_darts 无条件形，批 2 既档）一发吸收
——机制简化记档非语义损失；inj_on 前提同上冗余逐字保留。 -/
theorem injOnListOfDarts (L : fgraph ℕ) (phi : ℕ → ℕ)
    (_hinj : Set.InjOn phi (elementsOfList L)) :
    listOfDarts (L.map (List.map phi))
      = (listOfDarts L).map (fun d : ℕ × ℕ => (phi d.1, phi d.2)) :=
  la7_listOfDarts_map L phi

/-! ### §2 边界随收（tame_list.hl:13997/:14016/:14036） -/

/-- **HOL `tl_eq_nil`**（tame_list.hl:13997-:14004
`!s. ~(s = []) ==> (TL s = [] <=> s = [HD s])`）。
TL ↦ List.tail、HD ↦ head!（批 52/11 载体）；cases 两层（HOL
CONS_HD_TL/CONS_11 两发同构），cons 支 tail/head! 定义式 rfl 归一
show；空表支 absurd（非空前提封死 junk 面，head! 雷区体例）。 -/
theorem tl_eqNil {α : Type*} [Inhabited α] {s : List α} (hs : s ≠ []) :
    s.tail = [] ↔ s = [s.head!] := by
  cases s with
  | nil => exact absurd rfl hs
  | cons a t =>
    show t = [] ↔ a :: t = [a]
    cases t with
    | nil => simp
    | cons b t' => simp

/-- next_el 轨道不出表（HOL Seq2.mem_next_el 的 Function.iterate 迭代
形，tame_list.hl:14016 证体 :14031 槽件）——私件同证重推导体例。 -/
private theorem nextElIterateMem {r : List (ℕ × ℕ)} {d : ℕ × ℕ} (hd : d ∈ r)
    (i : ℕ) : (nextEl r)^[i] d ∈ r := by
  induction i with
  | zero => exact hd
  | succ _ ih =>
    rw [Function.iterate_succ_apply']
    exact nextEl_mem_of_mem ih

/-- **HOL `final_list_power_fn`**（tame_list.hl:14016-:14033
`!i L r. final_list L r ==> all (\d. (f_list L POWER i) d =
(next_el r POWER i) d) r`）。
final_list ↦ finalListSpine（批 7，定义形即 ∀∈ 零展开）；f_list ↦
Assembly fList（GoodListDefs.lean:62）；next_el ↦ 批 2 nextEl；POWER ↦
Function.iterate（批 12/56 载体）；Seq.allP 面 ↦ ∀∈ 体例。
i 归纳：零支 rfl（iterate_zero 定义式）；归纳步 iterate_succ_apply'
双发逐阶 + congrArg (fList L) ih 左轨换装桥（新雷区二）+ hf 逐点槽
（点 = `(nextEl r)^[i] d`，出表性由私件 nextElIterateMem 兜）。
HOL POWER_0/POWER;o_THM 两步机制面被 iterate 零支/apply' 吸收。 -/
theorem finalListPowerFn (i : ℕ) (L : fgraph ℕ) (r : List (ℕ × ℕ))
    (hf : finalListSpine L r) : ∀ d ∈ r, (fList L)^[i] d = (nextEl r)^[i] d := by
  intro d hd
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (congrArg (fList L) ih).trans
      (hf ((nextEl r)^[i] d) (nextElIterateMem hd i))

/-- **HOL `size2_cons`**（tame_list.hl:14036-:14054
`!xs. sizel xs = 2 ==> (?a b. xs = [a;b])`）。
sizel ↦ List.length；HOL list_CASES 三层 cases 逐层同构：nil/单件支
simp at h 收 False（length 归一撞数字墙），超长支 length_cons
simp only + omega 尾墙（复合 length 原子化体例），恰长支
⟨a,b,rfl⟩ 直投。 -/
theorem size2Cons {α : Type*} {xs : List α} (h : xs.length = 2) :
    ∃ a b, xs = [a, b] := by
  cases xs with
  | nil => simp at h
  | cons a t =>
    cases t with
    | nil => simp at h
    | cons b t' =>
      cases t' with
      | nil => exact ⟨a, b, rfl⟩
      | cons c t'' =>
        simp only [List.length_cons] at h
        omega

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；五件正文全绿零 sorryAx——
#print axioms Kepler.Text.TameSpine.injOnListOfFaces
#print axioms Kepler.Text.TameSpine.injOnListOfDarts
#print axioms Kepler.Text.TameSpine.tl_eqNil
#print axioms Kepler.Text.TameSpine.finalListPowerFn
#print axioms Kepler.Text.TameSpine.size2Cons
-/
