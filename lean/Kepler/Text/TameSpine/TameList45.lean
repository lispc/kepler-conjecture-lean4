/-
  Kepler.Text.TameSpine.TameList45 — B1 Tame_list 地基批 45：sumn/sizel
  算术章（tamespine-port-plan §4 批次表 B1 行；接续批 44 =
  TameList44.lean，批 44 终点 = HOL :12590；本批起点 = HOL :12593
  `sumn_cons`。行号均按主仓 reference/flyspeck（commit
  1ce0353）实测。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:12593-:12656）：

  件一：`sumn_cons` :12593-:12600
  `!h hs. sumn (h::hs) = h + sumn hs` ↦ `sumnCons`（真证）。
  Seq.sumn = foldr (+) 0（seq-compiled.hl:3408）↦ core List.sum
  （v4.32.2 Init/Data/List/Basic.lean:2067，[Add α][Zero α] 泛形，
  ℕ 数面实例同形）；sumn_cons 即 core List.sum_cons（:2071，rfl
  面）直投。

  件二：`sumn_size` :12601-:12610
  `!a. sumn (MAP (\u. 1) a) = sizel a` ↦ `sumnSize`（真证）。
  HOL 证体 LIST_INDUCT 两发 + sumn_cons + LENGTH；Lean 面同链
  induction：nil rfl 面、cons 段 map_cons + sum_cons + ih +
  omega（1 + t.length 与 t.length + 1 非 defeq，arith 桥走 omega）。

  件三：`sumn_le` :12612-:12631
  `!f g u. (!x. MEM x u ==> f x <= g x) ==> sumn (MAP f u) <=
  sumn (MAP g u)` ↦ `sumnLe`（真证）。HOL 证体 LIST_INDUCT +
  sumn_cons + LE_TRANS 两段（逐点槽 + ih 槽，两发加法单调）；Lean
  面同链 induction + Nat.add_le_add（core Init/Data/Nat/Basic.lean
  :514）。批 44 预记 "Mathlib sum_le_sum（to_additive 形）在册"
  复核为不对口：Algebra/Order/BigOperators/Group/List.lean 的
  to_additive sum_le_sum 全数 Forall₂/Sublist 面（:27/:38/:54/:62），
  逐点 MEM 槽 map 面无现成件（Finset.sum_le_sum 是 Finset 面，
  TameLp 在册但 List 面不通）——sumnLe induction 自证（如实记账）。

  章末 capstone：`normal_list_size_bound` :12633-:12656
  `!L N. normal_list L N ==> sizel N <= sizel (list_of_darts L)`
  ↦ `normalListSizeBound`（真证）。HOL 证体 LE_TRANS 过
  sizel (flatten N) 双段：第 1 段 size_flatten + shape 把
  sizel (flatten N) 折成 sumn (map sizel N)，sumn_size +
  sumn_le（逐点 1 <= sizel 段，1 <= n <=> ~(n=0) 桥 + size_eq0 +
  normal_list_uniq_nonnil）收 sizel N <= sizel (flatten N)；第 2 段
  Seq.uniq_leq_size（uniq 槽 normal_list、子集槽
  normal_list_list_of_darts + Seq.allP）收 sizel (flatten N) <=
  sizel (list_of_darts L)。Lean 面同链 calc 双段：sumnSize +
  sumnLe（逐点 1 ≤ s.length 槽 = NormalListSpine 合取项 2
  all-nonnil + List.length_eq_zero_iff 换装 + Nat.succ_le_of_lt）
  + sizeFlattenSpine ← 向；uniq_leq_size 段 = Batteries
  List.subperm_of_subset（Nodup 槽 = 合取项 1 N.flatten.Nodup
  直配）+ List.Subperm.length_le 两投影。

  载体折算盘点（批 44 头注预记侦察面，经全库 grep（含 LocalAuto
  族）+ 工具链（core v4.32.2/mathlib/batteries 全量）对拍复核）：
  - `Seq.sumn`（seq-compiled.hl:3408 `sumn = foldr (+) 0`）↦ core
    `List.sum`（Init/Data/List/Basic.lean:2067）；
  - `Seq.sizel`（seq-compiled.hl:18 `sizel = LENGTH`）↦
    `List.length`（批 3 以降全链惯例）；
  - `Seq.shape`（seq-compiled.hl:3671 `shape = map sizel`）↦ 内联
    `List.map List.length`（定义件直折算，size_flatten 一步并入）；
  - `Seq.size_flatten`（seq-compiled.hl:3690-:3691）= 本批
    sizeFlattenSpine 新落地（Mathlib `List.length_flatten` 件名本
    工具链确认不在册——批 44 预记复核坐实；induction 自证：
    flatten_cons + length_append + sum_cons 三方程 rfl 链）；
  - `Seq.uniq_leq_size`（seq-compiled.hl:2261-:2263）= Batteries
    `List.subperm_of_subset`（Batteries/Data/List/Perm.lean:138，
    签名 `(d : Nodup l₁) (H : l₁ ⊆ l₂)`，Nodup 槽形）+
    `List.Subperm.length_le`（Perm.lean:58）两投影（批 44 预记
    "subperm_of_subset 在册" 兑现，Nodup 槽直配 NormalListSpine
    合取项 1）；
  - `Seq.size_eq0`（seq-compiled.hl:1449-:1450 `(sizel s = 0) <=>
    (s = [])`）↦ core `List.length_eq_zero_iff`（Init/Data/List/
    Lemmas.lean:113）换装 + arith 桥（1 ≤ n ⇔ ~(n = 0)）收；
  - `normal_list` = 批 5 NormalListSpine（TameList5.lean:127；
    合取项 1 = uniq (flatten N) 进 subperm Nodup 槽、合取项 2 =
    all-nonnil 进 sumn_le 逐点槽）；
  - `normal_list_uniq_nonnil`（tame_list.hl:4498-:4500
    `!L N r. normal_list L N /\ MEM r N ==> (uniq r /\ ~(r = []))`，
    段级形）= 批 6 normalListUniqNonnil（TameList6.lean:630）；
    本批只消费其 all-nonnil 槽（NormalListSpine 合取项 2 直取，
    免经批 6 组装件）；
  - `normal_list_list_of_darts`（tame_list.hl:3643-:3647）= 批 5
    normalListListOfDarts（TameList5.lean:156）；⊆ 槽直喂
    subperm_of_subset（HOL Seq.allP 面零折算）；
  - `Seq.sumn0`/`Seq.all`/`upper_case`/`lower_case`/`MAP`/`MEM`
    等定义展开件 = Lean 面 rfl/simp 归一零折算。
  全库 grep（含 LocalAuto 族）sumnCons/sumnSize/sumnLe/
  sizeFlattenSpine/normalListSizeBound 五件名零撞车零现成载体
  ——镜像本体即本批件。

  新落地载体：sizeFlattenSpine 一件（Seq.size_flatten 换装，
  seq-compiled 领土）。私件：零。

  诚实记账：五件全真证，零新 def、零 sorry、零止损件、零记账债。
  sumnLe/sizeFlattenSpine 两件 induction 自证系批 44 预记偏差的
  如实兑现（sum_le_sum to_additive 形不对口/List.length_flatten
  不在册，见上）。范围决策：批 45 射程收口至 :12656（sumn/sizel
  算术章全章毕）；:12658 `connected_induction` 换章
  （connected_hypermap/comb_component/contour 领土），留批 46。
  红线遵守：零既有文件触碰、零 git 写操作。
  批 46 接续点：HOL :12658 `connected_induction`
  （connected_hypermap 章开章；侦察面：connected_hypermap/
  number_of_components/set_of_components/comb_component/
  is_in_component/existence_contour/lemma_def_contour 全族开工
  对拍）。
-/

import Kepler.Text.TameSpine.TameList44

namespace Kepler.Text.TameSpine

open Kepler.Assembly (GoodList listOfDarts)
open Kepler.Graphs (fgraph)

/-! ### §1 sumn 基础三件（tame_list.hl:12593-:12631） -/

/-- **HOL `sumn_cons`**（tame_list.hl:12593-:12600）
`!h hs. sumn (h::hs) = h + sumn hs`——Seq.sumn = foldr (+) 0 ↦
core List.sum 换装，sumn_cons 即 List.sum_cons（rfl 面）直投。 -/
theorem sumnCons {h : ℕ} {hs : List ℕ} : (h :: hs).sum = h + hs.sum :=
  List.sum_cons

/-- **HOL `sumn_size`**（tame_list.hl:12601-:12610）
`!a. sumn (MAP (\u. 1) a) = sizel a`——LIST_INDUCT 两发，cons 段
sumn_cons + LENGTH 后 arith 桥 omega 收。 -/
theorem sumnSize {α : Type*} (a : List α) :
    (a.map fun _ => (1:ℕ)).sum = a.length := by
  induction a with
  | nil => rfl
  | cons _ t ih =>
    show (1:ℕ) + (t.map fun _ => (1:ℕ)).sum = t.length + 1
    rw [ih]
    omega

/-- **HOL `sumn_le`**（tame_list.hl:12612-:12631）
`!f g u. (!x. MEM x u ==> f x <= g x) ==> sumn (MAP f u) <=
sumn (MAP g u)`——LIST_INDUCT + sumn_cons + LE_TRANS 两段
（逐点槽 + ih 槽）；Lean 面同链 induction + Nat.add_le_add
（Mathlib sum_le_sum to_additive 形为 Forall₂/Sublist 面，逐点
map 面无现成件，自证——头注记账）。 -/
theorem sumnLe {α : Type*} {f g : α → ℕ} {u : List α}
    (h : ∀ x ∈ u, f x ≤ g x) : (u.map f).sum ≤ (u.map g).sum := by
  induction u with
  | nil => exact Nat.le_refl _
  | cons a t ih =>
    show f a + (t.map f).sum ≤ g a + (t.map g).sum
    exact Nat.add_le_add (h a List.mem_cons_self ..)
      (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

/-! ### §2 normal_list_size_bound（tame_list.hl:12633-:12656） -/

/-- **HOL `Seq.size_flatten`**（seq-compiled.hl:3690-:3691；
`shape = map sizel`（:3671）一步内联）
`sizel (flatten ss) = sumn (shape ss)`——Mathlib
List.length_flatten 件名本工具链不在册（批 44 预记复核坐实），
induction 自证：flatten_cons + length_append + sum_cons 三方程
rfl 链。 -/
theorem sizeFlattenSpine {α : Type*} (ss : List (List α)) :
    ss.flatten.length = (ss.map List.length).sum := by
  induction ss with
  | nil => rfl
  | cons s t ih =>
    show (s ++ t.flatten).length = List.length s + (t.map List.length).sum
    rw [List.length_append, ih]

/-- **HOL `normal_list_size_bound`**（tame_list.hl:12633-:12656）
`!L N. normal_list L N ==> sizel N <= sizel (list_of_darts L)`
——LE_TRANS 过 sizel (flatten N) 双段：sumn_size + sumn_le 段
（逐点 1 ≤ sizel 槽 = NormalListSpine 合取项 2 all-nonnil +
size_eq0 换装）+ Seq.uniq_leq_size 段（uniq 槽 = 合取项 1
N.flatten.Nodup、子集槽 = normal_list_list_of_darts，Batteries
subperm_of_subset + Subperm.length_le 两投影）。 -/
theorem normalListSizeBound {L : fgraph ℕ} {hL : GoodList L}
    {N : List (List (ℕ × ℕ))} (h : NormalListSpine hL N) :
    N.length ≤ (listOfDarts L).length := by
  -- 第 1 段：sizel N <= sizel (flatten N)（HOL sumn_size + shape +
  -- sumn_le 逐点段）
  have h1 : N.length ≤ N.flatten.length := by
    have hpt : ∀ s ∈ N, (1:ℕ) ≤ s.length := fun s hs =>
      Nat.succ_le_of_lt
        (Nat.pos_of_ne_zero (List.length_eq_zero_iff.not.mpr (h.2.1 s hs)))
    calc N.length = (N.map fun _ => (1:ℕ)).sum := (sumnSize N).symm
      _ ≤ (N.map List.length).sum := sumnLe hpt
      _ = N.flatten.length := (sizeFlattenSpine N).symm
  -- 第 2 段：sizel (flatten N) <= sizel (list_of_darts L)
  --（HOL Seq.uniq_leq_size 槽：Nodup + 子集）
  exact h1.trans (List.Subperm.length_le
    (List.subperm_of_subset h.1 (normalListListOfDarts h)))

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；五件预期零 sorryAx）：
#print axioms Kepler.Text.TameSpine.sumnCons
#print axioms Kepler.Text.TameSpine.sumnSize
#print axioms Kepler.Text.TameSpine.sumnLe
#print axioms Kepler.Text.TameSpine.sizeFlattenSpine
#print axioms Kepler.Text.TameSpine.normalListSizeBound
-/
