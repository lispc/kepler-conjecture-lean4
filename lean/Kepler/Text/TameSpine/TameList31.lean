/-
  Kepler.Text.TameSpine.TameList31 — B1 Tame_list 地基批 31：final_list 章
  开局（tamespine-port-plan §4 批次表 B1 行；接续批 30 =
  TameList30.lean，批 30 终点 = HOL :11287（dih2k_quotient_card_NF 已落）；
  本批起点 = HOL :11290 `final_list_f_last`。行号均按主仓
  reference/flyspeck（commit 1ce0353）实测）。

  **载体重侦察勘误（批 30 头注处方修正，入档首条）**：批 30 预记
  「final_list/f_last 真缺仅两 def（fLast/finalList）」——实测两 def 及
  partition 机器**早已在库**（批 5/7/9 的 Spine 族落定）：
  `fLastSpine`（TameList5.lean:105）、`finalListSpine`/`partsSpine`/
  `partitionIntoAtom0`/`partitionIntoAtom`（TameList7.lean:481/:462/
  :446/:457）、`partitionIntoAtom0r`/`partitionIntoAtom0rCases`/
  `partsPure`（批 9，TameList9.lean:676/:682/:817，`partsr` rfl 记档在
  批 9 头注）。本批零 f_last/final_list 新 def；唯一新 def =
  `listOfFaces`（face_rep 载体，list_hypermap-compiled.hl:26
  `list_of_faces L = MAP list_pairs L`）。同名异体警示：tame_list.hl
  :5190 `final_list_face` 语境的 list_of_faces 系 `MAP (find_face L)
  (list_of_darts L)` 另一桩（批 8 finalListFace 已按彼载体消费），
  face_rep 证体明写 `List_hypermap.list_of_faces`，无歧义按 :26 镜像。
  附带勘误：GoodListDefs 头注记 list_pairs 桩位 :19，主仓实测 :22。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:11290-:11366）：

  主件：`final_list_f_last` :11290-:11304
  `!L r. ~(r = []) /\ final_list L r ==> f_last L r`（证体七行）——
  final_list 章开局：自足面（每 dart 处 f_list 与 next_el 相合）的
  LAST 元处亦相合。

  同章四件随收：`face_rep` :11305-:11320 / `parts_nil` :11348-:11354 /
  `uniq_sing` :11356-:11357 / `parts1` :11359-:11366。
  `good_face_rep` :11321-:11347 留批 32（处方见头注尾）。

  证明层侦察定论：
  · final_list_f_last 七行逐槽：REWRITE[final_list;f_last;GSYM Seq.allP]
    ↦ 两 def 已在库（`finalListSpine` 定义形即逐点 ∀∈，零展开步）；
    MEM_LAST :1364 ↦ `List.getLast_mem`（`fLastSpine` 的 `getLast!`
    junk 槽经批 5 `getLast!EqGetLast` 非空折算）；ONCE_REWRITE
    [EQ_SYM_EQ] ↦ `.symm`——全件三 tactic 槽两行装配；
  · face_rep :11305：REWRITE[list_of_faces;MEM_MAP] ↦ `List.mem_map`
    证人直取（∃f0 ∈ L, listPairs f0 = f）；EXISTS x + ASM_REWRITE 后
    尾墙 MATCH_MP Seq.unzip1_zip + size_rot ↦ Lean core
    `List.map_fst_zip`（`l₁.length ≤ l₂.length → map Prod.fst
    (zip l₁ l₂) = l₁`）+ 私件 `lengthRotOne`（rot1 长度保持：nil/
    单件两支 rfl，双 cons 支 drop/take 定义式分件）；零新 unzip 机器
    （HOL lower_case/Seq.unzip1 改装面被 core zip 词典吸收，零镜像）；
  · parts_nil :11348：HOL 一行 REWRITE[partsr;partition_into_atom0r_cases]
    ↦ `show` 定义性换装 partitionIntoAtom0r（partsr 槽，批 9 头注 rfl
    记档同形）+ `partitionIntoAtom0rCases.1`（nil 方程槽，批 9）；
  · uniq_sing :11356：`uniq` ↦ `List.Nodup`（GoodListDefs 载体约定）
    ↦ `List.nodup_singleton`（Mathlib）一发；
  · parts1 :11359：HOL MATCH_MP parts_pure + ASM_SIMP[MEM;NOT_CONS_NIL;
    uniq_sing;LAST_CLAUSES] ↦ 批 9 `partsPure` 直取（单件表三前提：
    `List.cons_ne_nil`/`List.nodup_singleton`/mem_cons rfl + getLast!
    singleton 链 simp 槽——`getLast!` 无 singleton 专名，经
    getLast!_eq_getLast?_getD + getLast?_singleton + getD_some simp
    链自解），结论零修饰即本件（HOL CONCLUSION 同形 `[r]`）。

  依赖面：批链全批 1-30；在库 TameList5（fLastSpine/getLast!EqGetLast）/
  TameList7（finalListSpine/partsSpine/partitionIntoAtom0）/
  TameList9（partitionIntoAtom0r/partitionIntoAtom0rCases/partsPure）+
  Kepler.Assembly.GoodListDefs（listPairs/fList/nextEl/eList，fgraph ℕ
  具体层）+ Lean core List.map_fst_zip/mem_map/getLast_mem + Mathlib
  List.nodup_singleton。

  诚实记账：本批五件全真证，零止损件、零记账债；新 def 一枚
  （listOfFaces）；记批 30 头注载体处方勘误一条（首段）。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git
  写操作。批 32 接续点：HOL :11321 `good_face_rep`
  `!L f. good_list L /\ good_list_nodes L /\
  simple_hypermap (hypermap_of_list L) /\ MEM f (list_of_faces L) ==>
  (?f0. list_pairs f0 = f /\ MEM f0 L /\ MAP FST f = f0 /\ uniq f0 /\
  ~(f0 = []))`。处方（五槽两路）：①`list_pairs f0 = f`/`MEM f0 L`/
  `MAP FST f = f0` 三槽 = 本批 `faceRep` 直取；②`uniq f0` 槽经
  `simple_hypermap_uniq`（:9254，⇐ 向）⟸ `simple_hypermap_all_uniq`
  （:9210，证体链 list_pairs_not_uniq/uniq_flatten_uniq/
  dart_hypermap_of_list/face_of_list/MEM_hypermap_of_list_node/
  find_face_alt/find_pair_list_unique——完整 hypermap_of_list face
  API 章，章级工程量宜独占一批）；③`~(f0 = [])` 槽经 good_list 第 2
  合取（`GoodList` 的 `∀ l ∈ L, l ≠ []`，在库直取）。
  载体注：`good_list_nodes` 在库桩 `GoodListNodes = True`
  （Assembly.lean:1344，只钉语义待 hypermapOfList 构造落地后补本体），
  消费形直取 True 即可。
-/

import Kepler.Text.TameSpine.TameList30

namespace Kepler.Text.TameSpine

open Kepler.Assembly (listPairs nextEl eList fList)
open Kepler.Graphs (fgraph)

/-! ### §0 face_rep 载体：list_of_faces（list_hypermap-compiled.hl:26） -/

/-- HOL `list_of_faces`（list_hypermap-compiled.hl:26
`list_of_faces L = MAP list_pairs L`）逐句镜像。（同名异体警示见头注：
final_list_face :5190 语境系 `MAP (find_face L) (list_of_darts L)`
另一桩，批 8 finalListFace 已消费彼形。） -/
def listOfFaces (L : fgraph ℕ) : List (List (ℕ × ℕ)) := L.map listPairs

/-! ### §1 主件 final_list_f_last（tame_list.hl:11290-:11304） -/

/-- **HOL `final_list_f_last`**（tame_list.hl:11290-:11304）
`!L r. ~(r = []) /\ final_list L r ==> f_last L r`——final_list 章
开局：自足面的 LAST 元处亦相合。HOL 证体三槽逐字：all/allP 展开 ↦
`finalListSpine` 定义形逐点 ∀∈（批 7 在库，零展开步）；MEM_LAST :1364
↦ `List.getLast_mem`（`getLast!` junk 槽经批 5 `getLast!EqGetLast`
非空折算）；ONCE_REWRITE[EQ_SYM_EQ] ↦ `.symm`。 -/
theorem finalListFLast (L : fgraph ℕ) {r : List (ℕ × ℕ)} (hne : r ≠ [])
    (hf : finalListSpine L r) : fLastSpine L r := by
  -- MEM (LAST r) r 槽：getLast! junk 折算 + core getLast_mem
  have hmem : r.getLast! ∈ r := by
    rw [getLast!EqGetLast hne]
    exact List.getLast_mem hne
  -- HOL ONCE_REWRITE[EQ_SYM_EQ] 槽：final_list 槽实例取对称
  exact (hf (r.getLast!) hmem).symm

/-! ### §2 face_rep（tame_list.hl:11305-:11320） -/

/-- 私件（face_rep 尾墙载体）：rot1 表长保持——HOL `Seq.size_rot` 面
（rot1 = drop 1 ++ take 1 内联，listPairs 桩位同形）。nil/单件两支
定义式，双 cons 支 drop/take 定义式分件后长度算术一发。 -/
private theorem lengthRotOne {α : Type*} : ∀ l : List α,
    (l.drop 1 ++ l.take 1).length = l.length
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
      have h1 : (a :: b :: t).drop 1 = b :: t := rfl
      have h2 : (a :: b :: t).take 1 = [a] := rfl
      have h3 : (a :: b :: t).length = (b :: t).length + 1 := rfl
      have h4 : [a].length = 1 := rfl
      rw [h1, h2, h3, List.length_append, h4]

/-- 私件（face_rep 尾墙）：`MAP FST (list_pairs l) = l`——HOL
Seq.unzip1_zip + Seq.size_rot 组合面的 zip-直写形（core
`List.map_fst_zip` 消费，长度前提即 `lengthRotOne`）。 -/
private theorem mapFstListPairs {α : Type*} : ∀ l : List α,
    (listPairs l).map Prod.fst = l
  | [] => rfl
  | a :: t => by
      show (List.zip (a :: t) ((a :: t).drop 1 ++ List.take 1 (a :: t))).map
        Prod.fst = a :: t
      rw [List.map_fst_zip (lengthRotOne (a :: t)).symm.le]

/-- **HOL `face_rep`**（tame_list.hl:11305-:11320）
`!L f. MEM f (list_of_faces L) ==> (?f0. list_pairs f0 = f /\
MEM f0 L /\ MAP FST f = f0)`——list_of_faces 每元皆 L 某面的
list_pairs 像，且 MAP FST 回投零损。HOL 证体：MEM_MAP 证人直取 +
尾墙 unzip1_zip/size_rot（↦ core List.map_fst_zip + `mapFstListPairs`）；
lower_case/Seq.unzip1 改装面零镜像。 -/
theorem faceRep (L : fgraph ℕ) (f : List (ℕ × ℕ))
    (hf : f ∈ listOfFaces L) :
    ∃ f0 : List ℕ, listPairs f0 = f ∧ f0 ∈ L ∧ f.map Prod.fst = f0 := by
  -- MEM f (MAP list_pairs L) 槽：证人 f0 ∈ L 直接展开
  obtain ⟨f0, hf0, hEq⟩ := List.mem_map.mp hf
  refine ⟨f0, hEq, hf0, ?_⟩
  -- 尾墙：f 换装 list_pairs f0 后 MAP FST 零损（unzip1_zip 槽）
  rw [← hEq]
  exact mapFstListPairs f0

/-! ### §3 parts 章三件（tame_list.hl:11348/:11356/:11359） -/

/-- **HOL `parts_nil`**（tame_list.hl:11348-:11354）`!L. parts L [] =
[]`——HOL 一行 REWRITE[partsr;partition_into_atom0r_cases]：partsr 槽
`show` 定义性换装（批 9 头注 rfl 记档同形）+ nil 方程槽
`partitionIntoAtom0rCases.1`（批 9）。 -/
theorem partsNil (L : fgraph ℕ) : partsSpine L [] = [] := by
  show partitionIntoAtom0r (fun d => fList L (eList d)) [] [] = []
  exact (partitionIntoAtom0rCases (fun d => fList L (eList d)) [] [] (0, 0)).1

/-- **HOL `uniq_sing`**（tame_list.hl:11356-:11357）`uniq [x]`——
`uniq` ↦ `List.Nodup`（GoodListDefs 载体约定）↦ `List.nodup_singleton`
一发。 -/
theorem uniqSing {α : Type*} (x : α) : [x].Nodup :=
  List.nodup_singleton x

/-- **HOL `parts1`**（tame_list.hl:11359-:11366）`!L h. parts L [h] =
[[h]]`——HOL MATCH_MP parts_pure + ASM_SIMP[MEM;NOT_CONS_NIL;uniq_sing;
LAST_CLAUSES] ↦ 批 9 `partsPure` 直取（单件表三前提 simp 槽：
`getLast!` 无 singleton 专名，经 getLast!_eq_getLast?_getD +
getLast?_singleton + getD_some 链自解）。 -/
theorem parts1 (L : fgraph ℕ) (h : ℕ × ℕ) : partsSpine L [h] = [[h]] :=
  partsPure L (List.cons_ne_nil h []) (uniqSing h)
    (by intro x hx
        rw [List.mem_singleton] at hx
        subst hx
        exact Or.inl (by simp))

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；五件预期标准三
[propext, Classical.choice, Quot.sound]）：
#print axioms Kepler.Text.TameSpine.finalListFLast
#print axioms Kepler.Text.TameSpine.faceRep
#print axioms Kepler.Text.TameSpine.partsNil
#print axioms Kepler.Text.TameSpine.uniqSing
#print axioms Kepler.Text.TameSpine.parts1
-/
