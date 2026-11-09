/-
  JcajyduAqLeaf8W05 — AQ8 波 0.5：六件共享上游（AQ8/AQ9 双收益）。

  ┌─ 件目与 HOL 锚 ───────────────────────────────────────────────
  │ ① fstEqNextYtransV0   AQ1.hl:851（= HOJODCM FST_EQ_NEXT_YTRANS）
  │ ② fstEqPrevZtransV0   AQ1.hl:796（= HOJODCM FST_EQ_PREV_ZTRANS）
  │ ③ fstNListPower       LEBHIRJ.hl:52（HOL FST_N_LIST_POWER）
  │ ④ goodListUniq        list_hypermap.vhl:820（HOL good_list_uniq）
  │ ⑤ listExtPowerInDarts vhl:729（HOL list_ext_power_in_darts）
  │ ⑥ hdMap               tame_list.hl:4772（HOL HD_MAP）
  └────────────────────────────────────────────────────────────────

  ┌─ 内容级去重扫描（全 6 名；名字 ≠ 内容，见 DELIVERY AQ8W05-4）──
  │ ① 零命中：AQ1 车道明知此二件，改用替代证法（`(fList d).1 = d.2`
  │    + 同面首点互异），见 JcajyduAqSplit1D.lean:21 记档；公开件未落。
  │ ② 同上（Split1D:22 同一记档）。
  │ ③ 私有同形两处：`fstNodeOrbit`（TameList7.lean:220，private）、
  │    `fstNodeOrbitT`（TameList16.lean:198，private）——不可跨文件导入，
  │    本件以公开的 `nListPowEqNodeMapPow` + `nodeEqFstSet` 重证。
  │ ④ 内容一行可合成：`uniqListOfFaces`（TameList50:211，公开）
  │    + `List.Nodup.of_map`（TameCorrG8:139 同款用法）；另有私件
  │    `goodListNodup`（TameCorrFloor:411，private）不可导入 → 本件落
  │    公开一行形。
  │ ⑤ 分量引擎均已在册：n 分量 = `nListMemDarts`（Split1B:64）、
  │    e 分量 = `goodListEList`（TameList5:336）、f 分量 =
  │    `fList_mem_darts`（TameLp:5113）；迭代归纳为新增（本件）。
  │ ⑥ 仅私件 `headMapLift`（TameList41，专用域两型）；公开泛型件零命中
  │    （`List.head!_map` 不在库，TameList28:56 实测记档）→ 本件落。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算；语义逐字对齐消费点）───────────────────────────
  │ ① HOL 以 `l'y L r x = y` 命名 y 再谈 `next_el r y`；Lean 直接取
  │    具体项 `lYSpine L r x`（消费点即此实例）。`all uniq L` 槽由
  │    `hm.1.1`（IsRestricted）+ `isRestrictedAllUniq` 内部导出，不加前提。
  │ ② 同①：HOL 的 z/z1 命名等式前件折叠为具体项
  │    `lZSpine L N r x` / `prevEl r (lZSpine L N r x)`。
  │ ③ HOL 无 `good_list_nodes` 前提；Lean 件加 `hgn : GoodListNodesTl L hL`
  │    （nodeEqFstSet 的载体需求；AQ8/AQ9 语境恒有 hgn）。
  │ ④ 逐字（`uniq` ↦ `List.Nodup`）。
  │ ⑤ HOL 三支是 `e/n/f_list_ext L`（限制函数）的幂；Lean 用总函数
  │    `eList`/`nList L`/`fList L` 的迭代——在 darts 面上同值
  │    （`good_list` 保证闭包），命题分量与顺序逐字（e,n,f）。
  │ ⑥ HOL `HD (MAP f s) = f (HD s)`；Lean `head!` 需 `Inhabited`
  │    两槽（HOL 的 HD 无默认元，前提 `s ≠ []` 同）。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件驼峰无前缀，私件 `aq8w05_` 前缀（本批无必需私件）。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf1
import Kepler.Text.TameSpine.JcajyduAqSplit1D
import Kepler.Text.TameSpine.JcajyduAqSplit1C
import Kepler.Text.TameSpine.JcajyduAqSplit1B
import Kepler.Text.TameSpine.TameList50
import Kepler.Text.TameSpine.TameList59
import Kepler.Text.TameSpine.TameList10

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face mem_darts_of_mem_findFace
  nextEl_mem_of_mem prevEl_mem_of_mem fList_mem_darts)

/-! ## §0 `hd_map`（HOL tame_list.hl:4772：`~(s=[]) ⇒ HD (MAP f s) = f (HD s)`） -/

/-- HOL `HD_MAP`（tame_list.hl:4772）：非空列表的 map 首元 = 首元的像。 -/
theorem hdMap {α β : Type} [Inhabited α] [Inhabited β] (s : List α) (f : α → β)
    (hs : s ≠ []) : (s.map f).head! = f s.head! := by
  match s with
  | [] => exact absurd rfl hs
  | _ :: _ => rfl

/-! ## §1 `good_list_uniq`（list_hypermap.vhl:820：`good_list L ⇒ uniq L`） -/

/-- HOL `good_list_uniq`（list_hypermap.vhl:820）：`good_list L ⇒ L.Nodup`。
一行合成：`uniq_list_of_faces`（listOfFaces = L.map listPairs 的 Nodup）
+ `List.Nodup.of_map`（map 不增重，免单射前提）。 -/
theorem goodListUniq (L : fgraph ℕ) (hL : GoodList L) : L.Nodup :=
  List.Nodup.of_map listPairs (uniqListOfFaces hL)

/-! ## §2 `FST_N_LIST_POWER`（LEBHIRJ.hl:52）

`good_list L ∧ MEM d (list_of_darts L) ⇒ FST ((n_list L POWER n) d) = FST d`。
Lean 路：`nListPowEqNodeMapPow`（Split1B:68）把 nList 幂换成 nodeMap 幂；
node 幂各点留 node（`mem_node_iff`），`nodeEqFstSet` 把 node 展开成
「同首点 dart 集」，读出 FST 等式。HOL 原文无 good_list_nodes，本件按
AQ11 清单的 nodeEqFstSet 路线显式带 hgn（见头注 DIFFERS ③）。 -/
theorem fstNListPower (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {d : ℕ × ℕ} (hd : d ∈ listOfDarts L) (n : ℕ) :
    ((nList L)^[n] d).1 = d.1 := by
  rw [nListPowEqNodeMapPow L hL hd n]
  have hdD : d ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hd
  have hmem : ((hypermapOfList L hL).nodeMap ^ n) d ∈ (hypermapOfList L hL).node d := by
    rw [(hypermapOfList L hL).mem_node_iff d (((hypermapOfList L hL).nodeMap ^ n) d)]
    exact ⟨n, rfl⟩
  rw [nodeEqFstSet L hL hgn hdD] at hmem
  exact hmem.2

/-! ## §3 `list_ext_power_in_darts`（list_hypermap.vhl:729）

`good_list L ∧ d ∈ darts_of_list L ⇒
(e_list_ext L POWER n) d ∈ darts_of_list L ∧
(n_list_ext L POWER n) d ∈ darts_of_list L ∧
(f_list_ext L POWER n) d ∈ darts_of_list L`。
Lean 载体：总函数 `eList`/`nList L`/`fList L` 的迭代（darts 面同值）。
三分量各三行归纳：e = `goodListEList`、n = `nListMemDarts`、
f = `fList_mem_darts`（HOL `e_list_ext/n_list_ext/f_list_ext` 的单步闭包）。 -/
theorem listExtPowerInDarts (L : fgraph ℕ) (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) (n : ℕ) :
    (fun x => eList x)^[n] d ∈ listOfDarts L ∧
      (nList L)^[n] d ∈ listOfDarts L ∧
      (fList L)^[n] d ∈ listOfDarts L := by
  refine ⟨?_, ?_, ?_⟩
  · induction n with
    | zero => simpa using hd
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact goodListEList hL ih
  · induction n with
    | zero => simpa using hd
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact nListMemDarts L hL ih
  · induction n with
    | zero => simpa using hd
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact fList_mem_darts hL.1 ih

/-! ## §4 `FST_EQ_NEXT_YTRANS_v0`（AQ1.hl:851）

`…marked ∧ ¬final ∧ l'y = y ⇒ FST (next_el r y) = FST y` 的 y := l'y 实例。
Lean 路（AQ1 车道的替代证法）：`loopListSpine` 在 y 处给出
`nextEl r y = fList L y ∨ nextEl r y = fList L (eList y)`；首支由
`nextRNotEqF` 排除，得 `nextEl r y = fList L (eList y)`；再用
`fListFstSnd`（`FST (fList x) = SND x`）与 `eList` 定义收口。 -/
theorem fstEqNextYtransV0 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    (nextEl r (lYSpine L r x)).1 = (lYSpine L r x).1 := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hloop : loopListSpine L r := hm.1.2.1.2.2.2.1 r hm.1.2.2.1
  have hny : nextEl r (lYSpine L r x) = fList L (eList (lYSpine L r x)) := by
    rcases (hloop (lYSpine L r x) hyr).2 with h1 | h1
    · exact absurd h1 (nextRNotEqF L hL hgn hunL hm hf)
    · exact h1
  have hyd : lYSpine L r x ∈ listOfDarts L := memYtransListOfDarts L hL hgn hm hf
  have he : eList (lYSpine L r x) ∈ listOfDarts L := goodListEList hL hyd
  rw [hny, fListFstSnd L hunL he]
  rfl

/-! ## §5 `FST_EQ_PREV_ZTRANS_v0`（AQ1.hl:796）

`…marked ∧ ¬final ∧ l'z = z ∧ prev_el r z = z1 ⇒ FST z1 = FST z` 的
具体项实例。Lean 路：`loopListSpine` 在 z1 = prevEl r l'z 处给两支；
首支 `nextEl r z1 = fList L z1` 经 `nextElPrevElUniq` 化为 `l'z = fList L z1`，
由 `prevRNotEqF` 排除；次支 `l'z = fList L (eList z1)` 即 z1e。
再由 `fListFstSnd` 把 `FST l'z` 转成 `(eList z1).2 = z1.1`。 -/
theorem fstEqPrevZtransV0 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    (prevEl r (lZSpine L N r x)).1 = (lZSpine L N r x).1 := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hz1r : prevEl r (lZSpine L N r x) ∈ r := prevEl_mem_of_mem hzr
  have hnextz1 : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hrnd _
  have hloop : loopListSpine L r := hm.1.2.1.2.2.2.1 r hm.1.2.2.1
  have hz1e : lZSpine L N r x = fList L (eList (prevEl r (lZSpine L N r x))) := by
    rcases (hloop (prevEl r (lZSpine L N r x)) hz1r).2 with h1 | h1
    · rw [hnextz1] at h1
      exact absurd h1.symm (prevRNotEqF L hL hgn hunL hm hf)
    · rw [hnextz1] at h1
      exact h1
  have hz1d : prevEl r (lZSpine L N r x) ∈ listOfDarts L := (hloop _ hz1r).1
  have he : eList (prevEl r (lZSpine L N r x)) ∈ listOfDarts L := goodListEList hL hz1d
  calc (prevEl r (lZSpine L N r x)).1
      = (eList (prevEl r (lZSpine L N r x))).2 := rfl
    _ = (fList L (eList (prevEl r (lZSpine L N r x)))).1 := (fListFstSnd L hunL he).symm
    _ = (lZSpine L N r x).1 := congrArg (fun d => d.1) hz1e.symm

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：六件全标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.hdMap
#print axioms Kepler.Text.TameSpine.goodListUniq
#print axioms Kepler.Text.TameSpine.fstNListPower
#print axioms Kepler.Text.TameSpine.listExtPowerInDarts
#print axioms Kepler.Text.TameSpine.fstEqNextYtransV0
#print axioms Kepler.Text.TameSpine.fstEqPrevZtransV0
