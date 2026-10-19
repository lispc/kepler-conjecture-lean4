/-
  Kepler.Text.TameSpine.TameList25 — B1 Tame_list 地基批 25：dih2k 章开局
  （tamespine-port-plan §4 批次表 B1 行；接续批 24 = TameList23→TameList24.lean，
  批 24 终点 = HOL :10794（elements_of_list_pr 已落，:10796 起留本批）；
  本批起点 = HOL :10796）。

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353，
  text_formalization/tame/tame_list.hl:10796-:10827）——dih2k 章开局：

  定义面：`dih2k_list`（tame_defs2.hl:573-574）新落 `Dih2kListSpine`；
  `iso_list`（tame_defs2.hl:62-65）**复用批 1 `IsoListSpine`**
  （TameList1.lean:67，不重落新 def——侦察结论见下）。

  主件：`iso_list_imp_dih2k` :10796-:10810
  `!L L'. iso_list (L,[]) (L',[]) /\ dih2k_list L ==> dih2k_list L'`。
  同名再证跳过：:10812-:10819 `fgraph_seed`（`!p. fgraph (Seed p) =
  [iota 0 (maxGon p); rev (iota 0 (maxGon p))]`，dih2k_list 展开面）
  与批 21 `fgraphSeed`（TameList21.lean:122，rfl 件）语句逐字同形——
  按同名件规则不重落，语义由已落件覆盖；本章余件（:10796/:10821）
  均不引用它。章内辅助件：`rev2` :10821-:10827
  `!x y. rev [x;y] = [y;x]`（泛型，Lean 面 defeq 直收）。
  自然边界：:10829 `is_normal_loop_list` 起 normal_list 章，留批 26。

  载体定名侦察定论（本批新核，任务面定义先行侦察）：
  · `iso_list`（tame_defs2.hl:62-65）：**在库已有同义载体直接复用**——
    批 1 `IsoListSpine`（TameList1.lean:67 `∃ phi, IsopListSpine phi L L'
    N N'`；显式 φ 形 `IsopListSpine` :58 即 tame_defs2.hl:66-69 逐槽
    折算：inj_on ↦ Set.InjOn（tame_defs.hl:343 同形）、elements_of_list
    ↦ TameLp.elementsOfList、MAP (MAP phi) ↦ L.map (List.map phi)、
    darts 对双层 MAP ↦ N.map (·map (fun u => (phi u.1, phi u.2)))，
    N : List (List (ℕ×ℕ)) 与 HOL N:(A#A)list list 同形；HOL (L,N)
    捆对 ↦ 四参数平铺批 1 头注已记档）。本批语句 iso_list (L,[]) (L',[])
    即 `IsoListSpine L L' [] []`（批 1 平铺序 (L L') (N N')）。
  · `dih2k_list`（tame_defs2.hl:573-574）：在库无同义载体（全库
    grep Dih2k/dih2k 仅 SphereKit/LocalAuto23 注记与 Assembly 超映射级
    FanHypermapIsoList，无列表级）——按在库体例新落 def `Dih2kListSpine`
    （def 层 `…Spine` 后缀，批 1 IsopListSpine/setOfListSpine 同例），
    语句体逐字：`∃ u, u.Nodup ∧ L = [u, u.reverse]`（uniq ↦ List.Nodup、
    rev ↦ List.reverse）。
  · 泛型幅度裁定：HOL iso_list/dih2k_list 泛型 A B；本批 ℕ 专属——
    批 1 IsoListSpine 即 ℕ 定形（复用既定），章内及下游使用
    （reduction1.hl:2490 quotient_list、AUQTZYZ_list.hl:24）全 ℕ；
    rev2 纯列表面无载体牵连，保持泛型 α。

  证明层侦察定论：
  · :10796 证明体（:10800-:10809）REWRITE_TAC[dih2k_list;iso_list;MAP]
    后证人 `MAP phi u`：HOL MATCH_MP_TAC uniq_map（tame_list.hl:972-983
    逐点式 `!u v. MEM u y /\ MEM v y /\ f u = f v ==> u = v`）↦
    Mathlib `List.Nodup.map_on`（Data/List/Nodup.lean:185 同逐点式）；
    本批取 iff 形 `List.nodup_map_iff_inj_on`（Nodup.lean:202，
    Nodup (map f l) ↔ Set.InjOn f ↑l）——门槛 inj_on phi
    (elements_of_list L) 经 hLeq 换元 + 批 24 `elementsOfListPr`
    （elementsOfList [u,u.reverse] = {x | x ∈ u}）一步化到 u 自身
    （HOL ASM_REWRITE_TAC[elements_of_list_pr;IN_ELIM_SET_OF_LIST]
    合一面），零 Meson。
  · L' = [MAP phi u; rev (MAP phi u)] 支 = HOL MAP/MAP_REVERSE 面：
    hL' + hLeq 换元后 `List.map_cons`/`List.map_nil`/`List.map_reverse`
    （Init.Data.List.Lemmas:2522 simp 面）一步 simp 收口。
  · :10821 rev2：HOL 证体 Seq.rev_cons/rev1/Seq.cats1 链在 Lean 面
    为二元表 reverse 的 delta/iota 归约——`rfl` 直收。

  依赖面（全为在案真件，零新增债）：批 1 `IsoListSpine`（def 复用）+
  批 24 `elementsOfListPr` + 批 21 `fgraphSeed`（同名跳过件语义覆盖）
  + TameLp `elementsOfList` + Mathlib List.Nodup/nodup_map_iff_inj_on/
  map_cons/map_nil/map_reverse。import 边：本模块 import TameList24
  （链式带全批 1-23 与 GoodGraph），零新增库依赖。

  诚实记账：本批一新 def 一主件一辅助件全部真证，零新增记账债（零
  止损件）。:10812 同名 fgraph_seed 再证按同名件规则跳过（批 21
  fgraphSeed 覆盖语义）。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git
  写操作。批 26 接续点：HOL :10829 `is_normal_loop_list` 起 normal_list
  章（`is_restricted (hypermap_of_list L) /\ good_list L /\
  good_list_nodes L /\ all (\r. ~(r=[])) N /\ all uniq N /\
  is_normal (hypermap_of_list L) (loop_family_of_list N) ==>
  all (loop_list L) N`，Hypermap.lemma_in_dart/dart_hypermap_of_list/
  one_step_list/one_step_contour 链，大件）。
-/

import Kepler.Text.TameSpine.TameList24

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (elementsOfList)

/-! ### §0 定义面：dih2k_list 新落（tame_defs2.hl:573-574） -/

/-- HOL `dih2k_list`（tame_defs2.hl:573-574）
`dih2k_list L <=> ?u. uniq u /\ L = [u; rev u]`——两元素表（面-背面）
折算 def 层新件（在库无同义载体，头注侦察记档）：uniq ↦ List.Nodup、
rev ↦ List.reverse。iso_list 面不另落 def——复用批 1 `IsoListSpine`
（TameList1.lean:67）。 -/
def Dih2kListSpine (L : fgraph ℕ) : Prop := ∃ u : List ℕ, u.Nodup ∧ L = [u, u.reverse]

/-! ### §1 iso_list_imp_dih2k（tame_list.hl:10796-:10810） -/

/-- **HOL `iso_list_imp_dih2k`**（tame_list.hl:10796-:10810）
`!L L'. iso_list (L,[]) (L',[]) /\ dih2k_list L ==> dih2k_list L'`——
HOL 证人 MAP phi u ↦ `u.map phi`：Nodup 支经 hLeq 换元 + 批 24
elementsOfListPr 把 InjOn 门槛一步化到 u 自身，交
`List.nodup_map_iff_inj_on`（HOL uniq_map :972 面）；L' 等式支
map_cons/map_nil/map_reverse simp 收口（HOL MAP/MAP_REVERSE 面）。
iso_list 面为批 1 `IsoListSpine`（(L,N) 捆对四参数平铺，N=[] 槽）。 -/
theorem isoListImpDih2k {L L' : fgraph ℕ}
    (hiso : IsoListSpine L L' [] []) (hdih : Dih2kListSpine L) : Dih2kListSpine L' := by
  obtain ⟨phi, hinj, hL', -⟩ := hiso
  obtain ⟨u, hu, hLeq⟩ := hdih
  refine ⟨u.map phi, ?_, ?_⟩
  · rw [hLeq] at hinj
    rw [elementsOfListPr u] at hinj
    exact (List.nodup_map_iff_inj_on hu).mpr hinj
  · rw [hL', hLeq]
    simp

/-! ### §2 rev2（tame_list.hl:10821-:10827） -/

/-- **HOL `rev2`**（tame_list.hl:10821-:10827）
`!x y. rev [x;y] = [y;x]`——HOL 证体 Seq.rev_cons/rev1/Seq.cats1 链
在 Lean 面为二元表 reverse 的 delta/iota 归约，`rfl` 直收。 -/
theorem rev2 {α : Type*} (x y : α) : ([x, y] : List α).reverse = [y, x] := rfl

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；isoListImpDih2k 预期标准三
[propext, Classical.choice, Quot.sound]，rev2 预期零公理）：
#print axioms Kepler.Text.TameSpine.isoListImpDih2k
#print axioms Kepler.Text.TameSpine.rev2
-/
