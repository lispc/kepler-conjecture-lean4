/-
  Kepler.Text.TameSpine.TameList30 — B1 Tame_list 地基批 30：quotient 章
  收口（tamespine-port-plan §4 批次表 B1 行；接续批 29 =
  TameList28.lean→TameList29.lean，批 29 终点 = HOL :11244
  （quotient_bij_face_set 已落）；本批起点 = HOL :11247
  `dih2k_quotient_card_NF`。行号均按主仓 reference/flyspeck
  （commit 1ce0353）实测；任务面所给 WRGCVDR.hl:2773 系参考行号，
  主仓实测 `dih2k` 定义桩 :86——与批 29 头注预记一致）。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:11247-:11287）：

  主件 1：`dih2k_quotient_card_NF` :11247-:11287（quotient 章收口墙）
  `!H NF x. ~(CARD(face H x)=0) /\ is_normal H NF /\
  dih2k (quotient H NF) (CARD (face H x)) ==> ~(SING NF)`
  ——二面体 k-层商 hypermap 的面基数非零 ⟹ 正规环族非单元
  （SING 反证：单元族商的 face_set 与 DIH2K 段终墙冲突）。

  其后 :11290 `final_list_f_last` 起 final_list 新章—— carriers 侦察
  定论（批 30 头注预记勘误入档）：HOL `final_list`/`f_last`
  （tame_defs2.hl:138/:78）的**底层载体链大半已在库**——
  `Kepler.Assembly.GoodListDefs`（listPairs:34/listOfDarts:38/
  nextEl:44/prevEl:50/findFaceDarts:55/eList:59/fList:62/nList:66，
  fgraph ℕ/ℕ × ℕ 具体层，头注自记 list_hypermap-compiled.hl 镜像
  桩位）＋ TameLp `nextEl_eq_getD` 桥（批 28 已消费面）；真缺件
  仅两件 def（`f_last` ↦ `nextEl r r.last = fList L r.last`、
  `final_list` ↦ `∀ d ∈ r, fList L d = nextEl r d`）＋主件七行
  （全/meallP 面 ↦ `∀ d ∈ r`，MEM_LAST ↦ `List.last_mem`，零偏函数
  totalization 负担——nextEl 已在库定案）。批 30 零落、留批 31
  两件 def + 主件轻量开局。

  定义面侦察定论（本批零新落 def——全部载体在库，逐槽记档）：
  · `quotient H NF`（hypermap.hl:9342）↦ `H.quotientHypermap hnf`
    （Hypermap.lean:7744，批 29 已消费面；`is_normal` 折算成显式
    `hnf : IsNormalFamily` 参数——本批 SING 前提 `NF = {L}` 经
    rintro 即 subst，hnf 槽自动换装单元族型，无需另行例示，批 29
    预记的「单元族例示」分支未触发）；
  · `is_normal`（hypermap.hl:8122）↦ `Hypermap.IsNormalFamily`
    （Hypermap.lean:6808）；`face_set`（hypermap.hl:167）↦
    `Hypermap.faceSet`（:1008）；`atoms_of_loop`（hypermap.hl:9688）
    ↦ `H.atomsOfLoop`（:7939）；`BIJ` ↦ Mathlib `Set.BijOn`
    （Operations.lean:309，And 三槽链——消费取 `.2.2` SurjOn 槽）；
  · `dih2k`（WRGCVDR.hl:86，五合取）↦ 在库 `Kepler.Text.dih2k_p3`
    （LocalAuto3.lean:127，泛型 `Hypermap α` 层）——本批证体只消费
    第 1 槽 `CARD (dart H) = 2 * k`（`.1` 投影），第 2-5 槽（dart =
    face ∪ node_map''face、has_orders 三件）在 HOL MESON 中同样
    未触及，零镜像记档；
  · `SING`（HOL `∃x. s = {x}`）↦ `∃ L : Loop α, NF = {L}` 直译
    （TameList1-29 无 SING 先例，本批首例记档；不取
    `Set.Subsingleton`——空族是 Subsingleton 而 HOL SING 非空，
    语义不等）；
  · `CARD(face H x)=0` 面 ↦ `(H.face x).ncard ≠ 0`（Set.ncard，
    TameList1/15 先例；批 28 `Loop.card_pos` 先例系 Loop 载体面，
    本件 face 系 Set 载体，改走 ncard）。

  证明层侦察定论：
  · HOL 证体五步：①INTRO lemma_finite_normal_loops
    （hypermap.hl:8342）+ lemma_finite_atoms_of_family
    （hypermap.hl:8317）+ quotient_bij_face_set——前两件**证体
    从未消费**（exploration leftovers，零镜像记档）；②SING 展开
    `∃a. NF = {a}`；③DIH2K_IMP_PRE_SIMPLE_HYP2（批 29 主件 1）
    实例化 H := quotient H NF；④dart 非空子目标（CARD_EQ_0 +
    node_map_and_darts + `k = 0 ⟺ 2*k = 0`）——Lean 面 Finset
    有限性内建，`Finset.card_ne_zero` + omega 一步吸收；⑤终墙
    单行 `ASM_MESON_TAC[lemma_in_face_set]`——实际机理（MESON
    逐字反推）：BIJ 的 SurjOn 槽对 `face Hq d` 与 `face Hq z`
    双应用（d := node_map Hq z；d ∈ dart Hq 走 lemma_dart_invariant，
    d ∈ face Hq d 走 face_refl；两 dart 成员 → face_set 成员走
    lemma_in_face_set:2727）拉出 `atoms_of_loop H L` 同源双等 ⇒
    `face Hq d = face Hq z` ⇒ `d ∈ face Hq z`（face_refl 运输），
    与 ③ 实例在 z 处的 `node_map Hq z ∉ face Hq z` 精确冲突。
    Lean 面零 MESON，六槽显式装配（SurjOn 双应用 + mem_image
    证人提取 + 单元集成员化 + DIH2K_IMP_PRE_SIMPLE_HYP 收口）。
  · `Hypermap.lemma_dart_invariant`（hypermap.hl:412）↦ 在库
    `H.dart_invariant`（Hypermap.lean:1299；本批只取 node_map 槽
    `nodeMap_apply_mem` :813）；`face_refl`（hypermap.hl:908）↦
    `H.mem_face_self`（:861）；`lemma_in_face_set`（:2727）↦
    `H.mem_darts_iff_face_mem`（:2790）。

  依赖面：批链全批 1-29 + LocalAuto3（dih2k_p3/
  DIH2K_IMP_PRE_SIMPLE_HYP 批 29 引入的 import 边沿用）+ 在库
  Hypermap quotientHypermap/IsNormalFamily/faceSet/atomsOfLoop/
  quotientBijFaceSet（批 29 主件 2，本件以例示消费——泛型 α
  保持批 29 裁定，无列表载体牵连）+ Mathlib Set.BijOn/mem_image/
  mem_singleton_iff/Finset.card_ne_zero。

  诚实记账：本批主件全真证，零新 def、零止损件、零记账债。
  final_list 新章零开局（底层载体链在库核查定论见头注首段，
  两件 def + 七行主件留批 31 轻量开局，接续点处方见头注尾）。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git
  写操作。批 31 接续点：HOL :11290 `final_list_f_last`
  `!L r. ~(r = []) /\ final_list L r ==> f_last L r`（证体七行）。
  处方：两件 def 直落（`fLast L r : nextEl r r.last = fList L r.last`
  ＋ `finalList L r : ∀ d ∈ r, fList L d = nextEl r d`——载体在库
  `Kepler.Assembly.GoodListDefs.fList:62/nextEl:44`，泛型裁定照
  nextEl 自带 `[BEq α]` 面；HOL `all`+`GSYM Seq.allP` 面 ↦
  `∀ d ∈ r` 点记号形，MEM_LAST ↦ `List.last_mem`）；主件装配即
  `fun h r hl => (h r hl).symm` 量级；其后 :11305 `face_rep` 起
  同章四件（face_rep:11305/good_face_rep:11321/parts_nil:11348/
  uniq_sing:11356 实测段）随后续批推进——face_rep 消费
  List_hypermap.list_of_faces/list_pairs（在库 listPairs 面已备）。
-/

import Kepler.Text.TameSpine.TameList29
import Kepler.Text.LocalAuto3

namespace Kepler.Text.TameSpine

/-! ### §1 dih2k_quotient_card_NF（tame_list.hl:11247-:11287）——quotient 章收口 -/

/-- **HOL `dih2k_quotient_card_NF`**（tame_list.hl:11247-:11287）
`!H NF x. ~(CARD(face H x)=0) /\ is_normal H NF /\
dih2k (quotient H NF) (CARD (face H x)) ==> ~(SING NF)`——quotient 章
收口：dih2k 层面基数非零的正规商 hypermap，其正规环族非单元。
HOL 证体五步 Lean 显式装配：SING 反证 → `Finset.card_ne_zero`
（HOL ④ dart 非空子目标，Finset 有限性内建吸收 CARD_EQ_0 面）→
SurjOn 槽双应用（HOL ⑤ 单行 MESON 的实际机理，lemma_in_face_set
↦ `mem_darts_iff_face_mem`、face_refl ↦ `mem_face_self`、
lemma_dart_invariant ↦ `nodeMap_apply_mem`）→ 批 29
`DIH2K_IMP_PRE_SIMPLE_HYP` 段终墙收口。HOL ①引入的
lemma_finite_normal_loops/lemma_finite_atoms_of_family 证体从未
消费，零镜像；`dih2k` 第 2-5 合取槽零触及，零镜像。 -/
theorem dih2kQuotientCardNF {α : Type*} [DecidableEq α] (H : Hypermap α)
    {NF : Set (Loop α)} (x : α) (hk : (H.face x).ncard ≠ 0)
    (hnf : H.IsNormalFamily NF)
    (hd : dih2k_p3 (H.quotientHypermap hnf) (H.face x).ncard) :
    ¬∃ L : Loop α, NF = {L} := by
  -- HOL ②：SING 展开（`∃a. NF = {a}`），hnf 槽随 subst 换装单元族型
  intro hS
  obtain ⟨L, rfl⟩ := hS
  have hcard := hd.1
  -- HOL ④：dart 非空子目标（CARD(dart) = 2k ≠ 0；Finset 有限性内建）
  have hne : (H.quotientHypermap hnf).darts.Nonempty := by
    apply Finset.card_ne_zero.mp
    omega
  obtain ⟨z, hz⟩ := hne
  -- d := node_map Hq z ∈ dart Hq（HOL lemma_dart_invariant node 槽）
  have hdart : (H.quotientHypermap hnf).nodeMap z ∈ (H.quotientHypermap hnf).darts :=
    (H.quotientHypermap hnf).nodeMap_apply_mem hz
  have hQ := quotientBijFaceSet H hnf
  -- face Hq d、face Hq z ∈ face_set Hq（HOL lemma_in_face_set 双应用）
  have hfd : (H.quotientHypermap hnf).face
      ((H.quotientHypermap hnf).nodeMap z) ∈ (H.quotientHypermap hnf).faceSet :=
    ((H.quotientHypermap hnf).mem_darts_iff_face_mem _).mp hdart
  have hfz : (H.quotientHypermap hnf).face z ∈ (H.quotientHypermap hnf).faceSet :=
    ((H.quotientHypermap hnf).mem_darts_iff_face_mem z).mp hz
  -- HOL ⑤：SurjOn 槽双应用，单元族上证人唯一化，双等同源
  obtain ⟨w, hw, hEqd⟩ := (Set.mem_image _ _ _).mp (hQ.2.2 hfd)
  obtain ⟨w', hw', hEqz⟩ := (Set.mem_image _ _ _).mp (hQ.2.2 hfz)
  simp only [Set.mem_singleton_iff.mp hw, Set.mem_singleton_iff.mp hw'] at hEqd hEqz
  rw [hEqd] at hEqz
  -- face Hq d = face Hq z ⟹ d ∈ face Hq z（HOL face_refl 运输半）
  have hmem : (H.quotientHypermap hnf).nodeMap z ∈ (H.quotientHypermap hnf).face z := by
    have hm := (H.quotientHypermap hnf).mem_face_self
      ((H.quotientHypermap hnf).nodeMap z)
    rwa [hEqz] at hm
  -- 段终墙精确冲突（HOL DIH2K_IMP_PRE_SIMPLE_HYP2 实例 @ z）
  exact DIH2K_IMP_PRE_SIMPLE_HYP hd hk z hz hmem

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；主件预期标准三
[propext, Classical.choice, Quot.sound]）：
#print axioms Kepler.Text.TameSpine.dih2kQuotientCardNF
-/
