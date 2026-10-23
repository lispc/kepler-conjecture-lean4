/-
  Kepler/Text/LP/LpSemantics — LP 终端语义层 keystone 首件（LP W6-B #1）。

  两件：
  1. `fullySurrounded_of_surroundedNode`：fan 前提下逐点 surrounded ⇒ 全 dart
     surrounded（HOL `CONTRAVENING_IMP_FULLY_SURROUNDED` 的去 contravening 化
     核心步；dart 两支的 `d.1 ∈ V` 归属由 TameLp 已证 `dartOfFan_fst_mem`
     承载——孤立点支取 `.2.1`、边支经 `FAN_in_setOfEdge`）。
  2. `contraveningLpFan`：HOL `contravening_lp_fan`
     （`formal_lp/hypermap/ineqs/lp_ineqs_proofs-compiled.hl:385-400`）直译：
     `Contravening V → LpFan V (ESTD V)`，五合取逐项落地——
     FAN ← `ContraFan.contraveningFanTl`（Packing + ballAnnulus + V ≠ ∅，
     非空由 `Contravening` 的 ncard = 13/14/15 合取项排除空集）；
     FullySurrounded ← 件 1；2.52 距离 ← `ContraFan.mem_ESTD` + `two_h0`
     （dist < 2.52 ⇒ {v,w} ∈ ESTD V 与 `{v,w} ∉ ESTD V` 矛盾，HOL `IN_ESTD`
     归谬步）；ballAnnulus / Packing ← `Contravening` 对应合取项。

  `LpFan` 直接消费 `Kepler.Text.TameLp.LpFan`（HOL `lp_fan` 的逐合取镜像，
  不重定义 `lp_fan`）；`ESTD` 同理用 `Kepler.Text.TameLp.ESTD`（与
  `ContraFan.ESTD` 同体 defeq，`contraveningFanTl` / `mem_ESTD` 经默认
  透明度 unfolding 直通）。

  公理面：`fullySurrounded_of_surroundedNode` 仅标准三（propext /
  Classical.choice / Quot.sound）；`contraveningLpFan` = 标准三 + ContraFan
  在案骨架公理——全部经 `ContraFan.contraveningFanTl`（→ `CKQOWSA` →
  `ESTD_fan7` 的 fan7 相交性 → 深几何核 `LEMMA_4_POINTS_FINAL`，
  ContraFan.lean:613 在案骨架）继承；本文件零新增未证原子。

  件 3（LP W6-B 第二件）：`lp_cond_lemma`（HOL
  `lp_ineqs_proofs-compiled.hl:186-327`）的装配形——`LpCond` 定义未入 Lean
  （def 冻结红线），七合取以显式合取直书；两枚未移植深件
  `fan_list_nodes_iso_BIJ` / `hyp_iso_eq_fan_list_iso` 以具名假设
  （`hbijNode` / `hdecomp`）显式提出，其余步骤（`res_inv` 逆构造
  `exists_nodeInverse`、对偶方向 BijOn 与三映射交换、
  `components_hypermap_of_list` 的 dart 投影支、junk-0/成员 iff）
  全部就地闭合。件 3 全部新件公理面纯标准三（深件债务在陈述前提上，
  不在公理里）。
-/
import Kepler.Text.TameLp
import Kepler.Text.LP.LPSchema

namespace Kepler.Text.LP.LpSemantics

open Kepler.Geom
open Kepler.Text.Fan
open Kepler.Text.TameLp
open Classical

-- 【W6-B 第三件 · 零删除改版】节点计数链 15 件新增（lpElementsCoverage /
-- lpBijOnNodeOfIso 等，见 LpCondLayer 内段注释）：hbijNode（= HOL
-- fan_list_nodes_iso_BIJ，list_hypermap_iso-compiled.hl:777-787）已真证；
-- 无假设主件 lpCondAssembly_nf / iso_of_lpCondAssembly_nf 追加于
-- LpCondLayer 尾部，原假设型主件原样保留（下游应消费 _nf 版）。

/-! ## 件 1：逐点 surrounded ⇒ 全 dart surrounded -/

/-- fan 前提下，`surroundedNode` 逐点成立即 `FullySurrounded`：
dart 的第一分量必在 `V` 中（`dartOfFan_fst_mem`，fan 的 `⋃₀ E ⊆ V` 两支
归属），再由该点的 surrounded 性质给出 `azimDart < π`。
（HOL `CONTRAVENING_IMP_FULLY_SURROUNDED` 的核心步。） -/
theorem fullySurrounded_of_surroundedNode {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) (hsurr : ∀ v ∈ V, surroundedNode V E v) :
    FullySurrounded V E := fun d hd =>
  hsurr d.1 (dartOfFan_fst_mem hfan hd) d hd rfl

/-! ## 件 2：`contravening_lp_fan` 直译 -/

/-- HOL `contravening_lp_fan`（`lp_ineqs_proofs-compiled.hl:385-400`）：
反例构型给出 LP 扇。五合取：FAN（`CONTRAVENING_FAN`，经 ContraFan 的
CKQOWSA 链）/ fully_surrounded（`CONTRAVENING_IMP_FULLY_SURROUNDED`）/
2.52 距离（`IN_ESTD` 归谬）/ ballAnnulus / Packing。 -/
theorem contraveningLpFan (V : Set V3) (hc : Contravening V) : LpFan V (ESTD V) := by
  have hne : V ≠ ∅ := by
    have hcard : V.ncard = 13 ∨ V.ncard = 14 ∨ V.ncard = 15 := hc.2.2.2.2.1
    rintro rfl
    simp at hcard
  have hfan : FAN 0 V (ESTD V) := ContraFan.contraveningFanTl V hc.1 hc.2.1 hne
  refine ⟨hfan, fullySurrounded_of_surroundedNode hfan hc.2.2.2.2.2.1, ?_, hc.2.1, hc.1⟩
  intro v w hv hw hvw hnotE
  by_contra hcon
  push_neg at hcon
  have hmem : {v, w} ∈ ESTD V :=
    ContraFan.mem_ESTD.mpr ⟨v, w, rfl, hv, hw, hvw,
      by linarith [ContraFan.two_h0, hcon]⟩
  exact hnotE hmem

/-! ## 件 3：`lp_cond_lemma` 装配层（LP W6-B 第二件）

HOL 原件（`lp_ineqs_proofs-compiled.hl:186-327`）从 `lp_fan + good_list +
good_list_nodes + hyp_iso f (hypermap_of_fan, hypermap_of_list)` 装配出
`?g h. lp_cond (L, g, h) (V, E)`。其上游深件
`fan_list_nodes_iso_BIJ`（节点双射）与 `hyp_iso_eq_fan_list_iso`（dart 同构
的节点对分解）依赖 σ-orbit 覆盖论证，Lean 侧 sigmaFan 轨道件未移植——本件
把这两步以具名假设（`hbijNode` / `hdecomp`）提出，其余全部就地闭合：
`res_inv` 逆构造、`BIJ_pair` 运输、iso 取逆、junk-0 语义与成员 iff。
深件落地后本件即自动成为 `lp_cond_lemma` 的完整直译（假设备注已逐字锚定
HOL 引理名）。 -/

open Kepler.Assembly (listPairs listOfDarts GoodList)
open Kepler.Graphs (fgraph)

section LpCondLayer

variable {V : Set V3} {E : Set (Set V3)}

/-- LpFan 排除孤立点：`FullySurrounded` 下每点必有边（即
`setOfEdge ≠ ∅`；HOL `fully_surrounded_is_non_isolated_fan` 簇的核心步：
`DART_EXISTS_TL` 的孤立点支直取分支条件的第三分量）。 -/
theorem lpFan_setOfEdge_ne (hlpfan : LpFan V E) {v : V3} (hv : v ∈ V) :
    setOfEdge v V E ≠ ∅ := by
  intro hempty
  obtain ⟨w, hw⟩ := DART_EXISTS_TL hlpfan.1 v hv
  rcases (Set.mem_union _ _ _).mp hw with hiso | h1
  · -- 孤立 dart（v,w）=（v,v）：azimDart = 2π 与 FullySurrounded 的逐 dart
    -- 上界矛盾
    have hvw : v = w := hiso.1
    subst hvw
    have hlt : azimDart V E (v, v) < Real.pi := hlpfan.2.1 (v, v) hw
    have h2pi : azimDart V E (v, v) = 2 * Real.pi := by simp [azimDart]
    have hpp : (0 : Real) < Real.pi := Real.pi_pos
    linarith
  · have hw_soe : w ∈ setOfEdge v V E :=
      (properties_of_setOfEdge_fan 0 V E v w hlpfan.1).mp h1
    rw [hempty] at hw_soe
    exact hw_soe

/-- LpFan 下 `dartOfFan = dart1OfFan`（无孤立点；HOL
`fully_surrounded_dart_of_fan_eq` 的 LpFan 形——HOL 那件以
`fully_surrounded` 为前提，此处孤立分支由 `lpFan_setOfEdge_ne` 排除）。 -/
theorem lpFan_dartOfFan_eq (hlpfan : LpFan V E) : dartOfFan V E = dart1OfFan V E := by
  rw [dartOfFan, Set.union_eq_right]
  rintro d ⟨-, hv, hsoe⟩
  exact absurd hsoe (lpFan_setOfEdge_ne hlpfan hv)

/-- `dart1OfFan` 中 dart 的两个分量都属 `V`
（HOL `PAIR_IN_DART_OF_FAN` 的 dart1 折算，经 `FAN_in_setOfEdge`）。 -/
theorem dart1OfFan_fst_snd_mem (hfan : FAN 0 V E) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) : d.1 ∈ V ∧ d.2 ∈ V :=
  let h := FAN_in_setOfEdge 0 V E d.1 d.2 hfan hd
  ⟨h.1, h.2.1⟩

/-- 列表侧 dart 投影：`listOfDarts L` 中 dart 的两个分量都在
`elementsOfList L`（HOL `components_hypermap_of_list` 的 dart 合取支之
`FST`/`SND` 部分；`list_pairs = zip (drop 1 ++ take 1)` 展开 + flatten/
eraseDups 归属）。 -/
theorem listOfDarts_fst_snd_mem_elementsOfList {L : fgraph ℕ} {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) : d.1 ∈ elementsOfList L ∧ d.2 ∈ elementsOfList L := by
  have memEl : ∀ {x : ℕ} {l : List ℕ}, x ∈ l → l ∈ L → x ∈ elementsOfList L :=
    fun {_ l} hx hl => List.mem_eraseDups.mpr (List.mem_flatten.mpr ⟨l, hl, hx⟩)
  obtain ⟨lp, hlp, hdl⟩ := List.mem_flatten.mp hd
  obtain ⟨l0, hl0, hEq⟩ := List.mem_map.mp hlp
  rw [← hEq] at hdl
  have hz : (d.1, d.2) ∈ l0.zip (l0.drop 1 ++ l0.take 1) := hdl
  obtain ⟨h1, h2⟩ := List.of_mem_zip hz
  refine ⟨memEl h1 hl0, memEl ?_ hl0⟩
  rcases List.mem_append.mp h2 with ha | hb
  · exact List.mem_of_mem_drop ha
  · exact List.mem_of_mem_take hb

/-- 节点双射的逆构造（HOL `res_inv` / `bij_res_inv` 套件的 Lean 折算）：
`BijOn h' V S` 给出 `h x = if x ∈ S then h' 的逆像 else 0` 形的全函数，
带四处性质（S 上逆像归 V、`h ∘ h' = id` 于 V、S 上成双射、S 外 junk 0）。
即 HOL `lp_cond_lemma` 脚本 :216-247 的 witness 段。 -/
theorem exists_nodeInverse {L : fgraph ℕ} {h' : V3 → ℕ}
    (hbij : Set.BijOn h' V (elementsOfList L)) :
    ∃ h : ℕ → V3,
      (∀ x ∈ elementsOfList L, h x ∈ V ∧ h' (h x) = x) ∧
      (∀ v ∈ V, h (h' v) = v) ∧
      Set.BijOn h (elementsOfList L) V ∧
      (∀ x, x ∉ elementsOfList L → h x = 0) := by
  have hex : ∀ x : ℕ, x ∈ elementsOfList L → ∃ v : V3, v ∈ V ∧ h' v = x :=
    fun x hx => hbij.surjOn hx
  choose! h hmem heq using hex
  refine ⟨fun x => if hx : x ∈ elementsOfList L then h x else 0, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hH : (fun x => if hx : x ∈ elementsOfList L then h x else 0) x = h x :=
      dif_pos hx
    rw [hH]
    exact ⟨hmem x hx, heq x hx⟩
  · intro v hv
    have hm : h' v ∈ elementsOfList L := hbij.mapsTo hv
    have hH : (fun x => if hx : x ∈ elementsOfList L then h x else 0) (h' v) =
        h (h' v) := dif_pos hm
    rw [hH]
    exact hbij.injOn (hmem (h' v) hm) hv (heq (h' v) hm)
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      have hH : (fun x => if hx : x ∈ elementsOfList L then h x else 0) x = h x :=
        dif_pos hx
      rw [hH]
      exact hmem x hx
    · intro x hx y hy hEq
      have e1 : h x = h y := by
        have q1 : (fun x => if hx : x ∈ elementsOfList L then h x else 0) x = h x :=
          dif_pos hx
        have q2 : (fun x => if hx : x ∈ elementsOfList L then h x else 0) y = h y :=
          dif_pos hy
        rw [q1, q2] at hEq
        exact hEq
      have e2 : h' (h x) = h' (h y) := congrArg h' e1
      rw [heq x hx, heq y hy] at e2
      exact e2
    · intro y hy
      have hm : h' y ∈ elementsOfList L := hbij.mapsTo hy
      have hH : (fun x => if hx : x ∈ elementsOfList L then h x else 0) (h' y) =
          h (h' y) := dif_pos hm
      exact ⟨h' y, hm, hH.trans (hbij.injOn (hmem (h' y) hm) hy (heq (h' y) hm))⟩
  · intro x hx
    exact dif_neg hx

/-! ### 节点计数链（HOL `fan_list_nodes_iso_BIJ`，list_hypermap_iso-compiled.hl:777-787）

HOL 原证 = `finite_surj_eq_bij`：SURJ（`fan_list_nodes_iso_surj` :719）+ 两侧有限
（`fan_imp_finite_set` :42 / `FINITE_SET_OF_LIST`）+ 基数链 `CARD V =
number_of_nodes(hypermap_of_fan) = number_of_nodes(hypermap_of_list) =
sizel(list_of_elements) = CARD(elements_of_list)`（`fan_number_of_nodes` :59 ←
`NODE_SET_AS_IMAGE`；`iso_number_of_nodes`；`good_list_nodes_condition`；
`card_set_of_list_uniq`+`uniq_list_of_elements`）。

Lean 侧结构对应：SURJ 两支对 `hyp_iso_eq_fan_list_iso` 的消费只是
`FST(f d) = h'(FST d)`——装配里即 `hdecomp` 假设，σ-orbit 内容零消费；
fan 侧基数走 `nFanPair` 定义性保 FST + `nFanPair_iterate`（Fan.lean:1045）的
注入（`NODE_SET_AS_IMAGE` 镜像）；iso 侧走 nodeMap 迭代交换的像运输
（`iso_number_of_nodes` 镜像）；list 侧基数由 `hnodes`（= HOL
`good_list_nodes` 的 nodeSet 等式形态）+ 覆盖件注入完成。-/

/-- elements 投影覆盖（converse 支）：`elementsOfList L` 的每个元素都是某个
dart 的第一分量。witness 取循环 zip 第二表 `l₀.drop 1 ++ l₀.take 1` 的第 i 项
（`List.getElem_zip` 一步展开），无 singleton/末元素分支。 -/
theorem lpElementsCoverage {L : fgraph ℕ} {x : ℕ} (hx : x ∈ elementsOfList L) :
    ∃ d ∈ listOfDarts L, d.1 = x := by
  obtain ⟨l0, hl0, hx0⟩ := List.mem_flatten.mp (List.mem_eraseDups.mp hx)
  obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx0
  have hn : 0 < l0.length := by omega
  have hlenA : (l0.drop 1 ++ l0.take 1).length = l0.length := by
    rw [List.length_append, List.length_drop, List.length_take]
    omega
  have hiA : i < (l0.drop 1 ++ l0.take 1).length := by omega
  have hiZ : i < (l0.zip (l0.drop 1 ++ l0.take 1)).length := by
    rw [List.length_zip, hlenA]
    omega
  have hz : (l0.zip (l0.drop 1 ++ l0.take 1))[i]'hiZ =
      (x, (l0.drop 1 ++ l0.take 1)[i]'hiA) := by
    rw [List.getElem_zip, hxi]
  have hmemz : (x, (l0.drop 1 ++ l0.take 1)[i]'hiA) ∈
      l0.zip (l0.drop 1 ++ l0.take 1) := by
    rw [← hz]
    exact List.getElem_mem hiZ
  refine ⟨(x, (l0.drop 1 ++ l0.take 1)[i]'hiA), ?_, rfl⟩
  exact List.mem_flatten.mpr ⟨l0.zip (l0.drop 1 ++ l0.take 1),
    List.mem_map.mpr ⟨l0, hl0, rfl⟩, hmemz⟩

/-- `hypermapOfList` 的 dart 集 coe → `listOfDarts` 成员（`darts_hypermapOfList`
的展开形）。 -/
private theorem lpMemDartsList {L : fgraph ℕ} {hL : GoodList L} {d : ℕ × ℕ}
    (hd : d ∈ (↑(hypermapOfList L hL).darts : Set (ℕ × ℕ))) : d ∈ listOfDarts L := by
  rwa [darts_hypermapOfList] at hd

/-- `listOfDarts` 成员 → `hypermapOfList` 的 dart 集 coe。 -/
private theorem lpCoeMemDartsList {L : fgraph ℕ} {hL : GoodList L} {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) : d ∈ (↑(hypermapOfList L hL).darts : Set (ℕ × ℕ)) := by
  rw [darts_hypermapOfList]
  exact hd

/-- node 成员的轨道刻画（`Hypermap.node` = `orbitMap nodeMap` 定义的 Iff 桥；
`(p ^ n)` ↔ `p^[n]` 经 `Equiv.Perm.coe_pow`）。 -/
private theorem lpMemNodeIff {α : Type*} [DecidableEq α] (H : Hypermap α) {x y : α} :
    y ∈ H.node x ↔ ∃ n : ℕ, (H.nodeMap : α ≃ α)^[n] x = y := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [← Equiv.Perm.coe_pow]
    exact hn
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [Equiv.Perm.coe_pow]
    exact hn

/-- fan nodeMap 迭代：留在 `dart1OfFan` 内且第一分量不变
（HOL `fst_n_list_ext_power` 的 fan 侧镜像；`nodeMapTl_apply` +
`nFanPair_iterate`）。 -/
private theorem lpNodeMapIterate {V : Set V3} {E : Set (Set V3)} (hfan : FAN 0 V E)
    {d : V3 × V3} (hd : d ∈ dart1OfFan V E) (n : ℕ) :
    (hypermapOfFanTl V E hfan).nodeMap^[n] d ∈ dart1OfFan V E ∧
      ((hypermapOfFanTl V E hfan).nodeMap^[n] d).1 = d.1 := by
  induction n with
  | zero => exact ⟨hd, rfl⟩
  | succ n ih =>
    obtain ⟨hmem, hfst⟩ := ih
    have hstep : (hypermapOfFanTl V E hfan).nodeMap^[n + 1] d =
        nFanPair 0 V E ((hypermapOfFanTl V E hfan).nodeMap^[n] d) := by
      rw [Function.iterate_succ_apply', nodeMapTl_apply hmem]
    refine ⟨?_, ?_⟩
    · rw [hstep]
      exact nFanPair_mem_dart1 hfan hmem
    · rw [hstep]
      simp [nFanPair, hfst]

/-- iso 的 nodeMap 迭代交换（`hisoComm` 的迭代化；HOL `iso_components` 镜像）。 -/
private theorem lpNodeIterComm {V : Set V3} {E : Set (Set V3)} {L : fgraph ℕ}
    {hL : GoodList L} {f : V3 × V3 → ℕ × ℕ}
    (hfan : FAN 0 V E)
    (hisoComm : ∀ d ∈ (hypermapOfFanTl V E hfan).darts,
        (hypermapOfList L hL).edgeMap (f d) =
          f ((hypermapOfFanTl V E hfan).edgeMap d) ∧
        (hypermapOfList L hL).nodeMap (f d) =
          f ((hypermapOfFanTl V E hfan).nodeMap d) ∧
        (hypermapOfList L hL).faceMap (f d) =
          f ((hypermapOfFanTl V E hfan).faceMap d))
    {d : V3 × V3} (hd : d ∈ dart1OfFan V E) (n : ℕ) :
    (hypermapOfList L hL).nodeMap^[n] (f d) =
      f ((hypermapOfFanTl V E hfan).nodeMap^[n] d) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hmem : (hypermapOfFanTl V E hfan).nodeMap^[n] d ∈ dart1OfFan V E :=
      (lpNodeMapIterate hfan hd n).1
    simp only [Function.iterate_succ_apply']
    rw [ih, (hisoComm _ (mem_dartsTl hmem)).2.1]

/-- 轨道运输：`f` 把 fan node 轨道送到 list node 轨道
（HOL `iso_components` 的 node 合取支镜像）。 -/
private theorem lpOrbitTransport {V : Set V3} {E : Set (Set V3)} {L : fgraph ℕ}
    {hL : GoodList L} {f : V3 × V3 → ℕ × ℕ}
    (hfan : FAN 0 V E)
    (hisoDart : Set.BijOn f ↑(hypermapOfFanTl V E hfan).darts
        ↑(hypermapOfList L hL).darts)
    (hisoComm : ∀ d ∈ (hypermapOfFanTl V E hfan).darts,
        (hypermapOfList L hL).edgeMap (f d) =
          f ((hypermapOfFanTl V E hfan).edgeMap d) ∧
        (hypermapOfList L hL).nodeMap (f d) =
          f ((hypermapOfFanTl V E hfan).nodeMap d) ∧
        (hypermapOfList L hL).faceMap (f d) =
          f ((hypermapOfFanTl V E hfan).faceMap d))
    {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    f '' ((hypermapOfFanTl V E hfan).node d) =
      (hypermapOfList L hL).node (f d) := by
  ext y
  constructor
  · rintro ⟨z, hz, hfz⟩
    obtain ⟨n, hn⟩ := (lpMemNodeIff _).mp hz
    have hy' : (hypermapOfList L hL).nodeMap^[n] (f d) = y := by
      rw [lpNodeIterComm hfan hisoComm hd n, ← hfz, hn]
    exact (lpMemNodeIff _).mpr ⟨n, hy'⟩
  · intro hy
    obtain ⟨n, hn⟩ := (lpMemNodeIff _).mp hy
    have hmemO : (hypermapOfFanTl V E hfan).nodeMap^[n] d ∈
        (hypermapOfFanTl V E hfan).node d := (lpMemNodeIff _).mpr ⟨n, rfl⟩
    refine ⟨_, hmemO, ?_⟩
    rw [← lpNodeIterComm hfan hisoComm hd n]
    exact hn

/-- fan 侧基数：`V.ncard ≤ nodeSet(hypermapOfFanTl).ncard`
（HOL `fan_number_of_nodes`/`NODE_SET_AS_IMAGE` 镜像；注入 `v ↦ node(v, w_v)`
的单射性由 `lpNodeMapIterate` 的第一分量不变性承载，**无需 σ 轮换性**）。 -/
private theorem lpFanNodeCardLe {V : Set V3} {E : Set (Set V3)} (hlpfan : LpFan V E) :
    V.ncard ≤ (hypermapOfFanTl V E hlpfan.1).nodeSet.ncard := by
  have hex : ∀ v : V3, ∃ w : V3, v ∈ V → {v, w} ∈ E := by
    intro v
    by_cases hv : v ∈ V
    · obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr (lpFan_setOfEdge_ne hlpfan hv)
      exact ⟨w, fun _ => hw.1⟩
    · exact ⟨v, fun hv' => absurd hv' hv⟩
  choose w hw using hex
  have hd1 : ∀ v ∈ V, (v, w v) ∈ dart1OfFan V E := fun v hv => by
    simp only [dart1OfFan, Set.mem_setOf_eq]
    exact hw v hv
  have hg : ∀ v ∈ V, (hypermapOfFanTl V E hlpfan.1).node (v, w v) ∈
      (hypermapOfFanTl V E hlpfan.1).nodeSet := by
    intro v hv
    exact Set.mem_setOf.mpr ⟨(v, w v), mem_dartsTl (hd1 v hv), rfl⟩
  refine Set.ncard_le_ncard_of_injOn
    (fun v : V3 => (hypermapOfFanTl V E hlpfan.1).node (v, w v)) hg ?_ ?_
  · intro a ha b hb hEq
    have hEq' : (hypermapOfFanTl V E hlpfan.1).node (a, w a) =
        (hypermapOfFanTl V E hlpfan.1).node (b, w b) := hEq
    have hmem' : (b, w b) ∈ (hypermapOfFanTl V E hlpfan.1).node (a, w a) := by
      rw [hEq']
      exact Hypermap.mem_node_self _ _
    obtain ⟨n, hn⟩ := (lpMemNodeIff _).mp hmem'
    have hit := lpNodeMapIterate hlpfan.1 (hd1 a ha) n
    rw [hn] at hit
    have hba : b = a := by simpa using hit.2
    exact hba.symm
  · exact Kepler.Text.setOfOrbits_finite (hypermapOfFanTl V E hlpfan.1).darts
      (hypermapOfFanTl V E hlpfan.1).nodeMap

/-- iso 侧基数：`nodeSet(fan).ncard ≤ nodeSet(list).ncard`
（HOL `iso_number_of_nodes` 镜像；`f '' O` 运输 + `hisoDart.injOn`）。 -/
private theorem lpIsoNodeCardLe {V : Set V3} {E : Set (Set V3)} {L : fgraph ℕ}
    {hL : GoodList L} {f : V3 × V3 → ℕ × ℕ}
    (hlpfan : LpFan V E)
    (hisoDart : Set.BijOn f ↑(hypermapOfFanTl V E hlpfan.1).darts
        ↑(hypermapOfList L hL).darts)
    (hisoComm : ∀ d ∈ (hypermapOfFanTl V E hlpfan.1).darts,
        (hypermapOfList L hL).edgeMap (f d) =
          f ((hypermapOfFanTl V E hlpfan.1).edgeMap d) ∧
        (hypermapOfList L hL).nodeMap (f d) =
          f ((hypermapOfFanTl V E hlpfan.1).nodeMap d) ∧
        (hypermapOfList L hL).faceMap (f d) =
          f ((hypermapOfFanTl V E hlpfan.1).faceMap d)) :
    (hypermapOfFanTl V E hlpfan.1).nodeSet.ncard ≤
      (hypermapOfList L hL).nodeSet.ncard := by
  have hfan : FAN 0 V E := hlpfan.1
  have hmaps : ∀ O ∈ (hypermapOfFanTl V E hfan).nodeSet,
      f '' O ∈ (hypermapOfList L hL).nodeSet := by
    intro O hO
    obtain ⟨d, hd, rfl⟩ := Set.mem_setOf.mp hO
    show f '' (hypermapOfFanTl V E hfan).node d ∈ (hypermapOfList L hL).nodeSet
    rw [lpOrbitTransport hfan hisoDart hisoComm (dartsTl_mem hd)]
    exact Set.mem_setOf.mpr ⟨f d,
      Finset.mem_coe.mpr (hisoDart.mapsTo (Finset.mem_coe.mpr hd)), rfl⟩
  refine Set.ncard_le_ncard_of_injOn (fun O : Set (V3 × V3) => f '' O) hmaps ?_ ?_
  · intro O hO O' hO' hEq
    obtain ⟨d, hd, rfl⟩ := Set.mem_setOf.mp hO
    obtain ⟨e, he, rfl⟩ := Set.mem_setOf.mp hO'
    have hEq' : f '' (hypermapOfFanTl V E hfan).node d =
        f '' (hypermapOfFanTl V E hfan).node e := hEq
    have hfd : f d ∈ f '' (hypermapOfFanTl V E hfan).node e := by
      rw [← hEq']
      exact ⟨d, Hypermap.mem_node_self _ _, rfl⟩
    obtain ⟨z, hz, hfz⟩ := hfd
    obtain ⟨n, hn⟩ := (lpMemNodeIff _).mp hz
    have hz2 : z ∈ dart1OfFan V E := by
      rw [← hn]
      exact (lpNodeMapIterate hfan (dartsTl_mem he) n).1
    have hzCoe : z ∈ (↑(hypermapOfFanTl V E hfan).darts : Set (V3 × V3)) := by
      rw [dartsTl_coe]
      exact hz2
    have hdCoe : d ∈ (↑(hypermapOfFanTl V E hfan).darts : Set (V3 × V3)) :=
      Finset.mem_coe.mpr hd
    have hz_eq : z = d := hisoDart.injOn hzCoe hdCoe hfz
    have hd_in : d ∈ (hypermapOfFanTl V E hfan).node e := by
      rw [← hz_eq]
      exact hz
    exact (Hypermap.node_eq_of_mem _ hd_in).symm
  · exact Kepler.Text.setOfOrbits_finite (hypermapOfList L hL).darts
      (hypermapOfList L hL).nodeMap

/-- list 侧基数：`nodeSet(hypermapOfList).ncard = elementsOfList.ncard`
（HOL `good_list_nodes_condition` + `card_set_of_list_uniq`/
`uniq_list_of_elements` 的镜像；nodeSet = nodesOfListSet 由 `hnodes` 给出，
node(x) 对 x 的单射性由覆盖件承载）。 -/
private theorem lpNodeListCardEq {L : fgraph ℕ} {hL : GoodList L}
    (hnodes : GoodListNodesTl L hL) :
    (hypermapOfList L hL).nodeSet.ncard = (elementsOfList L).ncard := by
  have hF : nodesOfListSet L =
      (fun x : ℕ => {d : ℕ × ℕ | d ∈ listOfDarts L ∧ d.1 = x}) '' elementsOfList L :=
    rfl
  have hfin : (elementsOfList L).Finite :=
    Set.Finite.subset (Finset.finite_toSet (listOfElements L).toFinset)
      (fun x hx => List.mem_toFinset.mpr hx)
  have hInj : Set.InjOn (fun x : ℕ => {d : ℕ × ℕ | d ∈ listOfDarts L ∧ d.1 = x})
      (elementsOfList L) := by
    intro x hx y hy hEq
    obtain ⟨d, hd, hd1⟩ := lpElementsCoverage hx
    have hmemx : d ∈ (fun x : ℕ => {d : ℕ × ℕ | d ∈ listOfDarts L ∧ d.1 = x}) x :=
      ⟨hd, hd1⟩
    rw [hEq] at hmemx
    exact hd1.symm.trans hmemx.2
  rw [hnodes, hF, Set.InjOn.ncard_image hInj]

/-- mapsTo 支：`h'` 把 V 送进 `elementsOfList`（HOL `fan_list_nodes_iso_surj`
第一支；`FST(f(v,w)) = h' v` 由 `hdecomp` 承载）。 -/
private theorem lpNodeMapsTo {V : Set V3} {E : Set (Set V3)} {L : fgraph ℕ}
    {hL : GoodList L} {h' : V3 → ℕ} {f : V3 × V3 → ℕ × ℕ}
    (hlpfan : LpFan V E)
    (hisoDart : Set.BijOn f ↑(hypermapOfFanTl V E hlpfan.1).darts
        ↑(hypermapOfList L hL).darts)
    (hdecomp : ∀ d ∈ dart1OfFan V E, f d = (h' d.1, h' d.2)) {v : V3} (hv : v ∈ V) :
    h' v ∈ elementsOfList L := by
  obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr (lpFan_setOfEdge_ne hlpfan hv)
  have hd : (v, w) ∈ dart1OfFan V E := Set.mem_setOf.mpr hw.1
  have hfd : f (v, w) ∈ (↑(hypermapOfList L hL).darts : Set (ℕ × ℕ)) :=
    hisoDart.mapsTo (Finset.mem_coe.mpr (mem_dartsTl hd))
  have hproj := listOfDarts_fst_snd_mem_elementsOfList (lpMemDartsList hfd)
  have hfst : (f (v, w)).1 = h' v := by rw [hdecomp (v, w) hd]
  rw [← hfst]
  exact hproj.1

/-- surjOn 支：每个元素都是某 `v ∈ V` 的像（HOL `fan_list_nodes_iso_surj`
第二支：覆盖件 + `hisoDart.surjOn` 逆 dart + `hdecomp`）。 -/
private theorem lpNodeSurjOn {V : Set V3} {E : Set (Set V3)} {L : fgraph ℕ}
    {hL : GoodList L} {h' : V3 → ℕ} {f : V3 × V3 → ℕ × ℕ}
    (hlpfan : LpFan V E)
    (hisoDart : Set.BijOn f ↑(hypermapOfFanTl V E hlpfan.1).darts
        ↑(hypermapOfList L hL).darts)
    (hdecomp : ∀ d ∈ dart1OfFan V E, f d = (h' d.1, h' d.2)) :
    Set.SurjOn h' V (elementsOfList L) := by
  intro x hx
  obtain ⟨d, hd, hd1⟩ := lpElementsCoverage hx
  obtain ⟨e, hemem, hfe⟩ := hisoDart.surjOn (lpCoeMemDartsList hd)
  have he1 : e ∈ dart1OfFan V E := dartsTl_mem hemem
  have hfst : (f e).1 = h' e.1 := by rw [hdecomp e he1]
  have hfex : (f e).1 = x := by rw [hfe, hd1]
  exact ⟨e.1, (dart1OfFan_fst_snd_mem hlpfan.1 he1).1, hfst.symm.trans hfex⟩

/-- `fan_list_nodes_iso_BIJ`（list_hypermap_iso-compiled.hl:777-787）的装配形：
`hbijNode : Set.BijOn h' V (elementsOfList L)` 的真证。基数链
`V ≤ nodeSet(fan) ≤ nodeSet(list) = elementsOfList`（件 5-7）+ surjOn +
鸽笼（`Set.ncard_sdiff_singleton_lt_of_mem`）给 injOn。σ-orbit 内容零消费。 -/
theorem lpBijOnNodeOfIso {V : Set V3} {E : Set (Set V3)} {L : fgraph ℕ}
    {hL : GoodList L} {h' : V3 → ℕ} {f : V3 × V3 → ℕ × ℕ}
    (hlpfan : LpFan V E) (hnodes : GoodListNodesTl L hL)
    (hdecomp : ∀ d ∈ dart1OfFan V E, f d = (h' d.1, h' d.2))
    (hisoDart : Set.BijOn f ↑(hypermapOfFanTl V E hlpfan.1).darts
        ↑(hypermapOfList L hL).darts)
    (hisoComm : ∀ d ∈ (hypermapOfFanTl V E hlpfan.1).darts,
        (hypermapOfList L hL).edgeMap (f d) =
          f ((hypermapOfFanTl V E hlpfan.1).edgeMap d) ∧
        (hypermapOfList L hL).nodeMap (f d) =
          f ((hypermapOfFanTl V E hlpfan.1).nodeMap d) ∧
        (hypermapOfList L hL).faceMap (f d) =
          f ((hypermapOfFanTl V E hlpfan.1).faceMap d)) :
    Set.BijOn h' V (elementsOfList L) := by
  have hmaps : Set.MapsTo h' V (elementsOfList L) := fun v hv =>
    lpNodeMapsTo hlpfan hisoDart hdecomp hv
  have hsurj : Set.SurjOn h' V (elementsOfList L) := lpNodeSurjOn hlpfan hisoDart hdecomp
  have hfinV : V.Finite := hlpfan.1.2.2.1.1
  have hfinL : (elementsOfList L).Finite :=
    Set.Finite.subset (Finset.finite_toSet (listOfElements L).toFinset)
      (fun x hx => List.mem_toFinset.mpr hx)
  have hchain : V.ncard ≤ (elementsOfList L).ncard :=
    le_trans (le_trans (lpFanNodeCardLe hlpfan) (lpIsoNodeCardLe hlpfan hisoDart hisoComm))
      (lpNodeListCardEq hnodes).le
  refine ⟨hmaps, ?_, hsurj⟩
  intro a ha b hb hab
  by_contra hne
  have hsub : elementsOfList L ⊆ h' '' (V \ {a}) := by
    intro z hz
    obtain ⟨v, hv, hvz⟩ := hsurj hz
    by_cases hva : v = a
    · subst hva
      exact ⟨b, ⟨hb, Ne.symm hne⟩, hab.symm.trans hvz⟩
    · exact ⟨v, ⟨hv, hva⟩, hvz⟩
  have hfinVd : (V \ {a}).Finite := Set.Finite.subset hfinV Set.sdiff_subset
  have h1 : (elementsOfList L).ncard ≤ (h' '' (V \ {a})).ncard :=
    Set.ncard_le_ncard hsub (hfinVd.image _)
  have h2 : (h' '' (V \ {a})).ncard ≤ (V \ {a}).ncard := Set.ncard_image_le hfinVd
  have h3 : (V \ {a}).ncard < V.ncard := Set.ncard_sdiff_singleton_lt_of_mem ha hfinV
  exact lt_irrefl _ (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h3 hchain) h1) h2)

/-- HOL `lp_cond_lemma`（`lp_ineqs_proofs-compiled.hl:186-327`）的装配形。
结论 = `lp_cond (L, g, h) (V, E)` 七合取的 Lean 直书展开（`LpCond` 定义未入
Lean，按 def 冻结红线以显式合取陈述；`hyp_iso` 双向均以 `Set.BijOn` +
三映射交换直书；末三合取支即 HOL 尾注 `∀x. h x = if x IN elements_of_list L
then res_inv … else vec 0` 的性质化）。两个具名假设即 HOL 深件、尚未移植：
- `hbijNode` = `fan_list_nodes_iso_BIJ`（list_hypermap_iso-compiled.hl:777；
  依赖 `hyp_iso_eq_fan_list_iso`(:676) + 节点计数链 `iso_number_of_nodes` /
  `NODE_SET_AS_IMAGE`）；
- `hdecomp` = `hyp_iso_eq_fan_list_iso` 的 dart 式结论（同一引理；其证明需
  σ-orbit 覆盖论证 `NODE_HYPERMAP_OF_FAN_ALT` + `fst_n_list_ext_power`，
  Lean 侧 sigmaFan 轨道件未移植）。
其余步骤逐条对照 HOL 脚本 :193-327：`res_inv` 逆构造（`exists_nodeInverse`）、
`BIJ_pair` 运输、iso 取逆（对偶方向由 `hdecomp` + 原前提 BijOn 重建）、
`x IN elements_of_list L <=> h x IN V`（junk 0 ∉ V 经 `V ⊆ ballAnnulus`）。 -/
theorem lpCondAssembly {V : Set V3} {E : Set (Set V3)} {L : fgraph ℕ} {hL : GoodList L}
    {h' : V3 → ℕ} {f : V3 × V3 → ℕ × ℕ}
    (hlpfan : LpFan V E) (hgood : GoodList L) (hnodes : GoodListNodesTl L hL)
    (hbijNode : Set.BijOn h' V (elementsOfList L))
    (hdecomp : ∀ d ∈ dart1OfFan V E, f d = (h' d.1, h' d.2))
    (hisoDart : Set.BijOn f ↑(hypermapOfFanTl V E hlpfan.1).darts
        ↑(hypermapOfList L hL).darts)
    (hisoComm : ∀ d ∈ (hypermapOfFanTl V E hlpfan.1).darts,
        (hypermapOfList L hL).edgeMap (f d) =
          f ((hypermapOfFanTl V E hlpfan.1).edgeMap d) ∧
        (hypermapOfList L hL).nodeMap (f d) =
          f ((hypermapOfFanTl V E hlpfan.1).nodeMap d) ∧
        (hypermapOfList L hL).faceMap (f d) =
          f ((hypermapOfFanTl V E hlpfan.1).faceMap d)) :
    ∃ g : ℕ × ℕ → V3 × V3, ∃ h : ℕ → V3,
      LpFan V E ∧ GoodList L ∧ GoodListNodesTl L hL ∧
      Set.BijOn g ↑(hypermapOfList L hL).darts
        ↑(hypermapOfFanTl V E hlpfan.1).darts ∧
      (∀ d ∈ (hypermapOfList L hL).darts,
          (hypermapOfFanTl V E hlpfan.1).edgeMap (g d) =
            g ((hypermapOfList L hL).edgeMap d) ∧
          (hypermapOfFanTl V E hlpfan.1).nodeMap (g d) =
            g ((hypermapOfList L hL).nodeMap d) ∧
          (hypermapOfFanTl V E hlpfan.1).faceMap (g d) =
            g ((hypermapOfList L hL).faceMap d)) ∧
      Set.BijOn h (elementsOfList L) V ∧
      (∀ d : ℕ × ℕ, g d = (h d.1, h d.2)) ∧
      (∀ x, x ∈ elementsOfList L ↔ h x ∈ V) ∧
      (∀ x ∈ elementsOfList L, h' (h x) = x) ∧
      (∀ v ∈ V, h (h' v) = v) ∧
      (∀ x, x ∉ elementsOfList L → h x = 0) := by
  obtain ⟨h, hmemS, hinvS, hbijH, hzero⟩ := exists_nodeInverse hbijNode
  -- 原点不在 V（`V ⊆ ballAnnulus`，ballAnnulus 是闭球去开球的环）
  have h0not : (0 : V3) ∉ ballAnnulus := by
    intro h0
    have hball : (0 : V3) ∈ Metric.ball (0 : V3) 2 := Metric.mem_ball_self (by norm_num)
    exact h0.2 hball
  have h0V : ∀ v ∈ V, v ≠ (0 : V3) := by
    intro v hv hv0
    have hvz : (0 : V3) ∈ V := by rw [← hv0]; exact hv
    exact h0not (hlpfan.2.2.2.1 hvz)
  -- 原件 witness 段（HOL :214-215）：g := pair-lift h，及其 dart1 恒等式
  have gfe : ∀ e ∈ dart1OfFan V E, (fun d : ℕ × ℕ => (h d.1, h d.2)) (f e) = e := by
    intro e he
    have hV := dart1OfFan_fst_snd_mem hlpfan.1 he
    have hd := hdecomp e he
    have h1 : (f e).1 = h' e.1 := by rw [hd]
    have h2 : (f e).2 = h' e.2 := by rw [hd]
    show (h (f e).1, h (f e).2) = e
    rw [h1, h2, hinvS e.1 hV.1, hinvS e.2 hV.2]
  -- coe-darts → listOfDarts 归属
  have hdartL_mem : ∀ ⦃d : ℕ × ℕ⦄,
      d ∈ (↑(hypermapOfList L hL).darts : Set (ℕ × ℕ)) → d ∈ listOfDarts L := by
    intro d hd
    have h0 : d ∈ (↑(hypermapOfList L hL).darts : Set (ℕ × ℕ)) := hd
    rwa [darts_hypermapOfList] at h0
  -- 对偶方向 BijOn（HOL :253-269 经 hyp_iso_inv + bij_ext 的路线，
  -- 此处以 hdecomp + 原前提 BijOn 重建）
  have hbijG : Set.BijOn (fun d : ℕ × ℕ => (h d.1, h d.2))
      (↑(hypermapOfList L hL).darts : Set (ℕ × ℕ))
      (↑(hypermapOfFanTl V E hlpfan.1).darts : Set (V3 × V3)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro d hd
      obtain ⟨e, hemem, hfe⟩ := hisoDart.surjOn hd
      have he1 : e ∈ dart1OfFan V E := dartsTl_mem hemem
      have hgd : (fun d : ℕ × ℕ => (h d.1, h d.2)) d =
          (fun d : ℕ × ℕ => (h d.1, h d.2)) (f e) := by rw [hfe]
      rw [hgd, gfe e he1]
      exact Finset.mem_coe.mpr (mem_dartsTl he1)
    · intro a ha b hb hEq
      have hPa := listOfDarts_fst_snd_mem_elementsOfList (hdartL_mem ha)
      have hPb := listOfDarts_fst_snd_mem_elementsOfList (hdartL_mem hb)
      have e1 : h a.1 = h b.1 := congrArg Prod.fst hEq
      have e2 : h a.2 = h b.2 := congrArg Prod.snd hEq
      have k1 : a.1 = b.1 := hbijH.injOn hPa.1 hPb.1 e1
      have k2 : a.2 = b.2 := hbijH.injOn hPa.2 hPb.2 e2
      have eta : a = (a.1, a.2) := rfl
      rw [eta, k1, k2]
    · intro e he
      have he1 : e ∈ dart1OfFan V E := dartsTl_mem he
      exact ⟨f e, hisoDart.mapsTo he, gfe e he1⟩
  -- 对偶方向交换律（HOL :270-276：g 为 f 的逐点逆，经 hyp_iso_inv 迁移）
  have hcommG : ∀ d ∈ (↑(hypermapOfList L hL).darts : Set (ℕ × ℕ)),
      (hypermapOfFanTl V E hlpfan.1).edgeMap ((fun d : ℕ × ℕ => (h d.1, h d.2)) d) =
        (fun d : ℕ × ℕ => (h d.1, h d.2)) ((hypermapOfList L hL).edgeMap d) ∧
      (hypermapOfFanTl V E hlpfan.1).nodeMap ((fun d : ℕ × ℕ => (h d.1, h d.2)) d) =
        (fun d : ℕ × ℕ => (h d.1, h d.2)) ((hypermapOfList L hL).nodeMap d) ∧
      (hypermapOfFanTl V E hlpfan.1).faceMap ((fun d : ℕ × ℕ => (h d.1, h d.2)) d) =
        (fun d : ℕ × ℕ => (h d.1, h d.2)) ((hypermapOfList L hL).faceMap d) := by
    intro d hd
    obtain ⟨e, hemem, hfe⟩ := hisoDart.surjOn hd
    have he1 : e ∈ dart1OfFan V E := dartsTl_mem hemem
    have gde : (fun d : ℕ × ℕ => (h d.1, h d.2)) d = e := by
      rw [← hfe]; exact gfe e he1
    refine ⟨?_, ?_, ?_⟩
    · have hfane : (hypermapOfFanTl V E hlpfan.1).edgeMap e ∈
        (hypermapOfFanTl V E hlpfan.1).darts := Hypermap.edgeMap_apply_mem _ hemem
      have hfane1 : (hypermapOfFanTl V E hlpfan.1).edgeMap e ∈ dart1OfFan V E :=
        dartsTl_mem hfane
      have hstep : (hypermapOfList L hL).edgeMap d =
          f ((hypermapOfFanTl V E hlpfan.1).edgeMap e) := by
        rw [← hfe]
        exact (hisoComm e hemem).1
      rw [hstep, gfe ((hypermapOfFanTl V E hlpfan.1).edgeMap e) hfane1, gde]
    · have hfane : (hypermapOfFanTl V E hlpfan.1).nodeMap e ∈
        (hypermapOfFanTl V E hlpfan.1).darts := Hypermap.nodeMap_apply_mem _ hemem
      have hfane1 : (hypermapOfFanTl V E hlpfan.1).nodeMap e ∈ dart1OfFan V E :=
        dartsTl_mem hfane
      have hstep : (hypermapOfList L hL).nodeMap d =
          f ((hypermapOfFanTl V E hlpfan.1).nodeMap e) := by
        rw [← hfe]
        exact (hisoComm e hemem).2.1
      rw [hstep, gfe ((hypermapOfFanTl V E hlpfan.1).nodeMap e) hfane1, gde]
    · have hfane : (hypermapOfFanTl V E hlpfan.1).faceMap e ∈
        (hypermapOfFanTl V E hlpfan.1).darts := Hypermap.faceMap_apply_mem _ hemem
      have hfane1 : (hypermapOfFanTl V E hlpfan.1).faceMap e ∈ dart1OfFan V E :=
        dartsTl_mem hfane
      have hstep : (hypermapOfList L hL).faceMap d =
          f ((hypermapOfFanTl V E hlpfan.1).faceMap e) := by
        rw [← hfe]
        exact (hisoComm e hemem).2.2
      rw [hstep, gfe ((hypermapOfFanTl V E hlpfan.1).faceMap e) hfane1, gde]
  -- 成员 iff（HOL :248-252 经 bij_res_inv；junk 0 ∉ V 由 ballAnnulus 承载）
  have hiff : ∀ x : ℕ, x ∈ elementsOfList L ↔ h x ∈ V := by
    intro x
    constructor
    · intro hx
      exact hbijH.mapsTo hx
    · intro hxv
      by_contra hx0
      have hzx : h x = 0 := hzero x hx0
      rw [hzx] at hxv
      exact h0V (0 : V3) hxv rfl
  refine ⟨fun d : ℕ × ℕ => (h d.1, h d.2), h, hlpfan, hgood, hnodes, hbijG, hcommG,
    hbijH, fun _ => rfl, hiff, fun x hx => (hmemS x hx).2, hinvS, hzero⟩

/-- `lpCondAssembly` 的 `Hypermap.Iso` 包装：同前提给出
`hypermapOfList L hL` 到 fan 超映射的 `Kepler.Text.Hypermap.Iso`
（W6 下游 ∃-形接口；HOL `lp_cond` 的 `hyp_iso g (hypermap_of_list,
hypermap_of_fan)` 合取支的同构包装形）。 -/
theorem iso_of_lpCondAssembly {V : Set V3} {E : Set (Set V3)} {L : fgraph ℕ}
    {hL : GoodList L} {h' : V3 → ℕ} {f : V3 × V3 → ℕ × ℕ}
    (hlpfan : LpFan V E) (hgood : GoodList L) (hnodes : GoodListNodesTl L hL)
    (hbijNode : Set.BijOn h' V (elementsOfList L))
    (hdecomp : ∀ d ∈ dart1OfFan V E, f d = (h' d.1, h' d.2))
    (hisoDart : Set.BijOn f ↑(hypermapOfFanTl V E hlpfan.1).darts
        ↑(hypermapOfList L hL).darts)
    (hisoComm : ∀ d ∈ (hypermapOfFanTl V E hlpfan.1).darts,
        (hypermapOfList L hL).edgeMap (f d) =
          f ((hypermapOfFanTl V E hlpfan.1).edgeMap d) ∧
        (hypermapOfList L hL).nodeMap (f d) =
          f ((hypermapOfFanTl V E hlpfan.1).nodeMap d) ∧
        (hypermapOfList L hL).faceMap (f d) =
          f ((hypermapOfFanTl V E hlpfan.1).faceMap d)) :
    Hypermap.Iso (hypermapOfList L hL) (hypermapOfFanTl V E hlpfan.1) := by
  obtain ⟨g, h, -, -, -, hbij, hcomm, -, -, -, -, -, -⟩ :=
    lpCondAssembly hlpfan hgood hnodes hbijNode hdecomp hisoDart hisoComm
  exact ⟨g, hbij, hcomm⟩

-- 【W6-B 第三件 · 零删除改版】`hbijNode`（= HOL `fan_list_nodes_iso_BIJ`，
-- list_hypermap_iso-compiled.hl:777-787 节点计数链）已由 `lpBijOnNodeOfIso`
-- 真证；下方 `_nf` 后缀的无假设主件供下游消费，上方原假设型主件原样保留。

/-- `lpCondAssembly` 的无假设版（W6-B 第三件）：原版的显式假设
`hbijNode : Set.BijOn h' V (elementsOfList L)` 由 `lpBijOnNodeOfIso`（节点
计数链，σ-orbit 内容零消费）就地真证消掉，前提面只剩 `hdecomp`
（= HOL `hyp_iso_eq_fan_list_iso` 的 dart 式结论，σ_fan 轮换性深件，仍开放）。
结论与 `lpCondAssembly` 逐字同型（证明 = 注入真证 hbijNode 后转调原版）；
下游应消费本版。 -/
theorem lpCondAssembly_nf {V : Set V3} {E : Set (Set V3)} {L : fgraph ℕ} {hL : GoodList L}
    {h' : V3 → ℕ} {f : V3 × V3 → ℕ × ℕ}
    (hlpfan : LpFan V E) (hgood : GoodList L) (hnodes : GoodListNodesTl L hL)
    (hdecomp : ∀ d ∈ dart1OfFan V E, f d = (h' d.1, h' d.2))
    (hisoDart : Set.BijOn f ↑(hypermapOfFanTl V E hlpfan.1).darts
        ↑(hypermapOfList L hL).darts)
    (hisoComm : ∀ d ∈ (hypermapOfFanTl V E hlpfan.1).darts,
        (hypermapOfList L hL).edgeMap (f d) =
          f ((hypermapOfFanTl V E hlpfan.1).edgeMap d) ∧
        (hypermapOfList L hL).nodeMap (f d) =
          f ((hypermapOfFanTl V E hlpfan.1).nodeMap d) ∧
        (hypermapOfList L hL).faceMap (f d) =
          f ((hypermapOfFanTl V E hlpfan.1).faceMap d)) :
    ∃ g : ℕ × ℕ → V3 × V3, ∃ h : ℕ → V3,
      LpFan V E ∧ GoodList L ∧ GoodListNodesTl L hL ∧
      Set.BijOn g ↑(hypermapOfList L hL).darts
        ↑(hypermapOfFanTl V E hlpfan.1).darts ∧
      (∀ d ∈ (hypermapOfList L hL).darts,
          (hypermapOfFanTl V E hlpfan.1).edgeMap (g d) =
            g ((hypermapOfList L hL).edgeMap d) ∧
          (hypermapOfFanTl V E hlpfan.1).nodeMap (g d) =
            g ((hypermapOfList L hL).nodeMap d) ∧
          (hypermapOfFanTl V E hlpfan.1).faceMap (g d) =
            g ((hypermapOfList L hL).faceMap d)) ∧
      Set.BijOn h (elementsOfList L) V ∧
      (∀ d : ℕ × ℕ, g d = (h d.1, h d.2)) ∧
      (∀ x, x ∈ elementsOfList L ↔ h x ∈ V) ∧
      (∀ x ∈ elementsOfList L, h' (h x) = x) ∧
      (∀ v ∈ V, h (h' v) = v) ∧
      (∀ x, x ∉ elementsOfList L → h x = 0) :=
  lpCondAssembly hlpfan hgood hnodes
    (lpBijOnNodeOfIso hlpfan hnodes hdecomp hisoDart hisoComm) hdecomp hisoDart hisoComm

/-- `lpCondAssembly_nf` 的 `Hypermap.Iso` 包装（`iso_of_lpCondAssembly` 的
无假设版；同注入真证 hbijNode 后转调原版）。下游应消费本版。 -/
theorem iso_of_lpCondAssembly_nf {V : Set V3} {E : Set (Set V3)} {L : fgraph ℕ}
    {hL : GoodList L} {h' : V3 → ℕ} {f : V3 × V3 → ℕ × ℕ}
    (hlpfan : LpFan V E) (hgood : GoodList L) (hnodes : GoodListNodesTl L hL)
    (hdecomp : ∀ d ∈ dart1OfFan V E, f d = (h' d.1, h' d.2))
    (hisoDart : Set.BijOn f ↑(hypermapOfFanTl V E hlpfan.1).darts
        ↑(hypermapOfList L hL).darts)
    (hisoComm : ∀ d ∈ (hypermapOfFanTl V E hlpfan.1).darts,
        (hypermapOfList L hL).edgeMap (f d) =
          f ((hypermapOfFanTl V E hlpfan.1).edgeMap d) ∧
        (hypermapOfList L hL).nodeMap (f d) =
          f ((hypermapOfFanTl V E hlpfan.1).nodeMap d) ∧
        (hypermapOfList L hL).faceMap (f d) =
          f ((hypermapOfFanTl V E hlpfan.1).faceMap d)) :
    Hypermap.Iso (hypermapOfList L hL) (hypermapOfFanTl V E hlpfan.1) :=
  iso_of_lpCondAssembly hlpfan hgood hnodes
    (lpBijOnNodeOfIso hlpfan hnodes hdecomp hisoDart hisoComm) hdecomp hisoDart hisoComm


/-! ## 件 4：`hdecomp` 深件（LP W6-B 第四件）

HOL `hyp_iso_eq_fan_list_iso`（list_hypermap_iso.vhl:647）的完整直译。缺口 =
σ_v 的**单循环性**（方位角序下降论证，NODE_HYPERMAP_OF_FAN_ALT
hypermap_and_fan.hl:1545 的证明核）。本波重构比 HOL 链更短：绕开
CYCLIC_SET_EDGE_FAN/PSUBSET/CARD 机制，直接用「方位角序 + 环回极小性」
两案例矛盾（见 lpSigmaOrbitCovers 的 docstring）。依赖链：
lpMonoAzimSigma（MONO_AZIM_SIGMA_FAN）→ lpSigmaFirstReturn（首回极小）→
lpSigmaCycleDistinct → lpSigmaOrbitCovers（覆盖）→ lpFanNodeEqSetOfEdge
（NODE_HYPERMAP_OF_FAN_ALT）→ lpExistsHdecomp（hdecomp）→
contraveningLpCond（contravening_lp_cond，lp_ineqs_proofs.vhl:348）。

list 侧 = lpPrevSndOfPairs / lpNListFst（n_list_ext_fst 的核心：face 表循环
prevEl 保第二分量）→ lpNodeMapListFst（fst_n_list_ext_power，
list_hypermap.vhl:742）。 -/

open Kepler.Assembly (findFaceDarts nList prevEl)
set_option maxHeartbeats 1000000 in
/-- A1: HOL MONO_AZIM_SIGMA_FAN（topology.hl:29）。 -/
theorem lpMonoAzimSigma {x : V3} (hfan : FAN x V E) (hu : {v, u} ∈ E)
    (hw : {v, w} ∈ E) (hne : sigmaFan x V E v w ≠ u) :
    azim x v u w ≤ azim x v u (sigmaFan x V E v w) := by
  have huS : u ∈ setOfEdge v V E := (properties_of_setOfEdge_fan x V E v u hfan).mp hu
  have hwS : w ∈ setOfEdge v V E := (properties_of_setOfEdge_fan x V E v w hfan).mp hw
  rcases eq_or_ne u w with huw | huw
  · -- u = w：目标 0 ≤ azim x v w σw
    rw [huw, azim_self]
    exact azim_nonneg x v w (sigmaFan x V E v w)
  by_cases hsw : setOfEdge v V E = {w}
  · exfalso
    have huw2 : u = w := by
      have hmem : u ∈ ({w} : Set V3) := hsw ▸ huS
      simpa using hmem
    exact huw huw2
  obtain ⟨hσS, hσne, hmin⟩ := SIGMA_FAN hsw hfan hwS
  have hσE : {v, sigmaFan x V E v w} ∈ E :=
    (properties_of_setOfEdge_fan x V E v _ hfan).mpr hσS
  by_contra hcon
  have hgt : azim x v u (sigmaFan x V E v w) < azim x v u w := not_le.mp hcon
  -- sum2：azim u w = azim u σ + azim σ w
  have hsum : azim x v u w =
      azim x v u (sigmaFan x V E v w) + azim x v (sigmaFan x V E v w) w :=
    sum2_azim_fan hfan hu hσE hw hgt.le
  -- azim w σ ≠ 0（否则 σ = w）
  have hne0 : azim x v w (sigmaFan x V E v w) ≠ 0 := by
    intro h0
    exact hσne (unique_azim0_point_fan (x := x) (V := V) (E := E) (v := v) (u := w) (w := sigmaFan x V E v w) hfan hw hσE h0).symm
  -- 补角（模板照 mono_sigma_fan：if 留在类型里，之后 if_neg 重写）
  have hC1 : azim x v (sigmaFan x V E v w) w
      = if azim x v w (sigmaFan x V E v w) = 0 then 0
        else 2 * Real.pi - azim x v w (sigmaFan x V E v w) :=
    azim_compl (z := x) (w := v) (w1 := w) (w2 := sigmaFan x V E v w)
      (fan_not_collinear hfan hw) (fan_not_collinear hfan hσE)
  rw [if_neg hne0] at hC1
  have hwu0 : azim x v u w ≠ 0 := by
    intro h0
    exact huw (unique_azim0_point_fan (x := x) (V := V) (E := E) (v := v) (u := u) (w := w) hfan hu hw h0)
  have hC2 : azim x v w u
      = if azim x v u w = 0 then 0 else 2 * Real.pi - azim x v u w :=
    azim_compl (z := x) (w := v) (w1 := u) (w2 := w)
      (fan_not_collinear hfan hu) (fan_not_collinear hfan hw)
  rw [if_neg hwu0] at hC2
  -- 极小性：azim w σ ≤ azim w u
  have hminw : azim x v w (sigmaFan x V E v w) ≤ azim x v w u := hmin u huS huw
  -- 算术矛盾
  have hnn : 0 ≤ azim x v u (sigmaFan x V E v w) :=
    azim_nonneg x v u (sigmaFan x V E v w)
  have hkey : azim x v u w = azim x v u (sigmaFan x V E v w) + azim x v u w := by
    rw [hsum, hC1]
    linarith [hminw, hC2]
  have hzero : azim x v u (sigmaFan x V E v w) = 0 := by linarith
  exact hne (unique_azim0_point_fan (x := x) (V := V) (E := E) (v := v) (u := u) (w := sigmaFan x V E v w) hfan hu hσE hzero).symm


/-- A2：σ 的迭代在邻集上单射（mono_sigma_fan 的迭代化）。 -/
theorem lpSigmaIterInject {x : V3} (hfan : FAN x V E) {v : V3} {a b : V3}
    (ha : a ∈ setOfEdge v V E) (hb : b ∈ setOfEdge v V E) :
    ∀ i : ℕ, (sigmaFan x V E v)^[i] a = (sigmaFan x V E v)^[i] b → a = b := by
  intro i
  induction i with
  | zero => exact fun heq => heq
  | succ i ih =>
    intro heq
    refine ih ?_
    have haE : {v, a} ∈ E := (properties_of_setOfEdge_fan x V E v a hfan).mpr ha
    have hbE : {v, b} ∈ E := (properties_of_setOfEdge_fan x V E v b hfan).mpr hb
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at heq
    exact mono_sigma_fan hfan (Kepler.Text.image_power_map_points hfan haE i)
      (Kepler.Text.image_power_map_points hfan hbE i) heq

/-- A3：σ-轨道首回存在且可取极小（鸽笼 + 迭代单射 + Nat.find）。 -/
theorem lpSigmaFirstReturn {x : V3} (hfan : FAN x V E) (hV : V.Finite) {v u : V3}
    (hu : {v, u} ∈ E) :
    ∃ k : ℕ, 1 ≤ k ∧ (sigmaFan x V E v)^[k] u = u ∧
      ∀ t : ℕ, 0 < t → t < k → (sigmaFan x V E v)^[t] u ≠ u := by
  have hfin : (setOfEdge v V E).Finite := remark_finite_fan1 v V E hV
  have hnotinj : ¬ Function.Injective (fun n : ℕ => (sigmaFan x V E v)^[n] u) := by
    intro hinj
    have h1 : (Set.range fun n : ℕ => (sigmaFan x V E v)^[n] u).Infinite :=
      Set.infinite_range_of_injective hinj
    have h2 : (Set.range fun n : ℕ => (sigmaFan x V E v)^[n] u).Finite :=
      hfin.subset (fun y hy => by
        obtain ⟨n, hn2⟩ := hy
        exact hn2 ▸ Kepler.Text.image_power_map_points hfan hu n)
    exact h2.not_infinite h1
  obtain ⟨i, j, heq, hij⟩ := Function.not_injective_iff.mp hnotinj
  -- 位移消去：i < j 时 σ^[j-i] u = u
  have hshift : ∃ k : ℕ, 1 ≤ k ∧ (sigmaFan x V E v)^[k] u = u := by
    rcases lt_or_gt_of_ne hij with h | h
    · refine ⟨j - i, by omega, ?_⟩
      have hidx : i + (j - i) = j := by omega
      have hstep : (sigmaFan x V E v)^[i] ((sigmaFan x V E v)^[j - i] u)
          = (sigmaFan x V E v)^[i] u := by
        rw [← Function.iterate_add_apply, hidx, heq]
      have huS : u ∈ setOfEdge v V E :=
        (properties_of_setOfEdge_fan x V E v u hfan).mp hu
      have hm1 : (sigmaFan x V E v)^[j - i] u ∈ setOfEdge v V E :=
        Kepler.Text.image_power_map_points hfan hu (j - i)
      exact lpSigmaIterInject hfan hm1 huS i hstep
    · refine ⟨i - j, by omega, ?_⟩
      have hjd : j + (i - j) = i := by omega
      have hstep : (sigmaFan x V E v)^[j] ((sigmaFan x V E v)^[i - j] u)
          = (sigmaFan x V E v)^[j] u := by
        rw [← Function.iterate_add_apply, hjd, ← heq]
      have huS : u ∈ setOfEdge v V E :=
        (properties_of_setOfEdge_fan x V E v u hfan).mp hu
      have hm1 : (sigmaFan x V E v)^[i - j] u ∈ setOfEdge v V E :=
        Kepler.Text.image_power_map_points hfan hu (i - j)
      exact lpSigmaIterInject hfan hm1 huS j hstep
  obtain ⟨k0, hk01, hk0⟩ := hshift
  have hex : ∃ n : ℕ, 1 ≤ n ∧ (sigmaFan x V E v)^[n] u = u := ⟨k0, hk01, hk0⟩
  refine ⟨Nat.find hex, Nat.find_spec hex |>.1, Nat.find_spec hex |>.2, ?_⟩
  intro t ht0 htk hcon
  exact Nat.find_min hex htk ⟨ht0, hcon⟩


/-- A5 前置：轨道点互异（首回极小性的直接推论）。 -/
theorem lpSigmaCycleDistinct {x : V3} (hfan : FAN x V E) {v u : V3}
    (hu : {v, u} ∈ E) {k : ℕ}
    (hmin : ∀ t : ℕ, 0 < t → t < k → (sigmaFan x V E v)^[t] u ≠ u)
    (t1 t2 : ℕ) (h12 : t1 < t2) (h2k : t2 < k) :
    (sigmaFan x V E v)^[t1] u ≠ (sigmaFan x V E v)^[t2] u := by
  intro heq
  have huS : u ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v u hfan).mp hu
  have hshift : (sigmaFan x V E v)^[t1] ((sigmaFan x V E v)^[t2 - t1] u)
      = (sigmaFan x V E v)^[t1] u := by
    rw [← Function.iterate_add_apply]
    have : t1 + (t2 - t1) = t2 := by omega
    rw [this, heq]
  have huS2 : (sigmaFan x V E v)^[t2 - t1] u ∈ setOfEdge v V E :=
    Kepler.Text.image_power_map_points hfan hu (t2 - t1)
  exact hmin (t2 - t1) (by omega) (by omega)
    (lpSigmaIterInject hfan huS2 huS t1 hshift)

set_option maxHeartbeats 1000000 in
/-- A5：σ-轨道覆盖整个邻集（单循环性；HOL key_lemma_cyclic_fan +
ORBITS_EQ_SET_EDGE_FAN 的合并重构，两案例矛盾）。 -/
theorem lpSigmaOrbitCovers {x : V3} (hfan : FAN x V E) (hV : V.Finite) {v w : V3}
    (hw : {v, w} ∈ E) :
    ∀ a ∈ setOfEdge v V E, ∃ n : ℕ, (sigmaFan x V E v)^[n] w = a := by
  have hwS : w ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v w hfan).mp hw
  by_cases hSing : setOfEdge v V E = {w}
  · intro a ha
    have : a = w := by
      have : a ∈ ({w} : Set V3) := hSing ▸ ha
      simpa using this
    exact ⟨0, this.symm⟩
  intro a ha
  by_contra haO
  -- 记号：θ(t) = azim x v w (σ^[t] w)，θa = azim x v w a
  have haE : {v, a} ∈ E := (properties_of_setOfEdge_fan x V E v a hfan).mpr ha
  have haw : a ≠ w := fun he => haO ⟨0, he.symm⟩
  obtain ⟨k, hk1, hkw, hmin⟩ := lpSigmaFirstReturn hfan hV hw
  -- k = 1 时 σ w = w 与 S ≠ {w} 矛盾
  have hk2 : 2 ≤ k := by
    by_contra hk
    have hk1' : k = 1 := by omega
    have hσw : (sigmaFan x V E v)^[1] w = w := by
      rw [← hk1']; exact hkw
    exact (SIGMA_FAN hSing hfan hwS).2.1 (by simpa using hσw)
  have hdist : ∀ (t1 t2 : ℕ), t1 < t2 → t2 < k →
      (sigmaFan x V E v)^[t1] w ≠ (sigmaFan x V E v)^[t2] w :=
    lpSigmaCycleDistinct (x := x) (V := V) (E := E) hfan hw hmin
  -- 边形式转换（setOfEdge 成员 ↔ {v, ·} ∈ E）
  have hEof : ∀ p : V3, p ∈ setOfEdge v V E → {v, p} ∈ E :=
    fun p hp => (properties_of_setOfEdge_fan x V E v p hfan).mpr hp
  -- θ-单射性：互异点角不同
  have hinjθ : ∀ p q : V3, p ∈ setOfEdge v V E → q ∈ setOfEdge v V E → p ≠ q →
      azim x v w p ≠ azim x v w q := by
    intro p q hpS hqS hpq heq
    exact hpq (unique_azim_point_fan (x := x) (V := V) (E := E) (v := v)
      (u := w) (w := p) (w1 := q) hfan hw (hEof p hpS) (hEof q hqS) heq)
  -- a 不在轨道上：∀ j < k, u_j ≠ a
  have hacyc : ∀ j : ℕ, j < k → (sigmaFan x V E v)^[j] w ≠ a := by
    intro j hj heqj
    exact haO ⟨j, heqj⟩
  have hpowS : ∀ j : ℕ, (sigmaFan x V E v)^[j] w ∈ setOfEdge v V E :=
    Kepler.Text.image_power_map_points hfan hw
  -- θ(1) < θ(a)：极小性 + 单射
  have h1lt : azim x v w ((sigmaFan x V E v)^[1] w) < azim x v w a := by
    have hmin1 : azim x v w (sigmaFan x V E v w)
        ≤ azim x v w a := (SIGMA_FAN hSing hfan hwS).2.2 a ha haw
    have hpq : sigmaFan x V E v w ≠ a := by
      intro he
      exact hacyc 1 (by omega) he
    have hσwS : sigmaFan x V E v w ∈ setOfEdge v V E :=
      sigma_fan_in_setOfEdge hfan hwS
    have hneq : azim x v w (sigmaFan x V E v w) ≠ azim x v w a :=
      fun he => hinjθ (sigmaFan x V E v w) a hσwS ha hpq he
    have hσ1 : (sigmaFan x V E v)^[1] w = sigmaFan x V E v w := rfl
    rw [hσ1]
    exact lt_of_le_of_ne hmin1 hneq
  -- 主案例
  by_cases hA : azim x v w ((sigmaFan x V E v)^[k - 1] w) < azim x v w a
  · -- 案例环回：θ(k-1) < θ(a)，用 u_{k-1} 处极小性 + 补角矛盾
    exfalso
    set uk1 := (sigmaFan x V E v)^[k - 1] w with huk1
    have huk1S : uk1 ∈ setOfEdge v V E := hpowS (k - 1)
    have hwuk1 : w ≠ uk1 := hdist 0 (k - 1) (by omega) (by omega)
    have hauk1 : a ≠ uk1 := by
      intro he
      exact hacyc (k - 1) (by omega) he.symm
    -- σ u_{k-1} = w
    have hσk : (sigmaFan x V E v)^[k] w = sigmaFan x V E v uk1 := by
      have hkeq : k = k - 1 + 1 := by omega
      rw [hkeq, Function.iterate_succ_apply', huk1]
    have hσkw : sigmaFan x V E v uk1 = w := by
      have h1 := hkw
      rw [hσk] at h1
      exact h1
    -- u_{k-1} 处极小性
    have hSne : setOfEdge v V E ≠ {uk1} := by
      intro he
      have hac : a ∈ ({uk1} : Set V3) := by rw [← he]; exact ha
      exact hauk1 (by simpa using hac)
    have hminU := (SIGMA_FAN hSne hfan huk1S).2.2 a ha hauk1
    rw [hσkw] at hminU
    -- azim x v uk1 w = 2π − θ(k-1)
    have hθk1 : azim x v w uk1 ≠ 0 := by
      intro h0
      exact hwuk1 (unique_azim0_point_fan (x := x) (V := V) (E := E) (v := v)
        (u := w) (w := uk1) hfan hw (hEof uk1 huk1S) h0)
    have hC1 : azim x v uk1 w
        = if azim x v w uk1 = 0 then 0
          else 2 * Real.pi - azim x v w uk1 :=
      azim_compl (z := x) (w := v) (w1 := w) (w2 := uk1)
        (fan_not_collinear hfan hw) (fan_not_collinear hfan (hEof uk1 huk1S))
    rw [if_neg hθk1] at hC1
    -- θ(a) = θ(k-1) + azim x v uk1 a（sum2，因 θ(k-1) ≤ θ(a)）
    have hsumA : azim x v w a = azim x v w uk1 + azim x v uk1 a :=
      sum2_azim_fan hfan hw (hEof uk1 huk1S) (hEof a ha) hA.le
    -- 算术矛盾
    have hlt2 : azim x v w a < 2 * Real.pi := azim_lt_two_pi x v w a
    linarith
  · -- 案例空隙：θ(a) ≤ θ(k-1) 且 ≠，取 j = max{t ∈ [1,k-1] | θ(t) < θ(a)} 矛盾
    exfalso
    have hBle : azim x v w a ≤ azim x v w ((sigmaFan x V E v)^[k - 1] w) :=
      le_of_not_gt hA
    have hauk1 : a ≠ (sigmaFan x V E v)^[k - 1] w := by
      intro he
      exact hacyc (k - 1) (by omega) he.symm
    have hBne : azim x v w a ≠ azim x v w ((sigmaFan x V E v)^[k - 1] w) :=
      fun he => hinjθ a ((sigmaFan x V E v)^[k - 1] w) ha
        (hpowS (k - 1)) hauk1 he
    have hB : azim x v w a < azim x v w ((sigmaFan x V E v)^[k - 1] w) :=
      lt_of_le_of_ne hBle hBne
    -- 最大下标集合
    set T : Finset ℕ :=
      (Finset.Icc 1 (k - 1)).filter
        (fun j => decide (azim x v w ((sigmaFan x V E v)^[j] w) < azim x v w a))
      with hT
    have h1T : 1 ∈ T := by
      rw [hT]
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (by omega), ?_⟩
      have hσ1 : (sigmaFan x V E v)^[1] w = sigmaFan x V E v w := rfl
      exact decide_eq_true (by rw [hσ1]; exact h1lt)
    have hTne : T.Nonempty := ⟨1, h1T⟩
    set jmax := T.max' hTne with hj
    have hjmem := T.max'_mem hTne
    obtain ⟨hjI, hjlt⟩ := Finset.mem_filter.mp hjmem
    obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.mp hjI
    have hjltP : azim x v w ((sigmaFan x V E v)^[jmax] w) < azim x v w a :=
      decide_eq_true_iff.mp hjlt
    -- j < k-1（否则与案例 B 前提矛盾）
    have hjk1 : jmax < k - 1 := by
      by_contra hcon
      have hjE : jmax = k - 1 := by omega
      rw [hjE] at hjltP
      exact absurd hjltP (not_lt.mpr hB.le)
    -- maximality：θ(j+1) 不 < θ(a)
    have hjmax : jmax + 1 ∉ T := by
      intro hcon
      have h2 := Finset.le_max' T (jmax + 1) hcon
      omega
    have hj1I : jmax + 1 ∈ Finset.Icc 1 (k - 1) := Finset.mem_Icc.mpr (by omega)
    have hnotlt : ¬ (azim x v w ((sigmaFan x V E v)^[jmax + 1] w) < azim x v w a) := by
      intro hcon
      exact hjmax (Finset.mem_filter.mpr ⟨hj1I, decide_eq_true hcon⟩)
    have hauj1 : a ≠ (sigmaFan x V E v)^[jmax + 1] w := by
      intro he
      exact hacyc (jmax + 1) (by omega) he.symm
    have hge : azim x v w a ≤ azim x v w ((sigmaFan x V E v)^[jmax + 1] w) :=
      le_of_not_gt hnotlt
    have hgt : azim x v w a ≠ azim x v w ((sigmaFan x V E v)^[jmax + 1] w) :=
      fun he => hinjθ a ((sigmaFan x V E v)^[jmax + 1] w) ha
        (hpowS (jmax + 1)) hauj1 he
    have hlt2 : azim x v w a < azim x v w ((sigmaFan x V E v)^[jmax + 1] w) :=
      lt_of_le_of_ne hge hgt
    -- u_j 处极小性
    have hujS : (sigmaFan x V E v)^[jmax] w ∈ setOfEdge v V E := hpowS jmax
    have hauj : a ≠ (sigmaFan x V E v)^[jmax] w := by
      intro he
      exact hacyc jmax (by omega) he.symm
    have hSnej : setOfEdge v V E ≠ {(sigmaFan x V E v)^[jmax] w} := by
      intro he
      have hac : a ∈ ({(sigmaFan x V E v)^[jmax] w} : Set V3) := by rw [← he]; exact ha
      exact hauj (by simpa using hac)
    have hminJ := (SIGMA_FAN hSnej hfan hujS).2.2 a ha hauj
    -- σ u_j = u_{j+1}
    have hσJ : sigmaFan x V E v ((sigmaFan x V E v)^[jmax] w)
        = (sigmaFan x V E v)^[jmax + 1] w := by
      rw [Function.iterate_succ_apply']
    rw [hσJ] at hminJ
    -- A1：θ(j) ≤ θ(j+1)
    have huju0 : (sigmaFan x V E v)^[jmax + 1] w ≠ w := by
      intro he
      exact hdist 0 (jmax + 1) (by omega) (by omega) he.symm
    have hmono := lpMonoAzimSigma (x := x) (V := V) (E := E) hfan hw
      (hEof _ hujS)
      (show sigmaFan x V E v ((sigmaFan x V E v)^[jmax] w) ≠ w by
        rw [hσJ]; exact huju0)
    rw [hσJ] at hmono
    -- sum2：θ(j+1) = θ(j) + azim u_j u_{j+1}
    have hsumJ1 : azim x v w ((sigmaFan x V E v)^[jmax + 1] w)
        = azim x v w ((sigmaFan x V E v)^[jmax] w)
          + azim x v ((sigmaFan x V E v)^[jmax] w)
            ((sigmaFan x V E v)^[jmax + 1] w) :=
      sum2_azim_fan hfan hw (hEof _ hujS) (hEof _ (hpowS (jmax + 1))) hmono
    -- sum2：θ(a) = θ(j) + azim u_j a
    have hsumJa : azim x v w a = azim x v w ((sigmaFan x V E v)^[jmax] w)
        + azim x v ((sigmaFan x V E v)^[jmax] w) a :=
      sum2_azim_fan hfan hw (hEof _ hujS) (hEof a ha) hjltP.le
    -- 算术矛盾
    linarith


/-- B1：fan 超映射的 node 轨道 = 第一分量不变的第二分量全体
（HOL NODE_HYPERMAP_OF_FAN_ALT，经单循环覆盖件）。 -/
theorem lpFanNodeEqSetOfEdge (hfan : FAN 0 V E) {v w : V3}
    (hw : (v, w) ∈ dart1OfFan V E) :
    (hypermapOfFanTl V E hfan).node (v, w) = {d | d.1 = v ∧ d.2 ∈ setOfEdge v V E} := by
  have hwe : {v, w} ∈ E := hw
  ext y
  constructor
  · rintro ⟨n, hn⟩
    rw [Equiv.Perm.coe_pow] at hn
    rw [nodeMapTl_iterate hw n] at hn
    rw [← hn]
    exact Set.mem_setOf.mpr ⟨rfl, Kepler.Text.image_power_map_points hfan hwe n⟩
  · rintro ⟨hy1, hu⟩
    obtain ⟨n, hn⟩ := lpSigmaOrbitCovers hfan hfan.2.2.1.1 hwe y.2 hu
    refine ⟨n, ?_⟩
    rw [Equiv.Perm.coe_pow, nodeMapTl_iterate hw n, hn]
    exact Prod.ext hy1.symm rfl

/-- C1 核心：prevEl 在循环 pair-表上保第二分量 = d.1（纯 zip 形态）。
（HOL prev_el_list_pairs_general / n_list_ext_fst 的核心步。） -/
private theorem lpPrevSndOfPairs {l : List ℕ}
    (hN : (l.zip (l.drop 1 ++ l.take 1)).Nodup)
    {d : ℕ × ℕ} (hd : d ∈ l.zip (l.drop 1 ++ l.take 1)) :
    (prevEl (l.zip (l.drop 1 ++ l.take 1)) d).2 = d.1 := by
  have hpos : 0 < (l.zip (l.drop 1 ++ l.take 1)).length := List.length_pos_of_mem hd
  have hilt : (l.zip (l.drop 1 ++ l.take 1)).idxOf d
      < (l.zip (l.drop 1 ++ l.take 1)).length := List.idxOf_lt_length_iff.mpr hd
  obtain ⟨i, hi, hdi⟩ := List.mem_iff_getElem.mp hd
  have hidx : (l.zip (l.drop 1 ++ l.take 1)).idxOf d = i := by
    rw [← hdi]; exact idxOf_getElem hN hi
  have hlenrot : (l.drop 1 ++ l.take 1).length = l.length := by
    rw [List.length_append, List.length_drop, List.length_take]; omega
  have hdlen : (l.drop 1).length = l.length - 1 := by rw [List.length_drop]
  have hlenS : (l.zip (l.drop 1 ++ l.take 1)).length = l.length := by
    rw [List.length_zip, hlenrot]; omega
  have hltL : i < l.length := by omega
  have hzipFst : ((l.zip (l.drop 1 ++ l.take 1))[i]'hi).1 = l[i]'hltL := by
    rw [List.getElem_zip]
  have hdx : d.1 = l[i]'hltL := by rw [← hdi]; exact hzipFst
  -- prevEl 的 getD 形（照 nextEl_prevEl 的 hy_getD 模板）
  have hpv : prevEl (l.zip (l.drop 1 ++ l.take 1)) d
      = (l.zip (l.drop 1 ++ l.take 1)).getD
        (((l.zip (l.drop 1 ++ l.take 1)).idxOf d
          + (l.zip (l.drop 1 ++ l.take 1)).length - 1)
          % (l.zip (l.drop 1 ++ l.take 1)).length) d := by
    unfold prevEl
    rw [if_neg (show ¬(d ∉ l.zip (l.drop 1 ++ l.take 1)) from not_not.mpr hd), li_idxOf_congr]
    split
    · rename_i h0
      rw [h0, getD_wrap_prev hpos]
      exact li_getLastD_getD hpos d
    · rename_i hne
      exact (getD_prev hilt hne d).symm
  rw [hpv, hidx]
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · -- i = 0：prevEl = 末位 (l[m-1], l[0])
    subst hi0
    rw [getD_wrap_prev hpos, getD_eq_getElem_of_lt (by omega)]
    have hv : (l.zip (l.drop 1 ++ l.take 1)).length - 1
        < (l.drop 1 ++ l.take 1).length := by omega
    have hneg : ¬((l.zip (l.drop 1 ++ l.take 1)).length - 1 < (l.drop 1).length) := by
      omega
    have hzero : (l.zip (l.drop 1 ++ l.take 1)).length - 1 - (l.drop 1).length = 0 := by
      omega
    rw [List.getElem_zip, List.getElem_append hv, dif_neg hneg]
    simp only [hzero, List.getElem_take]
    show l[0] = d.1
    exact hdx.symm
  · -- i ≥ 1：prevEl = 前位 (l[i-1], l[i])
    have hne0 : i ≠ 0 := by omega
    have hlt2 : i - 1 < (l.zip (l.drop 1 ++ l.take 1)).length := by omega
    rw [getD_prev (s := l.zip (l.drop 1 ++ l.take 1)) (j := i) hi hne0 d,
      getD_eq_getElem_of_lt hlt2]
    have hv : i - 1 < (l.drop 1 ++ l.take 1).length := by omega
    have hcond : i - 1 < (l.drop 1).length := by omega
    rw [List.getElem_zip, List.getElem_append hv, dif_pos hcond]
    have hdrop : ((l.drop 1)[i - 1]'(by omega))
        = l[1 + (i - 1)]'(by omega) := List.getElem_drop
    simp only [hdrop, show 1 + (i - 1) = i from by omega]
    show l[i]'hltL = d.1
    exact hdx.symm

/-- C1：list 侧 nodeMap 单步保第一分量（HOL n_list_ext_fst 的核心）。 -/
private theorem lpNListFst {L : fgraph ℕ} (hL : GoodList L)
    {d : ℕ × ℕ} (hd : d ∈ listOfDarts L) :
    (nList L d).1 = d.1 := by
  have hz : d ∈ findFaceDarts L d := (dart_in_face L d).mpr hd
  obtain ⟨l, hll, hfind, hdin⟩ := findFaceDarts_ex_of_self hz
  have hN : (l.zip (l.drop 1 ++ l.take 1)).Nodup := by
    have hnod := findFaceDarts_nodup hL.1 d
    rw [hfind] at hnod
    exact hnod
  have hdin' : d ∈ l.zip (l.drop 1 ++ l.take 1) := hdin
  show (prevEl (findFaceDarts L d) d).2 = d.1
  rw [hfind]
  exact lpPrevSndOfPairs hN hdin'

/-- C3：list 侧 nodeMap 迭代保第一分量（HOL fst_n_list_ext_power）。 -/
private theorem lpNodeMapListFst {L : fgraph ℕ} (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) (n : ℕ) :
    ((hypermapOfList L hL).nodeMap^[n] d).1 = d.1 := by
  have hmem : ∀ k : ℕ, (hypermapOfList L hL).nodeMap^[k] d ∈ listOfDarts L := by
    intro k
    induction k with
    | zero => exact hd
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      have hcur : (hypermapOfList L hL).nodeMap^[k] d ∈
          (↑(hypermapOfList L hL).darts : Set (ℕ × ℕ)) := by
        rw [darts_hypermapOfList]
        exact ih
      rw [nodeMap_hypermapOfList L hL hcur]
      exact (bijOn_nList hL).mapsTo ih
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hcur : (hypermapOfList L hL).nodeMap^[n] d ∈
        (↑(hypermapOfList L hL).darts : Set (ℕ × ℕ)) := by
      rw [darts_hypermapOfList]
      exact hmem n
    rw [nodeMap_hypermapOfList L hL hcur, lpNListFst hL (hmem n)]
    exact ih


theorem lpExistsHdecomp {V : Set V3} {E : Set (Set V3)} {L : fgraph ℕ}
    {hL : GoodList L} {f : V3 × V3 → ℕ × ℕ}
    (hlpfan : LpFan V E)
    (hisoDart : Set.BijOn f ↑(hypermapOfFanTl V E hlpfan.1).darts
        ↑(hypermapOfList L hL).darts)
    (hisoComm : ∀ d ∈ (hypermapOfFanTl V E hlpfan.1).darts,
        (hypermapOfList L hL).edgeMap (f d) =
          f ((hypermapOfFanTl V E hlpfan.1).edgeMap d) ∧
        (hypermapOfList L hL).nodeMap (f d) =
          f ((hypermapOfFanTl V E hlpfan.1).nodeMap d) ∧
        (hypermapOfList L hL).faceMap (f d) =
          f ((hypermapOfFanTl V E hlpfan.1).faceMap d)) :
    ∃ h' : V3 → ℕ, ∀ d ∈ dart1OfFan V E, f d = (h' d.1, h' d.2) := by
  have hfan : FAN 0 V E := hlpfan.1
  -- 全局见证函数
  have hex : ∀ x : V3, ∃ wx : V3, x ∈ V → wx ∈ setOfEdge x V E := by
    intro x
    by_cases hx : x ∈ V
    · obtain ⟨wv, hwv⟩ := Set.nonempty_iff_ne_empty.mpr (lpFan_setOfEdge_ne hlpfan hx)
      exact ⟨wv, fun _ => hwv⟩
    · exact ⟨x, fun hv => absurd hv hx⟩
  choose w hw using hex
  refine ⟨fun x => (f (x, w x)).1, ?_⟩
  -- FST 半：node 轨道运输 + list 侧 FST 保持
  have hFST : ∀ d ∈ dart1OfFan V E, (f d).1 = (f (d.1, w d.1)).1 := by
    intro d hd
    have hV := dart1OfFan_fst_snd_mem hfan hd
    have hd1 : (d.1, w d.1) ∈ dart1OfFan V E := by
      simp only [dart1OfFan, Set.mem_setOf_eq]
      exact (properties_of_setOfEdge_fan 0 V E d.1 (w d.1) hfan).mpr (hw d.1 hV.1)
    have hmem : (d.1, w d.1) ∈ {dd : V3 × V3 | dd.1 = d.1 ∧ dd.2 ∈ setOfEdge d.1 V E} :=
      ⟨rfl, hw d.1 hV.1⟩
    have hnode : (d.1, w d.1) ∈ (hypermapOfFanTl V E hfan).node d := by
      rw [lpFanNodeEqSetOfEdge hfan hd]
      exact hmem
    have htrans : f (d.1, w d.1) ∈ (hypermapOfList L hL).node (f d) := by
      have hT := lpOrbitTransport hfan hisoDart hisoComm hd
      rw [← hT]
      exact Set.mem_image_of_mem f hnode
    obtain ⟨n, hn⟩ := (lpMemNodeIff (hypermapOfList L hL)).mp htrans
    have hfd : f d ∈ listOfDarts L := by
      have hm := hisoDart.mapsTo (Finset.mem_coe.mpr (mem_dartsTl hd))
      rw [darts_hypermapOfList] at hm
      exact hm
    calc (f d).1
        = ((hypermapOfList L hL).nodeMap^[n] (f d)).1 :=
          (lpNodeMapListFst hL hfd n).symm
      _ = (f (d.1, w d.1)).1 := by rw [hn]
  -- SND 半：edge 映射两侧交换
  have hSND : ∀ d ∈ dart1OfFan V E, (f d).2 = (f (d.2, w d.2)).1 := by
    intro d hd
    have hV := dart1OfFan_fst_snd_mem hfan hd
    have hdmem : d ∈ (↑(hypermapOfFanTl V E hfan).darts : Set (V3 × V3)) :=
      Finset.mem_coe.mpr (mem_dartsTl hd)
    have hswapf : (hypermapOfFanTl V E hfan).edgeMap d = (d.2, d.1) := by
      rw [edgeMapTl_apply hd]
      rfl
    have hcomm := (hisoComm d hdmem).1
    rw [hswapf] at hcomm
    -- hcomm : edgeMap_G (f d) = f (d.2, d.1)
    have hfdG : f d ∈ (hypermapOfList L hL).darts := by
      have hm := hisoDart.mapsTo hdmem
      exact Finset.mem_coe.mp hm
    have hEl : (hypermapOfList L hL).edgeMap (f d) = ((f d).2, (f d).1) := by
      rw [edgeMap_hypermapOfList L hL hfdG]
      rfl
    rw [hEl] at hcomm
    -- hcomm : ((f d).2, (f d).1) = f (d.2, d.1)
    have hswapin : (d.2, d.1) ∈ dart1OfFan V E := by
      simp only [dart1OfFan, Set.mem_setOf_eq]
      rw [Set.pair_comm]
      exact hd
    have hFST2 := hFST (d.2, d.1) hswapin
    calc (f d).2 = (f (d.2, d.1)).1 := congrArg Prod.fst hcomm
      _ = (f (d.2, w d.2)).1 := hFST2
  -- 装配
  intro d hd
  have h1 := hFST d hd
  have h2 := hSND d hd
  show f d = ((f (d.1, w d.1)).1, (f (d.2, w d.2)).1)
  rw [← h1, ← h2]

/-! ### 终装配：`contravening_lp_cond`（lp_ineqs_proofs.vhl:348）

HOL `contravening_lp_cond L f: good_list L /\ good_list_nodes L /\
hyp_iso f (hypermap_of_fan (V,ESTD V), hypermap_of_list L) ==> ?g h. lp_cond
(L,g,h) (V,ESTD V)`：`contraveningLpFan`（件 2）+ `lpCondAssembly_nf`（件 3
的无假设主件）+ `lpExistsHdecomp`（件 4，hdecomp 消掉）三步装配。结论与
`lpCondAssembly_nf` 逐字同型（∃ g h 十一合取）。 -/
theorem contraveningLpCond {V : Set V3} (hc : Contravening V) {L : fgraph ℕ}
    {hL : GoodList L} {hnodes : GoodListNodesTl L hL} {f : V3 × V3 → ℕ × ℕ}
    (hisoDart : Set.BijOn f
        ↑(hypermapOfFanTl V (ESTD V) (contraveningLpFan V hc).1).darts
        ↑(hypermapOfList L hL).darts)
    (hisoComm : ∀ d ∈ (hypermapOfFanTl V (ESTD V) (contraveningLpFan V hc).1).darts,
        (hypermapOfList L hL).edgeMap (f d) =
          f ((hypermapOfFanTl V (ESTD V) (contraveningLpFan V hc).1).edgeMap d) ∧
        (hypermapOfList L hL).nodeMap (f d) =
          f ((hypermapOfFanTl V (ESTD V) (contraveningLpFan V hc).1).nodeMap d) ∧
        (hypermapOfList L hL).faceMap (f d) =
          f ((hypermapOfFanTl V (ESTD V) (contraveningLpFan V hc).1).faceMap d)) :
    ∃ h' : V3 → ℕ, ∃ g : ℕ × ℕ → V3 × V3, ∃ h : ℕ → V3,
      LpFan V (ESTD V) ∧ GoodList L ∧ GoodListNodesTl L hL ∧
      Set.BijOn g ↑(hypermapOfList L hL).darts
        ↑(hypermapOfFanTl V (ESTD V) (contraveningLpFan V hc).1).darts ∧
      (∀ d ∈ (hypermapOfList L hL).darts,
          (hypermapOfFanTl V (ESTD V) (contraveningLpFan V hc).1).edgeMap (g d) =
            g ((hypermapOfList L hL).edgeMap d) ∧
          (hypermapOfFanTl V (ESTD V) (contraveningLpFan V hc).1).nodeMap (g d) =
            g ((hypermapOfList L hL).nodeMap d) ∧
          (hypermapOfFanTl V (ESTD V) (contraveningLpFan V hc).1).faceMap (g d) =
            g ((hypermapOfList L hL).faceMap d)) ∧
      Set.BijOn h (elementsOfList L) V ∧
      (∀ d : ℕ × ℕ, g d = (h d.1, h d.2)) ∧
      (∀ x, x ∈ elementsOfList L ↔ h x ∈ V) ∧
      (∀ x ∈ elementsOfList L, h' (h x) = x) ∧
      (∀ v ∈ V, h (h' v) = v) ∧
      (∀ x, x ∉ elementsOfList L → h x = 0) := by
  have hlpfan : LpFan V (ESTD V) := contraveningLpFan V hc
  obtain ⟨h', hdecomp⟩ := lpExistsHdecomp hlpfan hisoDart hisoComm
  exact ⟨h', lpCondAssembly_nf hlpfan hL hnodes hdecomp hisoDart hisoComm⟩

end LpCondLayer

end Kepler.Text.LP.LpSemantics
