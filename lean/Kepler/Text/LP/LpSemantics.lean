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

end LpCondLayer

end Kepler.Text.LP.LpSemantics
