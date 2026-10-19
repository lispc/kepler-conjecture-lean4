/-
  Kepler.Text.TameSpine.TameList41 — B1 Tame_list 地基批 41：quotient 章
  iso_list 面（tamespine-port-plan §4 批次表 B1 行；接续批 40 =
  TameList40.lean，批 40 终点 = HOL :12265；本批起点 = HOL :12267
  `iso_list_quotient`。行号均按主仓 reference/flyspeck（commit 1ce0353）
  实测。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:12267-:12353）：

  主件：`iso_list_quotient` :12267-:12308
  `!L N L' N'. good_list L /\ normal_list L N /\
  is_edge_nondegenerate (hypermap_of_list L) /\ all uniq L /\
  iso_list (L,N) (L',N') ==> iso_list (quotient_list L N,[])
  (quotient_list L' N',[])`
  ↦ `isoListQuotientSpine`（真证）。HOL 证体 iso_list 展开 + 证人
  `phi` EXISTS + 首槽 inj_on_quotient_list（:11765）直取 + 展开
  quotient_list/core_list 后 iso_list_map_parts（:12239）GMATCH 收
  parts 面 + GSYM MAP_o / MAP_EQ 两层逐点化收口（叶槽 GMATCH_SIMP_TAC
  HD_MAP + parts_uniq_nonnil 供非空）；Lean 面 IsoListSpine 的 ∃-证人
  phi 原位复用（isopQuotientCore canonical 形核件一次成证，主件经
  isopListSpine_isoListSpine 同型的 ⟨phi, core⟩ 折叠回 ∃ 形），主方程
  isoListMapParts 一次重写 + coreListSpine 展开 + List.map_congr_left
  两层逐点（叶子 = head! 运输私件 headMapLift，非空由 partsUniqNonnil
  供给——对应 HOL 的 HD_MAP + parts_uniq_nonnil 消费）。

  随收件：`isop_list_quotient` :12311-:12352
  `!phi L N L' N'. good_list L /\ normal_list L N /\
  is_edge_nondegenerate (hypermap_of_list L) /\ all uniq L /\
  isop_list phi (L,N) (L',N') ==> isop_list phi
  (quotient_list L N,[]) (quotient_list L' N',[])`
  ↦ `isopListQuotientSpine`（真证）。HOL 证体与主件逐字同构（iso_list
  展开槽消失，phi 显式）；Lean 面同一核件 isopQuotientCore 直投。

  载体折算盘点（批 40 头注预记侦察面，经全库 grep（含 LocalAuto 族：
  Kepler/Text/LocalAuto3.lean、Kepler/Text/PackingAuto18.lean 等在册）
  对拍——流程雷 #39 本批零命中：预记缺口为真缺口，零撞车）：
  - `iso_list`/`isop_list`（tame_defs2.hl:62-:69）= 批 1
    IsoListSpine/IsopListSpine（TameList1.lean:83/:75）；
  - `quotient_list`/`core_list`（tame_defs2.hl:133-:134/:108-:110）
    = 批 7 quotientListSpine/coreListSpine（TameList7.lean:476/:471）；
  - `inj_on_quotient_list` :11765 = 批 37 injOnQuotientList
    （TameList37.lean:188，直取；其链底 elements_of_list_quotient_list
    :11747 同模块，list_of_darts_quotient_darts = 批 16）；
  - `parts_uniq_nonnil` :6572 = 批 9 partsUniqNonnil
    （TameList9.lean:1277，p 非空槽 .2.2.2.1）；
  - `iso_list_map_parts` :12239 = 批 40 isoListMapParts（直取）；
  - `HD_MAP` 面 = core List.head!（cons 支定义式收敛，本批私件
    headMapLift 一发收两型）；
  - `MAP_EQ`/`GSYM MAP_o` 面 = core List.map_congr_left 两层逐点
    （内联 map 复合直接由 congr_left 吃掉，零 map_map 归一——批 40
    MAP 三重复合层级陷阱的对偶解）。
  `is_edge_nondegenerate (hypermap_of_list L)` 前提经 inj_on_quotient_list
  链实消费（非死前提，批 40 同判）。`all uniq L` 前提同批 37 形
  `∀ l ∈ L, l.Nodup`，同样经 inj_on_quotient_list 链实消费。

  新落地载体：零（纯消费批）。私件：headMapLift（head! 运输面）、
  isopQuotientCore（canonical L'/N' 形核件，两件共享）。

  诚实记账：主件 + 随收件全真证，零新 def、零 sorry、零止损件、
  零记账债。红线遵守：零既有文件触碰、零 git 写操作。
  批 42 接续点：HOL :12354 `filter_mono`（filter/sizel 单调面开章——
  Lean 面 `List.filter`/`length` 形零新 def 可直译，同章伴件 :12380
  `iso_list_all_size`、MEMf_MAP 面随批侦察）。
-/

import Kepler.Text.TameSpine.TameList40

namespace Kepler.Text.TameSpine

open Kepler.Assembly (GoodList)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (hypermapOfList elementsOfList)

/-! ### §1 私件（head! 运输面） -/

/-- dart 表经提升映射后取头（HOL `HD_MAP` 同型折算：
`HD (MAP nphi x) = nphi (HD x)` 的 `.1` 投影面）。空表支由
partsUniqNonnil 的非空槽封死（HOL 同构——HD_MAP 消费依赖
parts_uniq_nonnil）；cons 支逐层定义式收敛。 -/
private theorem headMapLift (phi : ℕ → ℕ) {a : List (ℕ × ℕ)} (hne : a ≠ []) :
    (a.map (fun u => (phi u.1, phi u.2))).head!.1 = phi a.head!.1 := by
  cases a with
  | nil => exact absurd rfl hne
  | cons d t => rfl

/-! ### §2 核件（canonical 形，两件共享） -/

/-- 批 41 两件的共享核（HOL iso_list_quotient/isop_list_quotient 证体
同构部分的 canonical L'/N' 形）：首槽 inj_on_quotient_list（批 37）
直取，主方程经 isoListMapParts（批 40）重写 + coreListSpine 展开 +
两层 List.map_congr_left（叶子 headMapLift，非空由 partsUniqNonnil
供给）。 -/
private theorem isopQuotientCore (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup) (phi : ℕ → ℕ)
    (hinj : Set.InjOn phi (elementsOfList L))
    {L' : fgraph ℕ} {N' : List (List (ℕ × ℕ))}
    (hL'map : L' = L.map (List.map phi))
    (hN'map : N' = N.map (fun s => s.map (fun u => (phi u.1, phi u.2)))) :
    IsopListSpine phi (quotientListSpine L N) (quotientListSpine L' N') [] [] := by
  subst hL'map
  subst hN'map
  refine ⟨injOnQuotientList L hL hn hnedg hunL hinj, ?_, rfl⟩
  show coreListSpine
      ((N.map (fun s => s.map (fun u => (phi u.1, phi u.2)))).map
        (partsSpine (L.map (List.map phi))))
    = (coreListSpine (N.map (partsSpine L))).map (List.map phi)
  rw [isoListMapParts L hL hn hnedg phi hinj, coreListSpine, coreListSpine]
  simp only [List.map_map]
  refine List.map_congr_left (fun r hrN => ?_)
  show ((partsSpine L r).map (fun s => s.map (fun u => (phi u.1, phi u.2)))).map
      (fun a => a.head!.1)
    = ((partsSpine L r).map (fun a => a.head!.1)).map phi
  rw [List.map_map, List.map_map]
  exact List.map_congr_left (fun a ha =>
    headMapLift phi (partsUniqNonnil L hL hn hrN ha).2.2.2.1)

/-! ### §3 主件 iso_list_quotient（tame_list.hl:12267-:12308） -/

/-- **HOL `iso_list_quotient`**（tame_list.hl:12267-:12308）
`good_list L /\ normal_list L N /\ is_edge_nondegenerate
(hypermap_of_list L) /\ all uniq L /\ iso_list (L,N) (L',N') ==>
iso_list (quotient_list L N,[]) (quotient_list L' N',[])`
——quotient 章 iso_list 运输主件：证人 phi 自 iso_list 原位复用 +
首槽 inj_on_quotient_list（批 37）+ 主方程 iso_list_map_parts（批 40）
两层 MAP_EQ 逐点化。 -/
theorem isoListQuotientSpine (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup) {L' : fgraph ℕ} {N' : List (List (ℕ × ℕ))}
    (hiso : IsoListSpine L L' N N') :
    IsoListSpine (quotientListSpine L N) (quotientListSpine L' N') [] [] := by
  obtain ⟨phi, hinj, hL'map, hN'map⟩ := hiso
  exact ⟨phi, isopQuotientCore L hL hn hnedg hunL phi hinj hL'map hN'map⟩

/-! ### §4 随收件 isop_list_quotient（tame_list.hl:12311-:12352） -/

/-- **HOL `isop_list_quotient`**（tame_list.hl:12311-:12352）
`isop_list phi (L,N) (L',N') ==> isop_list phi (quotient_list L N,[])
(quotient_list L' N',[])`（前四前提同主件）——显式 phi 形随收件，
HOL 证体与主件逐字同构；Lean 面同核件直投。 -/
theorem isopListQuotientSpine (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup) (phi : ℕ → ℕ) {L' : fgraph ℕ}
    {N' : List (List (ℕ × ℕ))} (hisop : IsopListSpine phi L L' N N') :
    IsopListSpine phi (quotientListSpine L N) (quotientListSpine L' N') [] [] := by
  obtain ⟨hinj, hL'map, hN'map⟩ := hisop
  exact isopQuotientCore L hL hn hnedg hunL phi hinj hL'map hN'map

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；两件预期零 sorryAx）：
#print axioms Kepler.Text.TameSpine.isoListQuotientSpine
#print axioms Kepler.Text.TameSpine.isopListQuotientSpine
-/
