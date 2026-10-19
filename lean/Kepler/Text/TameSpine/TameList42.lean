/-
  Kepler.Text.TameSpine.TameList42 — B1 Tame_list 地基批 42：filter/sizel
  单调面（tamespine-port-plan §4 批次表 B1 行；接续批 41 =
  TameList41.lean，批 41 终点 = HOL :12352；本批起点 = HOL :12354
  `filter_mono`。行号均按主仓 reference/flyspeck（commit 1ce0353）
  实测。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:12354-:12406）：

  主件：`filter_mono` :12354-:12378
  `!p q r. (!x. MEM x r /\ p x ==> q x) ==> sizel (filter p r) <=
  sizel (filter q r)`
  ↦ `filterMonoSpine`（真证）。HOL 证体 LIST_INDUCT + 双 COND_CASES
  （p h 支经前提取 q h 走 SUC≤SUC；¬p h 支再二分——q h 支 m ≤ SUC n
  由 m ≤ n 放大、¬q h 支 IH 直投）逐句镜像；Lean 面 `List.filter`/
  `length` 形（批 12 sizel 记账 `sizel ↦ List.length`，零新 def），
  filter cons 支经 `List.filter_cons_of_pos/neg` + `List.length_cons`
  一发收口。

  主件：`iso_list_all_size` :12380-:12406
  `!L L'. iso_list (L,[]) (L',[]) /\ all (\v. sizel (filter (MEM v) L) > 1)
  (flatten L) ==> all (\v. sizel (filter (MEM v) L') > 1) (flatten L')`
  ↦ `isoListAllSizeSpine`（真证）。HOL 证体 iso_list 展开 + GSYM
  MAP_flatten + Seq.allP + MEM_MAP + lower_case（`Seq.filter_map` +
  `Seq.size_map` 面）把目标面化归 `sizel (filter (\x. MEM (phi x')
  (map phi x)) L) > 1`，ENOUGH_TO_SHOW 拆 `a > 1 ==> a <= b ==> b > 1`
  后 filter_mono 主件直用 + MEMf_MAP 槽收口；Lean 面 φ 自 IsoListSpine
  ∃ 展开、flatten·map 逐点化（mem_flatten + mem_map 两层 obtain）、
  filter 越过 map 经 core `List.filter_map` + `List.length_map`（对应
  HOL `Seq.filter_map` + `Seq.size_map`/lower_case 换装，复合槽
  `∘` 面 show defeq 展开——批 41 comp 叶雷同路）、单调槽 filterMonoSpine
  直投（对应 filter_mono 直用）+ MEMf_MAP 面 = core
  `List.mem_map_of_mem`（decide 双向换装）。

  载体折算盘点（批 41 头注预记侦察面，经全库 grep（含 LocalAuto 族：
  Kepler/Text/LocalAuto3.lean、Kepler/Text/PackingAuto18.lean 等在册）
  对拍——零撞车）：
  - `MEMf_MAP`（tame_list.hl:157-:161 `MEM x u ==> MEM (f x) (MAP f u)`）
    = core `List.mem_map_of_mem`（Init/Data/List/Lemmas.lean:1131，f
    隐式槽由预期类型定 phi）；
  - `MAP_flatten`（tame_list.hl:873-:879）面 = core `List.mem_flatten` +
    `List.mem_map` 两层逐点直拆（GSYM MAP_flatten 换装被逐点化吸收，
    本批不显式落 MAP_flatten 镜像件——HOL 证体亦只在 rewrite 链消费）；
  - `Seq.filter_map`/`Seq.size_map`（lower_case 换装包内）= core
    `List.filter_map`/`List.length_map`；
  - `lower_case`/`upper_case`（tame_list.hl:1397-:1401）= HOL Seq→List
    换装包，Lean 面 List 闭环零折算负担；
  - `Seq.allP`/`Seq2.ALL_all` 面 = `∀ v ∈ flatten L, P v`（批 7
    MarkedListSpine 第 5 合取同形：`1 < (L.filter (fun q =>
    decide (v ∈ q))).length` 逐字同槽）；
  - `sizel` ↦ `List.length`（批 12 sizel 记账，无新 def）。
  全库无 filter-长单调现成载体（Mathlib length_filter_le 族零命中，
  filter_mono 须自证——本批 §1 即镜像本体）。

  新落地载体：零（纯消费批）。私件：零（filterMonoSpine 作为章面
  公开件供下游 marked/size 界消费）。

  诚实记账：主件两件全真证，零新 def、零 sorry、零止损件、零记账债。
  红线遵守：零既有文件触碰、零 git 写操作。
  批 43 接续点：HOL :12408 `iso_list_final_list`（final_list 运输章
  开章——载体链大半在库：next_el_MEM_map = TameLp la7_nextEl_map
  （批 2/11 记账）、inj_on_dart_of_list 面（批 2/批 40 记账）、
  normal_list_uniq_nonnil（批 40 实录在库 T9 面）、f_list_map 载体链
  （tame_list.hl:3840，批 37 头注预记）；仍按雷 #39 先对拍。
-/

import Kepler.Text.TameSpine.TameList41

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)

/-! ### §1 filter/sizel 单调面（tame_list.hl:12354-:12378） -/

/-- **HOL `filter_mono`**（tame_list.hl:12354-:12378）
`!p q r. (!x. MEM x r /\ p x ==> q x) ==> sizel (filter p r) <=
sizel (filter q r)`——filter/sizel 单调面：r 上归纳，p h 支经前提取
q h 走 SUC≤SUC；¬p h 支 q h 支 m ≤ SUC n 由 m ≤ n 放大、¬q h 支 IH
直投。Lean 面 `List.filter`/`length` 形（批 12 sizel 记账），谓词取
`α → Bool`（decide 装载同批 7 MarkedListSpine 第 5 合取）。 -/
theorem filterMonoSpine {α : Type _} (p q : α → Bool) {r : List α}
    (h : ∀ x ∈ r, p x = true → q x = true) :
    (r.filter p).length ≤ (r.filter q).length := by
  induction r with
  | nil => simp
  | cons a t ih =>
    have ih' : (t.filter p).length ≤ (t.filter q).length :=
      ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
    by_cases hp : p a = true
    · have hqa : q a = true := h a List.mem_cons_self hp
      rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos hqa,
        List.length_cons, List.length_cons]
      exact Nat.succ_le_succ ih'
    · rw [List.filter_cons_of_neg hp]
      by_cases hq : q a = true
      · rw [List.filter_cons_of_pos hq, List.length_cons]
        exact Nat.le_trans ih' (Nat.le_succ _)
      · rw [List.filter_cons_of_neg hq]
        exact ih'

/-! ### §2 iso_list_all_size（tame_list.hl:12380-:12406） -/

/-- **HOL `iso_list_all_size`**（tame_list.hl:12380-:12406）
`iso_list (L,[]) (L',[]) /\ all (\v. sizel (filter (MEM v) L) > 1)
(flatten L) ==> all (\v. sizel (filter (MEM v) L') > 1) (flatten L')`
——iso 运输下顶点度 filter>1 下界的保持：v ∈ flatten L' 逐点化出
证人 a ∈ flatten L（v = phi a），filter 越过 MAP 越装
（`List.filter_map` + `List.length_map`，对应 HOL lower_case 包内
`Seq.filter_map`/`Seq.size_map`；复合槽 ∘ 面 show defeq 展开），
单调槽 filterMonoSpine 直投（MEMf_MAP 面 = `List.mem_map_of_mem`
decide 双向换装），单调槽 have 化后 hmono 一步 exact 收口
（`1 < a ≤ b ⟹ 1 < b` 为 refine lt_of_lt_of_le 预拆）。 -/
theorem isoListAllSizeSpine {L L' : fgraph ℕ} (hiso : IsoListSpine L L' [] [])
    (h : ∀ v ∈ L.flatten, 1 < (L.filter (fun s => decide (v ∈ s))).length) :
    ∀ v ∈ L'.flatten, 1 < (L'.filter (fun s => decide (v ∈ s))).length := by
  obtain ⟨phi, -, hL'map, -⟩ := hiso
  subst hL'map
  intro v hv
  rw [List.mem_flatten] at hv
  obtain ⟨r, hrL, hvr⟩ := hv
  rw [List.mem_map] at hrL
  obtain ⟨x, hxL, hrx⟩ := hrL
  subst hrx
  obtain ⟨a, hax, hva⟩ := List.mem_map.mp hvr
  subst hva
  have h1 := h a (List.mem_flatten_of_mem hxL hax)
  refine Nat.lt_of_lt_of_le h1 ?_
  rw [List.filter_map, List.length_map]
  show (L.filter (fun s => decide (a ∈ s))).length ≤
      (L.filter (fun s => decide (phi a ∈ List.map phi s))).length
  have hmono : (L.filter (fun s => decide (a ∈ s))).length ≤
      (L.filter (fun s => decide (phi a ∈ List.map phi s))).length :=
    filterMonoSpine (p := fun s => decide (a ∈ s))
      (q := fun s => decide (phi a ∈ List.map phi s))
      (fun s _ hs => decide_eq_true (List.mem_map_of_mem (of_decide_eq_true hs)))
  exact hmono

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；两件预期零 sorryAx）：
#print axioms Kepler.Text.TameSpine.filterMonoSpine
#print axioms Kepler.Text.TameSpine.isoListAllSizeSpine
-/
