/-
  Kepler.Text.TameSpine.TameList36 — B1 Tame_list 地基批 36：iso_list 章续
  （tamespine-port-plan §4 批次表 B1 行；接续批 35 = TameList35.lean，批 35
  终点 = HOL :11682（quotient_list_elements 已落）；本批起点 = HOL :11684
  `iso_list_nilfamily`。行号均按主仓 reference/flyspeck（commit 1ce0353）
  实测；批 35 预记的 :11688-:11701/:11703 偏移已实测勘误为 :11686-:11706/
  :11707（见下「跳过项」）。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:11684-:11744）：

  主件一：`iso_list_nilfamily` :11684-:11687
  `!L L' N N'. iso_list (L,N) (L',N') ==> iso_list (L,[]) (L',[])`
  ↦ `isoListNilFamily`（一行为，随收）。证明同 HOL（REWRITE_TAC[iso_list;
  MAP] + MESON）：取同一 φ 证人——inj_on 与 L' 方程逐槽原样搬运，N 槽
  `[] = ([]).map _` 定义式 rfl（List.map_nil 定义形，零 simp）。
  下游消费：tame_list.hl:12503（final_list 对合件 SUBCONJ 支）+
  MEEIXJO.hl:336——批 37 起待装配。

  主件二：`iso_list_mem_rN` :11709-:11721
  `!L N r x L' N' r' x'. good_list L' /\ MEM r N /\
  iso_list (L,([x]::r::N)) (L',([x']::r'::N')) ==> MEM r' N'`
  ↦ `isoListMemRN`（MEMf_MAP 面，批 2 memfMap 在库）。证明同 HOL
  （REWRITE_TAC[iso_list;MAP;CONS_11] + ASM_REWRITE + MEMf_MAP）：N 侧
  方程 `[x']::r'::N' = ([x]::r::N).map phil` 经 List.map_cons 两发
  （simp only 至不动点，beta 一并折尽）+ injection 双层拆条（CONS_11
  语义）得 `r' = r.map phil`、`N' = N.map phil`，目标即 memfMap hr
  `phil r ∈ MAP phil N`（雷区 #4 处方：拆条后 subst 交 memfMap 一次
  exact，beta 差 exact 吸收）。

  主件三：`iso_list_mem_xr` :11723-:11735（射程内随收）
  `!L N r x L' N' r' x'. good_list L' /\ MEM x r /\
  iso_list (L,([x]::r::N)) (L',([x']::r'::N')) ==> MEM x' r'`
  ↦ `isoListMemXR`（同 MEMf_MAP 面）。同链拆条：头槽 `[x'] = [phil x]`
  再 injection 一发得 `x' = phil x`，尾槽 `r' = r.map phil`，目标即
  memfMap hx `phil x ∈ MAP phil r`。MEEIXJO.hl:355 消费在案。

  主件四：`iso_list_cons` :11737-:11744（射程内随收）
  `!L N L' N' u u'. iso_list (L,(u::N)) (L',(u'::N')) ==> iso_list (L,N)
  (L',N')` ↦ `isoListCons`（一行为）。同链：N 侧方程 List.map_cons 一发
  + injection 头尾拆条，尾槽 `N' = N.map phil` 原样回装 ⟨φ 同人⟩——
  inj_on 与 L' 方程逐槽搬运（批 1 GNBEVVU obtain 逐槽惯例）。
  下游消费：tame_list.hl:12507 + MEEIXJO 面——批 37 起待装配。

  跳过项（非止损，照批 35 记档体例）：
  · :11686-:11706 `iso_list_cons` 系 HOL 源注释块（`(* ... *)` 内的
    未完成草稿 `st/r` 占位，非定理）；
  · :11707 `iso_list_marked_rN = 0` 系非定理数值占位（marked_list 章
    领土，B1 无消费）。

  载体折算：iso_list ↦ 批 1 `IsoListSpine`（tame_defs2.hl:62-65 def 复用，
  (L,N) 捆对四参数平铺，雷区 #11 记档：平铺序 (L L')(N N')）；phil :=
  `fun s => s.map (fun u => (phi u.1, phi u.2))`（批 1 IsopListSpine
  第三合取 N' 方程原形）；MAP/CONS_11 ↦ `List.map_cons` + `injection`
  双层拆条；MEMf_MAP ↦ 批 2 `memfMap`（TameList2.lean:195）。HOL 语句
  的 `good_list L'` 前提在 HOL 证体零消费（ASM_REWRITE 搭载），Lean 面
  逐字保留（`_hgoodL'` 记档不消费）。

  终点自然边界：`iso_list_cons` 后 :11747 入 `elements_of_list_
  quotient_list`（normal_list + is_edge_nondegenerate + all uniq 前提
  族、SUBSET 型新章——载体 listOfDartsQuotientDarts 批 16 在库），
  非本批射程，批 37 接续点。

  依赖面：批链全批 1-35；本批零新 def，消费面 = 批 1 IsoListSpine/
  IsopListSpine + 批 2 memfMap；核心 List.map_cons / injection。

  诚实记账：本批四件全部真证，零新 def、零 sorry、零止损件、零记账债。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零
  git 写操作。批 37 接续点：HOL :11747 `elements_of_list_quotient_list`
  `!L N. normal_list L N /\ is_edge_nondegenerate (hypermap_of_list L)
  /\ good_list L /\ all uniq L ==> elements_of_list (quotient_list L N)
  SUBSET elements_of_list L`（EXTENSION 折 Set.Subset 逐点 + 证人 y +
  `list_of_darts_quotient_darts` ↦ 批 16 `listOfDartsQuotientDarts`
  TameList16.lean:701 在库；mem_list_of_darts/elements_of_list 的
  darts↔elements 桥面需批 37 侦察）→ 其后 :11764 `inj_on_quotient_list`
  （inj_on_subset + 前件复用）。
-/

import Kepler.Text.TameSpine.TameList35

namespace Kepler.Text.TameSpine

open Kepler.Assembly (GoodList)
open Kepler.Graphs (fgraph)

/-! ### §1 iso_list_nilfamily（tame_list.hl:11684-:11687）——随收件 -/

/-- **HOL `iso_list_nilfamily`**（tame_list.hl:11684-:11687）
`!L L' N N'. iso_list (L,N) (L',N') ==> iso_list (L,[]) (L',[])`
——同一 φ 证人逐槽搬运（inj_on 与 L' 方程原样），N 槽 `[] = ([]).map _`
定义式 rfl。下游消费 tame_list.hl:12503 + MEEIXJO.hl:336。 -/
theorem isoListNilFamily {L L' : fgraph ℕ} {N N' : List (List (ℕ × ℕ))}
    (h : IsoListSpine L L' N N') : IsoListSpine L L' [] [] := by
  obtain ⟨phi, hinj, hL', -⟩ := h
  exact ⟨phi, hinj, hL', rfl⟩

/-! ### §2 iso_list_mem_rN / iso_list_mem_xr（:11709-:11735）——MEMf_MAP 面 -/

/-- **HOL `iso_list_mem_rN`**（tame_list.hl:11709-:11721）
`good_list L' /\ MEM r N /\ iso_list (L,([x]::r::N)) (L',([x']::r'::N'))
==> MEM r' N'`——N 侧方程 `List.map_cons` + injection 双层拆条
（CONS_11 语义）得 `r' = r.map phil`、`N' = N.map phil`，目标即批 2
`memfMap`。`good_list L'` 前提照 HOL 逐字保留（证体零消费）。 -/
theorem isoListMemRN {L L' : fgraph ℕ}
    {N N' : List (List (ℕ × ℕ))} {r r' : List (ℕ × ℕ)} {x x' : ℕ × ℕ}
    (_hgoodL' : GoodList L') (hr : r ∈ N)
    (h : IsoListSpine L L' ([x] :: r :: N) ([x'] :: r' :: N')) :
    r' ∈ N' := by
  obtain ⟨phi, -, -, hN'⟩ := h
  simp only [List.map_cons] at hN'
  injection hN' with _ hcons
  injection hcons with hr' htail
  subst hr'
  subst htail
  exact memfMap hr

/-- **HOL `iso_list_mem_xr`**（tame_list.hl:11723-:11735）
`good_list L' /\ MEM x r /\ iso_list (L,([x]::r::N)) (L',([x']::r'::N'))
==> MEM x' r'`——同链拆条：头槽 `[x'] = [phil x]` 再 injection 得
`x' = phil x`，尾槽 `r' = r.map phil`，目标即批 2 `memfMap`。
MEEIXJO.hl:355 消费在案。 -/
theorem isoListMemXR {L L' : fgraph ℕ}
    {N N' : List (List (ℕ × ℕ))} {r r' : List (ℕ × ℕ)} {x x' : ℕ × ℕ}
    (_hgoodL' : GoodList L') (hx : x ∈ r)
    (h : IsoListSpine L L' ([x] :: r :: N) ([x'] :: r' :: N')) :
    x' ∈ r' := by
  obtain ⟨phi, -, -, hN'⟩ := h
  simp only [List.map_cons] at hN'
  injection hN' with hhead hcons
  injection hcons with hr' _
  injection hhead with hx' _
  subst hr'
  subst hx'
  exact memfMap hx

/-! ### §3 iso_list_cons（tame_list.hl:11737-:11744）——随收件 -/

/-- **HOL `iso_list_cons`**（tame_list.hl:11737-:11744）
`!L N L' N' u u'. iso_list (L,(u::N)) (L',(u'::N')) ==> iso_list (L,N)
(L',N')`——N 侧方程 List.map_cons 一发 + injection 头尾拆条，尾槽
`N' = N.map phil` 原样回装（inj_on 与 L' 方程逐槽搬运）。下游消费
tame_list.hl:12507。 -/
theorem isoListCons {L L' : fgraph ℕ} {N N' : List (List (ℕ × ℕ))}
    {u u' : List (ℕ × ℕ)}
    (h : IsoListSpine L L' (u :: N) (u' :: N')) : IsoListSpine L L' N N' := by
  obtain ⟨phi, hinj, hL', hN'⟩ := h
  simp only [List.map_cons] at hN'
  injection hN' with _ hcons
  exact ⟨phi, hinj, hL', hcons⟩

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；四件预期标准三
[propext, Classical.choice, Quot.sound]，零 sorryAx）：
#print axioms Kepler.Text.TameSpine.isoListNilFamily
#print axioms Kepler.Text.TameSpine.isoListMemRN
#print axioms Kepler.Text.TameSpine.isoListMemXR
#print axioms Kepler.Text.TameSpine.isoListCons
-/
