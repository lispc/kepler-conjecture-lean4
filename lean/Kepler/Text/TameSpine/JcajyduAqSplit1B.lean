/-
  Kepler.Text.TameSpine.JcajyduAqSplit1B — 车道 `jcajydu-split1b`（AQ/E4b 第一批）：
  `aq3Concl` split.1 支的 **n_list 幂循环机核**（HOL AQ23.hl:359-:669 的 Lean 内核前段）。

  件目（15 声明 = 9 组，全真证）：
  ① `nListMemDarts`：`d ∈ list_of_darts L → n_list L d ∈ list_of_darts L`
     （GoodList 的 `bijOn_nList` 投影；HOL `list_ext_power_in_darts` 的单步核）；
  ② `nListPowEqNodeMapPow`（HOL `Lebhirj.n_list_ext_n_list_power` 的 Spine 形）：
     `(n_list L)^[k] d = (node_map)^k d`（d ∈ darts，归纳 + `nodeMap_hypermapOfList`）；
  ③ `nodeMapSymmEqFList`（HOL `inverse_n_list_ext` 环回）：
     `node_map.symm d = f_list L (e_list d)`（`inverse_hypermap_maps` 第二式 +
     edge/face 两桥）；
  ④ `nodeMapPowPredEqFList`（HOL `lemma_node_cycle` 终点合流）：
     `(node_map)^(node.ncard − 1) d = f_list L (e_list d)`（幂循环 + 逆元唯一性）；
  ⑤ `fListInjDarts`（HOL `F_LIST_INJ`，AQ23.hl:210）：`f_list` 在 darts 上单射
     （`bijOn_fList` 的 InjOn 投影）；
  ⑥ `countNodeFace`（HOL `Hojodcm.count_node_face`，HOJODCM.hl:607）：
     `sizel (filter (· = v) (flatten L)) = sizel (filter (v ∈ ·) L)`
     （`uniq L` + 逐面 `uniq`）。**类型层结论见 DELIVERY §0**：HOL 的 `L` 是
     顶点表层 `((A)list)list`，Lean `fgraph ℕ = List (List ℕ)` 同层，**零折算**；
  ⑦ `countDartsFst` + `szEqNodeCard`（**新桥**，取代 HOL `dart_of_card_node`
     的 BIJ 路线）：`sz v = (node d).ncard`（d ∈ darts、d.1 = v、
     `GoodListNodesTl`）——`sz` 的 flatten-计数 ↔ darts 首点计数 ↔ 面行计数；
  ⑧ `ndSpine` / `ndSpineNeNil` / `lastNdSpine` / `lastNdSpineEqFList`
     （HOL `LAST_UPT` + `LAST_MAP` + `LAST_FLATTEN_2` 的 nd 末元链 +
     循环合流）：`(nd x).getLast! = (n_list L)^[sz x.1 − 1] x`，且
     `(n_list L)^[sz d.1 − 1] d = f_list L z1`（d = e_list z1）；
  ⑨ `getLast?_flatten_of_ne`（private，List 层）+ `lastFlattenMapNdSpine` +
     `lastNew1EqFList`：**`LAST new1` 全链**——`((new2.map nd).flatten).getLast!
     = (nd (new2.getLast)).getLast! = f_list L z1`（`new2 ≠ []`、每块非空、
     `new2.getLast = e_list z1`）；三段 = HOL `LAST_FLATTEN_2` + `LAST_MAP` + ⑧。

  **DEF-FIX 语义**（`5628f300`）：`nd x` 末元 = `(nList L)^[sz − 1] x`（HOL 对齐）；
  本文件 ⑧ 按新语义写，`lastRange`（E4a，`2427169b`）是其末元指数载体。

  边界（未了清单见 DELIVERY §4，按 AGENTS §7 止损，不硬凑）：
  `uniqFstSplitNorm`（HOL AQ1:1373）及其前置 `uniq_flatten_map_upt_betwn`
  （AQ1:1135）/ `node_betwn_not_in_rtrans`（AQ1:1339）/ `betwn_not_in_fst_flatten`
  （AQ1:1247）不在本批；`prevRNotEqF`/`nextRNotEqF`（AQ1:612/:690）亦未落。
  ⇒ `f_lastSpine L split.1` 的**接线步**（`nextEl split.1 z1 = LAST new1`，
  需 `z1` 在 split.1 中唯一出现）与 `aq3Concl` 全式 **BLOCKED**（缺口与修法
  见 DELIVERY §4）；`LAST new1 = f_list L z1` 本体已在 ⑨ 落地。

  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameSpine.JcajyduAqSplit1
import Kepler.Text.TameSpine.JcajyduAqSnd
import Kepler.Text.TameSpine.JcajyduAqZUnlock

namespace Kepler.Text.TameSpine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Kepler.Assembly (nextEl prevEl eList fList GoodList findFaceDarts nList
  listOfDarts listPairs)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl nodesOfListSet listOfElements
  dart_in_face findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nodeMap_hypermapOfList edgeMap_hypermapOfList faceMap_hypermapOfList bijOn_nList
  bijOn_fList)

theorem nListMemDarts (L : fgraph ℕ) (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) : nList L d ∈ listOfDarts L :=
  (bijOn_nList hL).1 hd

theorem nListPowEqNodeMapPow (L : fgraph ℕ) (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) (k : ℕ) :
    (nList L)^[k] d = ((hypermapOfList L hL).nodeMap ^ k) d := by
  have hmem : ∀ i, (nList L)^[i] d ∈ listOfDarts L := by
    intro i
    induction i with
    | zero => simpa using hd
    | succ i ih => rw [Function.iterate_succ_apply']; exact nListMemDarts L hL ih
  have hdarts : ∀ i, ((hypermapOfList L hL).nodeMap ^ i) d ∈ (hypermapOfList L hL).darts := by
    intro i
    exact Kepler.Text.Hypermap.nodeMap_permutes (hypermapOfList L hL) |>.pow_apply_mem i
      (List.mem_toFinset.mpr hd)
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih,
      ← nodeMap_hypermapOfList L hL (hdarts k), pow_succ', Equiv.Perm.mul_apply]

theorem nodeMapSymmEqFList (L : fgraph ℕ) (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ (hypermapOfList L hL).darts) :
    (hypermapOfList L hL).nodeMap.symm d = fList L (eList d) := by
  change (hypermapOfList L hL).nodeMap⁻¹ d = fList L (eList d)
  obtain ⟨-, h2, -⟩ := Kepler.Text.Hypermap.inverse_hypermap_maps (hypermapOfList L hL)
  have he : eList d ∈ (hypermapOfList L hL).darts := by
    rw [show eList d = (d.2, d.1) from rfl]
    exact List.mem_toFinset.mpr (hL.2.2 d (List.mem_toFinset.mp hd))
  rw [h2, Equiv.Perm.mul_apply, edgeMap_hypermapOfList L hL hd,
    faceMap_hypermapOfList L hL he]

theorem nodeMapPowPredEqFList (L : fgraph ℕ) (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ (hypermapOfList L hL).darts) :
    ((hypermapOfList L hL).nodeMap ^ (((hypermapOfList L hL).node d).ncard - 1)) d
      = fList L (eList d) := by
  set H := hypermapOfList L hL
  have hn1 : 1 ≤ (H.node d).ncard := by
    have hpos : 0 < (H.node d).ncard := by
      rw [Set.ncard_pos (Kepler.Text.Hypermap.node_finite H d)]
      exact ⟨d, Kepler.Text.Hypermap.mem_node_self H d⟩
    omega
  have hcyc : (H.nodeMap ^ (H.node d).ncard) d = d :=
    Kepler.Text.Hypermap.pow_card_node_apply_self H d
  have hstep : H.nodeMap (((H.nodeMap) ^ ((H.node d).ncard - 1)) d) = d := by
    rw [← Equiv.Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel hn1]
    exact hcyc
  have hs : H.nodeMap.symm d = ((H.nodeMap) ^ ((H.node d).ncard - 1)) d := by
    apply H.nodeMap.injective
    rw [Equiv.apply_symm_apply, hstep]
  rw [← hs, nodeMapSymmEqFList L hL hd]

theorem fListInjDarts (L : fgraph ℕ) (hL : GoodList L) {y z : ℕ × ℕ}
    (hy : y ∈ listOfDarts L) (hz : z ∈ listOfDarts L) :
    fList L y = fList L z ↔ y = z :=
  ⟨fun h => (bijOn_fList hL.1).2.1 hy hz h, fun h => by rw [h]⟩

private theorem lenFilterEqOfNodup {α : Type*} [DecidableEq α] {l : List α}
    (h : l.Nodup) (v : α) :
    (l.filter (fun t => decide (t = v))).length = if v ∈ l then 1 else 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at h
    obtain ⟨hat, ht⟩ := h
    by_cases ha : a = v
    · subst ha
      have hnil : (t.filter (fun t => decide (t = a))) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx hxdec
        exact hat (of_decide_eq_true hxdec ▸ hx)
      rw [List.filter_cons, if_pos (by simp)]
      simp [hnil]
    · have hdec : ¬ (decide (a = v) = true) := by simpa using ha
      rw [List.filter_cons, if_neg hdec, ih ht]
      by_cases hvt : v ∈ t
      · rw [if_pos hvt, if_pos (List.mem_cons_of_mem a hvt)]
      · rw [if_neg hvt, if_neg (fun hc => hvt (List.mem_cons.mp hc |>.resolve_left
          (fun hv => ha hv.symm)))]

theorem countNodeFace (L : fgraph ℕ) (hL : L.Nodup) (hun : ∀ l ∈ L, l.Nodup) (v : ℕ) :
    (L.flatten.filter (fun t => decide (t = v))).length
      = (L.filter (fun l => decide (v ∈ l))).length := by
  induction L with
  | nil => simp
  | cons l ls ih =>
    rw [List.nodup_cons] at hL
    obtain ⟨hll, hls⟩ := hL
    have hlnd : l.Nodup := hun l (List.mem_cons_self ..)
    have hlsun : ∀ l' ∈ ls, l'.Nodup := fun l' h' => hun l' (List.mem_cons_of_mem _ h')
    rw [List.flatten_cons, List.filter_append, List.length_append, ih hls hlsun,
      List.filter_cons, lenFilterEqOfNodup hlnd v]
    by_cases hv : v ∈ l
    · rw [if_pos (c := decide (v ∈ l) = true) (decide_eq_true hv), if_pos (c := v ∈ l) hv]
      simp only [List.length_cons]
      omega
    · rw [if_neg (c := decide (v ∈ l) = true) (fun h => hv (of_decide_eq_true h)),
        if_neg (c := v ∈ l) hv]
      omega

private theorem lengthFilterFstZip {α : Type*} [DecidableEq α] (a b : List α)
    (h : b.length = a.length)
    (v : α) :
    ((a.zip b).filter (fun p : α × α => decide (p.1 = v))).length
      = (a.filter (fun x => decide (x = v))).length := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons a as ih =>
    cases b with
    | nil => simp at h
    | cons b bs =>
      rw [List.zip_cons_cons, List.filter_cons, List.filter_cons]
      have h' : bs.length = as.length := by simpa using h
      by_cases hav : decide (a = v) = true
      · rw [if_pos hav, if_pos hav]
        simp only [List.length_cons, ih bs h']
      · rw [if_neg hav, if_neg hav]
        exact ih bs h'

theorem countDartsFst (L : fgraph ℕ) (v : ℕ) :
    ((listOfDarts L).filter (fun d => decide (d.1 = v))).length
      = (L.flatten.filter (fun t => decide (t = v))).length := by
  induction L with
  | nil => simp [listOfDarts]
  | cons l ls ih =>
    simp only [listOfDarts, List.map_cons, List.flatten_cons, List.filter_append,
      List.length_append, ih]
    congr 1
    rw [listPairs]
    have hlen : (l.drop 1 ++ l.take 1).length = l.length := by
      rw [List.length_append, List.length_drop, List.length_take]; omega
    exact lengthFilterFstZip l (l.drop 1 ++ l.take 1) hlen v

theorem szEqNodeCard (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {d : ℕ × ℕ} (hd : d ∈ (hypermapOfList L hL).darts) :
    (L.flatten.filter (fun t => decide (t = d.1))).length
      = ((hypermapOfList L hL).node d).ncard := by
  set H := hypermapOfList L hL
  have hnode : H.node d = {d' : ℕ × ℕ | d' ∈ listOfDarts L ∧ d'.1 = d.1} := by
    have hmem : H.node d ∈ H.nodeSet := ⟨d, hd, rfl⟩
    rw [hgn] at hmem
    obtain ⟨x, _hx, hxeq⟩ := hmem
    have hxeq' : {d' : ℕ × ℕ | d' ∈ listOfDarts L ∧ d'.1 = x} = H.node d := hxeq
    have hdx : d.1 = x := by
      have hd' : d ∈ {d' : ℕ × ℕ | d' ∈ listOfDarts L ∧ d'.1 = x} := by
        rw [hxeq']; exact Kepler.Text.Hypermap.mem_node_self H d
      exact hd'.2
    rw [← hxeq', hdx]
  have hset : {d' : ℕ × ℕ | d' ∈ listOfDarts L ∧ d'.1 = d.1}
      = ↑((listOfDarts L).filter (fun d' => decide (d'.1 = d.1))).toFinset := by
    ext d'
    rw [Set.mem_setOf_eq, Finset.mem_coe, List.mem_toFinset, List.mem_filter]
    simp
  have hncard : (↑((listOfDarts L).filter (fun d' => decide (d'.1 = d.1))).toFinset
      : Set (ℕ × ℕ)).ncard
      = ((listOfDarts L).filter (fun d' => decide (d'.1 = d.1))).length := by
    rw [Set.ncard_eq_toFinset_card _ (Finset.finite_toSet _)]
    have hF : (Finset.finite_toSet ((listOfDarts L).filter
        (fun d' => decide (d'.1 = d.1))).toFinset).toFinset
        = ((listOfDarts L).filter (fun d' => decide (d'.1 = d.1))).toFinset := by
      ext x
      simp
    rw [hF, List.toFinset_card_of_nodup (hL.1.filter _)]
  rw [hnode, hset, hncard, countDartsFst L d.1]


noncomputable def ndSpine (L : fgraph ℕ) (x : ℕ × ℕ) : List (ℕ × ℕ) :=
  (List.range' 1 ((L.flatten.filter (fun t => decide (t = x.1))).length - 1)).map
    (fun i => (nList L)^[i] x)

theorem ndSpineNeNil (L : fgraph ℕ) (x : ℕ × ℕ)
    (h2 : 2 ≤ (L.flatten.filter (fun t => decide (t = x.1))).length) :
    ndSpine L x ≠ [] := by
  rw [ndSpine]
  intro h0
  exact List.ne_nil_of_length_pos (by rw [List.length_range']; omega)
    (List.map_eq_nil_iff.mp h0)

theorem lastNdSpine (L : fgraph ℕ) (x : ℕ × ℕ)
    (h2 : 2 ≤ (L.flatten.filter (fun t => decide (t = x.1))).length) :
    (ndSpine L x).getLast!
      = (nList L)^[((L.flatten.filter (fun t => decide (t = x.1))).length - 1)] x := by
  have hne : (List.range' 1 ((L.flatten.filter (fun t => decide (t = x.1))).length - 1))
      ≠ [] := List.ne_nil_of_length_pos (by rw [List.length_range']; omega)
  have hmapne : ndSpine L x ≠ [] := ndSpineNeNil L x h2
  rw [getLast!EqGetLast hmapne]
  unfold ndSpine
  rw [List.getLast_map hmapne]
  have hlr : (List.range' 1 ((L.flatten.filter (fun t => decide (t = x.1))).length - 1)).getLast hne
      = ((L.flatten.filter (fun t => decide (t = x.1))).length - 1) := by
    rw [← getLast!EqGetLast hne]
    exact lastRange h2
  rw [hlr]

theorem lastNdSpineEqFList (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {d z1 : ℕ × ℕ} (hd : d ∈ (hypermapOfList L hL).darts) (hz : d = eList z1) :
    (nList L)^[((L.flatten.filter (fun t => decide (t = d.1))).length - 1)] d
      = fList L z1 := by
  rw [nListPowEqNodeMapPow L hL (List.mem_toFinset.mp hd)]
  have hsz : (L.flatten.filter (fun t => decide (t = d.1))).length - 1
      = ((hypermapOfList L hL).node d).ncard - 1 := by
    rw [szEqNodeCard L hL hgn hd]
  rw [hsz, nodeMapPowPredEqFList L hL hd, hz]
  show fList L (eList (eList z1)) = fList L z1
  rw [show eList (eList z1) = z1 from by cases z1 with
    | mk a b => rfl]


/-- `flatten` 的末元（`getLast?` 形，零证明参搬运）：外层非空 + 每块非空 ⇒
`l.flatten.getLast? = (l.getLast hl).getLast?`——HOL `LAST_FLATTEN_2` 的
Option 形（避开 `getLast` 证明参的 dependent-rewrite）。 -/
private theorem getLast?_flatten_of_ne {α : Type*} (l : List (List α)) (hl : l ≠ [])
    (h : ∀ x ∈ l, x ≠ []) : l.flatten.getLast? = (l.getLast hl).getLast? := by
  induction l with
  | nil => exact absurd rfl hl
  | cons x t ih =>
    by_cases ht : t = []
    · subst ht
      simp
    · have htn : t.flatten ≠ [] := by
        obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil t ht
        have hz' : z ≠ [] := h z (List.mem_cons_of_mem x hz)
        obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil z hz'
        intro h0
        have hz0 : z = [] := (List.flatten_eq_nil_iff.mp h0) z hz
        rw [hz0] at hy
        exact List.not_mem_nil hy
      obtain ⟨w, hw⟩ : ∃ w, t.getLast? = some w := by
        cases hg : t.getLast? with
        | none => rw [List.getLast?_eq_none_iff] at hg; exact absurd hg ht
        | some w => exact ⟨w, rfl⟩
      have hw' : t.getLast ht = w := by
        rw [List.getLast?_eq_some_getLast ht] at hw
        exact Option.some.inj hw
      have hih := ih ht (fun z hz => h z (List.mem_cons_of_mem x hz))
      have hwne : w ≠ [] := by
        rw [← hw']
        exact h _ (List.mem_cons_of_mem x (List.getLast_mem ht))
      rw [List.flatten_cons, List.getLast?_append, hih, hw', List.getLast_cons ht, hw']
      cases hgw : w.getLast? with
      | none => rw [List.getLast?_eq_none_iff] at hgw; exact absurd hgw hwne
      | some u => simp

/-- **HOL `LAST_FLATTEN_2` + `LAST_MAP` 的组合**（`LAST new1` 链的中段）：
`new2 ≠ []` 且每个块的 `ndSpine` 非空 ⇒
`LAST ((new2.map ndSpine).flatten) = LAST (ndSpine (LAST new2))`。 -/
theorem lastFlattenMapNdSpine (L : fgraph ℕ) {new2 : List (ℕ × ℕ)} (hne : new2 ≠ [])
    (h2 : ∀ x ∈ new2, 2 ≤ (L.flatten.filter (fun t => decide (t = x.1))).length) :
    ((new2.map (ndSpine L)).flatten).getLast!
      = (ndSpine L (new2.getLast hne)).getLast! := by
  have hd1mem : new2.getLast hne ∈ new2 := List.getLast_mem hne
  have hd1ne : ndSpine L (new2.getLast hne) ≠ [] := ndSpineNeNil L _ (h2 _ hd1mem)
  have hmapne : new2.map (ndSpine L) ≠ [] := by simpa using hne
  have hall : ∀ x ∈ new2.map (ndSpine L), x ≠ [] := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact ndSpineNeNil L y (h2 y hy)
  rw [List.getLast!_eq_getLast?_getD, List.getLast!_eq_getLast?_getD,
    getLast?_flatten_of_ne (new2.map (ndSpine L)) hmapne hall,
    List.getLast_map hmapne, List.getLast?_eq_some_getLast hd1ne]

/-- **`LAST new1` 全链**（f_last split.1 的循环合流结论，HOL AQ23:502-:669 的 Lean 内核）：
`new1 = (new2.map nd).flatten`、`new2 ≠ []`、每块非空、且 `LAST (betwn f y z) = e_list z1`
⇒ `LAST new1 = f_list L z1`。三段：`lastFlattenMapNdSpine` → `lastNdSpine` → `lastNdSpineEqFList`。 -/
theorem lastNew1EqFList (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {new2 : List (ℕ × ℕ)} (hne : new2 ≠ [])
    (hmem : ∀ x ∈ new2, x ∈ (hypermapOfList L hL).darts)
    (h2 : ∀ x ∈ new2, 2 ≤ (L.flatten.filter (fun t => decide (t = x.1))).length)
    {z1 : ℕ × ℕ} (hz : new2.getLast hne = eList z1) :
    ((new2.map (ndSpine L)).flatten).getLast! = fList L z1 := by
  have hd1mem : new2.getLast hne ∈ new2 := List.getLast_mem hne
  rw [lastFlattenMapNdSpine L hne h2, lastNdSpine L _ (h2 _ hd1mem)]
  exact lastNdSpineEqFList L hL hgn (hmem _ hd1mem) hz

theorem two_le_sz_of_restricted (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hrestr : (hypermapOfList L hL).IsRestricted)
    {x : ℕ × ℕ} (hx : x ∈ (hypermapOfList L hL).darts) :
    2 ≤ (L.flatten.filter (fun t => decide (t = x.1))).length := by
  rw [szEqNodeCard L hL hgn hx]
  exact (Kepler.Text.Hypermap.nodeNondegenerate_two_le _).mp
    hrestr.nodeNondegenerate x hx


end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三 ⊆ [propext, Classical.choice,
Quot.sound]，零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.nListMemDarts
#print axioms Kepler.Text.TameSpine.nListPowEqNodeMapPow
#print axioms Kepler.Text.TameSpine.nodeMapSymmEqFList
#print axioms Kepler.Text.TameSpine.nodeMapPowPredEqFList
#print axioms Kepler.Text.TameSpine.fListInjDarts
#print axioms Kepler.Text.TameSpine.countNodeFace
#print axioms Kepler.Text.TameSpine.countDartsFst
#print axioms Kepler.Text.TameSpine.szEqNodeCard
#print axioms Kepler.Text.TameSpine.ndSpine
#print axioms Kepler.Text.TameSpine.ndSpineNeNil
#print axioms Kepler.Text.TameSpine.lastNdSpine
#print axioms Kepler.Text.TameSpine.lastNdSpineEqFList
#print axioms Kepler.Text.TameSpine.lastFlattenMapNdSpine
#print axioms Kepler.Text.TameSpine.lastNew1EqFList
#print axioms Kepler.Text.TameSpine.two_le_sz_of_restricted
