/-
  Kepler.Text.Reduction3Thm4TheoryB — T4-theory 后半：
  `minimalFaceCore`（reduction3.hl:1179）+ `hdVsSomeV`（:998）+
  `lastVsSomePrev`（:1067，T3 缓件二枚）。

  ┌─ 路线 ────────────────────────────────────────────────────────
  │ minimalFaceCore：core L r 与 f.vertices 同为
  │ `findList (quotientList.map listPairs) x`（findListUniq TameList9
  │ 双向：x ∈ listPairs f.vertices 经 loopChoiceProps 的
  │ x = (prevEl f.vertices v, v) + prevElListPairsEq；x ∈ listPairs
  │ (core L r) 经 listPairsCore TameList58（Spine 直调 + core/parts
  │ 桥）与 loopChoice2 的 x = LAST p），再用 **listPairsInj**
  │ （本文件 8 行：`(listPairs l).map Prod.fst = l`）收口。
  │ 不做 HOL 的 find_pair_list/map-back 路线（省 ~80 行）。
  │ hdVsSomeV / lastVsSomePrev：destTripleFull 的前/末段直接分情形；
  │ uvns 非空以 `h0 : transformCount ≠ 0` 槽供给（T2 的
  │ `transformCountNon0` + 批 E 一行代入，**本文件零 J2 依赖**）。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide。junk：LAST↦getLastD/getLast!、
  │ the↦getD 0（均带非空/在界守卫）。注释框行尾禁「减斜杠」（全战役头号
  │ 机械雷区，本文件已按 depth 核查）。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm4
import Kepler.Text.T4TheoryA
import Kepler.Text.ChainBridgeParts
import Kepler.Text.MoreLemma2Island1
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.MoreLemma2Island3
import Kepler.Text.TameSpine.TameList6
import Kepler.Text.TameSpine.TameList8
import Kepler.Text.TameSpine.TameList9
import Kepler.Text.TameSpine.TameList10
import Kepler.Text.TameSpine.TameList14
import Kepler.Text.TameSpine.TameList34
import Kepler.Text.TameSpine.TameList58

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (GoodList listOfDarts listPairs prevEl nextEl)
open Kepler.Graphs (Face Graph minimalFace minimalVertex nonFinals fgraph between)
open Kepler.Text.Reduction5 (Dart core finalList parts quotientList transformCount)
open Kepler.Text.ChainLists (findList markedList normalList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)

/-! ## §0 辅助 -/

private theorem map_fst_listPairs (l : List ℕ) : (listPairs l).map Prod.fst = l := by
  have hlen : l.length ≤ (l.drop 1 ++ l.take 1).length := by
    cases l with
    | nil => simp
    | cons x xs => simp
  rw [Kepler.Assembly.listPairs]
  exact List.map_fst_zip hlen

private theorem listPairsInj {l₁ l₂ : List ℕ} (h : listPairs l₁ = listPairs l₂) :
    l₁ = l₂ := by
  rw [← map_fst_listPairs l₁, ← map_fst_listPairs l₂, h]

/-- `core` 链/Spine 桥（`headD (0,0)` ↔ `head!`，parts 桥后逐点）。 -/
private theorem coreEqCoreSpine (L : fgraph ℕ) (r : List Dart) :
    core L r = Kepler.Text.TameSpine.coreSpine L r := by
  unfold core Kepler.Text.TameSpine.coreSpine
  rw [Kepler.Text.ChainBridge.parts_eq_partsSpine L r]
  congr 1
  funext p
  cases p with
  | nil => rfl
  | cons x xs => rfl

private theorem headD_append {α : Type} (d : α) (a b : List α) :
    (a ++ b).headD d = if a = [] then b.headD d else a.headD d := by
  cases a with
  | nil => rfl
  | cons x xs => rfl

private theorem getLastD_append_of_ne {α : Type} (d : α) (a : List α) {b : List α}
    (h : b ≠ []) : (a ++ b).getLastD d = b.getLastD d := by
  induction a generalizing d with
  | nil => rfl
  | cons x xs ih =>
    rw [List.cons_append, List.getLastD_cons, ih]
    cases b with
    | nil => exact (h rfl).elim
    | cons y ys => rw [List.getLastD_cons, List.getLastD_cons]

private theorem getLast!_mem_of_ne {α : Type} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! ∈ l := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast h, Option.getD_some]
  exact List.getLast_mem h

/-- 非空表上 `getLast?` 的 `getLastD` 形（缺省一致时）。 -/
private theorem getLast?_eq_some_getLastD {α : Type} {l : List α} (h : l ≠ [])
    {d : α} : l.getLast? = some (l.getLastD d) := by
  rw [List.getLast?_eq_some_getLast h, List.getLastD_eq_getLast?,
    List.getLast?_eq_some_getLast h]
  simp

/-- `lastDestTriple0` 的 getLastD 形（T2 的 getLast? 形 + 上式）。 -/
private theorem lastDestTriple0D {uvns : List (ℕ × ℕ × ℕ)} (h : uvns ≠ [])
    (f : List ℕ) (s : List (Option ℕ)) :
    (destTriple0 f s uvns).getLastD none
      = some ((uvns.getLastD (0, 0, 0)).2.1) := by
  rw [List.getLastD_eq_getLast?, lastDestTriple0 uvns h f s,
    getLast?_eq_some_getLastD h (d := (0, 0, 0))]
  simp only [Option.map_some, Option.getD_some]

/-- `destTriple0` 在空 sofar + 非空 uvns 时以 `some u` 开头。 -/
private theorem destTriple0_nil_head (f : List ℕ) (u v n : ℕ)
    (ts : List (ℕ × ℕ × ℕ)) :
    (destTriple0 f [] ((u, v, n) :: ts)).headD none = some u := by
  rw [show destTriple0 f [] ((u, v, n) :: ts)
      = destTriple0 f ([some u] ++ List.replicate n (none : Option ℕ) ++ [some v])
        ts from rfl]
  rw [hdDestTriple0 ts f _ (by simp)]
  simp

/-! ## §A `minimalFace_core`（reduction3.hl:1179） -/

theorem minimalFaceCore (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hir : (hypermapOfList L hL).IsRestricted)
    (N : List (List Dart)) (r : List Dart) (x : Dart)
    (g : Graph) (hmq : matchQuotientList g L N)
    (hm : markedList L hL N r x)
    (hng : g.final = false)
    (f : Face) (v : ℕ)
    (hf : minimalFace (nonFinals g) = f) (hv : v = minimalVertex g f)
    (hlc : loopChoice2 g L N = (r, x)) :
    core L r = f.vertices := by
  -- marked 分解
  obtain ⟨_hmres, hmn, hrN, hxr, hmqd, _hnext, _hfin, _hflag, _hsflag⟩ := hm
  dsimp only at hmqd
  -- loopChoice2 展开（保留原式供 loopChoiceProps）
  have hlc0 := hlc
  simp only [loopChoice2] at hlc
  rw [hf, ← hv] at hlc
  have hr : r = findList N (prevEl f.vertices v, v) := by
    simpa using congrArg Prod.fst hlc.symm
  have hx : x = (findList (parts L r) (prevEl f.vertices v, v)).getLastD (0, 0) := by
    have h2 : x = (findList (parts L (findList N (prevEl f.vertices v, v)))
        (prevEl f.vertices v, v)).getLastD (0, 0) := by
      simpa using congrArg Prod.snd hlc.symm
    rwa [← hr] at h2
  -- 结构事实
  have hne : nonFinals g ≠ [] := by
    intro h
    have hg : g.final = true := by simp [Graph.final, h]
    rw [hg] at hng
    exact Bool.noConfusion hng
  have hf_q : f.vertices ∈ quotientList L N := by
    rw [← hmq.2]
    have h2 := minimalFaceVerticesMemFgraph (g := g) hne
    rw [hf] at h2
    exact h2
  have hcore_q : core L r ∈ quotientList L N := by
    rw [Kepler.Text.MoreLemma2Island1.quotientListCore]
    exact List.mem_map.mpr ⟨r, hrN, rfl⟩
  have hnS : Kepler.Text.TameSpine.NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hmn
  have hunL : ∀ l ∈ L, l.Nodup :=
    (Kepler.Text.TameSpine.simpleHypermapUniq L hL hgn).mp hir.simple
  have hgq : GoodList (Kepler.Text.TameSpine.quotientListSpine L N) :=
    Kepler.Text.TameSpine.goodListQuotient L hL hnS hir.edgeNondegenerate hunL
  have hgq' : GoodList (quotientList L N) := by
    rw [Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine]
    exact hgq
  have hnun : ((quotientList L N).map listPairs).flatten.Nodup := hgq'.1
  -- loopChoiceProps：x = (prevEl f.vertices v, v)，f.vertices 成员
  obtain ⟨_, _, _, hxd⟩ :=
    loopChoiceProps L hL hgn hir N hmn g hng
      hmqd.1 hmq r x f v hf hv.symm hlc0
  have hx_d : x = (prevEl f.vertices v, v) := hxd.symm
  -- x ∈ listPairs f.vertices
  have hfvnd : f.vertices.Nodup := hmqd.1 f.vertices hf_q
  have hfvne : f.vertices ≠ [] := by
    rw [← hf]
    exact minimalFaceNonnil L hL hgn hir N hmn g hmq hng
  have hwmem : v ∈ f.vertices := by
    have := Kepler.Text.TameSpine.memMinimalVertex g f hfvne
    rwa [← hv] at this
  have hx_f : x ∈ listPairs f.vertices := by
    rw [hx_d]
    exact prevElListPairsEq hfvnd hwmem
  -- x ∈ listPairs (core L r)
  have hrnd : r.Nodup := by
    have := Kepler.Text.TameSpine.normalListUniqNonnil hnS hrN
    exact this.1
  have hrne : r ≠ [] := (Kepler.Text.TameSpine.normalListUniqNonnil hnS hrN).2
  have hd_r : (prevEl f.vertices v, v) ∈ r := by
    have hxr' : x ∈ r := hxr
    rwa [hx_d] at hxr'
  have hd_flat : (prevEl f.vertices v, v) ∈ (parts L r).flatten := by
    rw [Kepler.Text.MoreLemma2Island2.partsFlatten L hrnd hrne]
    exact hd_r
  have hp0N : findList (parts L r) (prevEl f.vertices v, v) ∈ parts L r := by
    rw [Kepler.Text.ChainBridge.findList_eq_findListSpine]
    exact Kepler.Text.TameSpine.findListSpineMemN hd_flat
  have hp0ne : findList (parts L r) (prevEl f.vertices v, v) ≠ [] :=
    Kepler.Text.MoreLemma2Island2.partsAllNonnil L r _ hp0N
  have hlast : x = (findList (parts L r) (prevEl f.vertices v, v)).getLast! := by
    rw [hx, ← Kepler.Text.ChainBridge.getLast!_eq_getLastD]
  have hx_core : x ∈ listPairs (core L r) := by
    have hlc' := Kepler.Text.TameSpine.listPairsCore L hL hnS
      hir.edgeNondegenerate hunL (r := r) hrN
    rw [← coreEqCoreSpine, ← Kepler.Text.ChainBridge.parts_eq_partsSpine L r] at hlc'
    rw [hlc']
    exact List.mem_map.mpr ⟨_, hp0N, hlast.symm⟩
  -- findListUniq 双向
  have hfq' : listPairs f.vertices ∈ (quotientList L N).map listPairs :=
    List.mem_map.mpr ⟨f.vertices, hf_q, rfl⟩
  have hcq' : listPairs (core L r) ∈ (quotientList L N).map listPairs :=
    List.mem_map.mpr ⟨core L r, hcore_q, rfl⟩
  have hfind1 : findList ((quotientList L N).map listPairs) x
      = listPairs f.vertices := by
    rw [Kepler.Text.ChainBridge.findList_eq_findListSpine]
    exact Kepler.Text.TameSpine.findListUniq hnun hx_f hfq'
  have hfind2 : findList ((quotientList L N).map listPairs) x
      = listPairs (core L r) := by
    rw [Kepler.Text.ChainBridge.findList_eq_findListSpine]
    exact Kepler.Text.TameSpine.findListUniq hnun hx_core hcq'
  exact (listPairsInj (hfind1.symm.trans hfind2)).symm


/-! ## §B `hd_vs_some_v`（reduction3.hl:998）

`destTripleFull` 展开后按 `initialSeg` 分情形：
- `v ≠ u`（u = 首三元首分量）：`initialSeg = some v :: …` 非空 ⇒
  `headD = some v`；
- `v = u`：`initialSeg = []`，`uvns ≠ []`（`h0` 槽 + `coreTripleV4_length`）
  ⇒ `destTriple0 f [] uvns` 以 `some u` 开头 ⇒ `headD = some u = some v`。 -/

/-- `destTriple0` 在空 sofar/非空 uvns 下以首三元首分量开头（一般形）。 -/
private theorem destTriple0_nil_head' (f : List ℕ) :
    ∀ {uvns : List (ℕ × ℕ × ℕ)}, uvns ≠ [] →
      (destTriple0 f [] uvns).headD none = some (uvns.headD (0, 0, 0)).1
  | [], h => absurd rfl h
  | (u, v, n) :: ts, _ => destTriple0_nil_head f u v n ts

/-- HOL `hd_vs_some_v`（reduction3.hl:998）。`h0 : transformCount ≠ 0`
槽（批 E 后由 T2 `transformCountNon0` 供给，本文件零 J2 依赖）。 -/
theorem hdVsSomeV (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) (g : Graph) (f : Face) (v : ℕ)
    (uvns : List (ℕ × ℕ × ℕ)) (vs : List (Option ℕ))
    (h0 : transformCount L N r x ≠ 0)
    (huvns : uvns = coreTripleV4 L N r x)
    (hvs : vs = destTripleFull f.vertices v uvns) :
    vs.headD none = some v := by
  have hne : uvns ≠ [] := by
    rw [huvns]
    intro h
    apply h0
    have hlen := coreTripleV4_length L N r x
    rw [h] at hlen
    simpa using hlen.symm
  have hdest_ne : destTriple0 f.vertices [] uvns ≠ [] :=
    destTriple0Nonnil uvns f.vertices [] (Or.inl hne)
  rw [hvs]
  simp only [destTripleFull]
  by_cases hcase : v = (uvns.headD (0, 0, 0)).1
  · simp only [if_pos hcase, List.nil_append]
    rw [headD_append, if_neg hdest_ne]
    rw [destTriple0_nil_head' f.vertices hne, hcase]
  · simp only [if_neg hcase]
    rw [headD_append]
    have h1 : ((some v :: (between f.vertices v (uvns.headD (0, 0, 0)).1).map some)
        ++ destTriple0 f.vertices [] uvns) ≠ ([] : List (Option ℕ)) := by
      intro h
      exact absurd (List.append_eq_nil_iff.mp h).1 (List.cons_ne_nil _ _)
    rw [if_neg h1]
    rw [headD_append, if_neg (List.cons_ne_nil _ _)]
    rfl

/-! ## §C `last_vs_some_prev`（reduction3.hl:1067）

按 `finalSeg` 分情形：
- 非空：`LAST vs = LAST finalSeg = some (prevEl f.vertices v)`；
- 空（`v' = u0`）：`LAST vs = LAST (dest ++ []) = some v' = some u0`。 -/

/-- HOL `last_vs_some_prev`（reduction3.hl:1067）。`h0` 槽同 §B。 -/
theorem lastVsSomePrev (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) (g : Graph) (f : Face) (v : ℕ)
    (uvns : List (ℕ × ℕ × ℕ)) (vs : List (Option ℕ))
    (h0 : transformCount L N r x ≠ 0)
    (huvns : uvns = coreTripleV4 L N r x)
    (hvs : vs = destTripleFull f.vertices v uvns) :
    vs.getLastD none = some (prevEl f.vertices v) := by
  have hne : uvns ≠ [] := by
    rw [huvns]
    intro h
    apply h0
    have hlen := coreTripleV4_length L N r x
    rw [h] at hlen
    simpa using hlen.symm
  rw [hvs]
  simp only [destTripleFull]
  by_cases hcase : (uvns.getLastD (0, 0, 0)).2.1 = prevEl f.vertices v
  · -- finalSeg = []：LAST vs = LAST dest
    simp only [if_pos hcase, List.append_nil]
    rw [getLastD_append_of_ne none _ (destTriple0Nonnil uvns f.vertices [] (Or.inl hne))]
    rw [lastDestTriple0D hne f.vertices []]
    rw [hcase]
  · -- finalSeg 非空：LAST vs = LAST finalSeg = some u0
    simp only [if_neg hcase]
    rw [getLastD_append_of_ne none _
      (by
        show (between f.vertices (uvns.getLastD (0, 0, 0)).2.1 (prevEl f.vertices v)).map some
            ++ [some (prevEl f.vertices v)] ≠ []
        exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))]
    rw [List.getLastD_concat]

end Kepler.Text.Reduction3


-- 探针（编译即执行）
#print axioms Kepler.Text.Reduction3.minimalFaceCore
#print axioms Kepler.Text.Reduction3.hdVsSomeV
#print axioms Kepler.Text.Reduction3.lastVsSomePrev
