/-
  Kepler.Text.Reduction5J5UvnsChainCl — U1b：走行分类三件套（U 段第二小波）。
  `ChainCl f D l`（相邻 Some 项 ⇒ `nextEl f` 相邻 ∨ `D a b`）+ 三段保持引理。
  消费 nb56 getD 五件；`sizeBetwnChainPub` 私落（`Thm6C:55` 同名件 private）。

  纪律：零公理、零占位证明；私有重落（不改既有文件）。
-/

import Kepler.Text.Reduction5J5UvnsGetD
import Kepler.Text.Reduction5BetwnBase
import Kepler.Text.Reduction3Thm6B
import Kepler.Text.Reduction5J5Pnxvwfs
import Kepler.Text.Reduction4Subseg4
import Kepler.Text.Reduction5J5Termination
import Kepler.Text.TameSpine.Reduction3NcvibwuSpineB2d
import Kepler.Text.TameSpine.JcajyduRed2Tav2
import Kepler.Text.TameSpine.JcajyduAqLeaf10
import Kepler.Text.Reduction5J5FstNe

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts listOfDarts listPairs)
open Kepler.Graphs (fgraph between)

/-- 走行分类谓词（相邻 Some 项 `nextEl f` 相邻，或落入分类谓词 `D`）。 -/
def ChainCl (f : List ℕ) (D : ℕ → ℕ → Prop) (l : List (Option ℕ)) : Prop :=
  ∀ j : ℕ, j + 1 < l.length → (l.getD j none).isSome → (l.getD (j + 1) none).isSome →
    nextEl f ((l.getD j none).getD 0) = (l.getD (j + 1) none).getD 0 ∨
      D ((l.getD j none).getD 0) ((l.getD (j + 1) none).getD 0)

/-- **① 首段**：`[some y] ++ nseq n none ++ [some z]` 的 `ChainCl`
（唯一可能相邻的 Some 对是 (y,z)，且仅当 `n = 0`）。 -/
theorem chainClBase (f : List ℕ) (D : ℕ → ℕ → Prop) (y z n : ℕ)
    (hdisj : n = 0 → D y z) :
    ChainCl f D ([some y] ++ List.replicate n (none : Option ℕ) ++ [some z]) := by
  intro j hj1 hs1 hs2
  cases j with
  | zero =>
    have h2 : ((List.replicate n (none : Option ℕ) ++ [some z]).getD 0 none).isSome = true := by
      simpa using hs2
    rw [uvnsGetDRepZV] at h2
    by_cases hn : n = 0
    · right
      simpa [hn, uvnsGetDRepZV] using hdisj hn
    · exfalso
      rw [if_neg (by omega : (0 : ℕ) ≠ n)] at h2
      simp at h2
  | succ k =>
    have h1 : ((List.replicate n (none : Option ℕ) ++ [some z]).getD k none).isSome = true := by
      simpa using hs1
    have h2 : ((List.replicate n (none : Option ℕ) ++ [some z]).getD (k + 1) none).isSome = true := by
      simpa using hs2
    rw [uvnsGetDRepZV] at h1 h2
    by_cases e1 : k = n
    · by_cases e2 : k + 1 = n
      · rw [if_pos e1] at h1
        rw [if_pos e2] at h2
        omega
      · rw [if_neg e2] at h2
        simp at h2
    · rw [if_neg e1] at h1
      simp at h1

/-- **② 纯 Nones 追加**（destTriple0 步进 case `u0 = u`）：
`pfx ++ nseq n none ++ [some z]` 的 `ChainCl`；跨越对仅当 `n = 0`，由 `D w z` 收口。
`hlastD` 是「pfx 末位取值为 w」的接口（调用方由 `getLastD` 供）。 -/
theorem chainClNsAppend (f : List ℕ) (D : ℕ → ℕ → Prop)
    (pfx : List (Option ℕ)) (w zv n : ℕ)
    (hcl : ChainCl f D pfx)
    (hlastD : ∀ j, j + 1 = pfx.length → (pfx.getD j none).getD 0 = w)
    (hdisj : n = 0 → D w zv) :
    ChainCl f D (pfx ++ (List.replicate n (none : Option ℕ) ++ [some zv])) := by
  intro j hj1 hs1 hs2
  simp only [uvnsGetDAppend (l := pfx) (m := List.replicate n (none : Option ℕ) ++ [some zv]) (j := j),
    uvnsGetDAppend (l := pfx) (m := List.replicate n (none : Option ℕ) ++ [some zv]) (j := j + 1)]
    at hs1 hs2 ⊢
  by_cases hj : j + 1 < pfx.length
  · simp only [dif_pos (by omega : j < pfx.length), dif_pos hj] at hs1 hs2 ⊢
    exact hcl j hj hs1 hs2
  · by_cases hje : j + 1 = pfx.length
    · -- 跨越对：pfx 末元 w × app 首项（仅 n=0 时 = some zv）
      simp only [dif_pos (by omega : j < pfx.length), dif_neg (by omega : ¬ j + 1 < pfx.length),
        show j + 1 - pfx.length = 0 from by omega] at hs1 hs2 ⊢
      have hw : (pfx.getD j none).getD 0 = w := hlastD j hje
      simp only [uvnsGetDRepZV] at hs2
      by_cases hn : n = 0
      · right
        rw [hw]
        have hb : ((List.replicate n (none : Option ℕ) ++ [some zv]).getD 0 none).getD 0 = zv := by
          rw [uvnsGetDRepZV, if_pos hn.symm]
          rfl
        rw [hb]
        exact hdisj hn
      · exfalso
        simp only [if_neg (by omega : (0 : ℕ) ≠ n)] at hs2
        simp at hs2
    · -- j ≥ pfx.length：两元都在 app 的 nseq 段
      simp only [dif_neg (by omega : ¬ j < pfx.length), dif_neg (by omega : ¬ j + 1 < pfx.length)] at hs1 hs2 ⊢
      simp only [uvnsGetDRepZV] at hs1 hs2
      by_cases e1 : j - pfx.length = n
      · simp only [if_pos e1] at hs1
        by_cases e2 : j + 1 - pfx.length = n
        · simp only [if_pos e2] at hs2
          omega
        · simp only [if_neg e2] at hs2
          simp at hs2
      · simp only [if_neg e1] at hs1
        simp at hs1


/-- `|between| = indexf - 1`（私有重落；`Thm6C:55` 同名件为 private）。 -/
theorem sizeBetwnChainPub {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    {s : List α} {x y : α} (hnd : s.Nodup) (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
    (between s x y).length = (Kepler.Text.TameSpine.indexf x y s) - 1 := by
  rw [Kepler.Text.TameSpine.sizeBetwn hnd hx hy hne]

/-- `(r.map some ++ rest).getD t`（`t` 界内）= `some (r.getD t 0)`。 -/
theorem uvnsGetDMapSomeApp {r : List ℕ} (rest : List (Option ℕ)) {t : ℕ}
    (ht : t < r.length) :
    (r.map some ++ rest).getD t none = some (r.getD t 0) := by
  rw [uvnsGetDAppend (l := r.map some) (m := rest) (j := t)]
  rw [dif_pos (by simpa using ht)]
  exact uvnsGetDMapSome ht

/-- `(r.map some ++ rest).getD (|r| + m) = rest.getD m`。 -/
theorem uvnsGetDMapAdd {r : List ℕ} (rest : List (Option ℕ)) (m : ℕ) :
    (r.map some ++ rest).getD (r.length + m) none = rest.getD m none := by
  rw [uvnsGetDAppend (l := r.map some) (m := rest) (j := r.length + m)]
  rw [dif_neg (by simp)]
  rw [List.length_map]
  rw [show r.length + m - r.length = m from by omega]

/-- **③ 带首 Some 的追加**（destTriple0 步进 case `nextEl u0 = u` 与弧支）：
`pfx ++ r.map some ++ [some u] ++ nseq n none ++ [some z]` 的 `ChainCl`。
三 junction 由调用方供：`r=[]` 时 `w→u`（`hfirst`）、`r≠[]` 时 `w→r 首`
（`hfirstR`）、`r 末→u`（`hlastR`）；`r` 内部相邻由 `hchain`；`u→z` 仅当
`n = 0`（`hdisj`）。 -/
theorem chainClSomeAppend (f : List ℕ) (D : ℕ → ℕ → Prop)
    (pfx : List (Option ℕ)) (w : ℕ) (r : List ℕ) (u zv n : ℕ)
    (hcl : ChainCl f D pfx)
    (hlastD : ∀ j, j + 1 = pfx.length → (pfx.getD j none).getD 0 = w)
    (hfirst : r = [] → nextEl f w = u ∨ D w u)
    (hfirstR : r ≠ [] → nextEl f w = r.getD 0 0)
    (hchain : ∀ j, j + 1 < r.length → nextEl f (r.getD j 0) = r.getD (j + 1) 0)
    (hlastR : r ≠ [] → nextEl f (r.getD (r.length - 1) 0) = u)
    (hdisj : n = 0 → D u zv) :
    ChainCl f D (pfx ++ (r.map some ++ [some u] ++
      List.replicate n (none : Option ℕ) ++ [some zv])) := by
  intro j hj1 hs1 hs2
  set rest : List (Option ℕ) := [some u] ++ List.replicate n (none : Option ℕ) ++ [some zv] with hrest
  have happ : r.map some ++ [some u] ++ List.replicate n (none : Option ℕ) ++ [some zv]
      = r.map some ++ rest := by
    rw [hrest]
    simp only [List.append_assoc]
  rw [happ] at hs1 hs2 ⊢
  simp only [uvnsGetDAppend (l := pfx) (m := r.map some ++ rest) (j := j),
    uvnsGetDAppend (l := pfx) (m := r.map some ++ rest) (j := j + 1)] at hs1 hs2 ⊢
  by_cases hj : j + 1 < pfx.length
  · simp only [dif_pos (by omega : j < pfx.length), dif_pos hj] at hs1 hs2 ⊢
    exact hcl j hj hs1 hs2
  · by_cases hje : j + 1 = pfx.length
    · -- 跨越：pfx 末 w × app 首项
      simp only [dif_pos (by omega : j < pfx.length), dif_neg (by omega : ¬ j + 1 < pfx.length),
        show j + 1 - pfx.length = 0 from by omega] at hs1 hs2 ⊢
      rw [hlastD j hje]
      cases r with
      | nil =>
        have h0 : ((List.map some [] ++ rest).getD 0 none).getD 0 = u := by
          simp [hrest]
        rcases hfirst rfl with h | h
        · left
          rw [h0]
          exact h
        · right
          rw [h0]
          exact h
      | cons a r'' =>
        have h0 : (((a :: r'').map some ++ rest).getD 0 none).getD 0
            = (a :: r'').getD 0 0 := by
          simp
        left
        rw [h0]
        exact hfirstR (by simp)
    · -- j ≥ pfx.length：t := j - pfx.length
      simp only [dif_neg (by omega : ¬ j < pfx.length),
        dif_neg (by omega : ¬ j + 1 < pfx.length)] at hs1 hs2 ⊢
      set t : ℕ := j - pfx.length with htdef
      simp only [show j + 1 - pfx.length = t + 1 from by omega] at hs2 ⊢
      by_cases ht0 : t < r.length
      · -- t 落在 r.map some 内
        simp only [uvnsGetDMapSomeApp (rest := rest) (t := t) ht0] at hs1 hs2 ⊢
        have hrne : r ≠ [] := by
          intro h
          rw [h] at ht0
          simp at ht0
        by_cases ht1 : t + 1 < r.length
        · simp only [uvnsGetDMapSomeApp (rest := rest) (t := t + 1) ht1] at hs2 ⊢
          left
          exact hchain t ht1
        · -- t 是 r 的末位：次元 = rest 首项 u
          have hte : t + 1 = r.length := by omega
          rw [show t + 1 = r.length + 0 from by omega] at hs2 ⊢
          simp only [uvnsGetDMapAdd (rest := rest) (m := 0)] at hs2 ⊢
          have hrest0 : rest.getD 0 none = some u := by
            simp [hrest]
          simp only [hrest0] at hs2 ⊢
          left
          rw [show t = r.length - 1 from by omega]
          exact hlastR hrne
      · -- t ≥ r.length
        by_cases htr : t = r.length
        · -- 首 = u（rest 首项）
          simp only [show t = r.length + 0 from by omega] at hs1 ⊢
          simp only [uvnsGetDMapAdd (rest := rest) (m := 0)] at hs1 ⊢
          have hrest0 : rest.getD 0 none = some u := by
            simp [hrest]
          simp only [hrest0] at hs1 ⊢
          simp only [show t + 1 = r.length + 1 from by omega] at hs2 ⊢
          simp only [uvnsGetDMapAdd (rest := rest) (m := 1)] at hs2 ⊢
          have hrest1 : rest.getD 1 none
              = (List.replicate n (none : Option ℕ) ++ [some zv]).getD 0 none := by
            simp [hrest]
          simp only [hrest1] at hs2 ⊢
          simp only [uvnsGetDRepZV] at hs2 ⊢
          by_cases hn : n = 0
          · right
            rw [if_pos hn.symm]
            exact hdisj hn
          · exfalso
            simp only [if_neg (by omega : (0 : ℕ) ≠ n)] at hs2
            simp at hs2
        · -- t > r.length：首在 rest 的 nseq 段（`> [some u]`），次元同段——isSome 互斥
          have hlt : r.length < t := by omega
          have ht_split : t = r.length + (t - r.length) := by omega
          rw [ht_split] at hs1
          rw [ht_split]
          simp only [uvnsGetDMapAdd (rest := rest) (m := t - r.length)] at hs1 ⊢
          have ht_split' : t + 1 = r.length + (t + 1 - r.length) := by omega
          rw [ht_split'] at hs2
          simp only [show r.length + (t - r.length) + 1 = r.length + (t + 1 - r.length) from by omega] at ⊢
          simp only [uvnsGetDMapAdd (rest := rest) (m := t + 1 - r.length)] at hs2 ⊢
          simp only [hrest] at hs1 hs2
          simp only [uvnsGetDHeadRepCons] at hs1 hs2
          simp only [if_neg (by omega : t - r.length ≠ 0)] at hs1
          simp only [uvnsGetDRepZV] at hs1
          have hk1 : t + 1 - r.length ≠ 0 := by omega
          simp only [if_neg hk1] at hs2
          simp only [show t + 1 - r.length - 1 = t - r.length from by omega] at hs2
          simp only [uvnsGetDRepZV] at hs2
          by_cases e1 : t - r.length - 1 = n
          · simp only [if_pos e1] at hs1
            by_cases e2 : t - r.length = n
            · simp only [if_pos e2] at hs2
              omega
            · simp only [if_neg e2] at hs2
              simp at hs2
          · simp only [if_neg e1] at hs1
            simp at hs1

/-! ## §3 U1c 前置：last/getLastD 桥（私有重落） -/

/-- `l.getD (|l|-1) = l.getLastD`。 -/
theorem uvnsGetDLastD {l : List (Option ℕ)} (hne : l ≠ []) :
    l.getD (l.length - 1) none = l.getLastD none := by
  have h1 : l.getLastD none = l.getLast hne := by
    induction l with
    | nil => exact absurd rfl hne
    | cons a t ih =>
      cases t with
      | nil => rfl
      | cons b t => simpa using ih (by simp)
  rw [h1]
  have hlt : l.length - 1 < l.length := by
    cases l with
    | nil => exact absurd rfl hne
    | cons a t => simp
  rw [Kepler.Text.TameLp.getD_eq_getElem_of_lt hlt (none : Option ℕ),
    List.getLast_eq_getElem]

/-- `l.getLastD = l.getLast`（非空时）。 -/
theorem uvnsGetLastDEqGetLast {l : List (Option ℕ)} (hne : l ≠ []) :
    l.getLastD none = l.getLast hne := by
  induction l with
  | nil => exact absurd rfl hne
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b t => simpa using ih (by simp)

/-- `l = l.dropLast ++ [last]`（`getLast` 形式）。 -/
theorem uvnsEqDropLastAppend {α : Type} {l : List α} {a : α}
    (hne : l ≠ []) (h : l.getLast hne = a) : l = l.dropLast ++ [a] := by
  rw [← h, List.dropLast_append_getLast hne]

/-! ## §4 U1c 主线：mid 段前缀归纳（`sizeVs` 骨架改 Cl+last 不变量） -/

/-- UVNS 分类谓词（每段 `(y_t, z_t)` 且 `betwn (find_face) y_t z_t = []`）。 -/
def UvnsD (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart) (k : ℕ) :
    ℕ → ℕ → Prop :=
  fun a b => ∃ t, t < k ∧ a = (ytrans L N r x t).1 ∧ b = (ztrans L N r x t).1 ∧
    (between (findFaceDarts L x) (ytrans L N r x t) (ztrans L N r x t)).length = 0


/-! ## §4 U1c 主线：mid 段前缀归纳（`sizeVs` 骨架改 Cl+last 不变量） -/

/-- **mid 段前缀归纳**：`destTriple0 f [] (uvns.take (i+1))` 的 `ChainCl` +
末元 = `z_i`。base = 单段 `chainClBase`；succ = `destTriple0Cat2` 拆段 +
`destTriple0` 步进三分支（三支各取独立分支等式 + 显式桥）。 -/
theorem chainClMid
    (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r) (hk : transformCount L N r x = k) :
    ∀ i, i + 1 ≤ k →
      ChainCl (core L r) (UvnsD L N r x k)
        (Kepler.Text.Reduction3.destTriple0 (core L r) []
          ((Kepler.Text.Reduction3.coreTripleV4 L N r x).take (i + 1))) ∧
      (Kepler.Text.Reduction3.destTriple0 (core L r) []
          ((Kepler.Text.Reduction3.coreTripleV4 L N r x).take (i + 1))).getLastD none
        = some (ztrans L N r x i).1 := by
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' j => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' j
  have hk0 : 0 < k := by
    have h := Kepler.Text.Reduction5.transformCountNon0OfMarked L hL hgn haq hm hnf
    rw [hk] at h
    exact Nat.pos_of_ne_zero h
  have hnf_i : ∀ i, i < k → ¬ finalList L (rtrans L N r x i) := fun i hi =>
    Kepler.Text.Reduction4.transformCount_not i (by rw [hk]; exact hi)
  have hcoreof : ∀ u ∈ r, u.1 ∈ core L r :=
    Kepler.Text.Reduction4Idx.finalAssumptionMemFstCore L hL hm
  have hym : ∀ i, i < k → (ytrans L N r x i).1 ∈ core L r := fun i hi =>
    hcoreof _ (pnxvwfs1 L hL hgn haq i (hnf_i i hi) hm)
  have hzm : ∀ i, i < k → (ztrans L N r x i).1 ∈ core L r := fun i hi =>
    hcoreof _ (pnxvwfs2 L hL hgn haq i (hnf_i i hi) hm)
  have hrnd : (core L r).Nodup := Kepler.Text.Reduction4Idx.markedListUniqCore L hL hm
  have hlen0 : (Kepler.Text.Reduction3.coreTripleV4 L N r x).length = k := by
    rw [Kepler.Text.Reduction3.coreTripleV4_length]
    exact hk
  have hget : ∀ i (hi : i < k),
      (Kepler.Text.Reduction3.coreTripleV4 L N r x)[i]'(by rw [hlen0]; exact hi) =
        ((ytrans L N r x i).1, (ztrans L N r x i).1,
          (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length) := by
    intro i hi
    exact Kepler.Text.Reduction3.elCoreTriple L N r x i (by rw [hk]; exact hi)
  set uvns := Kepler.Text.Reduction3.coreTripleV4 L N r x with huv
  have hlen : uvns.length = k := hlen0
  intro i
  induction i with
  | zero =>
    intro h1k
    have h0len : 0 < uvns.length := by rw [hlen]; exact hk0
    have htake1 : uvns.take 1 = [uvns[0]'h0len] := uvnsGetDTakeOne uvns h0len
    rw [htake1]
    have hg0 : uvns[0]'h0len =
        ((ytrans L N r x 0).1, (ztrans L N r x 0).1,
          (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0)).length) :=
      hget 0 hk0
    rw [hg0]
    rw [show Kepler.Text.Reduction3.destTriple0 (core L r) []
          [((ytrans L N r x 0).1, (ztrans L N r x 0).1,
            (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0)).length)]
        = Kepler.Text.Reduction3.destTriple0 (core L r)
          ([some (ytrans L N r x 0).1] ++
            List.replicate (between (findFaceDarts L x) (ytrans L N r x 0)
              (ztrans L N r x 0)).length (none : Option ℕ) ++
            [some (ztrans L N r x 0).1]) [] from rfl]
    rw [Kepler.Text.Reduction3.destTriple0Nil]
    refine ⟨chainClBase _ _ _ _ _ ?_, ?_⟩
    · intro hn
      exact ⟨0, hk0, rfl, rfl, hn⟩
    · rw [List.getLastD_concat]
  | succ i ih =>
    intro hik
    have hi1 : i + 1 ≤ k := by omega
    have hi1lt : i + 1 < k := by omega
    have hilt : i < k := by omega
    obtain ⟨hCl, hlast⟩ := ih hi1
    have hgeti : uvns[i + 1]'(by rw [hlen]; exact hi1lt) =
        ((ytrans L N r x (i + 1)).1, (ztrans L N r x (i + 1)).1,
          (between (findFaceDarts L x) (ytrans L N r x (i + 1))
            (ztrans L N r x (i + 1))).length) := hget (i + 1) hi1lt
    have htake : uvns.take (i + 1 + 1)
        = uvns.take (i + 1) ++ [uvns[i + 1]'(by rw [hlen]; exact hi1lt)] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by rw [hlen]; exact hi1lt)]
      rfl
    have ha_ne : uvns.take (i + 1) ≠ [] := by
      intro h
      have hc := congrArg List.length h
      rw [List.length_take, hlen, Nat.min_eq_left hi1] at hc
      simp at hc
    have hL1ne : Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (i + 1)) ≠ [] := by
      intro h
      rw [h] at hlast
      simp at hlast
    have hlast' : (Kepler.Text.Reduction3.destTriple0 (core L r) []
        (uvns.take (i + 1))).getLast hL1ne = some (ztrans L N r x i).1 := by
      rw [← uvnsGetLastDEqGetLast hL1ne]
      exact hlast
    have hL1eq : Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (i + 1))
        = (Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (i + 1))).dropLast
          ++ [some (ztrans L N r x i).1] :=
      uvnsEqDropLastAppend hL1ne hlast'
    have hcat2 : Kepler.Text.Reduction3.destTriple0 (core L r) []
          (uvns.take (i + 1) ++ [uvns[i + 1]'(by rw [hlen]; exact hi1lt)])
        = (Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (i + 1))).dropLast
          ++ Kepler.Text.Reduction3.destTriple0 (core L r) [some (ztrans L N r x i).1]
            [uvns[i + 1]'(by rw [hlen]; exact hi1lt)] :=
      Kepler.Text.Reduction3.destTriple0Cat2 (core L r) [] (uvns.take (i + 1))
        [uvns[i + 1]'(by rw [hlen]; exact hi1lt)]
        (Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (i + 1))).dropLast
        (ztrans L N r x i).1 ha_ne (fun h => absurd rfl h) hL1eq
    rw [htake, hcat2, hgeti]
    by_cases h1 : (ztrans L N r x i).1 = (ytrans L N r x (i + 1)).1
    · -- 分支 1（`u0 = u`）：追加 `nseq ++ [some z_{i+1}]`
      have hpc : Kepler.Text.Reduction3.destTriple0 (core L r) [some (ztrans L N r x i).1]
          [((ytrans L N r x (i + 1)).1, (ztrans L N r x (i + 1)).1,
            (between (findFaceDarts L x) (ytrans L N r x (i + 1))
              (ztrans L N r x (i + 1))).length)]
          = [some (ztrans L N r x i).1] ++
            (List.replicate (between (findFaceDarts L x) (ytrans L N r x (i + 1))
              (ztrans L N r x (i + 1))).length (none : Option ℕ)
              ++ [some (ztrans L N r x (i + 1)).1]) := by
        simp only [Kepler.Text.Reduction3.destTriple0]
        rw [if_neg (by simp : ¬ ([some (ztrans L N r x i).1] : List (Option ℕ)) = [])]
        rw [show ([some (ztrans L N r x i).1] : List (Option ℕ)).getLastD none
            = some (ztrans L N r x i).1 from rfl]
        simp only [Option.getD_some, if_pos h1]
        rfl
      refine ⟨?_, ?_⟩
      · have hbridge : (Kepler.Text.Reduction3.destTriple0 (core L r) []
            (uvns.take (i + 1))).dropLast
            ++ ([some (ztrans L N r x i).1] ++
              (List.replicate (between (findFaceDarts L x) (ytrans L N r x (i + 1))
                (ztrans L N r x (i + 1))).length (none : Option ℕ)
                ++ [some (ztrans L N r x (i + 1)).1]))
            = Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (i + 1))
              ++ (List.replicate (between (findFaceDarts L x) (ytrans L N r x (i + 1))
                (ztrans L N r x (i + 1))).length (none : Option ℕ)
                ++ [some (ztrans L N r x (i + 1)).1]) := by
          rw [← List.append_assoc, ← hL1eq]
        rw [hpc, hbridge]
        exact chainClNsAppend (core L r) (UvnsD L N r x k)
          (Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (i + 1)))
          (ztrans L N r x i).1 (ztrans L N r x (i + 1)).1
          (between (findFaceDarts L x) (ytrans L N r x (i + 1))
            (ztrans L N r x (i + 1))).length hCl
          (fun j hj => by
            have hdj : (Kepler.Text.Reduction3.destTriple0 (core L r) []
                (uvns.take (i + 1))).getD j none = some (ztrans L N r x i).1 := by
              rw [show j = (Kepler.Text.Reduction3.destTriple0 (core L r) []
                (uvns.take (i + 1))).length - 1 from by omega, uvnsGetDLastD hL1ne]
              exact hlast
            rw [hdj]
            rfl)
          (fun hn => ⟨i + 1, hi1lt, h1, rfl, hn⟩)
      · have hbridge2 : ((Kepler.Text.Reduction3.destTriple0 (core L r) []
            (uvns.take (i + 1))).dropLast
            ++ ([some (ztrans L N r x i).1] ++
              (List.replicate (between (findFaceDarts L x) (ytrans L N r x (i + 1))
                (ztrans L N r x (i + 1))).length (none : Option ℕ)
                ++ [some (ztrans L N r x (i + 1)).1]))).getLastD none
            = some (ztrans L N r x (i + 1)).1 := by
          rw [← List.append_assoc, ← hL1eq, ← List.append_assoc, List.getLastD_concat]
        rw [hpc]
        exact hbridge2
    · by_cases h2 : nextEl (core L r) (ztrans L N r x i).1 = (ytrans L N r x (i + 1)).1
      · -- 分支 2（`nextEl u0 = u`）：追加 `[some y_{i+1}] ++ nseq ++ [some z_{i+1}]`
        have hpc2 : Kepler.Text.Reduction3.destTriple0 (core L r) [some (ztrans L N r x i).1]
            [((ytrans L N r x (i + 1)).1, (ztrans L N r x (i + 1)).1,
              (between (findFaceDarts L x) (ytrans L N r x (i + 1))
                (ztrans L N r x (i + 1))).length)]
            = [some (ztrans L N r x i).1] ++
              ([some (ytrans L N r x (i + 1)).1] ++
                (List.replicate (between (findFaceDarts L x) (ytrans L N r x (i + 1))
                  (ztrans L N r x (i + 1))).length (none : Option ℕ)
                  ++ [some (ztrans L N r x (i + 1)).1])) := by
          simp only [Kepler.Text.Reduction3.destTriple0]
          rw [if_neg (by simp : ¬ ([some (ztrans L N r x i).1] : List (Option ℕ)) = [])]
          rw [show ([some (ztrans L N r x i).1] : List (Option ℕ)).getLastD none
              = some (ztrans L N r x i).1 from rfl]
          simp only [Option.getD_some, if_neg h1, if_pos h2]
          rfl
        refine ⟨?_, ?_⟩
        · have hbridge : (Kepler.Text.Reduction3.destTriple0 (core L r) []
              (uvns.take (i + 1))).dropLast
              ++ ([some (ztrans L N r x i).1] ++
                ([some (ytrans L N r x (i + 1)).1] ++
                  (List.replicate (between (findFaceDarts L x) (ytrans L N r x (i + 1))
                    (ztrans L N r x (i + 1))).length (none : Option ℕ)
                    ++ [some (ztrans L N r x (i + 1)).1])))
              = Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (i + 1))
                ++ ([some (ytrans L N r x (i + 1)).1] ++
                  (List.replicate (between (findFaceDarts L x) (ytrans L N r x (i + 1))
                    (ztrans L N r x (i + 1))).length (none : Option ℕ)
                    ++ [some (ztrans L N r x (i + 1)).1])) := by
            rw [← List.append_assoc, ← hL1eq]
          rw [hpc2, hbridge]
          refine chainClSomeAppend (core L r) (UvnsD L N r x k)
            (Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (i + 1)))
            (ztrans L N r x i).1 [] (ytrans L N r x (i + 1)).1
            (ztrans L N r x (i + 1)).1
            (between (findFaceDarts L x) (ytrans L N r x (i + 1))
              (ztrans L N r x (i + 1))).length hCl ?_ ?_ ?_ ?_ ?_ ?_
          · intro j hj
            have hdj : (Kepler.Text.Reduction3.destTriple0 (core L r) []
                (uvns.take (i + 1))).getD j none = some (ztrans L N r x i).1 := by
              rw [show j = (Kepler.Text.Reduction3.destTriple0 (core L r) []
                (uvns.take (i + 1))).length - 1 from by omega, uvnsGetDLastD hL1ne]
              exact hlast
            rw [hdj]
            rfl
          · intro _
            exact Or.inl h2
          · intro hr
            exact absurd rfl hr
          · intro j hj
            simp at hj
          · intro hr
            exact absurd rfl hr
          · intro hn
            exact ⟨i + 1, hi1lt, rfl, rfl, hn⟩
        · have hbridge2 : ((Kepler.Text.Reduction3.destTriple0 (core L r) []
              (uvns.take (i + 1))).dropLast
              ++ ([some (ztrans L N r x i).1] ++
                ([some (ytrans L N r x (i + 1)).1] ++
                  (List.replicate (between (findFaceDarts L x) (ytrans L N r x (i + 1))
                    (ztrans L N r x (i + 1))).length (none : Option ℕ)
                    ++ [some (ztrans L N r x (i + 1)).1])))).getLastD none
              = some (ztrans L N r x (i + 1)).1 := by
            rw [← List.append_assoc, ← hL1eq, ← List.append_assoc, ← List.append_assoc,
              List.getLastD_concat]
          rw [hpc2]
          exact hbridge2
      · -- 分支 3（else）：追加 `arc ++ [some y_{i+1}] ++ nseq ++ [some z_{i+1}]`
        have hne : (ztrans L N r x i).1 ≠ (ytrans L N r x (i + 1)).1 := h1
        have hpc3 : Kepler.Text.Reduction3.destTriple0 (core L r) [some (ztrans L N r x i).1]
            [((ytrans L N r x (i + 1)).1, (ztrans L N r x (i + 1)).1,
              (between (findFaceDarts L x) (ytrans L N r x (i + 1))
                (ztrans L N r x (i + 1))).length)]
            = [some (ztrans L N r x i).1] ++
              ((between (core L r) (ztrans L N r x i).1
                  (ytrans L N r x (i + 1)).1).map some
                ++ ([some (ytrans L N r x (i + 1)).1] ++
                  (List.replicate (between (findFaceDarts L x) (ytrans L N r x (i + 1))
                    (ztrans L N r x (i + 1))).length (none : Option ℕ)
                    ++ [some (ztrans L N r x (i + 1)).1]))) := by
          simp only [Kepler.Text.Reduction3.destTriple0]
          rw [if_neg (by simp : ¬ ([some (ztrans L N r x i).1] : List (Option ℕ)) = [])]
          rw [show ([some (ztrans L N r x i).1] : List (Option ℕ)).getLastD none
              = some (ztrans L N r x i).1 from rfl]
          simp only [Option.getD_some, if_neg h1, if_neg h2]
          simp only [List.append_assoc]
        refine ⟨?_, ?_⟩
        · have hbridge : (Kepler.Text.Reduction3.destTriple0 (core L r) []
              (uvns.take (i + 1))).dropLast
              ++ ([some (ztrans L N r x i).1] ++
                ((between (core L r) (ztrans L N r x i).1
                    (ytrans L N r x (i + 1)).1).map some
                  ++ ([some (ytrans L N r x (i + 1)).1] ++
                    (List.replicate (between (findFaceDarts L x) (ytrans L N r x (i + 1))
                      (ztrans L N r x (i + 1))).length (none : Option ℕ)
                      ++ [some (ztrans L N r x (i + 1)).1]))))
              = Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (i + 1))
                ++ ((between (core L r) (ztrans L N r x i).1
                    (ytrans L N r x (i + 1)).1).map some
                  ++ ([some (ytrans L N r x (i + 1)).1] ++
                    (List.replicate (between (findFaceDarts L x) (ytrans L N r x (i + 1))
                      (ztrans L N r x (i + 1))).length (none : Option ℕ)
                      ++ [some (ztrans L N r x (i + 1)).1]))) := by
            rw [← List.append_assoc, ← hL1eq]
          rw [hpc3, hbridge]
          rw [show Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (i + 1))
                ++ ((between (core L r) (ztrans L N r x i).1 (ytrans L N r x (i + 1)).1).map some
                  ++ ([some (ytrans L N r x (i + 1)).1] ++
                    (List.replicate (between (findFaceDarts L x) (ytrans L N r x (i + 1))
                      (ztrans L N r x (i + 1))).length (none : Option ℕ)
                      ++ [some (ztrans L N r x (i + 1)).1])))
              = Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (i + 1))
                ++ (((between (core L r) (ztrans L N r x i).1
                      (ytrans L N r x (i + 1)).1).map some
                  ++ [some (ytrans L N r x (i + 1)).1]) ++
                  List.replicate (between (findFaceDarts L x) (ytrans L N r x (i + 1))
                    (ztrans L N r x (i + 1))).length (none : Option ℕ)
                  ++ [some (ztrans L N r x (i + 1)).1]) from by
            simp only [List.append_assoc]]
          have hpos : 0 < (between (core L r) (ztrans L N r x i).1
              (ytrans L N r x (i + 1)).1).length := by
            by_contra h
            exact h2 (Kepler.Text.TameSpine.aq10_betwnEqNil
              (List.length_eq_zero_iff.mp (by omega : (between (core L r) (ztrans L N r x i).1
                (ytrans L N r x (i + 1)).1).length = 0))
              (hzm i hilt) (hym (i + 1) hi1lt) hne hrnd)
          refine chainClSomeAppend (core L r) (UvnsD L N r x k)
            (Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (i + 1)))
            (ztrans L N r x i).1
            (between (core L r) (ztrans L N r x i).1 (ytrans L N r x (i + 1)).1)
            (ytrans L N r x (i + 1)).1 (ztrans L N r x (i + 1)).1
            (between (findFaceDarts L x) (ytrans L N r x (i + 1))
              (ztrans L N r x (i + 1))).length hCl ?_ ?_ ?_ ?_ ?_ ?_
          · intro j hj
            have hdj : (Kepler.Text.Reduction3.destTriple0 (core L r) []
                (uvns.take (i + 1))).getD j none = some (ztrans L N r x i).1 := by
              rw [show j = (Kepler.Text.Reduction3.destTriple0 (core L r) []
                (uvns.take (i + 1))).length - 1 from by omega, uvnsGetDLastD hL1ne]
              exact hlast
            rw [hdj]
            rfl
          · intro hr
            exact absurd (List.length_eq_zero_iff.mpr hr) (by omega : (between (core L r)
              (ztrans L N r x i).1 (ytrans L N r x (i + 1)).1).length ≠ 0)
          · intro _
            have hd0 : (between (core L r) (ztrans L N r x i).1
                (ytrans L N r x (i + 1)).1).getD 0 0
                = nextEl (core L r) (ztrans L N r x i).1 := by
              rw [Kepler.Text.TameLp.getD_eq_getElem_of_lt hpos 0,
                Kepler.Text.TameSpine.betwnOrbit hne hrnd (hzm i hilt) (hym (i + 1) hi1lt) hpos]
              simp
            exact hd0.symm
          · intro j hj
            have hj1 : j < (between (core L r) (ztrans L N r x i).1
                (ytrans L N r x (i + 1)).1).length := by omega
            have e1 : (between (core L r) (ztrans L N r x i).1
                (ytrans L N r x (i + 1)).1).getD j 0
                = (between (core L r) (ztrans L N r x i).1
                    (ytrans L N r x (i + 1)).1)[j]'hj1 :=
              Kepler.Text.TameLp.getD_eq_getElem_of_lt hj1 0
            have e2 : (between (core L r) (ztrans L N r x i).1
                (ytrans L N r x (i + 1)).1).getD (j + 1) 0
                = (between (core L r) (ztrans L N r x i).1
                    (ytrans L N r x (i + 1)).1)[j + 1]'hj :=
              Kepler.Text.TameLp.getD_eq_getElem_of_lt hj 0
            rw [e1, e2,
              Kepler.Text.TameSpine.betwnOrbit hne hrnd (hzm i hilt) (hym (i + 1) hi1lt) hj1,
              Kepler.Text.TameSpine.betwnOrbit hne hrnd (hzm i hilt) (hym (i + 1) hi1lt) hj]
            simp only [Function.iterate_succ_apply']
          · intro hr
            have hb : (between (core L r) (ztrans L N r x i).1
                (ytrans L N r x (i + 1)).1) ≠ [] := by
              intro h
              rw [h] at hpos
              simp at hpos
            have hlastb := Kepler.Text.Reduction5.nextLastBetwn (r := core L r)
              (y := (ztrans L N r x i).1) (z := (ytrans L N r x (i + 1)).1)
              (hzm i hilt) (hym (i + 1) hi1lt) hrnd hne hb
            have e : (between (core L r) (ztrans L N r x i).1
                (ytrans L N r x (i + 1)).1).getD
                ((between (core L r) (ztrans L N r x i).1
                  (ytrans L N r x (i + 1)).1).length - 1) 0
                = (between (core L r) (ztrans L N r x i).1
                    (ytrans L N r x (i + 1)).1).getLast hb := by
              rw [Kepler.Text.TameLp.getD_eq_getElem_of_lt (by omega : (between (core L r)
                (ztrans L N r x i).1 (ytrans L N r x (i + 1)).1).length - 1
                < (between (core L r) (ztrans L N r x i).1
                  (ytrans L N r x (i + 1)).1).length) 0, List.getLast_eq_getElem]
            rw [e]
            exact hlastb
          · intro hn
            exact ⟨i + 1, hi1lt, rfl, rfl, hn⟩
        · have hbridge2 : ((Kepler.Text.Reduction3.destTriple0 (core L r) []
              (uvns.take (i + 1))).dropLast
              ++ ([some (ztrans L N r x i).1] ++
                ((between (core L r) (ztrans L N r x i).1
                    (ytrans L N r x (i + 1)).1).map some
                  ++ ([some (ytrans L N r x (i + 1)).1] ++
                    (List.replicate (between (findFaceDarts L x) (ytrans L N r x (i + 1))
                      (ztrans L N r x (i + 1))).length (none : Option ℕ)
                      ++ [some (ztrans L N r x (i + 1)).1]))))).getLastD none
              = some (ztrans L N r x (i + 1)).1 := by
            rw [← List.append_assoc, ← hL1eq]
            rw [show Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (i + 1))
                  ++ ((between (core L r) (ztrans L N r x i).1
                      (ytrans L N r x (i + 1)).1).map some
                    ++ ([some (ytrans L N r x (i + 1)).1] ++
                      (List.replicate (between (findFaceDarts L x) (ytrans L N r x (i + 1))
                        (ztrans L N r x (i + 1))).length (none : Option ℕ)
                        ++ [some (ztrans L N r x (i + 1)).1])))
                = (((Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (i + 1))
                    ++ (between (core L r) (ztrans L N r x i).1
                        (ytrans L N r x (i + 1)).1).map some) ++
                    [some (ytrans L N r x (i + 1)).1]) ++
                    List.replicate (between (findFaceDarts L x) (ytrans L N r x (i + 1))
                      (ztrans L N r x (i + 1))).length (none : Option ℕ))
                  ++ [some (ztrans L N r x (i + 1)).1] from by
              simp only [List.append_assoc]]
            rw [List.getLastD_concat]
          rw [hpc3]
          exact hbridge2

/-! ## §5 U1c 收尾 I：`MemIn` 工具 + mid 段成员归纳 -/

/-- 成员谓词：Some 项取值 ∈ S。 -/
def MemIn (S : ℕ → Prop) (l : List (Option ℕ)) : Prop :=
  ∀ j, j < l.length → (l.getD j none).isSome → S ((l.getD j none).getD 0)

/-- 单点 Some。 -/
theorem memInSingle (S : ℕ → Prop) (w : ℕ) (hw : S w) : MemIn S [some w] := by
  intro j hj hsome
  have hj0 : j = 0 := by simpa using hj
  subst hj0
  simpa using hw

/-- 首段 `[some y] ++ nseq ++ [some z]`。 -/
theorem memInBase (S : ℕ → Prop) (y z n : ℕ) (hy : S y) (hz : S z) :
    MemIn S ([some y] ++ List.replicate n (none : Option ℕ) ++ [some z]) := by
  intro j hj hsome
  rw [uvnsGetDHeadRepCons] at hsome
  by_cases h0 : j = 0
  · have hv : (([some y] ++ List.replicate n (none : Option ℕ) ++ [some z]).getD j none).getD 0 = y := by
      rw [uvnsGetDHeadRepCons, if_pos h0]
      rfl
    rw [hv]
    exact hy
  · rw [if_neg h0] at hsome
    rw [uvnsGetDRepZV] at hsome
    by_cases h1 : j - 1 = n
    · have hv : (([some y] ++ List.replicate n (none : Option ℕ) ++ [some z]).getD j none).getD 0 = z := by
        rw [uvnsGetDHeadRepCons, if_neg h0, uvnsGetDRepZV, if_pos h1]
        rfl
      rw [hv]
      exact hz
    · rw [if_neg h1] at hsome
      simp at hsome

/-- nseq 追加。 -/
theorem memInNsAppend (S : ℕ → Prop) (pfx : List (Option ℕ)) (zv n : ℕ)
    (hp : MemIn S pfx) (hz : S zv) :
    MemIn S (pfx ++ (List.replicate n (none : Option ℕ) ++ [some zv])) := by
  intro j hj hsome
  simp only [uvnsGetDAppend (l := pfx) (m := List.replicate n (none : Option ℕ) ++ [some zv]) (j := j)] at hsome
  by_cases hj' : j < pfx.length
  · simp only [dif_pos hj'] at hsome
    have hv : (pfx ++ (List.replicate n (none : Option ℕ) ++ [some zv])).getD j none
        = pfx.getD j none := by
      rw [uvnsGetDAppend, dif_pos hj']
    rw [hv]
    exact hp j hj' hsome
  · simp only [dif_neg hj'] at hsome
    rw [uvnsGetDRepZV] at hsome
    by_cases ht : j - pfx.length = n
    · have hv : ((pfx ++ (List.replicate n (none : Option ℕ) ++ [some zv])).getD j none).getD 0 = zv := by
        rw [uvnsGetDAppend, dif_neg hj', uvnsGetDRepZV, if_pos ht]
        rfl
      rw [hv]
      exact hz
    · rw [if_neg ht] at hsome
      simp at hsome

/-- 带首 Some 的追加（`r` 是任意 ℕ 链）。 -/
theorem memInSomeAppend (S : ℕ → Prop) (pfx : List (Option ℕ)) (r : List ℕ)
    (u zv n : ℕ) (hp : MemIn S pfx) (hr : ∀ t ∈ r, S t) (hu : S u) (hz : S zv) :
    MemIn S (pfx ++ (r.map some ++ [some u] ++
      List.replicate n (none : Option ℕ) ++ [some zv])) := by
  intro j hj hsome
  set rest : List (Option ℕ) := [some u] ++ List.replicate n (none : Option ℕ) ++ [some zv] with hrest
  have happ : r.map some ++ [some u] ++ List.replicate n (none : Option ℕ) ++ [some zv]
      = r.map some ++ rest := by
    rw [hrest]
    simp only [List.append_assoc]
  rw [happ] at hsome ⊢
  simp only [uvnsGetDAppend (l := pfx) (m := r.map some ++ rest) (j := j)] at hsome
  by_cases hj' : j < pfx.length
  · simp only [dif_pos hj'] at hsome
    have hv : (pfx ++ (r.map some ++ rest)).getD j none = pfx.getD j none := by
      rw [uvnsGetDAppend, dif_pos hj']
    rw [hv]
    exact hp j hj' hsome
  · simp only [dif_neg hj'] at hsome
    set t := j - pfx.length with htdef
    by_cases ht : t < r.length
    · have hv : (r.map some ++ rest).getD t none = some (r.getD t 0) :=
        uvnsGetDMapSomeApp rest ht
      have hv2 : ((pfx ++ (r.map some ++ rest)).getD j none).getD 0 = r.getD t 0 := by
        rw [uvnsGetDAppend, dif_neg hj', hv]
        rfl
      rw [hv2]
      exact hr _ (by
        rw [Kepler.Text.TameLp.getD_eq_getElem_of_lt ht 0]
        exact List.getElem_mem _)
    · by_cases ht2 : t = r.length
      · have hv : (r.map some ++ rest).getD t none = rest.getD 0 none := by
          rw [show t = r.length + 0 from by omega, uvnsGetDMapAdd]
        have hv2 : ((pfx ++ (r.map some ++ rest)).getD j none).getD 0 = u := by
          rw [uvnsGetDAppend, dif_neg hj', hv, hrest]
          simp
        rw [hv2]
        exact hu
      · have hlt : r.length < t := by omega
        have hv : (r.map some ++ rest).getD t none = rest.getD (t - r.length) none := by
          rw [← uvnsGetDMapAdd rest (t - r.length)]
          congr 1
          omega
        rw [hv] at hsome
        rw [hrest] at hsome
        rw [uvnsGetDHeadRepCons] at hsome
        by_cases hk0 : t - r.length = 0
        · rw [if_pos hk0] at hsome
          have hv2 : ((pfx ++ (r.map some ++ rest)).getD j none).getD 0 = u := by
            rw [uvnsGetDAppend, dif_neg hj', hv, hrest, uvnsGetDHeadRepCons, if_pos hk0]
            rfl
          rw [hv2]
          exact hu
        · rw [if_neg hk0] at hsome
          rw [uvnsGetDRepZV] at hsome
          by_cases hN : t - r.length - 1 = n
          · rw [if_pos hN] at hsome
            have hv2 : ((pfx ++ (r.map some ++ rest)).getD j none).getD 0 = zv := by
              rw [uvnsGetDAppend, dif_neg hj', hv, hrest, uvnsGetDHeadRepCons, if_neg hk0,
                uvnsGetDRepZV, if_pos hN]
              rfl
            rw [hv2]
            exact hz
          · rw [if_neg hN] at hsome
            simp at hsome

/-- append 成员保持。 -/
theorem memInAppend (S : ℕ → Prop) (l1 l2 : List (Option ℕ))
    (h1 : MemIn S l1) (h2 : MemIn S l2) : MemIn S (l1 ++ l2) := by
  intro j hj hsome
  simp only [List.length_append] at hj
  simp only [uvnsGetDAppend (l := l1) (m := l2) (j := j)] at hsome
  by_cases hj' : j < l1.length
  · simp only [dif_pos hj'] at hsome
    have hv : (l1 ++ l2).getD j none = l1.getD j none := by
      rw [uvnsGetDAppend, dif_pos hj']
    rw [hv]
    exact h1 j hj' hsome
  · simp only [dif_neg hj'] at hsome
    have hv : (l1 ++ l2).getD j none = l2.getD (j - l1.length) none := by
      rw [uvnsGetDAppend, dif_neg hj']
    rw [hv]
    exact h2 (j - l1.length) (by omega) hsome

/-- 前缀成员保持（`a ++ b` 的成员 ⇒ `a` 的成员）。 -/
theorem memInPrefix (S : ℕ → Prop) (a b : List (Option ℕ))
    (h : MemIn S (a ++ b)) : MemIn S a := by
  intro j hj hsome
  have hlt : j < (a ++ b).length := by
    simp only [List.length_append]; omega
  have hv : (a ++ b).getD j none = a.getD j none := by
    rw [uvnsGetDAppend, dif_pos hj]
  have hsome' : ((a ++ b).getD j none).isSome := by rwa [← hv] at hsome
  have hres := h j hlt hsome'
  rwa [hv] at hres

/-- `destTriple0` 单 triple 的成员（三分支各为 `memInBase`/`memInSomeAppend`）。 -/
theorem memInDestSingle (f : List ℕ) (S : ℕ → Prop) (w y z n : ℕ)
    (hw : S w) (hy : S y) (hz : S z) (harc : ∀ t ∈ between f w y, S t) :
    MemIn S (Kepler.Text.Reduction3.destTriple0 f [some w] [(y, z, n)]) := by
  simp only [Kepler.Text.Reduction3.destTriple0]
  rw [if_neg (by simp : ¬ ([some w] : List (Option ℕ)) = [])]
  rw [show ([some w] : List (Option ℕ)).getLastD none = some w from rfl]
  simp only [Option.getD_some]
  split
  · exact memInBase S w z n hw hz
  · split
    · exact memInSomeAppend S [some w] [] y z n (memInSingle S w hw)
        (fun t ht => absurd ht (by simp)) hy hz
    · exact memInSomeAppend S [some w] (between f w y) y z n (memInSingle S w hw) harc hy hz

/-- `destTriple0` 单 triple 的末元（三分支均以 `[some z]` 收）。 -/
theorem getLastDDestSingle (f : List ℕ) (w y z n : ℕ) :
    (Kepler.Text.Reduction3.destTriple0 f [some w] [(y, z, n)]).getLastD none = some z := by
  simp only [Kepler.Text.Reduction3.destTriple0]
  rw [if_neg (by simp : ¬ ([some w] : List (Option ℕ)) = [])]
  rw [show ([some w] : List (Option ℕ)).getLastD none = some w from rfl]
  simp only [Option.getD_some]
  split
  · simp only [List.getLastD_concat]
  · split
    · simp only [List.getLastD_concat]
    · simp only [List.getLastD_concat]

/-- **mid 段成员归纳**：`destTriple0 f [] (uvns.take (i+1))` 的 `MemIn` +
末元 = `z_i`（与 `chainClMid` 同骨架，无 junction 需求）。 -/
theorem memMid
    (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r) (hk : transformCount L N r x = k) :
    ∀ i, i + 1 ≤ k →
      MemIn (fun w => w ∈ core L r)
        (Kepler.Text.Reduction3.destTriple0 (core L r) []
          ((Kepler.Text.Reduction3.coreTripleV4 L N r x).take (i + 1))) ∧
      (Kepler.Text.Reduction3.destTriple0 (core L r) []
          ((Kepler.Text.Reduction3.coreTripleV4 L N r x).take (i + 1))).getLastD none
        = some (ztrans L N r x i).1 := by
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' j => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' j
  have hk0 : 0 < k := by
    have h := Kepler.Text.Reduction5.transformCountNon0OfMarked L hL hgn haq hm hnf
    rw [hk] at h
    exact Nat.pos_of_ne_zero h
  have hnf_i : ∀ i, i < k → ¬ finalList L (rtrans L N r x i) := fun i hi =>
    Kepler.Text.Reduction4.transformCount_not i (by rw [hk]; exact hi)
  have hcoreof : ∀ u ∈ r, u.1 ∈ core L r :=
    Kepler.Text.Reduction4Idx.finalAssumptionMemFstCore L hL hm
  have hym : ∀ i, i < k → (ytrans L N r x i).1 ∈ core L r := fun i hi =>
    hcoreof _ (pnxvwfs1 L hL hgn haq i (hnf_i i hi) hm)
  have hzm : ∀ i, i < k → (ztrans L N r x i).1 ∈ core L r := fun i hi =>
    hcoreof _ (pnxvwfs2 L hL hgn haq i (hnf_i i hi) hm)
  have hlen0 : (Kepler.Text.Reduction3.coreTripleV4 L N r x).length = k := by
    rw [Kepler.Text.Reduction3.coreTripleV4_length]
    exact hk
  have hget : ∀ i (hi : i < k),
      (Kepler.Text.Reduction3.coreTripleV4 L N r x)[i]'(by rw [hlen0]; exact hi) =
        ((ytrans L N r x i).1, (ztrans L N r x i).1,
          (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length) := by
    intro i hi
    exact Kepler.Text.Reduction3.elCoreTriple L N r x i (by rw [hk]; exact hi)
  set uvns := Kepler.Text.Reduction3.coreTripleV4 L N r x with huv
  have hlen : uvns.length = k := hlen0
  intro i
  induction i with
  | zero =>
    intro h1k
    have h0len : 0 < uvns.length := by rw [hlen]; exact hk0
    have htake1 : uvns.take 1 = [uvns[0]'h0len] := uvnsGetDTakeOne uvns h0len
    rw [htake1]
    have hg0 : uvns[0]'h0len =
        ((ytrans L N r x 0).1, (ztrans L N r x 0).1,
          (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0)).length) :=
      hget 0 hk0
    rw [hg0]
    rw [show Kepler.Text.Reduction3.destTriple0 (core L r) []
          [((ytrans L N r x 0).1, (ztrans L N r x 0).1,
            (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0)).length)]
        = Kepler.Text.Reduction3.destTriple0 (core L r)
          ([some (ytrans L N r x 0).1] ++
            List.replicate (between (findFaceDarts L x) (ytrans L N r x 0)
              (ztrans L N r x 0)).length (none : Option ℕ) ++
            [some (ztrans L N r x 0).1]) [] from rfl]
    rw [Kepler.Text.Reduction3.destTriple0Nil]
    exact ⟨memInBase (fun w => w ∈ core L r) (ytrans L N r x 0).1
        (ztrans L N r x 0).1 _ (hym 0 hk0) (hzm 0 hk0), by rw [List.getLastD_concat]⟩
  | succ i ih =>
    intro hik
    have hi1 : i + 1 ≤ k := by omega
    have hi1lt : i + 1 < k := by omega
    have hilt : i < k := by omega
    obtain ⟨hMem, hlast⟩ := ih hi1
    have hgeti : uvns[i + 1]'(by rw [hlen]; exact hi1lt) =
        ((ytrans L N r x (i + 1)).1, (ztrans L N r x (i + 1)).1,
          (between (findFaceDarts L x) (ytrans L N r x (i + 1))
            (ztrans L N r x (i + 1))).length) := hget (i + 1) hi1lt
    have htake : uvns.take (i + 1 + 1)
        = uvns.take (i + 1) ++ [uvns[i + 1]'(by rw [hlen]; exact hi1lt)] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by rw [hlen]; exact hi1lt)]
      rfl
    have ha_ne : uvns.take (i + 1) ≠ [] := by
      intro h
      have hc := congrArg List.length h
      rw [List.length_take, hlen, Nat.min_eq_left hi1] at hc
      simp at hc
    have hL1ne : Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (i + 1)) ≠ [] := by
      intro h
      rw [h] at hlast
      simp at hlast
    have hlast' : (Kepler.Text.Reduction3.destTriple0 (core L r) []
        (uvns.take (i + 1))).getLast hL1ne = some (ztrans L N r x i).1 := by
      rw [← uvnsGetLastDEqGetLast hL1ne]
      exact hlast
    have hL1eq : Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (i + 1))
        = (Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (i + 1))).dropLast
          ++ [some (ztrans L N r x i).1] :=
      uvnsEqDropLastAppend hL1ne hlast'
    have hcat2 : Kepler.Text.Reduction3.destTriple0 (core L r) []
          (uvns.take (i + 1) ++ [uvns[i + 1]'(by rw [hlen]; exact hi1lt)])
        = (Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (i + 1))).dropLast
          ++ Kepler.Text.Reduction3.destTriple0 (core L r) [some (ztrans L N r x i).1]
            [uvns[i + 1]'(by rw [hlen]; exact hi1lt)] :=
      Kepler.Text.Reduction3.destTriple0Cat2 (core L r) [] (uvns.take (i + 1))
        [uvns[i + 1]'(by rw [hlen]; exact hi1lt)]
        (Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (i + 1))).dropLast
        (ztrans L N r x i).1 ha_ne (fun h => absurd rfl h) hL1eq
    rw [htake, hcat2, hgeti]
    have hgd : (Kepler.Text.Reduction3.destTriple0 (core L r) [some (ztrans L N r x i).1]
        [((ytrans L N r x (i + 1)).1, (ztrans L N r x (i + 1)).1,
          (between (findFaceDarts L x) (ytrans L N r x (i + 1))
            (ztrans L N r x (i + 1))).length)]).getLastD none
        = some (ztrans L N r x (i + 1)).1 :=
      getLastDDestSingle (core L r) (ztrans L N r x i).1 (ytrans L N r x (i + 1)).1
        (ztrans L N r x (i + 1)).1 _
    have hXne : Kepler.Text.Reduction3.destTriple0 (core L r) [some (ztrans L N r x i).1]
        [((ytrans L N r x (i + 1)).1, (ztrans L N r x (i + 1)).1,
          (between (findFaceDarts L x) (ytrans L N r x (i + 1))
            (ztrans L N r x (i + 1))).length)] ≠ [] := by
      intro h
      rw [h] at hgd
      simp at hgd
    refine ⟨memInAppend (fun w => w ∈ core L r) _ _
      (memInPrefix (fun w => w ∈ core L r) _ _
        (by rw [← hL1eq]; exact hMem))
      (memInDestSingle (core L r) (fun w => w ∈ core L r) (ztrans L N r x i).1
        (ytrans L N r x (i + 1)).1 (ztrans L N r x (i + 1)).1 _
        (hzm i hilt) (hym (i + 1) hi1lt) (hzm (i + 1) hi1lt)
        (fun t ht => Kepler.Text.Reduction5.betwnMem ht)), ?_⟩
    have hcomp : ((Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (i + 1))).dropLast
        ++ Kepler.Text.Reduction3.destTriple0 (core L r) [some (ztrans L N r x i).1]
          [((ytrans L N r x (i + 1)).1, (ztrans L N r x (i + 1)).1,
            (between (findFaceDarts L x) (ytrans L N r x (i + 1))
              (ztrans L N r x (i + 1))).length)]).getLastD none
        = (Kepler.Text.Reduction3.destTriple0 (core L r) [some (ztrans L N r x i).1]
          [((ytrans L N r x (i + 1)).1, (ztrans L N r x (i + 1)).1,
            (between (findFaceDarts L x) (ytrans L N r x (i + 1))
              (ztrans L N r x (i + 1))).length)]).getLastD none := by
      have hneA : ((Kepler.Text.Reduction3.destTriple0 (core L r) []
            (uvns.take (i + 1))).dropLast
          ++ Kepler.Text.Reduction3.destTriple0 (core L r) [some (ztrans L N r x i).1]
            [((ytrans L N r x (i + 1)).1, (ztrans L N r x (i + 1)).1,
              (between (findFaceDarts L x) (ytrans L N r x (i + 1))
                (ztrans L N r x (i + 1))).length)]) ≠ [] := by
        intro h
        have h2 := congrArg List.length h
        simp only [List.length_append, List.length_nil] at h2
        have hX : (Kepler.Text.Reduction3.destTriple0 (core L r) [some (ztrans L N r x i).1]
            [((ytrans L N r x (i + 1)).1, (ztrans L N r x (i + 1)).1,
              (between (findFaceDarts L x) (ytrans L N r x (i + 1))
                (ztrans L N r x (i + 1))).length)]).length = 0 := by omega
        exact hXne (List.length_eq_zero_iff.mp hX)
      rw [uvnsGetLastDEqGetLast hneA, uvnsGetLastDEqGetLast hXne]
      exact List.getLast_append_of_right_ne_nil _ _ hXne
    rw [hcomp]
    exact hgd

end Kepler.Text.Reduction5

#print axioms Kepler.Text.Reduction5.ChainCl
#print axioms Kepler.Text.Reduction5.chainClBase
#print axioms Kepler.Text.Reduction5.chainClNsAppend
#print axioms Kepler.Text.Reduction5.sizeBetwnChainPub
#print axioms Kepler.Text.Reduction5.uvnsGetDMapSomeApp
#print axioms Kepler.Text.Reduction5.uvnsGetDMapAdd
#print axioms Kepler.Text.Reduction5.chainClSomeAppend
#print axioms Kepler.Text.Reduction5.uvnsGetDLastD
#print axioms Kepler.Text.Reduction5.uvnsEqDropLastAppend
#print axioms Kepler.Text.Reduction5.UvnsD
#print axioms Kepler.Text.Reduction5.chainClMid
#print axioms Kepler.Text.Reduction5.MemIn
#print axioms Kepler.Text.Reduction5.memInBase
#print axioms Kepler.Text.Reduction5.memInSomeAppend
#print axioms Kepler.Text.Reduction5.memInDestSingle
#print axioms Kepler.Text.Reduction5.getLastDDestSingle
#print axioms Kepler.Text.Reduction5.memMid
