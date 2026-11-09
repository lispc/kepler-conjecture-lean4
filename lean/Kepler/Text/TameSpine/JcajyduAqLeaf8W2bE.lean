/-
  JcajyduAqLeaf8W2bE — AQ8 波 2b-ii：`uniq_fst_betwn_rev_parts` + `eq_fst_betwn_rev_parts`。

  ┌─ 范围（HOL AQ8.hl:2135 / :2269，合计 247 行）─────────────────
  │ ① aq8w2e_uniqFstBetwnRevParts   AQ8.hl:2135（134 行）
  │    `uniq (map (FST o HD) (parts L (rev (flatten (map F (betwn …))))))`
  │ ② aq8w2e_eqFstBetwnRevParts     AQ8.hl:2269（113 行）
  │    `(map (FST o HD) (parts L g)) = rev (map FST (betwn …))`
  │ 两件共用同一内核：`parts_rev_f_betwn_pure`（W2b-i-2c 已落，无条件
  │ 形 `aq8w2d_partsRevFBetwnPure`）+ 块首 `FST` 逐点（`fstNListPower`）。
  └────────────────────────────────────────────────────────────────

  ┌─ 结构（与 HOL 逐句对表）─────────────────────────────────────
  │ 记 `W = betwn (find_face L x) (l'y) (l'z)`、`sz d = sizel (filter
  │ (· = FST d) (flatten L))`、`F d = map (nList^i d) (upt 1 (sz d))`、
  │ `G d = rev (F d)`、`g = rev (flatten (map F W))`。
  │ ① `parts L g = rev (map G W)`（W2b-i-2c）。
  │ ② `map (FST o HD) (rev (map G W)) = rev (map (FST o HD∘G) W)`
  │    （`Seq.map_rev` + `map_comp`）；逐点 `FST (HD (G d)) = FST d`：
  │    块首 ∈ 块（块非空 `blockNonnil`），块元素 = `nList^j d`，
  │    故其 FST = `FST d`（`FST_N_LIST_POWER`）。⇒ 转成 `uniq (map FST W)`。
  │ ③ `uniq (map FST W)`：HOL 路（`uniq_map` + `eq_in_map`）在 Lean 侧
  │    已由 W1b 落成 `aq8w1_uniqFstBetwnParts`（`parts L W = MAP [·]`
  │    后逐点单射：同 FST ⇒ 同 node（`MEM_hypermap_of_list_node`）+
  │    同 face（面相等 + `faceTable_subset`）⇒ Simple 的
  │    `node ∩ face = {u}` 塌出相等）。本件直接复用该结论。
  │ ④ ②式两边 `rev` 消去（`congr 1`）即得 ② 的等式形。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算）─────────────────────────────────────────────
  │ ① `upt 1 k` ↦ `range' 1 k`；`POWER` ↦ iterate；`rev` ↦ reverse；
  │    `sizel (filter …)` ↦ `.length`；`FST`/`SND` ↦ `.1`/`.2`。
  │ ② `FST o HD` ↦ `fun q => q.head!.1`（parts 的件非空，`HD` ↦ `head!`
  │    在非空面上同值；W1b `aq8w1_uniqFstBetwnParts` 同款折算）。
  │ ② HOL 的 `g` 是自由变元 + `rev(flatten …) = g` 前件；Lean 同形
  │    （`hg : g = (…).flatten.reverse`，方向按 W2bC/W2bD 既有约定）。
  │ ③ `~final`/`good_list`/`good_list_nodes`/`marked_list` ↦ 显式
  │    `hf`/`hL`/`hgn`/`hm`；`all uniq L` 由 `isRestrictedAllUniq` 内部导出。
  │ ④ `uniq g` / `~(betwn … = [])` 保持为入参（HOL 原假设，不新增槽）。
  │ ⑤ between 窗口特化（`aq8w2d_hHBetwn` 类）本波不做，留 W3 按需。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件 `aq8w2e_` 前缀，私件同前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W2bD
import Kepler.Text.TameSpine.JcajyduAqLeaf8W1b
import Kepler.Text.TameSpine.JcajyduAqLeaf8W05
import Kepler.Text.TameSpine.JcajyduBetwnBase

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl findFaceDarts_nodup)

/-! ## §0 块首 FST（`FST (HD (G d)) = FST d`） -/

/-- 块首的 `FST` = 代表的 `FST`：块元素都是 `(nList)^[j] d`（块非空 ⇒
`head! ∈ 块`），`FST_N_LIST_POWER`（W0.5 `fstNListPower`）逐点给出
`((nList)^[j] d).1 = d.1`。 -/
private theorem aq8w2e_blockHeadFst (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {d : ℕ × ℕ} (hd : d ∈ listOfDarts L) (k : ℕ)
    (hk : 0 < k) :
    ((List.range' 1 k).reverse.map (fun i => (nList L)^[i] d)).head!.1 = d.1 := by
  have hne : (List.range' 1 k).reverse.map (fun i => (nList L)^[i] d) ≠ [] :=
    aq8w2b_blockNonnil L hk d
  have hmem : ((List.range' 1 k).reverse.map (fun i => (nList L)^[i] d)).head!
      ∈ (List.range' 1 k).reverse.map (fun i => (nList L)^[i] d) :=
    List.head!_mem_self hne
  rw [List.map_reverse] at hmem
  obtain ⟨j, -, hjeq⟩ := List.mem_map.mp (List.mem_reverse.mp hmem)
  rw [List.map_reverse, ← hjeq]
  exact fstNListPower L hL hgn hd j

/-! ## §1 `uniq_fst_betwn_rev_parts`（HOL AQ8.hl:2135） -/

/-- **HOL `uniq_fst_betwn_rev_parts`**（AQ8.hl:2135）：
`uniq (map (FST o HD) (parts L g))`，其中
`g = rev (flatten (map (fun d => map (nList^i d) (upt 1 (sz d))) (betwn …)))`。

`parts L g = rev (map G W)`（W2b-i-2c 无条件形）⇒ 两侧改写成
`uniq (map (fun d => FST d) W)`（块首 FST 逐点），再由 W1b
`aq8w1_uniqFstBetwnParts`（`parts L W = MAP [·]` 的单点形）收口。 -/
theorem aq8w2e_uniqFstBetwnRevParts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (g : List (ℕ × ℕ))
    (hg : g = (((between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
      (fun d => (List.range' 1 ((L.flatten.filter (fun t => decide (t = d.1))).length)).map
        (fun i => (nList L)^[i] d))).flatten).reverse)
    (hne : g ≠ []) (hun : g.Nodup) :
    ((partsSpine L g).map (fun q => q.head!.1)).Nodup := by
  -- 窗口无重（W1b 同款语境推导）
  have hWnd : (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).Nodup := by
    have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
    have hz : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
    have hy : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
    have hyz : lYSpine L r x ≠ lZSpine L N r x := hyneSupply L hL hgn hunL hm hf
    have hpp := pplhuljV0 L hL hgn hunL hm hf
    have hfnd : (findFaceDarts L x).Nodup := findFaceDarts_nodup hL.1 x
    exact uniqBetwn hfnd hpp.1 hpp.2.1 hyz
  -- parts L g = prt（W2b-i-2c 无条件形）
  have hparts : partsSpine L g = ((between (findFaceDarts L x) (lYSpine L r x)
      (lZSpine L N r x)).map
      (fun d => (List.range' 1 ((L.flatten.filter (fun t => decide (t = d.1))).length)).reverse.map
        (fun i => (nList L)^[i] d))).reverse :=
    aq8w2d_partsRevFBetwnPure L hL hgn
      (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x))
      (fun d => (L.flatten.filter (fun t => decide (t = d.1))).length) g
      (fun _ _ => rfl) (aq8w2bB_WDarts L) hWnd hg hne hun (aq8w2bB_szPosBetwn L)
  rw [hparts]
  -- map/rev 交换：`map f (rev (map G W)) = rev (map (f∘G) W)`
  rw [List.map_reverse, List.nodup_reverse, List.map_map]
  -- 逐点 `FST (HD (G d)) = FST d`
  have hcongr : ((between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
        ((fun q => q.head!.1) ∘ fun d =>
          (List.range' 1 ((L.flatten.filter (fun t => decide (t = d.1))).length)).reverse.map
            (fun i => (nList L)^[i] d)))
      = (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
          (fun d => d.1) :=
    List.map_congr_left
      (fun d hd => aq8w2e_blockHeadFst L hL hgn (aq8w2bB_WDarts L d hd) _ (aq8w2bB_szPosBetwn L d hd))
  rw [hcongr]
  -- `uniq (map FST W)` ← W1b 单点形
  have hpartsW : partsSpine L (between (findFaceDarts L x) (lYSpine L r x)
      (lZSpine L N r x)) = (between (findFaceDarts L x) (lYSpine L r x)
        (lZSpine L N r x)).map (fun d => [d]) :=
    aqs_partsFBetwnPure L hL hgn hm hf
  have huniqW : ((between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
      (fun d => [d])).map (fun q => q.head!.1)
      = (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
          (fun d => d.1) := by
    rw [List.map_map]
    rfl
  rw [← huniqW, ← hpartsW]
  exact aq8w1_uniqFstBetwnParts L hL hgn hm hf

/-! ## §2 `eq_fst_betwn_rev_parts`（HOL AQ8.hl:2269） -/

/-- **HOL `eq_fst_betwn_rev_parts`**（AQ8.hl:2269）：
`map (FST o HD) (parts L g) = rev (map FST (betwn …))`。

与 §1 同一内核：`parts L g = rev (map G W)` + 块首 FST 逐点，两边 `rev`
消去（`congr 1`）。 -/
theorem aq8w2e_eqFstBetwnRevParts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (g : List (ℕ × ℕ))
    (hg : g = (((between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
      (fun d => (List.range' 1 ((L.flatten.filter (fun t => decide (t = d.1))).length)).map
        (fun i => (nList L)^[i] d))).flatten).reverse)
    (hne : g ≠ []) (hun : g.Nodup) :
    ((partsSpine L g).map (fun q => q.head!.1))
      = ((between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
          (fun d => d.1)).reverse := by
  have hWnd : (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).Nodup := by
    have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
    have hz : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
    have hy : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
    have hyz : lYSpine L r x ≠ lZSpine L N r x := hyneSupply L hL hgn hunL hm hf
    have hpp := pplhuljV0 L hL hgn hunL hm hf
    have hfnd : (findFaceDarts L x).Nodup := findFaceDarts_nodup hL.1 x
    exact uniqBetwn hfnd hpp.1 hpp.2.1 hyz
  have hparts : partsSpine L g = ((between (findFaceDarts L x) (lYSpine L r x)
      (lZSpine L N r x)).map
      (fun d => (List.range' 1 ((L.flatten.filter (fun t => decide (t = d.1))).length)).reverse.map
        (fun i => (nList L)^[i] d))).reverse :=
    aq8w2d_partsRevFBetwnPure L hL hgn
      (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x))
      (fun d => (L.flatten.filter (fun t => decide (t = d.1))).length) g
      (fun _ _ => rfl) (aq8w2bB_WDarts L) hWnd hg hne hun (aq8w2bB_szPosBetwn L)
  rw [hparts, List.map_reverse, List.map_map]
  congr 1
  exact List.map_congr_left
    (fun d hd => aq8w2e_blockHeadFst L hL hgn (aq8w2bB_WDarts L d hd) _ (aq8w2bB_szPosBetwn L d hd))

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：两件全 ⊆ 标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq8w2e_uniqFstBetwnRevParts
#print axioms Kepler.Text.TameSpine.aq8w2e_eqFstBetwnRevParts
