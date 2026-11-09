/-
  Kepler.Text.TameSpine.JcajyduAqLeaf1 — AQ1 叶第一批：`split.1` 的 `Nodup`
  + 弧端点排除（HOL `uniq_fst_split_norm` AQ1.hl:1373 的 Lean 前半，及它吃的
  `FST_SND_MEM_SPLIT_NORMAL_F` / `FST_FLITER_MEM_SPLIT_NORMAL_F` 所需的分裂事实）。

  目标槽（`aq1Concl`，`JcajyduAqTowerBase.lean:227`）：
  `∀ N r x, GoodListNodesTl L hL → MarkedListSpineFull hL N r x →
     (ntransSpine L N r x 1).flatten.Nodup`

  本批钉死 `ntrans 1 = replace r [split.2] N ++ [split.1]` 的**第一半**：
  `split.1.Nodup`，以及后续装配必需的三条分离事实。

  ┌─ 件表 ────────────────────────────────────────────────────────
  │ §0 弧端点排除（Simple 塌缩，AGENTS §7.1 #17 的 node 轨道路线）：
  │   ① `aq1_nextElYNeZ`：`nextEl r y ≠ z`（若相等则 `nodeMap.symm y = z`
  │      落在 `node y`，与 `z ∈ face y` 及 `node ∩ face = {y}` 塌出 `z = y`）；
  │   ② `aq1_nextElYNePrevElZ`：`nextEl r y ≠ prevEl r z`（AQ3 段3 同证，
  │      抽成本文件公开件；`nodeMap z = z1`、`nodeMap z1 = y` ⇒ `y ∈ node z`
  │      ⇒ `node y = node z` ⇒ `z ∈ node y`）。
  │ §1 `ndSpine` 块：③ `aq1_ndSpineNodup`（nodeMap 幂在 `1..ncard−1` 上互异，
  │      `injOrbit_iff_pairwise` + `szEqNodeCard`）；④ `aq1_windowFstInj`
  │      （面表同首点两 dart 相同，Simple 塌缩）；⑤ `aq1_new1Nodup`
  │      （块内 Nodup + 块间首点不同 ⇒ flatten Nodup）。
  │ §2 分离：⑥ `aq1_ndSpineNotMemFlatten` / `aq1_new1NotMemFlatten`
  │      （`windowFstNotMemNFlatten` + `ndSpineFstEq`）；
  │      ⑦ `aq1_split1Nodup` = `new1.reverse` Nodup ∧ `f1` Nodup
  │      （`uniqAppendBetwn`）∧ 两侧不交（new1 元素 ∉ `flatten N`，f1 ⊆ r）。

  ┌─ 边界（`aq1` 本体未落，精确到件；见 DELIVERY §2）───────────────
  │ ① `N = N₁ ++ r :: N₂` 的 replace/flatten 分解（`r ∈ N` +
  │    `List.mem_iff_append`）：`flatten (replace r [split.2] N) ++ split.1`
  │    = `(flatten N₁) ++ split.2 ++ (flatten N₂) ++ split.1`；
  │ ② 成员二分：`d ∈ split.1 → d ∈ r ∨ d ∉ N.flatten`（本文件 §2 已有
  │    new1 侧；f1 侧 ⊆ r），`d ∈ split.2 → d ∈ r ∨ d ∉ N.flatten`
  │    （f2 ⊆ r；window 侧 `betwnNotInRtrans` + `windowFstNotMemNFlatten`）；
  │ ③ 互不交：`split.1 ∩ split.2 = ∅`——new1×window 需 Simple（同
  │    `aq1_windowFstInj` 的 node/face 塌缩），f1×f2 需「互补弧互不相交」
  │    （HOL `not_betwn1` 家族；本树 TameList72 的同名件是 private）；
  │ ④ 总装：`List.nodup_append` × 3 + `List.nodup_flatten` + `ntrans1`。
  │ **估 ~150–250 行**（③ 是主风险点）；届时总文件会超 450 行 ⇒ 按 §7
  │ 拆第二批（`JcajyduAqLeaf1` 续或 `JcajyduAqLeaf1B`）。
  └──────────────────────────────────────────────────────────────

  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameSpine.JcajyduAqSplit1H
import Kepler.Text.TameCorrCard

namespace Kepler.Text.TameSpine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Kepler.Assembly (nextEl prevEl eList fList GoodList findFaceDarts nList
  listOfDarts listPairs)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nextEl_mem_of_mem prevEl_mem_of_mem)

/-! ## §0 弧端点排除 -/

/-- **`nextEl r y ≠ l'z`**（HOL `uniq_fst_split_norm` 隐含支的 Lean 初等形）：
若 `nextEl r y = z`，则 `nodeMap.symm y = fList (eList y) = nextEl r y = z`，
即 `z ∈ node y`（`nodeMap_symm_mem_node`）；又 `z ∈ face y`（`find_face` 成员），
`simpleHypermapList` 的 `node ∩ face = {y}` 塌出 `z = y`，撞 `hqymrtx3List`。 -/
theorem aq1_nextElYNeZ (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    nextEl r (lYSpine L r x) ≠ lZSpine L N r x := by
  intro h
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hyz : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hyd : lYSpine L r x ∈ listOfDarts L := memYtransListOfDarts L hL hgn hm hf
  have hDy : lYSpine L r x ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hyd
  have hzf : lZSpine L N r x ∈ findFaceDarts L (lYSpine L r x) :=
    zMemFindFaceDarts L hL hgn hunL hm hf
  -- loop 在 y：第二支成立（第一支撞 `nextRNotEqF`）
  have hloop : loopListSpine L r := hm.1.2.1.2.2.2.1 r hm.1.2.2.1
  have hny : nextEl r (lYSpine L r x) = fList L (eList (lYSpine L r x)) := by
    rcases (hloop (lYSpine L r x) hyr).2 with h1 | h1
    · exact absurd h1 (nextRNotEqF L hL hgn hunL hm hf)
    · exact h1
  have hsymm : (hypermapOfList L hL).nodeMap.symm (lYSpine L r x) = lZSpine L N r x := by
    rw [nodeMapSymmEqFList L hL hDy]
    exact hny.symm.trans h
  have hzn : lZSpine L N r x ∈ (hypermapOfList L hL).node (lYSpine L r x) := by
    rw [← hsymm]
    exact (hypermapOfList L hL).nodeMap_symm_mem_node
      ((hypermapOfList L hL).mem_node_self _)
  have hzf2 : lZSpine L N r x ∈ (hypermapOfList L hL).face (lYSpine L r x) :=
    Kepler.Text.TameCorrCard.faceTableSubset hL hyd hzf
  have hsimple := simpleHypermapList L hL hgn hunL
  have hinter : lZSpine L N r x ∈ (hypermapOfList L hL).node (lYSpine L r x)
      ∩ (hypermapOfList L hL).face (lYSpine L r x) := ⟨hzn, hzf2⟩
  rw [hsimple (lYSpine L r x) hDy] at hinter
  exact hyz (Set.mem_singleton_iff.mp hinter).symm

/-- **`nextEl r y ≠ prevEl r z`**（AQ3 split.1 的 `f_last` 段3 抽成公开件）：
若相等，则 `nodeMap z = prevEl r z`、`nodeMap (prevEl r z) = y`，故
`y = nodeMap² z ∈ node z`；`node y = node z` 给 `z ∈ node y`，
配 `z ∈ face y` 与 `node ∩ face = {y}` 塌出 `z = y`，撞 `hqymrtx3List`。 -/
theorem aq1_nextElYNePrevElZ (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    nextEl r (lYSpine L r x) ≠ prevEl r (lZSpine L N r x) := by
  intro hra
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hyz : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hz1r : prevEl r (lZSpine L N r x) ∈ r := prevEl_mem_of_mem hzr
  have hnextz1 : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hrnd _
  have hyd : lYSpine L r x ∈ listOfDarts L := memYtransListOfDarts L hL hgn hm hf
  have hloop : loopListSpine L r := hm.1.2.1.2.2.2.1 r hm.1.2.2.1
  have hzd : lZSpine L N r x ∈ listOfDarts L :=
    normalListListOfDarts hm.1.2.1 (lZSpine L N r x)
      (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hzr⟩)
  have hz1d : prevEl r (lZSpine L N r x) ∈ listOfDarts L := (hloop _ hz1r).1
  have hDz : lZSpine L N r x ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hzd
  have hDz1 : prevEl r (lZSpine L N r x) ∈ (hypermapOfList L hL).darts :=
    List.mem_toFinset.mpr hz1d
  have hDy : lYSpine L r x ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hyd
  have hny : nextEl r (lYSpine L r x) = fList L (eList (lYSpine L r x)) := by
    rcases (hloop (lYSpine L r x) hyr).2 with h1 | h1
    · exact absurd h1 (nextRNotEqF L hL hgn hunL hm hf)
    · exact h1
  have hz1e : lZSpine L N r x = fList L (eList (prevEl r (lZSpine L N r x))) := by
    rcases (hloop (prevEl r (lZSpine L N r x)) hz1r).2 with h1 | h1
    · rw [hnextz1] at h1
      exact absurd h1.symm (prevRNotEqF L hL hgn hunL hm hf)
    · rw [hnextz1] at h1
      exact h1
  -- nodeMap z = prevEl r z
  have hsymm1 : (hypermapOfList L hL).nodeMap.symm (prevEl r (lZSpine L N r x))
      = lZSpine L N r x := by
    rw [nodeMapSymmEqFList L hL hDz1]
    exact hz1e.symm
  have hnmapz : (hypermapOfList L hL).nodeMap (lZSpine L N r x)
      = prevEl r (lZSpine L N r x) := by
    have h := congrArg (hypermapOfList L hL).nodeMap hsymm1
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  -- nodeMap (prevEl r z) = y
  have hsymmy : (hypermapOfList L hL).nodeMap.symm (lYSpine L r x)
      = prevEl r (lZSpine L N r x) := by
    rw [nodeMapSymmEqFList L hL hDy]
    exact hny.symm.trans hra
  have hnmaps1 : (hypermapOfList L hL).nodeMap (prevEl r (lZSpine L N r x))
      = lYSpine L r x := by
    have h := congrArg (hypermapOfList L hL).nodeMap hsymmy
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  have hyn : lYSpine L r x ∈ (hypermapOfList L hL).node (lZSpine L N r x) := by
    rw [(hypermapOfList L hL).mem_node_iff (lZSpine L N r x) (lYSpine L r x)]
    refine ⟨2, ?_⟩
    rw [pow_two, Equiv.Perm.mul_apply, hnmapz, hnmaps1]
  have hnodeq : (hypermapOfList L hL).node (lZSpine L N r x)
      = (hypermapOfList L hL).node (lYSpine L r x) :=
    (hypermapOfList L hL).node_eq_of_mem hyn
  have hzn : lZSpine L N r x ∈ (hypermapOfList L hL).node (lYSpine L r x) := by
    rw [← hnodeq]
    exact (hypermapOfList L hL).mem_node_self _
  have hzf : lZSpine L N r x ∈ findFaceDarts L (lYSpine L r x) :=
    zMemFindFaceDarts L hL hgn hunL hm hf
  have hzf2 : lZSpine L N r x ∈ (hypermapOfList L hL).face (lYSpine L r x) :=
    Kepler.Text.TameCorrCard.faceTableSubset hL hyd hzf
  have hsimple := simpleHypermapList L hL hgn hunL
  have hinter : lZSpine L N r x ∈ (hypermapOfList L hL).node (lYSpine L r x)
      ∩ (hypermapOfList L hL).face (lYSpine L r x) := ⟨hzn, hzf2⟩
  rw [hsimple (lYSpine L r x) hDy] at hinter
  exact hyz (Set.mem_singleton_iff.mp hinter).symm


/-! ## §1 `ndSpine` 块：块内 Nodup、首点互异、flatten Nodup -/

/-- **`ndSpine` 块 Nodup**：`ndSpine L d` 是 `nodeMap^1..^ncard-1`，两两互异
（`injOrbit_iff_pairwise` 在 `m = ncard−1` 处给幂的成对单射；`sz = ncard` 由
`szEqNodeCard` 供）。 -/
theorem aq1_ndSpineNodup (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {d : ℕ × ℕ} (hd : d ∈ (hypermapOfList L hL).darts)
    (h2 : 2 ≤ (L.flatten.filter (fun t => decide (t = d.1))).length) :
    (ndSpine L d).Nodup := by
  have hdL : d ∈ listOfDarts L := List.mem_toFinset.mp hd
  set m := (L.flatten.filter (fun t => decide (t = d.1))).length - 1 with hmdef
  have hsz : m = (Kepler.Text.orbitMap (hypermapOfList L hL).nodeMap d).ncard - 1 := by
    rw [hmdef, szEqNodeCard L hL hgn hd]
    exact congrArg (· - 1) (congrArg Set.ncard
      (show (hypermapOfList L hL).node d
        = Kepler.Text.orbitMap (hypermapOfList L hL).nodeMap d from rfl))
  have hmpos : 1 ≤ m := by
    rw [hmdef]; omega
  rw [ndSpine, List.nodup_map_iff_inj_on (List.nodup_range' (s := 1) (n := m))]
  intro i hi j hj hij
  obtain ⟨i', hi'lt, rfl⟩ := List.mem_range'.mp hi
  obtain ⟨j', hj'lt, rfl⟩ := List.mem_range'.mp hj
  have hp : ((hypermapOfList L hL).nodeMap ^ (1 + 1 * i')) d
      = ((hypermapOfList L hL).nodeMap ^ (1 + 1 * j')) d := by
    simpa only [nListPowEqNodeMapPow L hL hdL] using hij
  have huniq := (hypermapOfList L hL).nodeMap_permutes.injOrbit_of_lt_ncard
    (x := d) (m := (Kepler.Text.orbitMap (hypermapOfList L hL).nodeMap d).ncard - 1) (by omega)
  have hle1 : 1 + 1 * i' ≤ (Kepler.Text.orbitMap (hypermapOfList L hL).nodeMap d).ncard - 1 := by omega
  have hle2 : 1 + 1 * j' ≤ (Kepler.Text.orbitMap (hypermapOfList L hL).nodeMap d).ncard - 1 := by omega
  have heq : 1 + 1 * i' = 1 + 1 * j' :=
    (injOrbit_iff_pairwise (hypermapOfList L hL).nodeMap d
      ((Kepler.Text.orbitMap (hypermapOfList L hL).nodeMap d).ncard - 1)).mp huniq
      (1 + 1 * i') (1 + 1 * j') hle1 hle2 hp
  omega

/-- **窗口两 dart 同首点 ⇒ 同一**（`nodeEqFstSet` + `faceTableSubset` + Simple）：
面表 `find_FACE` 的两个成员若首点相同，则它们是同一个 dart。 -/
theorem aq1_windowFstInj (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ∀ d ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x),
      ∀ d' ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x),
        d.1 = d'.1 → d = d' := by
  intro d hd d' hd' hfsteq
  have hd'd : d' ∈ listOfDarts L := mem_darts_of_mem_findFace L (memBetweenOfMem hd')
  have hd'dD : d' ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hd'd
  have hddD : d ∈ (hypermapOfList L hL).darts :=
    List.mem_toFinset.mpr (mem_darts_of_mem_findFace L (memBetweenOfMem hd))
  have hdn : d ∈ (hypermapOfList L hL).node d' := by
    rw [nodeEqFstSet L hL hgn hd'dD]
    exact ⟨List.mem_toFinset.mp hddD, hfsteq⟩
  have hyd : lYSpine L r x ∈ listOfDarts L := memYtransListOfDarts L hL hgn hm hf
  have hdfy : d ∈ (hypermapOfList L hL).face (lYSpine L r x) :=
    Kepler.Text.TameCorrCard.faceTableSubset hL hyd (memBetweenOfMem hd)
  have hd'fy : d' ∈ (hypermapOfList L hL).face (lYSpine L r x) :=
    Kepler.Text.TameCorrCard.faceTableSubset hL hyd (memBetweenOfMem hd')
  have hd'f : d ∈ (hypermapOfList L hL).face d' := by
    rw [← (hypermapOfList L hL).face_eq_of_mem hd'fy]
    exact hdfy
  have hsimple := simpleHypermapList L hL hgn hunL
  have hinter : d ∈ (hypermapOfList L hL).node d' ∩ (hypermapOfList L hL).face d' :=
    ⟨hdn, hd'f⟩
  rw [hsimple d' hd'dD] at hinter
  exact Set.mem_singleton_iff.mp hinter

/-- **`(new2.map ndSpine).flatten` Nodup**（`new2` = 窗口）：块内 Nodup
（`aq1_ndSpineNodup`）、块间不交（首点不同，`aq1_windowFstInj` 给「同首点即同
dart」，与 `new2.Nodup` 冲突）。 -/
theorem aq1_new1Nodup (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    (((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)).map (ndSpine L)).flatten).Nodup := by
  have hfst := aq1_windowFstInj L hL hgn hunL hm hf
  have key : ∀ (w : List (ℕ × ℕ)), w.Nodup →
      (∀ d ∈ w, d ∈ (hypermapOfList L hL).darts) →
      (∀ d ∈ w, 2 ≤ (L.flatten.filter (fun t => decide (t = d.1))).length) →
      (∀ d ∈ w, ∀ d' ∈ w, d.1 = d'.1 → d = d') →
      (w.map (ndSpine L)).flatten.Nodup := by
    intro w hwn hwD hwsz hwfst
    induction w with
    | nil => simp
    | cons a t ih =>
      rw [List.map_cons, List.flatten_cons, List.nodup_append]
      refine ⟨aq1_ndSpineNodup L hL hgn (hwD a (List.mem_cons_self ..))
        (hwsz a (List.mem_cons_self ..)), ?_, ?_⟩
      · exact ih (List.nodup_cons.mp hwn).2
          (fun d hd => hwD d (List.mem_cons_of_mem _ hd))
          (fun d hd => hwsz d (List.mem_cons_of_mem _ hd))
          (fun d hd d' hd' => hwfst d (List.mem_cons_of_mem _ hd) d'
            (List.mem_cons_of_mem _ hd'))
      · intro e he f' hf'
        obtain ⟨blk, hblk, hf'mem⟩ := List.mem_flatten.mp hf'
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hblk
        have haD : a ∈ (hypermapOfList L hL).darts := hwD a (List.mem_cons_self ..)
        have hbD : b ∈ (hypermapOfList L hL).darts := hwD b (List.mem_cons_of_mem _ hb)
        have hane : a ≠ b := by
          intro hab
          exact (List.nodup_cons.mp hwn).1 (hab ▸ hb)
        have hfst1 : e.1 = a.1 := ndSpineFstEq L hL hgn haD he
        have hfst2 : f'.1 = b.1 := ndSpineFstEq L hL hgn hbD hf'mem
        intro hef
        apply hane
        exact hwfst a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb)
          (by rw [← hfst1, hef, hfst2])
  have hmem : ∀ d ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x), d ∈ (hypermapOfList L hL).darts := fun d hd =>
    List.mem_toFinset.mpr (mem_darts_of_mem_findFace L (memBetweenOfMem hd))
  have hsz : ∀ d ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x), 2 ≤ (L.flatten.filter (fun t => decide (t = d.1))).length :=
    fun d hd => two_le_sz_of_restricted L hL hgn hm.1.1 (hmem d hd)
  exact key _ (uniqBetwn (findFaceDarts_nodup hL.1 _)
    (dart_in_face L _ |>.mpr (memYtransListOfDarts L hL hgn hm hf))
    (zMemFindFaceDarts L hL hgn hunL hm hf)
    (hqymrtx3List L hL hgn hunL hm hf)) hmem hsz hfst

/-! ## §2 `new1` 与 `flatten N` 分离、`split.1` Nodup -/

/-- `ndSpine` 元素不吃 `flatten N`（首点 ∉ `flatten N` 的首点表）。 -/
theorem aq1_ndSpineNotMemFlatten (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {d : ℕ × ℕ} (hd : d ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)) {e : ℕ × ℕ} (he : e ∈ ndSpine L d) :
    e ∉ N.flatten := by
  intro hemem
  have hdD : d ∈ (hypermapOfList L hL).darts :=
    List.mem_toFinset.mpr (mem_darts_of_mem_findFace L (memBetweenOfMem hd))
  have hefst : e.1 = d.1 := ndSpineFstEq L hL hgn hdD he
  apply windowFstNotMemNFlatten L hL hgn hunL hm hf hd
  rw [← hefst]
  exact List.mem_map.mpr ⟨e, hemem, rfl⟩

/-- `new1` 的每个元素都不吃 `flatten N`。 -/
theorem aq1_new1NotMemFlatten (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ∀ e ∈ ((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)).map (ndSpine L)).flatten, e ∉ N.flatten := by
  intro e he
  obtain ⟨blk, hblk, hmem⟩ := List.mem_flatten.mp he
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hblk
  exact aq1_ndSpineNotMemFlatten L hL hgn hunL hm hf hd hmem

/-- **`split.1` Nodup**（HOL `uniq_fst_split_norm` 的 Lean 形）：
`split.1 = new1.reverse ++ f1`，三件——`new1` Nodup（`aq1_new1Nodup`）、
`f1` Nodup（`uniqAppendBetwn`，吃 `nextEl r y ≠ prevEl r z`）、两侧不交
（`new1` 元素 ∉ `flatten N`，而 `f1 ⊆ r ⊆ flatten N`）。 -/
theorem aq1_split1Nodup (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).1.Nodup := by
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hz1r : prevEl r (lZSpine L N r x) ∈ r := prevEl_mem_of_mem hzr
  have hra : nextEl r (lYSpine L r x) ≠ prevEl r (lZSpine L N r x) :=
    aq1_nextElYNePrevElZ L hL hgn hunL hm hf
  have hnextz1 : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hrnd _
  have hsplit : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (prevEl r (lZSpine L N r x))).1
      = ((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).map (ndSpine L)).flatten.reverse
        ++ ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
            (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]) := by
    rw [split1Unfold L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (prevEl r (lZSpine L N r x)), hnextz1]
  have hf1 : ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
      (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]).Nodup :=
    uniqAppendBetwn hrnd (nextEl_mem_of_mem hyr) hz1r hra
  have hnew1 : (((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)).map (ndSpine L)).flatten).Nodup :=
    aq1_new1Nodup L hL hgn hunL hm hf
  rw [hsplit, List.nodup_append]
  refine ⟨(List.nodup_reverse).mpr hnew1, hf1, ?_⟩
  intro a ha b hb hab
  have haN : a ∉ N.flatten :=
    aq1_new1NotMemFlatten L hL hgn hunL hm hf a (List.mem_reverse.mp ha)
  have hbr : b ∈ r := by
    rcases List.mem_append.mp hb with h1 | h2
    · rcases List.mem_append.mp h1 with h3 | h3
      · rw [List.mem_singleton] at h3
        exact h3 ▸ (nextEl_mem_of_mem hyr)
      · exact memBetweenOfMem h3
    · rw [List.mem_singleton] at h2
      exact h2 ▸ hz1r
  exact haN (hab ▸ List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hbr⟩)

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq1_nextElYNeZ
#print axioms Kepler.Text.TameSpine.aq1_nextElYNePrevElZ
#print axioms Kepler.Text.TameSpine.aq1_ndSpineNodup
#print axioms Kepler.Text.TameSpine.aq1_windowFstInj
#print axioms Kepler.Text.TameSpine.aq1_new1Nodup
#print axioms Kepler.Text.TameSpine.aq1_ndSpineNotMemFlatten
#print axioms Kepler.Text.TameSpine.aq1_new1NotMemFlatten
#print axioms Kepler.Text.TameSpine.aq1_split1Nodup
