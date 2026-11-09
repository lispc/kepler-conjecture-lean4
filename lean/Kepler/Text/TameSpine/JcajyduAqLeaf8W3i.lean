/-
  JcajyduAqLeaf8W3i — AQ8 波 3i：HOL `set_of_list f` 取值链还原 + 收窄件。

  ┌─ 还原表（AQ8.hl:509-520 / :2252-2263，两处同形）──────────────
  │ 步 | HOL tactic                                      | Lean 对应（本波核对）
  │ ---+-------------------------------------------------+--------------------
  │ 1  | `Tame_list.betwn_mem[\`f\`;\`y\`;\`z\`;\`u\`]`      | `betwnMem`（TameList3:977）
  │    | ⇒ `MEM u (betwn f y z) ⇒ MEM u f`              | 同形（`f` implicit）
  │ 2  | 同 1，`v`                                        | 同
  │ 3  | `mem_find_face_imp_faces_eq[\`u\`;\`x\`;\`L\`]`     | `aq10_memFindFaceImpFacesEq hL.1 huF`
  │ 4  | 同 3，`v`                                        | 同
  │ 5  | `MEM_hypermap_of_list_node[\`L\`;\`u\`;\`v\`]`      | `memHypermapOfListNode hL hgn huD`
  │    | （同 FST + 同 dart 集 ⇒ `v ∈ node u`）            | `.mpr ⟨heq, hvD⟩`
  │ 6  | `is_restricted; simple_hypermap`                  | `simpleHypermapList L hL hgn hunL`
  │ 7  | `face_of_list[\`L\`;\`u\`]`（`set_of_list (find_face L u) = face u`） | `faceTableSubset hL huD`
  │ 8  | `v IN node u INTER set_of_list f`                | `⟨hnode, hface⟩`（`set_of_list f` 的
  │    |                                                  | 成员性由 **f-弧**（步 1/3）给，
  │    |                                                  | 非 r-弧 ⇒ 收窄点）
  │ 9  | `IN_SING ⇒ v = u`                                | `Set.mem_singleton_iff.mp`
  │ 结论：**u、v 只取 `betwn f y z`（面表弧）**，面成员性来自 f-弧，
  │ 不需要 r-弧 ⇒ W3d/W3e 的 `hR`/`harcF` 全称形（对 r）**不在 HOL 消费点**。
  └────────────────────────────────────────────────────────────────

  ┌─ 本波件（收窄形，新定理；不碰已落库三件）──────────────────────
  │ ① aq8w3i_fstHdInjPartsFaceArc  GSUBGOAL#8 的**收窄形**：
  │    `parts L (betwn f y z)` 上 `(FST∘HD)` 单射——u、v 只取自 f-弧，
  │    面成员性由 `aq8w3e_betwnFaceSubFaceX`（无条件件，W3e）供。
  │    零 condition 槽（无 h1..h5、无 hR/harcF）。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算）────────────────────────────────────────────────
  │ `set_of_list f` ↦ `findFaceDarts L (lYSpine L r x)` 的成员性；
  │ `parts_f_betwn_pure` 在本件只作形状参考（W1b `aqs_partsFBetwnPure`
  │ 在库）；`FST o HD` ↦ `fun p => p.head!.1`。逐字。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件 `aq8w3i_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W3e
import Kepler.Text.TameSpine.JcajyduBetwnBase

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face findFaceDarts_nodup
  mem_darts_of_mem_findFace)

/-- **GSUBGOAL#8 的收窄形**（按 HOL :509-520 / :2252-2263 原形）：
`u, v` 取自**面表弧** `betwn (find_face L (l'y)) (l'y) (l'z)`，同 `FST∘HD` ⇒ `u = v`。

面成员性由 f-弧供（`betwnMem` + `aq8w3e_betwnFaceSubFaceX`），
不经 `hR`/`harcF` 的 r-弧全称形（已证为假）。 -/
theorem aq8w3i_fstHdInjPartsFaceArc (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ∀ u ∈ partsSpine L (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x)),
      ∀ v ∈ partsSpine L (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x)),
        (u.head!).1 = (v.head!).1 → u = v := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hpp := pplhuljV0 L hL hgn hunL hm hf
  have hyne : lYSpine L r x ≠ lZSpine L N r x := hyneSupply L hL hgn hunL hm hf
  have hyf : lYSpine L r x ∈ findFaceDarts L (lYSpine L r x) :=
    (dart_in_face L _).mpr (memYtransListOfDarts L hL hgn hm hf)
  have hzf : lZSpine L N r x ∈ findFaceDarts L (lYSpine L r x) :=
    zMemFindFaceDarts L hL hgn hunL hm hf
  have hnd : (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)).Nodup :=
    uniqBetwn (findFaceDarts_nodup hL.1 _) hyf hzf hyne
  intro u hu v hv heq
  by_cases hne : between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x) = []
  · rw [hne] at hu
    exact absurd hu (by simp [partsSpine, partitionIntoAtom, partitionIntoAtom0])
  · have hune : u ≠ [] := partsAllNonnil L hnd hne u hu
    have hvne : v ≠ [] := partsAllNonnil L hnd hne v hv
    have hup : u.head! ∈ u := List.head!_mem_self hune
    have hvp : v.head! ∈ v := List.head!_mem_self hvne
    have hua : u.head! ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x) := memPartsImp L hnd hne hu _ hup
    have hva : v.head! ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x) := memPartsImp L hnd hne hv _ hvp
    -- dart 集与面成员性（均走 f-弧）
    have huD : u.head! ∈ listOfDarts L := mem_darts_of_mem_findFace L (betwnMem hua)
    have hvD : v.head! ∈ listOfDarts L := mem_darts_of_mem_findFace L (betwnMem hva)
    have hufx : u.head! ∈ findFaceDarts L x := aq8w3e_betwnFaceSubFaceX L hL hgn hm hf _ hua
    have hvfx : v.head! ∈ findFaceDarts L x := aq8w3e_betwnFaceSubFaceX L hL hgn hm hf _ hva
    -- 同 node
    have hnode : v.head! ∈ (hypermapOfList L hL).node u.head! :=
      (memHypermapOfListNode hL hgn huD).mpr ⟨heq, hvD⟩
    -- 同面 ⇒ v.head! ∈ face u.head!
    have hfin : v.head! ∈ findFaceDarts L (u.head!) := by
      rw [aq10_memFindFaceImpFacesEq hL.1 hufx]
      exact hvfx
    have hface : v.head! ∈ (hypermapOfList L hL).face u.head! :=
      Kepler.Text.TameCorrCard.faceTableSubset hL huD hfin
    -- Simple 塌缩
    have hsimple := simpleHypermapList L hL hgn hunL
    have hinter : v.head! ∈ (hypermapOfList L hL).node u.head!
        ∩ (hypermapOfList L hL).face u.head! := ⟨hnode, hface⟩
    rw [hsimple u.head! (List.mem_toFinset.mpr huD)] at hinter
    have hheadEq : v.head! = u.head! := Set.mem_singleton_iff.mp hinter
    -- 两 part 共享 head ⇒ 同一 part
    have hfl : (partsSpine L (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x))).flatten.Nodup := by
      rw [partsFlatten L hnd hne]; exact hnd
    exact uniqSublistUnique _ hfl u hu v hv
      ⟨u.head!, hup, by rw [← hheadEq]; exact hvp⟩

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：⊆ 标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq8w3i_fstHdInjPartsFaceArc
