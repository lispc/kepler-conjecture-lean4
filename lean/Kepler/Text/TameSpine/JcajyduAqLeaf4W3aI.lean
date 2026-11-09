/-
  Kepler.Text.TameSpine.JcajyduAqLeaf4W3aI — AQ4 W3a-i：`prevEl new1` 的 A/B/C 三类。

  `w = betwn (findFaceDarts L y) y z`、`block d = ndSpine L d`、`new1 = (w.map block).flatten`。
  这三件是 `aq4_loopS1` 的 new1 侧（原 W3a 止损遗留），**只按 prevEl 归约路线**：
  `nextEl s1 x = prevEl new1 x`（`nextElCat2` + `la7_nextEl_reverse`）。

  ┌─ 件表 ────────────────────────────────────────────────────────
  │ ① `aq4_ndSpinePowNe`（私件）：块内幂互异（1 ≤ i,j ≤ sz-1 且 i≠j）；
  │ ② `aq4_prevElNew1Interior`（A）：`2 ≤ i ≤ sz-1` ⇒
  │    `prevEl new1 ((nList)^i d) = (nList)^(i-1) d`；
  │ ③ `aq4_prevElNew1BlockHead`（B）：`d ≠ head w` ⇒
  │    `prevEl new1 ((ndSpine d).head!) = (ndSpine (prevEl w d)).getLast!`；
  │ ④ `aq4_prevElNew1FirstBlock`（C）：`d = head w` ⇒
  │    `prevEl new1 ((ndSpine (w.head!)).head!) = new1.getLast!`（回卷）。
  └──────────────────────────────────────────────────────────────

  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf4W3

namespace Kepler.Text.TameSpine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts findFaceDarts GoodList)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nextEl_mem_of_mem prevEl_mem_of_mem getD_eq_getElem_of_lt)

/-- 私件：`l ≠ []` 时 `l.getLast! ∈ l`（`getLast!EqGetLast` + `List.getLast_mem`）。 -/
private theorem aq4_getLastBangMem {α : Type*} [Inhabited α] {l : List α} (h : l ≠ []) :
    l.getLast! ∈ l := by
  rw [getLast!EqGetLast h]
  exact List.getLast_mem h

/-- 私件：`ndSpine` 内幂互异（`1 ≤ i,j ≤ sz-1`、`i ≠ j`）；`idxOf` 定位
（`idxOf (f^k) = k-1`）+ `Nodup` 注入。 -/
theorem aq4_ndSpinePowNe (L : fgraph ℕ) {d : ℕ × ℕ}
    (hnd : (ndSpine L d).Nodup)
    (hsz : 2 ≤ (L.flatten.filter (fun t => decide (t = d.1))).length)
    {i j : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ (L.flatten.filter (fun t => decide (t = d.1))).length - 1)
    (hj1 : 1 ≤ j) (hj2 : j ≤ (L.flatten.filter (fun t => decide (t = d.1))).length - 1)
    (hij : i ≠ j) :
    (nList L)^[i] d ≠ (nList L)^[j] d := by
  intro heq
  have hdef : ndSpine L d = (List.range' 1 ((List.filter (fun t => decide (t = d.1))
      (List.flatten L)).length - 1)).map (fun k => (nList L)^[k] d) := rfl
  have hidx : ∀ (k : ℕ), 1 ≤ k → k ≤ (List.filter (fun t => decide (t = d.1))
      (List.flatten L)).length - 1 → (ndSpine L d).idxOf ((nList L)^[k] d) = k - 1 := by
    intro k hk1 hk2
    have hpos : k - 1 < (ndSpine L d).length := by
      rw [hdef, List.length_map, List.length_range']
      omega
    have hget : (ndSpine L d)[k - 1] = (nList L)^[k] d := by
      show ((List.range' 1 ((List.filter (fun t => decide (t = d.1))
        (List.flatten L)).length - 1)).map (fun j => (nList L)^[j] d))[k - 1]
        = (nList L)^[k] d
      rw [List.getElem_map, List.getElem_range']
      show (nList L)^[1 + 1 * (k - 1)] d = (nList L)^[k] d
      rw [show 1 + 1 * (k - 1) = k from by omega]
    rw [← hget]
    exact List.Nodup.idxOf_getElem hnd (k - 1) hpos
  have e : i - 1 = j - 1 := by
    rw [← hidx i hi1 hi2, ← hidx j hj1 hj2, heq]
  omega

/-- **A 块内前驱**：`2 ≤ i ≤ sz-1` 时 `prevEl new1 ((nList)^i d) = (nList)^(i-1) d`。
`new1 = P'.flatten ++ (block d ++ Q'.flatten)`（`List.append_of_mem`）；先 `nextEl new1 (f^(i-1)) = f^i`
（Cat1 绕前缀 + Cat2 入块 + `aq4_nextElNdSpine`），再 `prevEl_nextEl` 唯一性。 -/
theorem aq4_prevElNew1Interior (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {w : List (ℕ × ℕ)} {d : ℕ × ℕ} (hdw : d ∈ w)
    (hnd : ((w.map (ndSpine L)).flatten).Nodup)
    (hdDart : d ∈ (hypermapOfList L hL).darts)
    (h2 : 2 ≤ (L.flatten.filter (fun t => decide (t = d.1))).length)
    {i : ℕ} (hi1 : 2 ≤ i)
    (hi2 : i ≤ (L.flatten.filter (fun t => decide (t = d.1))).length - 1) :
    prevEl ((w.map (ndSpine L)).flatten) ((nList L)^[i] d) = (nList L)^[i - 1] d := by
  have hsz := h2
  have hblknd : (ndSpine L d).Nodup := aq1_ndSpineNodup L hL hgn hdDart h2
  have hblkne : ndSpine L d ≠ [] := ndSpineNeNil L d h2
  -- x = f^i d、y = f^(i-1) d
  have hxmem : (nList L)^[i] d ∈ ndSpine L d := by
    rw [show ndSpine L d = (List.range' 1 ((List.filter (fun t => decide (t = d.1))
        (List.flatten L)).length - 1)).map (fun k => (nList L)^[k] d) from rfl]
    rw [List.mem_map]
    exact ⟨i, by rw [List.mem_range']; exact ⟨i - 1, by omega, by omega⟩, rfl⟩
  have hymem : (nList L)^[i - 1] d ∈ ndSpine L d := by
    rw [show ndSpine L d = (List.range' 1 ((List.filter (fun t => decide (t = d.1))
        (List.flatten L)).length - 1)).map (fun k => (nList L)^[k] d) from rfl]
    rw [List.mem_map]
    exact ⟨i - 1, by rw [List.mem_range']; exact ⟨i - 2, by omega, by omega⟩, rfl⟩
  -- 块分解：blocks = P' ++ block d :: Q'
  have hblkmem : ndSpine L d ∈ w.map (ndSpine L) := List.mem_map.mpr ⟨d, hdw, rfl⟩
  obtain ⟨P', Q', hblocksP⟩ := List.append_of_mem hblkmem
  have hnew1eq2 : (w.map (ndSpine L)).flatten
      = (P'.flatten ++ ndSpine L d) ++ Q'.flatten := by
    rw [hblocksP]
    simp only [List.flatten_append, List.flatten_cons]
    rw [List.append_assoc]
  have hnew1nd2 : ((P'.flatten ++ ndSpine L d) ++ Q'.flatten).Nodup := hnew1eq2 ▸ hnd
  have hprefnd : (P'.flatten ++ ndSpine L d).Nodup :=
    List.Sublist.nodup (List.sublist_append_left _ _) hnew1nd2
  have hyne : (nList L)^[i - 1] d ≠ (ndSpine L d).getLast! := by
    intro hcon
    have hlast : (ndSpine L d).getLast! = (nList L)^[(List.filter (fun t => decide (t = d.1))
        (List.flatten L)).length - 1] d := lastNdSpine L d h2
    rw [hlast] at hcon
    exact aq4_ndSpinePowNe L hblknd hsz (by omega) (by omega) (by omega) (by omega)
      (by omega) hcon
  have hprefne : P'.flatten ++ ndSpine L d ≠ [] :=
    List.ne_nil_of_mem (List.mem_append_right P'.flatten hymem)
  -- nextEl new1 y = nextEl (block d) y
  have hstep1 : nextEl (w.map (ndSpine L)).flatten ((nList L)^[i - 1] d)
      = nextEl (P'.flatten ++ ndSpine L d) ((nList L)^[i - 1] d) := by
    rw [hnew1eq2]
    exact nextElCat1 hprefnd (List.mem_append_right P'.flatten hymem) (by
      rw [getLast!AppendRight _ _ hblkne]; exact hyne)
  have hstep2 : nextEl (P'.flatten ++ ndSpine L d) ((nList L)^[i - 1] d)
      = nextEl (ndSpine L d) ((nList L)^[i - 1] d) := by
    exact nextElCat2 hprefnd hymem hyne
  have hstep3 : nextEl (ndSpine L d) ((nList L)^[i - 1] d) = (nList L)^[i] d := by
    have := aq4_nextElNdSpine L hL hgn hdDart h2 (i := i - 1) (by omega) (by omega)
    rwa [show i - 1 + 1 = i from by omega] at this
  have hnext : nextEl (w.map (ndSpine L)).flatten ((nList L)^[i - 1] d) = (nList L)^[i] d := by
    rw [hstep1, hstep2, hstep3]
  have hymem' : (nList L)^[i - 1] d ∈ (w.map (ndSpine L)).flatten :=
    List.mem_flatten.mpr ⟨ndSpine L d, hblkmem, hymem⟩
  have hres : prevEl (w.map (ndSpine L)).flatten ((nList L)^[i] d) = (nList L)^[i - 1] d := by
    have := Kepler.Text.TameLp.prevEl_nextEl hnd hymem'
    rw [hnext] at this
    exact this
  exact hres

/-- **B 块边界前驱**：`w = P ++ d :: Q`、`P ≠ []`（即 `d ≠ head w`）⇒
`prevEl new1 ((ndSpine d).head!) = (ndSpine (prevEl w d)).getLast!`。
`nextEl new1 (last block(prevEl w d)) = head block d`（`aq4_nextElBlockLast`）+ `prevEl_nextEl`；
`prevEl w d = P.getLast!`（`nextElCatLast1` + `prevEl_nextEl`）。 -/
theorem aq4_prevElNew1BlockHead (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {w : List (ℕ × ℕ)} {d : ℕ × ℕ} {P Q : List (ℕ × ℕ)}
    (hwP : w = P ++ d :: Q) (hP : P ≠ [])
    (hndW : w.Nodup)
    (hnd : ((w.map (ndSpine L)).flatten).Nodup)
    (h2 : 2 ≤ (L.flatten.filter (fun t => decide (t = d.1))).length)
    (hblkne : ∀ e ∈ w, 2 ≤ (L.flatten.filter (fun t => decide (t = e.1))).length)
    (hblkDart : ∀ e ∈ w, e ∈ (hypermapOfList L hL).darts) :
    prevEl ((w.map (ndSpine L)).flatten) ((ndSpine L d).head!)
      = (ndSpine L (prevEl w d)).getLast! := by
  have hblkneD : ndSpine L d ≠ [] := ndSpineNeNil L d h2
  have hdW : d ∈ w := by rw [hwP]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hdprevW : P.getLast! ∈ w := by
    rw [hwP]
    exact List.mem_append_left (d :: Q) (aq4_getLastBangMem hP)
  have h2prev : 2 ≤ (L.flatten.filter (fun t => decide (t = P.getLast!.1))).length :=
    hblkne _ hdprevW
  have hblknePrev : ndSpine L P.getLast! ≠ [] := ndSpineNeNil L P.getLast! h2prev
  -- blocks 分解
  have hPdec : P = P.dropLast ++ [P.getLast!] := by
    rw [getLast!EqGetLast hP]
    exact (List.dropLast_append_getLast hP).symm
  have hPmap : P.map (ndSpine L)
      = (P.dropLast).map (ndSpine L) ++ [ndSpine L P.getLast!] := by
    conv_lhs => rw [hPdec]
    rw [List.map_append, List.map_cons, List.map_nil]
  have hblocksEq : w.map (ndSpine L)
      = ((P.dropLast).map (ndSpine L)) ++ (ndSpine L P.getLast!)
          :: (ndSpine L d :: Q.map (ndSpine L)) := by
    calc w.map (ndSpine L)
        = (P ++ d :: Q).map (ndSpine L) := by rw [hwP]
      _ = P.map (ndSpine L) ++ ndSpine L d :: Q.map (ndSpine L) := by
          rw [List.map_append, List.map_cons]
      _ = ((P.dropLast).map (ndSpine L) ++ [ndSpine L P.getLast!])
            ++ ndSpine L d :: Q.map (ndSpine L) := by rw [hPmap]
      _ = ((P.dropLast).map (ndSpine L)) ++ (ndSpine L P.getLast!)
            :: (ndSpine L d :: Q.map (ndSpine L)) := by
          rw [List.append_assoc]; rfl
  -- Q'' 各块非空
  have hQne : ∀ x ∈ (ndSpine L d :: Q.map (ndSpine L)), x ≠ [] := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hblkneD
    · obtain ⟨e, heQ, rfl⟩ := List.mem_map.mp hx
      have heW : e ∈ w := by rw [hwP]; exact List.mem_append_right _ (List.mem_cons_of_mem _ heQ)
      exact ndSpineNeNil L e (hblkne e heW)
  -- nextEl blocks.flatten (last block dprev) = head block d
  have hnextBlocks : nextEl (w.map (ndSpine L)).flatten (ndSpine L P.getLast!).getLast!
      = (ndSpine L d).head! := by
    have h := aq4_nextElBlockLast (blocks := w.map (ndSpine L))
      (P := (P.dropLast).map (ndSpine L)) (b := ndSpine L P.getLast!)
      (Q := ndSpine L d :: Q.map (ndSpine L)) hnd hblocksEq hblknePrev
      (List.ne_nil_of_mem (List.mem_cons_self ..)) hQne
    exact h
  -- prevEl w d = P.getLast!
  have hprevW : prevEl w d = P.getLast! := by
    have hnext : nextEl w P.getLast! = d := by
      rw [hwP]
      exact nextElCatLast1 (hwP ▸ hndW) hP (by simp)
    have h := Kepler.Text.TameLp.prevEl_nextEl hndW hdprevW
    rw [hnext] at h
    exact h
  -- 收口
  have hlastmem : (ndSpine L P.getLast!).getLast! ∈ (w.map (ndSpine L)).flatten := by
    exact List.mem_flatten.mpr ⟨ndSpine L P.getLast!,
      List.mem_map.mpr ⟨P.getLast!, hdprevW, rfl⟩,
      aq4_getLastBangMem hblknePrev⟩
  have h := Kepler.Text.TameLp.prevEl_nextEl hnd hlastmem
  rw [hnextBlocks] at h
  rw [hprevW]
  exact h

/-- **C 首块回卷**：`d = head w`（`w ≠ []`）⇒
`prevEl new1 ((ndSpine (w.head!)).head!) = new1.getLast!`
（`prevElLastHd`：首元的 prevEl 回卷到末元）。 -/
theorem aq4_prevElNew1FirstBlock (L : fgraph ℕ)
    {w : List (ℕ × ℕ)} (hne : w ≠ [])
    (hnd : ((w.map (ndSpine L)).flatten).Nodup)
    (hblkne : ∀ e ∈ w, 2 ≤ (L.flatten.filter (fun t => decide (t = e.1))).length) :
    prevEl ((w.map (ndSpine L)).flatten) ((ndSpine L (w.head!)).head!)
      = ((w.map (ndSpine L)).flatten).getLast! := by
  obtain ⟨d0, Q, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hd0ne : ndSpine L d0 ≠ [] := ndSpineNeNil L d0 (hblkne d0 (List.mem_cons_self ..))
  have hne1 : ((d0 :: Q).map (ndSpine L)).flatten ≠ [] :=
    List.ne_nil_of_mem (List.mem_flatten.mpr ⟨ndSpine L d0,
      List.mem_map.mpr ⟨d0, List.mem_cons_self .., rfl⟩, aq4_getLastBangMem hd0ne⟩)
  have hhead : ((d0 :: Q).map (ndSpine L)).flatten.head! = (ndSpine L d0).head! := by
    rw [List.map_cons, List.flatten_cons]
    exact List.head!_append _ hd0ne
  have h := prevElLastHd hnd hne1
  rw [hhead] at h
  exact h.trans (getLast!EqGetLast hne1).symm

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq4_ndSpinePowNe
#print axioms Kepler.Text.TameSpine.aq4_prevElNew1Interior
#print axioms Kepler.Text.TameSpine.aq4_prevElNew1BlockHead
#print axioms Kepler.Text.TameSpine.aq4_prevElNew1FirstBlock
