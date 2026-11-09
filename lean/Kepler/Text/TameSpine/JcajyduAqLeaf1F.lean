/-
  Kepler.Text.TameSpine.JcajyduAqLeaf1F — AQ1 叶第六批（收口）：
  `f1 × f2` 的互不交（弧恒等式的 ⊇ 半向 + 互补弧分离）。

  背景：`ntrans 1` 的 flatten 已由 Leaf1B 化成
  `(N₁.flatten ++ s2) ++ N₂.flatten ++ s1`，其中
  `s1 = new1.reverse ++ f1`（`split.1`）、`s2 = f2 ++ new2`（`split.2`），
  `f1 = [y1] ++ betwn r y1 z1 ++ [z1]`（`y1 = nextEl r y`、`z1 = prevEl r z`）、
  `f2 = [z] ++ betwn r z y ++ [y]`。六对互不交里五对 + `new1×new2` /
  `new1×f2` / `f1×new2` 已在 Leaf1/1B/1C/1D 就位；本批补最后一块 `f1 × f2`。

  路线（`aq1e_betwnSubset` 的对称件；**改用公开 `indexfBetwnEq` 弧判据**，
  省掉 `betwnTakeDrop` 的 take/drop 下标直算——路线勘误见 DELIVERY）：
  ① `y1`、`z1` 都在 `betwn r y z` 里；
  ② `betwn r y1 z1 ⊆ betwn r y z`：`indexfBetwnEq` + `indexfAddSum`
     （`indexf y y1 = 1`、`indexf z1 z = 1`）+ `indexfAddBetwn` + omega；
  ③ 互补弧分离 `betwn r y z ⊥ betwn r z y`（`indexfAddBetwn` ×4 +
     `indexfAntisym` ×3 + omega = `Reduction4.betwnDisjoint` 的局部重证，
     避免 TameSpine 反向 import）；
  ④ `f1 ⊥ f2`：⊆ 半向（②）+ `notBetwn1/2`（端点）。

  交付节奏：§1（件 1）/ §2-⊆ 半向 / §2-⊥（`f1×f2`）/ §3+§4（总装）四笔 patch
  增量交付，各笔自洽可独立落库；下件表为**总表**。

  ┌─ 件表 ────────────────────────────────────────────────────────────
  │ §1 件 1（零风险，可独立落库）：
  │   ① `aq1f_nextElMemBetwn`：`nextEl r y ≠ z → nextEl r y ∈ betwn r y z`；
  │   ② `aq1f_z1MemBetwn`（件 1 的 `z1` 侧支撑）：`nextEl r z1 = z` ⇒
  │      `z1 ∈ betwn r y z`；
  │   ③ `aq1f_betwnLenAdd`：`|betwn r y1 z1| + |betwn r z y| = |r| - 4`。
  │ §2 `f1 × f2`：
  │   ④ `aq1f_betwnSubBetwn`、⑤ `aq1f_f1SubBetwn`（⊇ 半向）、
  │   ⑥ `aq1f_disjBetwnComp`、⑦ `aq1f_f1DisjF2`（互不交）。
  └──────────────────────────────────────────────────────────────────

  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf1
import Kepler.Text.TameSpine.JcajyduAqLeaf1B
import Kepler.Text.TameSpine.JcajyduAqLeaf1C
import Kepler.Text.TameSpine.JcajyduAqLeaf1D
import Kepler.Text.TameSpine.JcajyduAqLeaf1E
import Kepler.Text.TameSpine.TameList72

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

/-! ## §0 私件：`indexf y1 z1` 与 `indexf y z1` 的差一步关系 -/

/-- 私件：`indexf (nextEl r y) z1 r = indexf y z1 r - 1`
（`y1` 是 `y` 的后继、`z1` 不是 `y1` 的前驱 ⇒ `y1` 不落在 `z1` 紧前）。
`indexfAddSum` 的界由「`indexf y1 z1 = len-1` ⇒ `indexf z1 y1 = 1` ⇒
`nextEl r z1 = y1` ⇒ `z = y1`（`hnext`）」反证。 -/
private theorem aq1f_indexfY1Z1 {r : List (ℕ × ℕ)} {y z z1 : ℕ × ℕ}
    (hrnd : r.Nodup) (hy : y ∈ r) (hz : z ∈ r) (hne : y ≠ z)
    (hz1r : z1 ∈ r) (hnext : nextEl r z1 = z) (hy1z : nextEl r y ≠ z)
    (hra : nextEl r y ≠ z1) :
    indexf (nextEl r y) z1 r = indexf y z1 r - 1 := by
  have hy1r : nextEl r y ∈ r := nextEl_mem_of_mem hy
  have hlen : 1 < r.length := sizelGt1 hy hz hne
  have hi1 : indexf y (nextEl r y) r = 1 := nextElIndexf hy hy1r hrnd rfl hlen
  have hneLast : indexf (nextEl r y) z1 r ≠ r.length - 1 := by
    intro h
    have hanti := indexfAntisym hy1r hz1r hra
    have h1 : indexf z1 (nextEl r y) r = 1 := by omega
    have h2 : nextEl r z1 = nextEl r y := indexfOne hz1r hy1r hrnd h1
    exact hy1z (by rw [← h2]; exact hnext)
  have hsum : indexf y (nextEl r y) r + indexf (nextEl r y) z1 r
      = indexf y z1 r :=
    indexfAddSum hy hy1r hz1r (by
      have := indexfLtSizel hy1r hz1r
      omega)
  omega

/-! ## §1 件 1：开弧端点成员性 + 弧长计数 -/

/-- **`nextEl r y ∈ betwn r y z`**（本树原先缺的开弧端点成员性）：
`y1 = nextEl r y` 是 `y` 的后继，只要 `y1 ≠ z` 就落在开弧 `betwn r y z` 内。
路线：`indexfBetwnEq`（公开弧判据）+ `nextElIndexf`（`indexf y y1 = 1`）+
`indexfOne`（`indexf y z = 1` 会给出 `y1 = z`）反证 + `indexfZeroEq`。 -/
theorem aq1f_nextElMemBetwn {r : List (ℕ × ℕ)} {y z : ℕ × ℕ}
    (hrnd : r.Nodup) (hy : y ∈ r) (hz : z ∈ r) (hne : y ≠ z)
    (hy1z : nextEl r y ≠ z) :
    nextEl r y ∈ between r y z := by
  have hy1r : nextEl r y ∈ r := nextEl_mem_of_mem hy
  have hlen : 1 < r.length := sizelGt1 hy hz hne
  have h1 : indexf y (nextEl r y) r = 1 := nextElIndexf hy hy1r hrnd rfl hlen
  have h2 : indexf y z r ≠ 1 := fun h => hy1z (indexfOne hy hz hrnd h)
  have h3 : indexf y z r ≠ 0 := fun h => hne (indexfZeroEq hy hz h)
  rw [indexfBetwnEq hne hrnd hy hz, h1]
  omega

/-- **`z1 ∈ betwn r y z`**（`z1 = prevEl r z`，以 `nextEl r z1 = z` 供入）：
`betwnCases` 四支——`z1 = y` 撞 `nextEl r y ≠ z`（`hnext` 折桥）、
`z1 = z` 撞 `nextElRefl`（`r = [z]` 与 `y ≠ z` 冲突）、
`z1 ∈ betwn r z y` 用 `indexfAntisym`（`indexf z1 z = 1`）挤爆右界。 -/
theorem aq1f_z1MemBetwn {r : List (ℕ × ℕ)} {y z z1 : ℕ × ℕ}
    (hrnd : r.Nodup) (hy : y ∈ r) (hz : z ∈ r) (hne : y ≠ z)
    (hz1r : z1 ∈ r) (hnext : nextEl r z1 = z) (hy1z : nextEl r y ≠ z) :
    z1 ∈ between r y z := by
  have hlen : 1 < r.length := sizelGt1 hy hz hne
  have hz1z : z1 ≠ z := by
    intro h
    have hsingle : r = [z] := nextElRefl hz (h ▸ hnext) hrnd
    rw [hsingle] at hy
    exact hne (by simpa using hy)
  rcases betwnCases hne hrnd hy hz1r hz with h | h | h | h
  · exact absurd (h ▸ hnext) hy1z
  · exact absurd h hz1z
  · exact h
  · have hb := indexfBetwn (Ne.symm hne) hrnd hz hy h
    have hidx : indexf z1 z r = 1 := nextElIndexf hz1r hz hrnd hnext hlen
    have hanti : indexf z1 z r + indexf z z1 r = r.length :=
      indexfAntisym hz1r hz hz1z
    have hlt := indexfLtSizel hz hy
    omega

/-- **弧长计数**：`|betwn r y1 z1| + |betwn r z y| = |r| - 4`
（`y1 = nextEl r y`、`z1 = prevEl r z`；`indexf` 计数形，供基数夹逼路线复用）。
`sizeBetwn` ×2 + `aq1f_indexfY1Z1` + `indexfAddBetwn` + `indexfAntisym` + omega。 -/
theorem aq1f_betwnLenAdd {r : List (ℕ × ℕ)} {y z z1 : ℕ × ℕ}
    (hrnd : r.Nodup) (hy : y ∈ r) (hz : z ∈ r) (hne : y ≠ z)
    (hz1r : z1 ∈ r) (hnext : nextEl r z1 = z) (hy1z : nextEl r y ≠ z)
    (hra : nextEl r y ≠ z1) :
    (between r (nextEl r y) z1).length + (between r z y).length
      = r.length - 4 := by
  have hy1r : nextEl r y ∈ r := nextEl_mem_of_mem hy
  have hlen : 1 < r.length := sizelGt1 hy hz hne
  have hz1mem : z1 ∈ between r y z :=
    aq1f_z1MemBetwn hrnd hy hz hne hz1r hnext hy1z
  have hz1z : indexf z1 z r = 1 := nextElIndexf hz1r hz hrnd hnext hlen
  have hidx : indexf (nextEl r y) z1 r = indexf y z1 r - 1 :=
    aq1f_indexfY1Z1 hrnd hy hz hne hz1r hnext hy1z hra
  have hsz1 : (between r (nextEl r y) z1).length = indexf (nextEl r y) z1 r - 1 :=
    sizeBetwn hrnd hy1r hz1r hra
  have hsz2 : (between r z y).length = indexf z y r - 1 :=
    sizeBetwn hrnd hz hy (Ne.symm hne)
  have hadd1 : indexf y z1 r + indexf z1 z r = indexf y z r :=
    indexfAddBetwn hne hrnd hy hz1mem hz
  have hanti2 : indexf y z r + indexf z y r = r.length :=
    indexfAntisym hy hz hne
  have hpos : 0 < indexf y z1 r := (indexfBetwn hne hrnd hy hz hz1mem).1
  have hpos2 : 0 < indexf (nextEl r y) z1 r := by
    rcases Nat.eq_zero_or_pos (indexf (nextEl r y) z1 r) with h0 | h
    · exact absurd (indexfZeroEq hy1r hz1r h0) hra
    · exact h
  have hpos3 : 0 < indexf z y r := by
    rcases Nat.eq_zero_or_pos (indexf z y r) with h0 | h
    · exact absurd (indexfZeroEq hz hy h0).symm hne
    · exact h
  omega

/-! ## §2 `f1 × f2`：⊇ 半向 + 互补弧分离 -/

/-- **`betwn r y1 z1 ⊆ betwn r y z`**（弧恒等式的中间段）：`indexfBetwnEq`
双向 + 两条加法桥（`indexf y y1 = 1`、`indexf z1 z = 1`）+ omega。 -/
theorem aq1f_betwnSubBetwn {r : List (ℕ × ℕ)} {y z z1 : ℕ × ℕ}
    (hrnd : r.Nodup) (hy : y ∈ r) (hz : z ∈ r) (hne : y ≠ z)
    (hz1r : z1 ∈ r) (hnext : nextEl r z1 = z) (hy1z : nextEl r y ≠ z)
    (hra : nextEl r y ≠ z1) :
    between r (nextEl r y) z1 ⊆ between r y z := by
  intro d hd
  have hy1r : nextEl r y ∈ r := nextEl_mem_of_mem hy
  have hdmem : d ∈ r := betwnMem hd
  have hlen : 1 < r.length := sizelGt1 hy hz hne
  have hz1mem : z1 ∈ between r y z :=
    aq1f_z1MemBetwn hrnd hy hz hne hz1r hnext hy1z
  have hz1z : indexf z1 z r = 1 := nextElIndexf hz1r hz hrnd hnext hlen
  have hi1 : indexf y (nextEl r y) r = 1 := nextElIndexf hy hy1r hrnd rfl hlen
  have hidx : indexf (nextEl r y) z1 r = indexf y z1 r - 1 :=
    aq1f_indexfY1Z1 hrnd hy hz hne hz1r hnext hy1z hra
  have hb := indexfBetwn hra hrnd hy1r hz1r hd
  have hb1 : 0 < indexf y z1 r := (indexfBetwn hne hrnd hy hz hz1mem).1
  have hadd1 : indexf y z1 r + indexf z1 z r = indexf y z r :=
    indexfAddBetwn hne hrnd hy hz1mem hz
  have hsum1 : indexf y (nextEl r y) r + indexf (nextEl r y) d r
      = indexf y d r :=
    indexfAddSum hy hy1r hdmem (by
      have := indexfLtSizel hy1r hz1r
      omega)
  rw [indexfBetwnEq hne hrnd hy hz]
  constructor <;> omega

/-- **`f1 ⊆ betwn r y z`**（弧恒等式的 ⊇ 全段；`f1` 三段逐段）：
`y1 ∈ betwn`（`aq1f_nextElMemBetwn`）、`betwn y1 z1 ⊆ betwn`（上件）、
`z1 ∈ betwn`（`aq1f_z1MemBetwn`）。 -/
theorem aq1f_f1SubBetwn {r : List (ℕ × ℕ)} {y z z1 : ℕ × ℕ}
    (hrnd : r.Nodup) (hy : y ∈ r) (hz : z ∈ r) (hne : y ≠ z)
    (hz1r : z1 ∈ r) (hnext : nextEl r z1 = z) (hy1z : nextEl r y ≠ z)
    (hra : nextEl r y ≠ z1) :
    ∀ d ∈ ([nextEl r y] ++ between r (nextEl r y) z1) ++ [z1],
      d ∈ between r y z := by
  intro d hd
  rcases List.mem_append.mp hd with h | h
  · rcases List.mem_append.mp h with h1 | h1
    · rw [List.mem_singleton] at h1
      subst h1
      exact aq1f_nextElMemBetwn hrnd hy hz hne hy1z
    · exact aq1f_betwnSubBetwn hrnd hy hz hne hz1r hnext hy1z hra h1
  · rw [List.mem_singleton] at h
    subst h
    exact aq1f_z1MemBetwn hrnd hy hz hne hz1r hnext hy1z

/-- **互补弧分离 `betwn r y z ⊥ betwn r z y`**
（`Kepler.Text.Reduction4.betwnDisjoint` 的局部重证；TameSpine 不得反向
import Reduction4）：设 `e = d`，`indexfAddBetwn` ×2 给
`a + b = indexf y z`、`c + a' = indexf z y`，`indexfAntisym` ×3 给
`a + a' = c + b = indexf y z + indexf z y = |r|` ⇒ `b + c = 0`，
与 `0 < b`、`0 < c` 冲突。 -/
theorem aq1f_disjBetwnComp {r : List (ℕ × ℕ)} {y z : ℕ × ℕ}
    (hrnd : r.Nodup) (hy : y ∈ r) (hz : z ∈ r) (hne : y ≠ z) :
    ∀ d ∈ between r y z, ∀ e ∈ between r z y, d ≠ e := by
  intro d hd e he hde
  rw [← hde] at he
  have hdm : d ∈ r := betwnMem hd
  have h1 : indexf y d r + indexf d z r = indexf y z r :=
    indexfAddBetwn hne hrnd hy hd hz
  have h2 : indexf z d r + indexf d y r = indexf z y r :=
    indexfAddBetwn (Ne.symm hne) hrnd hz he hy
  have h3 : indexf y d r + indexf d y r = r.length :=
    indexfAntisym hy hdm (fun h => notBetwn1 hrnd hz (h ▸ hd))
  have h4 : indexf z d r + indexf d z r = r.length :=
    indexfAntisym hz hdm (fun h => notBetwn2 hrnd (h ▸ hd))
  have h5 : indexf y z r + indexf z y r = r.length :=
    indexfAntisym hy hz hne
  have h6 : 0 < indexf y d r := (indexfBetwn hne hrnd hy hz hd).1
  have h7 : 0 < indexf z d r := (indexfBetwn (Ne.symm hne) hrnd hz hy he).1
  omega

/-- **`f1 ⊥ f2`**（六对互不交的最后一块）：`f1 ⊆ betwn r y z`，
`f2 = [z] ++ betwn r z y ++ [y]` 的中间段由互补弧分离排掉，两端点由
`notBetwn2`（`z`）/`notBetwn1`（`y`）排掉。 -/
theorem aq1f_f1DisjF2 {r : List (ℕ × ℕ)} {y z z1 : ℕ × ℕ}
    (hrnd : r.Nodup) (hy : y ∈ r) (hz : z ∈ r) (hne : y ≠ z)
    (hz1r : z1 ∈ r) (hnext : nextEl r z1 = z) (hy1z : nextEl r y ≠ z)
    (hra : nextEl r y ≠ z1) :
    ∀ d ∈ ([nextEl r y] ++ between r (nextEl r y) z1) ++ [z1],
      ∀ e ∈ ([z] ++ between r z y) ++ [y], d ≠ e := by
  intro d hd e he hde
  have hdmem : d ∈ between r y z :=
    aq1f_f1SubBetwn hrnd hy hz hne hz1r hnext hy1z hra d hd
  rcases List.mem_append.mp he with h | h
  · rcases List.mem_append.mp h with h1 | h1
    · rw [List.mem_singleton] at h1
      exact notBetwn2 hrnd (h1 ▸ (hde ▸ hdmem))
    · exact aq1f_disjBetwnComp hrnd hy hz hne d hdmem e h1 hde
  · rw [List.mem_singleton] at h
    exact notBetwn1 hrnd hz (h ▸ (hde ▸ hdmem))

/-! ## §3 总装件：四段拼接的 Nodup -/

/-- 私件：四段 `((A ++ B) ++ C) ++ D` 的 Nodup（`nodup_append` 三层 +
六对互不交；六对来自 `aq1c_disjOfDich` 五对 + `f1×f2` 一对）。 -/
private theorem aq1f_nodup4 {α : Type*} {A B C D : List α}
    (hA : A.Nodup) (hB : B.Nodup) (hC : C.Nodup) (hD : D.Nodup)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a ≠ b) (hAC : ∀ a ∈ A, ∀ c ∈ C, a ≠ c)
    (hBC : ∀ b ∈ B, ∀ c ∈ C, b ≠ c) (hAD : ∀ a ∈ A, ∀ d ∈ D, a ≠ d)
    (hBD : ∀ b ∈ B, ∀ d ∈ D, b ≠ d) (hCD : ∀ c ∈ C, ∀ d ∈ D, c ≠ d) :
    ((A ++ B) ++ C ++ D).Nodup := by
  rw [List.nodup_append]
  refine ⟨?_, hD, ?_⟩
  · rw [List.nodup_append]
    refine ⟨List.nodup_append.mpr ⟨hA, hB, hAB⟩, hC, ?_⟩
    intro x hx c hc
    rcases List.mem_append.mp hx with h | h
    · exact hAC x h c hc
    · exact hBC x h c hc
  · intro x hx d hd
    rcases List.mem_append.mp hx with h | h
    · rcases List.mem_append.mp h with h1 | h1
      · exact hAD x h1 d hd
      · exact hBD x h1 d hd
    · exact hCD x h d hd

/-! ## §4 `aq1` 总装（HOL `AQ1`，AQ1.hl:2153-:2201） -/

/-- **HOL `AQ1_concl`**（AQ1.hl:2147）真证：`uniq (flatten (ntrans L N r x 1))`。
final 支 = `ntransId` + `normal_list` 合取 1；¬final 支 = `aq1b_flattenNtrans1`
的切口形 `(N₁.flatten ++ s2) ++ N₂.flatten ++ s1`，Nodup 由
`aq1f_nodup4` 收口（s2 的 Nodup = `hsndClean`、s1 = `aq1_split1Nodup`、
五对 = `aq1c_disjOfDich`、`s1 × s2` 四子对 = `aq1d_new1DisjNew2` /
`aq1c_new1DisjF2` / `aq1c_f1DisjNew2` / `aq1f_f1DisjF2`）。 -/
theorem aq1 (L : fgraph ℕ) (hL : GoodList L) : aq1Concl L hL := by
  intro N r x hgn hm
  -- `aq1Concl` 无 `all uniq L` 槽：由 `IsRestricted.simple` + `simple ↔ all uniq` 现取
  have hunL : ∀ l ∈ L, l.Nodup := (simpleHypermapUniq L hL hgn).mp hm.1.1.simple
  by_cases hfin : finalListSpine L r
  · rw [ntransId L N r x hfin]
    exact hm.1.2.1.1
  · obtain ⟨N₁, N₂, hN, hnot, hflat⟩ :=
      aq1b_flattenNtrans1 L hL hgn hunL hm hfin
    rw [hflat]
    obtain ⟨hfN1, hfN2, hdisj1r, hdisj2r, hdisj12⟩ :=
      aq1c_flattenParts hm.1.2.1.1 hN
    have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
    have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hfin
    have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hfin
    have hyne : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hfin
    have hz1r : prevEl r (lZSpine L N r x) ∈ r := prevEl_mem_of_mem hzr
    have hnextz1 : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
      nextElPrevElUniq hrnd _
    have hra : nextEl r (lYSpine L r x) ≠ prevEl r (lZSpine L N r x) :=
      aq1_nextElYNePrevElZ L hL hgn hunL hm hfin
    have hy1z : nextEl r (lYSpine L r x) ≠ lZSpine L N r x :=
      aq1_nextElYNeZ L hL hgn hunL hm hfin
    -- `s1` / `s2` 的分段展开
    have hs1eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).1
        = (((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
              (lZSpine L N r x)).map (ndSpine L)).flatten).reverse
          ++ ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
              (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]) := by
      rw [split1Unfold L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (prevEl r (lZSpine L N r x)), hnextz1]
    have hs2eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).2
        = ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
            ++ [lYSpine L r x])
          ++ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
              (lZSpine L N r x) := by
      simp only [splitNormalListSpine]
      rw [hnextz1]
    -- `N₁` / `N₂` 的 flatten 落回 `N.flatten`
    have hN1sub : ∀ d ∈ N₁.flatten, d ∈ N.flatten := by
      intro d hd
      obtain ⟨l, hl, hdl⟩ := List.mem_flatten.mp hd
      exact List.mem_flatten.mpr ⟨l, by rw [hN]; exact List.mem_append_left _ hl, hdl⟩
    have hN2sub : ∀ d ∈ N₂.flatten, d ∈ N.flatten := by
      intro d hd
      obtain ⟨l, hl, hdl⟩ := List.mem_flatten.mp hd
      exact List.mem_flatten.mpr
        ⟨l, by rw [hN]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hl), hdl⟩
    -- 六对互不交（A = N₁.flatten、B = s2、C = N₂.flatten、D = s1）
    have hAB : ∀ a ∈ N₁.flatten,
        ∀ b ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).2, a ≠ b := by
      intro a ha b hb
      exact Ne.symm (aq1c_disjOfDich (A := (splitNormalListSpine L r
          (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (prevEl r (lZSpine L N r x))).2) (B := N₁.flatten) (r := r)
          (M := N.flatten) (fun d hd => aq1b_split2Mem L hL hgn hunL hm hfin hd) hN1sub hdisj1r
          b hb a ha)
    have hAC : ∀ a ∈ N₁.flatten, ∀ b ∈ N₂.flatten, a ≠ b := by
      intro a ha b hb hab
      exact hdisj12 a ha (hab ▸ hb)
    have hBC : ∀ a ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).2,
        ∀ b ∈ N₂.flatten, a ≠ b := by
      intro a ha b hb
      exact aq1c_disjOfDich (A := (splitNormalListSpine L r
          (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (prevEl r (lZSpine L N r x))).2) (B := N₂.flatten) (r := r)
          (M := N.flatten) (fun d hd => aq1b_split2Mem L hL hgn hunL hm hfin hd) hN2sub hdisj2r
          a ha b hb
    have hAD : ∀ a ∈ N₁.flatten,
        ∀ b ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).1, a ≠ b := by
      intro a ha b hb
      exact Ne.symm (aq1c_disjOfDich (A := (splitNormalListSpine L r
          (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (prevEl r (lZSpine L N r x))).1) (B := N₁.flatten) (r := r)
          (M := N.flatten) (fun d hd => aq1b_split1Mem L hL hgn hunL hm hfin hd) hN1sub hdisj1r
          b hb a ha)
    have hCD : ∀ a ∈ N₂.flatten,
        ∀ b ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).1, a ≠ b := by
      intro a ha b hb
      exact Ne.symm (aq1c_disjOfDich (A := (splitNormalListSpine L r
          (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (prevEl r (lZSpine L N r x))).1) (B := N₂.flatten) (r := r)
          (M := N.flatten) (fun d hd => aq1b_split1Mem L hL hgn hunL hm hfin hd) hN2sub hdisj2r
          b hb a ha)
    have hBD : ∀ a ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).2,
        ∀ b ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).1, a ≠ b := by
      intro a ha b hb
      rw [hs2eq] at ha
      rw [hs1eq] at hb
      rcases List.mem_append.mp ha with ha' | ha'
      · rcases List.mem_append.mp hb with hb' | hb'
        · exact Ne.symm (aq1c_new1DisjF2 L hL hgn hunL hm hfin b
            (List.mem_reverse.mp hb') a ha')
        · exact Ne.symm (aq1f_f1DisjF2 hrnd hyr hzr hyne hz1r hnextz1 hy1z hra
            b hb' a ha')
      · rcases List.mem_append.mp hb with hb' | hb'
        · exact Ne.symm (aq1d_new1DisjNew2 L hL hgn hunL hm hfin b
            (List.mem_reverse.mp hb') a ha')
        · exact Ne.symm (aq1c_f1DisjNew2 L hL hgn hunL hm hfin b hb' a ha')
    exact aq1f_nodup4 hfN1 (hsndClean L hL hgn hunL hm hfin) hfN2
      (aq1_split1Nodup L hL hgn hunL hm hfin) hAB hAC hBC hAD hBD hCD

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq1f_nextElMemBetwn
#print axioms Kepler.Text.TameSpine.aq1f_z1MemBetwn
#print axioms Kepler.Text.TameSpine.aq1f_betwnLenAdd
#print axioms Kepler.Text.TameSpine.aq1f_betwnSubBetwn
#print axioms Kepler.Text.TameSpine.aq1f_f1SubBetwn
#print axioms Kepler.Text.TameSpine.aq1f_disjBetwnComp
#print axioms Kepler.Text.TameSpine.aq1f_f1DisjF2
#print axioms Kepler.Text.TameSpine.aq1
