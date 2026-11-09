/-
  JcajyduAqLeaf8W0 — AQ8 波 0：五件共享地基（HOL AQ8.hl:386/144/1617/276/48）。

  ┌─ 件目与 HOL 锚 ───────────────────────────────────────────────
  │ ① MEM_PARTS_IMP      AQ8.hl:386  → memPartsImp（parts 成员回落到 r）
  │ ② next_cat_betwn_same AQ8.hl:144 → nextCatBetwnSame（后缀在同弧上的 next_el）
  │ ③ flatten_rev        AQ8.hl:1617 → flattenRev（纯列表泛型引理）
  │ ④ indexf_eq_in_parts AQ8.hl:276  → indexfEqInParts（part 内 indexf 降为 idxOf）
  │ ⑤ snd_mem_rtran1     AQ8.hl:48   → sndMemRtran1（split 后半段进 ntrans 步 1）
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算；语义逐字对齐消费点）───────────────────────────
  │ ① `uniq r` ↦ `r.Nodup`；`MEM p (parts L r)` ↦ `p ∈ partsSpine L r`
  │    （链 parts 与 Spine partsSpine 为镜像；W0 统一取 Spine 面）。
  │ ② `next_cat_betwn_same` HOL 为泛型 `!r y z a s`（任意 dart 类型）；
  │    本件取 Dart 专用形（`List (ℕ × ℕ)`），载体重用 AQ10-b1 的
  │    `aq10_nextElPrefix`（其内部走 Dart 专用 `nextElCat1/2/Last1`）。
  │    AQ8 的消费点全为 Dart，语义零损失；泛型化留待有消费需求时再开。
  │ ③ `normal_list L N` ↦ `NormalListSpine hL N`（`r ∈ N` 由 HOL
  │    normal_list 的合取项给出；本件按条件槽风格显式入参 `hrN : r ∈ N`）。
  │ ④ HOL `indexl x p` ↦ `p.idxOf x`；HOL `HD p` ↦ `p.head!`。
  │ ⑤ `snd_mem_rtran1` 的 HOL 前件 `marked_list L N r x` 在 Lean 侧只用到
  │    `r ∈ N`（其余标记槽本件不消费），故显式入参 `hrN : r ∈ N` +
  │    `hnf : ¬ finalListSpine L r`（条件槽形，供 AQ8 后续直接喂）。
  └────────────────────────────────────────────────────────────────

  ┌─ 依赖（均已落库，零新定义/零新公理）──────────────────────────
  │ partsFlatten/partsUniq/partsAllNonnil（TameList9）、
  │ nextElPartsPower/indexfHd（TameList10）、indexfN/nextElnIndexf
  │ （TameList3）、normalListUniqNonnil（TameList6）、
  │ transformListSpine/ntransSpine/splitNormalListSpine/finalListSpine
  │ （TameList17）、aq10_nextElPrefix（JcajyduAqLeaf10F，已落库 443696fe）。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件驼峰无前缀，私件 `aq8w0_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf10F
import Kepler.Text.TameSpine.TameList17
import Kepler.Text.TameSpine.TameList10
import Kepler.Text.TameSpine.TameList9
import Kepler.Text.TameSpine.TameList6
import Kepler.Text.TameSpine.TameList3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl fList findFaceDarts GoodList)

/-! ## §0 `flatten_rev`（HOL AQ8.hl:1617，纯列表泛型）

HOL 原式 `flatten(rev (map (rev o f) r)) = rev(flatten (map f r))`。
Lean 侧 `rev ↦ List.reverse`、`flatten ↦ List.flatten`、`rev o f ↦
fun a => (f a).reverse`；对 `r` 归纳，`reverse_cons`/`flatten_append`/
`flatten_cons`/`reverse_append` 四段收口，无任何列表载体限定。 -/
theorem flattenRev {α β : Type} (r : List α) (f : α → List β) :
    ((r.map fun a => (f a).reverse).reverse).flatten =
      ((r.map f).flatten).reverse := by
  induction r with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons, List.reverse_cons, List.flatten_append, List.flatten_cons,
      List.flatten_nil, List.append_nil, ih]
    rw [List.map_cons, List.flatten_cons, List.reverse_append]

/-! ## §1 `MEM_PARTS_IMP`（HOL AQ8.hl:386）

`uniq r ∧ r ≠ [] ∧ p ∈ parts L r ⇒ ∀ a ∈ p, a ∈ r`。
HOL 证走 `parts_flatten` 一次改写 + `mem_flatten` 存在量化；Lean 侧同路，
`partsFlatten L hun hne : (partsSpine L r).flatten = r`。 -/
theorem memPartsImp (L : fgraph ℕ) {r p : List (ℕ × ℕ)} (hun : r.Nodup)
    (hne : r ≠ []) (hp : p ∈ partsSpine L r) : ∀ a ∈ p, a ∈ r := by
  intro a ha
  have hflat : (partsSpine L r).flatten = r := partsFlatten L hun hne
  have hmem : a ∈ (partsSpine L r).flatten := List.mem_flatten.mpr ⟨p, hp, ha⟩
  rwa [hflat] at hmem

/-! ## §2 `next_cat_betwn_same`（HOL AQ8.hl:144）

`uniq r ∧ y ∈ r ∧ z ∈ r ∧ y ≠ z ∧ a ∈ s ∧
s = [z] ++ (betwn r z y ++ [y]) ∧ a ≠ y ⇒ next_el s a = next_el r a`。
Dart 专用形：直接调 AQ10-b1 的 `aq10_nextElPrefix`（该件已覆盖
左端点/内部/末元三支）；本件只做 `s` 消去 + 结合律对齐。 -/
theorem nextCatBetwnSame (r : List (ℕ × ℕ)) {y z a : ℕ × ℕ} {s : List (ℕ × ℕ)}
    (hnd : r.Nodup) (hy : y ∈ r) (hz : z ∈ r) (hyz : y ≠ z) (ha : a ∈ s)
    (hs : s = [z] ++ (between r z y ++ [y])) (hay : a ≠ y) :
    nextEl s a = nextEl r a := by
  subst hs
  rw [← List.append_assoc] at ha ⊢
  exact aq10_nextElPrefix r hnd hz hy hyz.symm ha hay

/-! ## §3 `indexf_eq_in_parts`（HOL AQ8.hl:276）

`normal_list L N ∧ r ∈ N ∧ x ∈ p ∧ p ∈ parts L r ⇒
indexf (HD p) x r = indexl x p`。
HOL 路线：`next_eln_indexf`（r 侧）+ `next_el_parts_power`（i = indexl x p、
基元 HD p）+ `indexf_indexl_hd`/`indexf_n`（p 侧）。Lean 侧同构：
`nextElPartsPower L hrun hrne hp hhead (p.idxOf x)` 把 r 侧幂桥到 p 侧，
`indexfN`（经 `indexfHd` 换装）给出 p 侧终点 = x，再以 `nextElnIndexf`
在 r 侧读出 `indexf = p.idxOf x`。长度槽 `p.idxOf x < r.length` 由
`subperm_of_subset` + `Subperm.length_le`（p ⊆ r 且 p 无重）取得。 -/
theorem indexfEqInParts (L : fgraph ℕ) {hL : GoodList L} {N : List (List (ℕ × ℕ))}
    {r p : List (ℕ × ℕ)} {x : ℕ × ℕ} (hn : NormalListSpine hL N) (hrN : r ∈ N)
    (hx : x ∈ p) (hp : p ∈ partsSpine L r) :
    indexf p.head! x r = p.idxOf x := by
  obtain ⟨hrun, hrne⟩ := normalListUniqNonnil hn hrN
  have hpun : p.Nodup := partsUniq L hrun hrne p hp
  have hpne : p ≠ [] := partsAllNonnil L hrun hrne p hp
  have hhead : p.head! ∈ p := List.head!_mem_self hpne
  have hxr : x ∈ r := memPartsImp L hrun hrne hp x hx
  have hheadr : p.head! ∈ r := memPartsImp L hrun hrne hp p.head! hhead
  -- 长度槽：p ⊆ r 且 p 无重 ⇒ p 是 r 的子置换 ⇒ 长度不增
  have hsub : List.Subperm p r :=
    List.subperm_of_subset hpun (fun a ha => memPartsImp L hrun hrne hp a ha)
  have hlen : p.length ≤ r.length := List.Subperm.length_le hsub
  have hidxlt : p.idxOf x < p.length := List.idxOf_lt_length_iff.mpr hx
  have hlt : p.idxOf x < r.length := Nat.lt_of_lt_of_le hidxlt hlen
  -- HOL next_el_parts_power：i = indexl x p，基元 = HD p
  have hpow : (nextEl r)^[p.idxOf x] p.head! = (nextEl p)^[p.idxOf x] p.head! :=
    nextElPartsPower L hrun hrne hp hhead (p.idxOf x) (by
      have h0 : p.idxOf p.head! = 0 := indexHd0 hpne
      omega)
  -- p 侧：indexf_n 经 indexf_indexl_hd 换装为 idxOf 幂
  have hpn : (nextEl p)^[p.idxOf x] p.head! = x := by
    have h := indexfN hhead hx hpun
    rwa [indexfHd hx] at h
  have hrn : (nextEl r)^[p.idxOf x] p.head! = x := by rw [hpow, hpn]
  exact nextElnIndexf hheadr hxr hrun hrn hlt

/-! ## §4 `snd_mem_rtran1`（HOL AQ8.hl:48）

`…marked ∧ ¬final_list ⇒ MEM (SND (split_normal_list ...)) (ntrans … 1)`。
条件槽形：只取 `hrN : r ∈ N`（marked_list 的合取项）与 `¬ finalListSpine`。
`ntransSpine … 1` 展开 = `(transformListSpine … (N,r)).1`，非终态支为
`replaceSpine r [split.2] N ++ [split.1]`；命中段 `replaceSpine r [split.2] N`
在 `r ∈ N` 下吸收 `split.2`（`MEM2_replace` 的 replaceSpine 版，私件）。 -/

/-- 私件（HOL `MEM2_replace` 的 replaceSpine 版，tame_list.hl:566）：
命中元素被替换段吸收。 -/
private theorem aq8w0_memReplaceSpineOfMem {α : Type} [DecidableEq α] {z x : α}
    {ys xs : List α} (hz : z ∈ xs) (hx : x ∈ ys) : x ∈ replaceSpine z ys xs := by
  induction xs with
  | nil => exact absurd hz (by simp)
  | cons a t ih =>
    rw [replaceSpine]
    by_cases haz : a = z
    · rw [if_pos haz]
      exact List.mem_append.mpr (Or.inl hx)
    · rw [if_neg haz]
      rcases List.mem_cons.mp hz with h | h
      · exact absurd h.symm haz
      · exact List.mem_cons_of_mem _ (ih h)

/-- HOL `snd_mem_rtran1`（AQ8.hl:48）的条件槽形。 -/
theorem sndMemRtran1 (L : fgraph ℕ) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hrN : r ∈ N) (hnf : ¬ finalListSpine L r) :
    (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (prevEl r (lZSpine L N r x))).2 ∈ ntransSpine L N r x 1 := by
  unfold ntransSpine
  rw [Function.iterate_one]
  unfold transformListSpine
  dsimp only
  rw [if_neg hnf]
  exact List.mem_append.mpr
    (Or.inl (aq8w0_memReplaceSpineOfMem hrN (List.mem_singleton_self _)))

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：五件全标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.flattenRev
#print axioms Kepler.Text.TameSpine.memPartsImp
#print axioms Kepler.Text.TameSpine.nextCatBetwnSame
#print axioms Kepler.Text.TameSpine.indexfEqInParts
#print axioms Kepler.Text.TameSpine.sndMemRtran1
