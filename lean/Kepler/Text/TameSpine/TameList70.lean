/-
  Kepler.Text.TameSpine.TameList70 — B3 D 链第十一批：DANGEYJ.hl §1-§3 基础件
  （HOL 对账段：DANGEYJ.hl :25-:363；接续批 69 = TameList69.lean 615 行，
  md5 34a14cd1d2eed429b970c1fb2eb6cf7a）。本批 = split_at/indexl 自足族 +
  首个 betwn-nextEl 桥；批 71 起点 = DANGEYJ.hl :365 APPEND_FST_SPLIT。

  ┌─ 本批战绩小结 ────────────────────────────────────────────────
  │ 落点：20 声明（16 公开定理 + 4 枚私有辅件），零 sorry、零 axiom
  │ 声明；`lake build Kepler.Text.TameSpine.TameList70` 9502 jobs 全绿
  │ （clone /tmp/p4t21，单发串行、零旗标、零 -K）。
  │ axiom 探针 16/16 全公开件零 sorryAx：10 件标准三
  │ [propext, Classical.choice, Quot.sound]、4 件 [propext]
  │ （not_mem_split_at_rec / not_mem_split_at / not_betwn / betwn_sing1）、
  │ 2 件无公理（fst_fun / fst_snd_fun）；快照 t70_axiom_audit.log 全文。
  │
  │ §1 基础小件（:25-:67）：transform_list_power_rep（批 17 transform 定义层
  │ 的 POWER 迭代形）/ not_mem_split_at_rec / not_mem_split_at（
  │ ListAuxLemmas splitAtRec_notRam / splitAt_no_ram 直投）/ not_betwn /
  │ fst_fun / fst_snd_fun（λ 投影 rfl）。
  │ §2 betwn/membership/indexl 族（:72-:193）：not_in_mem_betwn /
  │ in_uniq_betwn（set_between_id）/ SND_SPLIT_SING / betwn_sing1 /
  │ snd_split_at_rec_const（TameList3 sndSplitAtAcc 双发）/ SND_EMPTY_INDEXL /
  │ HD_FST_SPLIT_AT_REC（TameList3 fstSplitAtAcc + head!_append）/
  │ INDEXL_SND_EMPTY / INDEXL_EQ_SND_EMPTY。
  │ §3 HD_BETWN1（:198-:363）：首个 betwn-nextEl 桥——
  │ between r r1 r1 = post ++ pre 的循环移位形 + splitAt 位置的 idxOf 换算
  │ 收 nextEl 的两分支（post=[] 时 headD 回绕到 pre.head!）。
  └──────────────────────────────────────────────────────────────

  载体折算（沿批 3/17 约定）：`betwn` ↦ `Kepler.Graphs.between`、
  `split_at_rec`/`split_at` ↦ `Kepler.Graphs.splitAtRec`/`splitAt`、
  `uniq` ↦ `List.Nodup`、`indexl` ↦ `List.idxOf`、`sizel` ↦ `List.length`、
  `next_el` ↦ `Kepler.Assembly.nextEl`、`HD` ↦ `List.head!`（配
  `[Inhabited α]` 载体伪参）、`FST`/`SND` ↦ `Prod.fst`/`Prod.snd`、
  `POWER n` ↦ `Function.iterate n`。

  诚实强化/记账：
  - 载体 `Kepler.Graphs.splitAtRec`/`between` 按 `[BEq α]` 定义，本批定理
    统一携带 `[BEq α] [LawfulBEq α]`（与批 3 TameList3 同约定；HOL 的
    Leibniz 等式在 LawfulBEq 下保真）。`fst_fun`/`fst_snd_fun` 与
    `transform_list_power_rep` 不涉 BEq，无此约束。
  - `in_uniq_betwn` 的 HOL 证词消费 `split_at_snd/fst_antirefl`；
    Lean 侧一律经 `set_between_id`（ListAuxLemmas）一步收，语句不动。
  - `between_self_eq`（私件）的语句不需要 `MEM r1 r`（r1 ∉ r 时两边同为
    r = [] ++ r），签名保留 h1 以对账 HOL 前提形状，证体零消费。

  新雷区（本批实测记档，编号承批 69 的 #183）：
  - #184 `rw [splitAt_ram h]` 的目标若同时含 `r.idxOf r1` 与
    `(splitAt r1 r).1.length` 类项，`rw` 会把 `splitAt r1 r` 参数里的 `r`
    也重写，生成嵌套 `splitAt r1 (pre ++ r1 :: post)`，omega/rfl 全部失配。
    正确姿势：先 `set pre := (splitAt r1 r).1` / `set post := ...` 把
    splitAt 项全抽象成局部定义，再 `rw [hram]`（本批 idxOf_splitAt /
    splitAt_lengths 两处实测）。
  - #185 `set` 绑定的局部定义不能 `cases`：`cases pre`/`cases post` 不会把
    定义替换进目标/假设（目标仍是 `pre ++ [r1]`，上下文仍是
    `pre := (splitAt r1 r).1`），`rfl`/`absurd rfl` 直接失败。改用
    `obtain ⟨b, p, hp⟩ := List.exists_cons_of_ne_nil h` 再 `rw [hp]`
    （本批 nextEl_splitAt 正负两支实测）。
  - #186 `nextEl` 在 `Kepler.Assembly` 命名空间未默认可见：裸写触发
    autoImplicit 把它绑成新变量，报 "Function expected at nextEl…
    identifier is unknown"，`unfold nextEl` 则报 "Local variable nextEl has
    no definition"。须 `open Kepler.Assembly (nextEl)`（TameList3 同款）。
  - #187 `List.getD_append_right` 在 `List` 命名空间内，根命名空间裸名
    unknown；写全 `List.getD_append_right`（与 TameList0-69 常用
    `List.getD_eq_getElem_of_lt` 同一约定）。
  - #188 if 计数的奖励：`between_self_eq` 只改 LHS（非 if），
    `nextEl_splitAt` 只给 RHS 一个 if；`rw [if_pos hpost, if_pos hpost]`
    第二发必然 "Did not find an occurrence of the pattern"。一 if 一
    `if_pos`（本批 HD_BETWN1 两支实测）。

  批 71 接续点（精确）：DANGEYJ.hl :365 `APPEND_FST_SPLIT`
  （`!l u v. FST (split_at_rec r1 (APPEND u v) l) = APPEND u (FST (split_at_rec r1 v l))`）
  → :372 `sym_fst_snd_in_betwn` → 后续 betwn 机器至 :949 文件末。
-/
import Kepler.Text.TameSpine.TameList69

/-! # DANGEYJ.hl §1-§3：split_at 基础件 / betwn-membership-indexl 族 / HD_BETWN1

HOL 对账：`DANGEYJ.hl:25-:363`（16 定理）。 -/

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl)
open Kepler.Graphs (fgraph between splitAtRec splitAt splitAt_ram splitAt_no_ram
  splitAt_in_fst splitAt_in_snd splitAt_distinct_ram_fst splitAt_distinct_ram_snd
  splitAtRec_notRam set_between_id between_def)

variable {α : Type*}

/-! ### §1 基础小件（DANGEYJ.hl:25-:67） -/

/-- **HOL `transform_list_power_rep`**（DANGEYJ.hl:25）：
`!j. (transform_list L x POWER j) (N,r) = ntrans L N r x j, rtrans L N r x j`。
POWER 迭代 ↦ `Function.iterate`，ntrans/rtrans ↦ 批 17 载体（Prod 投影）。 -/
theorem transform_list_power_rep (L : fgraph ℕ) (x : ℕ × ℕ)
    (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ)) (j : ℕ) :
    (transformListSpine L x)^[j] (N, r) =
      (ntransSpine L N r x j, rtransSpine L N r x j) := rfl

/-- **HOL `not_mem_split_at_rec`**（DANGEYJ.hl:30）：
`!r l. ~(MEM ram1 r) ==> split_at_rec ram1 l r = APPEND l r,[]`。
`splitAtRec_notRam`（ListAuxLemmas）逐字同构直投。 -/
theorem not_mem_split_at_rec [BEq α] [LawfulBEq α] {ram1 : α} {r l : List α}
    (h : ram1 ∉ r) : splitAtRec ram1 l r = (l ++ r, []) :=
  splitAtRec_notRam (c := ram1) (us := l) (vs := r) h

/-- **HOL `not_mem_split_at`**（DANGEYJ.hl:41）：
`!r. ~(MEM ram1 r) ==> split_at ram1 r = r,[]`。`splitAt_no_ram` 直投。 -/
theorem not_mem_split_at [BEq α] [LawfulBEq α] {ram1 : α} {r : List α}
    (h : ram1 ∉ r) : splitAt ram1 r = (r, []) :=
  splitAt_no_ram (c := ram1) (vs := r) h

/-- **HOL `not_betwn`**（DANGEYJ.hl:47）：
`~(MEM ram1 r) /\ ~(MEM ram2 r) ==> betwn r ram1 ram2 = r`。
`between_def` 展开后两次 `splitAt_no_ram` 收两分支。 -/
theorem not_betwn [BEq α] [LawfulBEq α] {ram1 ram2 : α} {r : List α}
    (h : ram1 ∉ r ∧ ram2 ∉ r) : between r ram1 ram2 = r := by
  rw [between_def, splitAt_no_ram (c := ram1) (vs := r) h.1]
  simp [splitAt_no_ram (c := ram2) (vs := r) h.2]

/-- **HOL `fst_fun`**（DANGEYJ.hl:53）：`(\(a:A,b:B). a) c = FST c`。λ β 归约。 -/
theorem fst_fun {β : Type*} (c : α × β) : (fun p : α × β => p.1) c = c.1 := rfl

/-- **HOL `fst_snd_fun`**（DANGEYJ.hl:62）：
`(\(a:A,b:B). f a b) c = f (FST c) (SND c)`。λ β 归约。 -/
theorem fst_snd_fun {β γ : Type*} (f : α → β → γ) (c : α × β) :
    (fun p : α × β => f p.1 p.2) c = f c.1 c.2 := rfl

/-! ### §2 betwn / membership / indexl 族（DANGEYJ.hl:72-:193） -/

/-- **HOL `not_in_mem_betwn`**（DANGEYJ.hl:72）：
`!r r1 r2. ~(MEM r1 r) /\ MEM r2 r /\ MEM x r ==>
r2 = x \/ MEM x (betwn r r2 r1)`。
r1 不在 r ⇒ 第一次切分的两段都不含 r1，between 退化为 `post ++ pre`；
再把 x ∈ r = pre ++ r2 :: post 三分。 -/
theorem not_in_mem_betwn [BEq α] [LawfulBEq α] {r : List α} {r1 r2 x : α}
    (h1 : r1 ∉ r) (h2 : r2 ∈ r) (hx : x ∈ r) :
    r2 = x ∨ x ∈ between r r2 r1 := by
  have hpre : r1 ∉ (splitAt r2 r).1 := fun hm => h1 (splitAt_in_fst hm)
  have hcont : ¬ (splitAt r2 r).2.contains r1 := by
    intro hc
    exact h1 (splitAt_in_snd (List.contains_iff_mem.mp hc))
  have hb : between r r2 r1 = (splitAt r2 r).2 ++ (splitAt r2 r).1 := by
    rw [between_def, if_neg hcont, splitAt_no_ram hpre]
  rw [hb]
  have hram := splitAt_ram h2
  rw [hram, List.mem_append, List.mem_cons] at hx
  rcases hx with hx | hx | hx
  · exact Or.inr (List.mem_append_right _ hx)
  · exact Or.inl hx.symm
  · exact Or.inr (List.mem_append_left _ hx)

/-- **HOL `in_uniq_betwn`**（DANGEYJ.hl:83）：
`!r r1. MEM r1 r /\ MEM x r /\ uniq r ==>
r1 = x \/ MEM x (betwn r r1 r1)`。
`set_between_id`（ListAuxLemmas：`y ∈ between xs x x ↔ y ∈ xs ∧ y ≠ x`）一步收。 -/
theorem in_uniq_betwn [BEq α] [LawfulBEq α] {r : List α} {r1 x : α}
    (h1 : r1 ∈ r) (hx : x ∈ r) (hnd : r.Nodup) :
    r1 = x ∨ x ∈ between r r1 r1 := by
  by_cases h : x = r1
  · exact Or.inl h.symm
  · exact Or.inr ((set_between_id (x := r1) (y := x) hnd h1).mpr ⟨hx, h⟩)

/-- **HOL `SND_SPLIT_SING`**（DANGEYJ.hl:93）：`SND (split_at r1 [a]) = []`。 -/
theorem SND_SPLIT_SING [BEq α] [LawfulBEq α] {r1 a : α} :
    (splitAt r1 [a]).2 = [] := by
  by_cases h : a = r1
  · subst h
    simp [splitAt, splitAtRec]
  · have hb : (a == r1) = false := beq_eq_false_iff_ne.mpr h
    simp [splitAt, splitAtRec, hb]

/-- **HOL `betwn_sing1`**（DANGEYJ.hl:98）：`betwn [a] a r2 = []`。 -/
theorem betwn_sing1 [BEq α] [LawfulBEq α] {a r2 : α} : between [a] a r2 = [] := by
  simp [between_def, splitAt, splitAtRec]

/-- **HOL `snd_split_at_rec_const`**（DANGEYJ.hl:104）：
`!t u v. SND (split_at_rec r1 u t) = SND (split_at_rec r1 v t)`。
TameList3 `sndSplitAtAcc`（两个累加器都归约到 `b = []`）双发。 -/
theorem snd_split_at_rec_const [BEq α] [LawfulBEq α] {r1 : α} (t u v : List α) :
    (splitAtRec r1 u t).2 = (splitAtRec r1 v t).2 :=
  (sndSplitAtAcc t r1 u).trans (sndSplitAtAcc t r1 v).symm

/-- 私件：`r.idxOf r1 = (splitAt r1 r).1.length`（`splitAt_ram` 分解 +
`idxOf_append_of_notMem`；第一次切分前缀不含 r1）。 -/
private theorem idxOf_splitAt [BEq α] [LawfulBEq α] {r : List α} {r1 : α}
    (h1 : r1 ∈ r) (hnd : r.Nodup) :
    r.idxOf r1 = (splitAt r1 r).1.length := by
  set pre := (splitAt r1 r).1 with hpredef
  set post := (splitAt r1 r).2 with hpostdef
  have hram : r = pre ++ r1 :: post := by
    rw [hpredef, hpostdef]
    exact splitAt_ram h1
  have hpre : r1 ∉ pre := by
    rw [hpredef]
    exact splitAt_distinct_ram_fst hnd
  rw [hram, List.idxOf_append_of_notMem hpre, List.idxOf_cons_self, Nat.add_zero]

/-- 私件：`split_at` 两段长度分解（`r = pre ++ r1 :: post` 的长度读数）。 -/
private theorem splitAt_lengths [BEq α] [LawfulBEq α] {r : List α} {r1 : α}
    (h1 : r1 ∈ r) :
    r.length = (splitAt r1 r).1.length + 1 + (splitAt r1 r).2.length := by
  set pre := (splitAt r1 r).1 with hpredef
  set post := (splitAt r1 r).2 with hpostdef
  have hram : r = pre ++ r1 :: post := by
    rw [hpredef, hpostdef]
    exact splitAt_ram h1
  rw [hram, List.length_append, List.length_cons]
  omega

/-- **HOL `SND_EMPTY_INDEXL`**（DANGEYJ.hl:110）：
`!r. MEM r1 r /\ uniq r /\ SND (split_at r1 r) = [] ==>
indexl r1 r = sizel r - 1`。
idxOf 换到前缀长度（`idxOf_splitAt`），post = [] 后长度算术收。 -/
theorem SND_EMPTY_INDEXL [BEq α] [LawfulBEq α] {r : List α} {r1 : α}
    (h1 : r1 ∈ r) (hnd : r.Nodup) (hs : (splitAt r1 r).2 = []) :
    r.idxOf r1 = r.length - 1 := by
  have hidx := idxOf_splitAt h1 hnd
  have hlen := splitAt_lengths (r := r) h1
  rw [hidx, hlen, hs, List.length_nil]
  omega

/-- **HOL `HD_FST_SPLIT_AT_REC`**（DANGEYJ.hl:146）：
`!t u. ~(u=[]) ==> HD (FST (split_at_rec r1 u t)) = HD u`。
TameList3 `fstSplitAtAcc` 把 LHS 前缀化 `u ++ _`，再 `head!_append` 收。 -/
theorem HD_FST_SPLIT_AT_REC [Inhabited α] [BEq α] [LawfulBEq α] {r1 : α}
    {t u : List α} (hu : u ≠ []) :
    (splitAtRec r1 u t).1.head! = u.head! := by
  rw [show (splitAtRec r1 u t).1 = u ++ (splitAtRec r1 [] t).1 from
    (fstSplitAtAcc t r1 u).symm]
  exact List.head!_append _ hu

/-- **HOL `INDEXL_SND_EMPTY`**（DANGEYJ.hl:154）：
`!r. MEM r1 r /\ uniq r /\ indexl r1 r = sizel r - 1 ==>
SND (split_at r1 r) = []`。
idxOf = 前缀长度，与长度分解一起 omega 出 post 长度 = 0。 -/
theorem INDEXL_SND_EMPTY [BEq α] [LawfulBEq α] {r : List α} {r1 : α}
    (h1 : r1 ∈ r) (hnd : r.Nodup) (hidx : r.idxOf r1 = r.length - 1) :
    (splitAt r1 r).2 = [] := by
  have hix := idxOf_splitAt h1 hnd
  have hlen := splitAt_lengths (r := r) h1
  have hpost : (splitAt r1 r).2.length = 0 := by
    rw [hix] at hidx
    omega
  exact List.length_eq_zero_iff.mp hpost

/-- **HOL `INDEXL_EQ_SND_EMPTY`**（DANGEYJ.hl:187）：
`!r. MEM r1 r /\ uniq r ==>
(indexl r1 r = sizel r - 1 <=> SND (split_at r1 r) = [])`。
前两件的 iff 组装。 -/
theorem INDEXL_EQ_SND_EMPTY [BEq α] [LawfulBEq α] {r : List α} {r1 : α}
    (h1 : r1 ∈ r) (hnd : r.Nodup) :
    (r.idxOf r1 = r.length - 1) ↔ (splitAt r1 r).2 = [] :=
  ⟨INDEXL_SND_EMPTY h1 hnd, SND_EMPTY_INDEXL h1 hnd⟩

/-! ### §3 首个 betwn-nextEl 桥：`HD_BETWN1`（DANGEYJ.hl:198-:363） -/

/-- 私件：`between r r1 r1 = post ++ pre`（Nodup 下第一次切分后循环左移；
`set_between_id` 证体内的显式形）。 -/
private theorem between_self_eq [BEq α] [LawfulBEq α] {r : List α} {r1 : α}
    (_h1 : r1 ∈ r) (hnd : r.Nodup) :
    between r r1 r1 = (splitAt r1 r).2 ++ (splitAt r1 r).1 := by
  have hpre : r1 ∉ (splitAt r1 r).1 := splitAt_distinct_ram_fst hnd
  have hcont : ¬ (splitAt r1 r).2.contains r1 :=
    mt List.contains_iff_mem.mp (splitAt_distinct_ram_snd hnd)
  rw [between_def, if_neg hcont, splitAt_no_ram hpre]

/-- 私件：`nextEl` 在 `split_at` 分解下的两分支形（post 非空取 post.head!，
post 空回绕到 pre.head!）。 -/
private theorem nextEl_splitAt [Inhabited α] [BEq α] [LawfulBEq α] {r : List α}
    {r1 : α} (h1 : r1 ∈ r) (hnd : r.Nodup) (hne : r ≠ [r1]) :
    nextEl r r1 =
      if (splitAt r1 r).2 = [] then (splitAt r1 r).1.head!
      else (splitAt r1 r).2.head! := by
  set pre := (splitAt r1 r).1 with hpredef
  set post := (splitAt r1 r).2 with hpostdef
  have hram : r = pre ++ r1 :: post := by
    rw [hpredef, hpostdef]
    exact splitAt_ram h1
  have hidx : r.idxOf r1 = pre.length := idxOf_splitAt h1 hnd
  have hlen : r.length = pre.length + 1 + post.length := splitAt_lengths (r := r) h1
  by_cases hpost : post = []
  · rw [if_pos hpost]
    unfold nextEl
    have hidxlast : r.idxOf r1 = r.length - 1 := by
      rw [hidx, hlen, hpost, List.length_nil]
      omega
    rw [if_pos hidxlast]
    have hpre : pre ≠ [] := by
      intro hp
      apply hne
      rw [hram, hpost, hp]
      rfl
    rw [hram, hpost]
    obtain ⟨b, p, hp⟩ := List.exists_cons_of_ne_nil hpre
    rw [hp]
    rfl
  · rw [if_neg hpost]
    unfold nextEl
    have hidxlt : ¬ (r.idxOf r1 = r.length - 1) := by
      have hplen : post.length ≠ 0 := fun h0 =>
        hpost (List.length_eq_zero_iff.mp h0)
      rw [hidx, hlen]
      omega
    rw [if_neg hidxlt]
    rw [hidx, hram]
    rw [List.getD_append_right (l := pre) (l' := r1 :: post) (d := r1)
      (n := pre.length + 1) (by omega)]
    have hn : pre.length + 1 - pre.length = 1 := by omega
    rw [hn]
    obtain ⟨b, p, hp⟩ := List.exists_cons_of_ne_nil hpost
    rw [hp]
    simp

/-- **HOL `HD_BETWN1`**（DANGEYJ.hl:198-:363）：
`!r r1. MEM r1 r /\ uniq r /\ ~(r=[r1]) ==> HD (betwn r r1 r1) = next_el r r1`。
`between_self_eq` 化左为 `post ++ pre` 的 head!，`nextEl_splitAt` 化右为同
两分支；post 非空由 `head!_append` 收，post 空时 hne 保证 pre 非空。 -/
theorem HD_BETWN1 [Inhabited α] [BEq α] [LawfulBEq α] {r : List α} {r1 : α}
    (h1 : r1 ∈ r) (hnd : r.Nodup) (hne : r ≠ [r1]) :
    (between r r1 r1).head! = nextEl r r1 := by
  rw [between_self_eq h1 hnd, nextEl_splitAt h1 hnd hne]
  by_cases hpost : (splitAt r1 r).2 = []
  · rw [if_pos hpost, hpost]
    simp
  · rw [if_neg hpost]
    exact List.head!_append _ hpost

end Kepler.Text.TameSpine
