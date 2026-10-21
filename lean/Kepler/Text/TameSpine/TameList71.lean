/-
  Kepler.Text.TameSpine.TameList71 — B3 D 链第十二批：DANGEYJ.hl §4-§7
  split 复合 / betwn 交叠 / HD-nth 桥（HOL 对账段：DANGEYJ.hl :365-:736；
  接续批 70 = TameList70.lean 329 行，md5 e79474e7906a781a7e7e64639f2f799b）。
  本批终点 = :736 HD_BETWN2 末；批 72 起点 = :739 SPLIT_NORMAL_LIST_CASES
  （依赖 split_normal_list 定义）+ :813 DANGEYJ 主定理。

  ┌─ 本批战绩小结 ────────────────────────────────────────────────
  │ 落点：18 公开定理 + 6 枚私有辅件（notMemFstSplitAt /
  │ mem_fst_splitAt_append_mem / snd_splitAt_append_mem /
  │ fst_splitAt_prefix / nextEl_splitAt_snd / nextEl_splitAt_fst），
  │ 642 行，零 sorry、零 axiom 声明；`lake build
  │ Kepler.Text.TameSpine.TameList71` 9503 jobs 全绿（clone /tmp/p4t21，
  │ 单发串行、零旗标、零 -K，本模块 4.3s，零本模块 linter 警告）。
  │ axiom 探针 18/18 全零 sorryAx：15 件标准三 [propext,
  │ Classical.choice, Quot.sound]、2 件 [propext]（split_at_rec_hd_fst /
  │ FST_NOT_IMP_NOT_SLPLIT）、1 件无公理（mem_imp_not_nil）；
  │ 快照 t71_axiom_audit.log 全文。
  │
  │ §0 私有辅件：notMemFstSplitAt（首次命中性质，**免 Nodup**）/
  │ mem_fst_splitAt_append_mem / snd_splitAt_append_mem（前后缀单调）/
  │ fst_splitAt_prefix（FST 前缀分解）/ nextEl_splitAt_snd / _fst
  │ （nextEl 两分支，免 Nodup）。
  │ §1 split 复合族（:365-:456）：APPEND_FST_SPLIT（归纳 + 结合律换装）/
  │ sym_fst_snd_in_betwn / sym_fst_snd_in_split（前缀定位后 r2 留后缀）/
  │ SND_TWO_SPLIT（sndSplitAtAcc 消累加器 + splitAt_dist_ram_all）/
  │ split_at_rec_hd_fst / FST_SND_SYM_SPLIT（A ++ r3 :: B ++ r2 :: C）/
  │ uniq_snd_split。
  │ §2 嵌套 MEM 族（:460-:539）：MEM_FST_FST_SPLIT /
  │ MEM_SND_FST_FST_SPLIT（前缀单调）/ MEM_SND_FST_FST_SPLIT2
  │ （splitAt_dist_ram 定 FST(splitAt r3 r)）。
  │ §3 betwn/HD 桥（:542-:736）：BETWN_TWO_MEM（split_between + head 消前段）/
  │ mem_imp_not_nil / HD_FST_SPLIT / HD_NTH_FST_SND_SPLIT /
  │ HD_SND_NTH_SPLIT_AT（getD 位移）/ FST_NOT_IMP_NOT_SLPLIT /
  │ HD_FST_FST_SPLIT（headl ↦ headD）/ HD_BETWN2（forward/wrap 两支）。
  └──────────────────────────────────────────────────────────────

  载体折算（沿批 3/70 约定）：`betwn` ↦ `Kepler.Graphs.between`、
  `split_at_rec`/`split_at` ↦ `splitAtRec`/`splitAt`、`uniq` ↦ `List.Nodup`、
  `indexl` ↦ `List.idxOf`、`sizel` ↦ `List.length`、`next_el` ↦
  `Kepler.Assembly.nextEl`、`HD` ↦ `List.head!`（配 `[Inhabited α]`）、
  `headl x0 s` ↦ `s.headD x0`、`nth x0 s i` ↦ `s.getD i x0`。

  诚实强化/记账：
  - `split_at_rec_hd_fst`/`HD_NTH_FST_SND_SPLIT`/`HD_SND_NTH_SPLIT_AT`/
    `HD_BETWN2` 的 HOL 部分前提在 Lean 证体中零消费（前者 h 仅用于
    head! 载体衔接；后三者 r2 侧前提冗余），签名按 HOL 原句保留，
    未用绑定按批 70 体例记 `_h*`。
  - `BETWN_TWO_MEM` 消费 `Kepler.Graphs.split_between`（其签名携带
    `[DecidableEq α]`）；本批证体以 `classical` 局部实例供给，定理签名
    仍只带 `[BEq α] [LawfulBEq α]`（与批 53 记档的 DecidableEq 槽同款）。
  - `notMemFstSplitAt` 无需 Nodup（splitAt 首次命中性质，直接由
    `fstSplitAtTake` 与 `List.mem_take_iff_idxOf_lt` 收），供本批
    `HD_SND_NTH_SPLIT_AT`（HOL 无 uniq 前提）与两条 nextEl 私件共用；
    故 `nextEl_splitAt_snd/_fst` 也均免 Nodup（HOL 无此前提）。
  - `HD_NTH_FST_SND_SPLIT` 的 `hnd` 亦零消费（`notMemFstSplitAt` 免
    Nodup 已足够）；HOL 原句 uniq 前提保留。

  新雷区（本批实测记档，编号承批 70 的 #188）：
  - #189 Lean `++` 为**左结合**：`rw [hram]` 把 `p ++ s` 的 `p` 换成
    `pre ++ c :: post` 后得到**左嵌套** `(pre ++ c :: post) ++ s`，
    `splitAt_append_of_not_mem` 的模式 `splitAt c (us ++ vs)` 要求右嵌套；
    须先 `rw [List.append_assoc]`，再对 `(c :: post) ++ s` 补
    `List.cons_append` 才能让 `splitAt` 的 cons 模式归约（本批三条私件
    与 APPEND_FST_SPLIT 实测）。
  - #190 `set x := e` 会把 **goal** 中出现的 e 抽象成 x（假设通常不动）：
    之后对原表达式形态 `rw [← hxdef]` 会 "pattern not found"。证体一律按
    set 后形态书写；给辅助件传原始形态参数时用 `by rwa [← hSdef]`
    反向装换（本批 HD_NTH_FST_SND_SPLIT / HD_SND_NTH_SPLIT_AT /
    HD_BETWN2 实测），根因是 goal 已被抽象而 helper 签名仍是原形态。
  - #191 `simp only [splitAtRec, hb]` 只把条件重写成 `false = true`，
    不会归约 `if false = true`；须补 `Bool.false_eq_true` + `↓reduceIte`
    （本批 APPEND_FST_SPLIT 实测；full `simp` 亦可行但会连带结合律重写）。
  - #192 `rw [List.append_assoc]` 后残局可能仅 defeq 而 `rw` 不自动
    `rfl`，须显式补 `rfl`；且 `rw [← List.append_assoc]` 在目标已是
    右嵌套时必然 "pattern not found"——先判方向（本批 hl/ht/hdec 三处）。
  - #193 跨模块 `private` 件不可见再次实证（§0' 体例）：批 70 的
    `idxOf_splitAt`/`splitAt_lengths`/`nextEl_splitAt`/`between_self_eq`
    全为 private；本批重立 `notMemFstSplitAt` 并**去掉 Nodup**，
    批 72 若需 `idxOf r1 = (splitAt r1 r).1.length` 仍须在批内重证或提升
    可见性。
  - #194 `rw [sndSplitAtAcc ...]` 的匹配不看 `splitAt` 的 defeq 展开：
    目标内出现 `(splitAtRec r1 [] r).2` 时第一实参必须写
    `splitAtRec r1 [] r` 形态，写 `(splitAt r1 r).2` 不匹配；收尾用
    `simpa [splitAt]` 桥回（本批 SND_TWO_SPLIT 实测）。

  批 72 接续点（精确）：DANGEYJ.hl :739 `SPLIT_NORMAL_LIST_CASES`
  （`MEM x r /\ uniq r ==> MEM x (FST (split_normal_list L r f ram1 ram2)) \/
  MEM x (SND ...)`；侦察预记：`split_normal_list` 定义在 TameList7 头注
  记为 tame_defs2.hl:435-:472 未全落，须先普查；消费
  `Seq2.next_el_outside`/`next_el_refl`/`not_betwn1/2`/`betwn_cases`/
  `mem_next_el`/`MEM_HD` 等）→ :813 `DANGEYJ` 主定理
  （`transform_assumption_v2`/`good_list`/`marked_list`/ntrans/rtrans/
  `set_of_list_flatten` 大件）→ :949 文件末。预计批 72 收章。
-/
import Kepler.Text.TameSpine.TameList70

/-! # DANGEYJ.hl §4-§7：split 复合族 / betwn 交叠 / HD-nth 桥

HOL 对账：`DANGEYJ.hl:365-:736`（18 定理）。 -/

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl)
open Kepler.Graphs (fgraph between splitAtRec splitAt splitAt_ram splitAt_no_ram
  splitAt_in_fst splitAt_in_snd splitAt_distinct_ram_fst splitAt_distinct_ram_snd
  splitAtRec_notRam set_between_id between_def splitAt_append_of_not_mem
  splitAt_dist_ram splitAt_dist_ram_all between_of_splitAt split_between
  splitAt_distinct_snd)

variable {α : Type*}

/-! ### §0 私有辅件：前缀/后缀拆分单调性与 nextEl 两分支 -/

/-- 私件：`c ∉ FST (split_at c vs)`（首次命中性质；无需 Nodup）。 -/
private theorem notMemFstSplitAt [BEq α] [LawfulBEq α] {c : α} {vs : List α} :
    c ∉ (splitAt c vs).1 := by
  have hfst : (splitAt c vs).1 = vs.take (vs.idxOf c) := by
    simp only [splitAt]
    rw [fstSplitAtTake vs c []]
    simp
  rw [hfst]
  intro hc
  have hmem : c ∈ vs := List.mem_of_mem_take hc
  have hlt := (List.mem_take_iff_idxOf_lt hmem).mp hc
  omega

/-- 私件：`MEM x (FST (split_at c p)) ==> MEM x (FST (split_at c (p ++ s)))`。 -/
private theorem mem_fst_splitAt_append_mem [BEq α] [LawfulBEq α] {c x : α}
    {p s : List α} (h : x ∈ (splitAt c p).1) : x ∈ (splitAt c (p ++ s)).1 := by
  by_cases hc : c ∈ p
  · set pre := (splitAt c p).1 with hpredef
    set post := (splitAt c p).2 with hpostdef
    have hram : p = pre ++ c :: post := by
      rw [hpredef, hpostdef]
      exact splitAt_ram hc
    have hpre : c ∉ pre := by
      rw [hpredef]
      exact notMemFstSplitAt
    rw [hram, List.append_assoc, List.cons_append, splitAt_append_of_not_mem hpre]
    simp only [splitAt, splitAtRec, beq_self_eq_true, ↓reduceIte, List.append_nil]
    exact h
  · rw [splitAt_append_of_not_mem hc]
    exact List.mem_append_left _ (by rwa [splitAt_no_ram hc] at h)

/-- 私件：`MEM x (SND (split_at c p)) ==> MEM x (SND (split_at c (p ++ s)))`。 -/
private theorem snd_splitAt_append_mem [BEq α] [LawfulBEq α] {c x : α}
    {p s : List α} (h : x ∈ (splitAt c p).2) : x ∈ (splitAt c (p ++ s)).2 := by
  by_cases hc : c ∈ p
  · set pre := (splitAt c p).1 with hpredef
    set post := (splitAt c p).2 with hpostdef
    have hram : p = pre ++ c :: post := by
      rw [hpredef, hpostdef]
      exact splitAt_ram hc
    have hpre : c ∉ pre := by
      rw [hpredef]
      exact notMemFstSplitAt
    rw [hram, List.append_assoc, List.cons_append, splitAt_append_of_not_mem hpre]
    simp only [splitAt, splitAtRec, beq_self_eq_true, ↓reduceIte]
    exact List.mem_append_left _ h
  · rw [splitAt_no_ram hc] at h
    exact absurd h (by simp)

/-- 私件：`FST (split_at c (p ++ s))` 以 `FST (split_at c p)` 为前缀。 -/
private theorem fst_splitAt_prefix [BEq α] [LawfulBEq α] {c : α} {p s : List α} :
    ∃ w, (splitAt c (p ++ s)).1 = (splitAt c p).1 ++ w := by
  by_cases hc : c ∈ p
  · refine ⟨[], ?_⟩
    set pre := (splitAt c p).1 with hpredef
    set post := (splitAt c p).2 with hpostdef
    have hram : p = pre ++ c :: post := by
      rw [hpredef, hpostdef]
      exact splitAt_ram hc
    have hpre : c ∉ pre := by
      rw [hpredef]
      exact notMemFstSplitAt
    rw [hram, List.append_assoc, List.cons_append, splitAt_append_of_not_mem hpre]
    simp [splitAt, splitAtRec, hpredef]
  · refine ⟨(splitAt c s).1, ?_⟩
    rw [splitAt_append_of_not_mem hc, splitAt_no_ram hc]

/-- 私件：`SND (split_at r1 r) ≠ [] ==> next_el r r1 = HD (SND (split_at r1 r))`
（批 70 `nextEl_splitAt` 的 post 非空分支独立形）。 -/
private theorem nextEl_splitAt_snd [Inhabited α] [BEq α] [LawfulBEq α] {r1 : α}
    {r : List α} (h1 : r1 ∈ r) (hS : (splitAt r1 r).2 ≠ []) :
    nextEl r r1 = (splitAt r1 r).2.head! := by
  set P := (splitAt r1 r).1 with hPdef
  set S := (splitAt r1 r).2 with hSdef
  have hSne : S ≠ [] := by rwa [hSdef]
  have hram : r = P ++ r1 :: S := by
    rw [hPdef, hSdef]
    exact splitAt_ram h1
  have hP : r1 ∉ P := by
    rw [hPdef]
    exact notMemFstSplitAt
  have hidx : r.idxOf r1 = P.length := by
    rw [hram, List.idxOf_append_of_notMem hP, List.idxOf_cons_self, Nat.add_zero]
  have hlen : r.length = P.length + 1 + S.length := by
    rw [hram, List.length_append, List.length_cons]
    omega
  unfold nextEl
  have hidxlt : ¬(r.idxOf r1 = r.length - 1) := by
    have hSlen : S.length ≠ 0 := fun h0 => hSne (List.length_eq_zero_iff.mp h0)
    rw [hidx, hlen]
    omega
  rw [if_neg hidxlt, hidx, hram]
  rw [List.getD_append_right (l := P) (l' := r1 :: S) (d := r1)
    (n := P.length + 1) (by omega)]
  rw [show P.length + 1 - P.length = 1 from by omega]
  obtain ⟨b, p, hp⟩ := List.exists_cons_of_ne_nil hSne
  rw [hp]
  rfl

/-- 私件：`SND (split_at r1 r) = []` 且前段非空时
`next_el r r1 = HD (FST (split_at r1 r))`（post 空回绕分支）。 -/
private theorem nextEl_splitAt_fst [Inhabited α] [BEq α] [LawfulBEq α] {r1 : α}
    {r : List α} (h1 : r1 ∈ r) (hS : (splitAt r1 r).2 = [])
    (hP : (splitAt r1 r).1 ≠ []) :
    nextEl r r1 = (splitAt r1 r).1.head! := by
  set P := (splitAt r1 r).1 with hPdef
  set S := (splitAt r1 r).2 with hSdef
  have hPne : P ≠ [] := by rwa [hPdef]
  have hram : r = P ++ r1 :: S := by
    rw [hPdef, hSdef]
    exact splitAt_ram h1
  have hP' : r1 ∉ P := by
    rw [hPdef]
    exact notMemFstSplitAt
  have hidx : r.idxOf r1 = P.length := by
    rw [hram, List.idxOf_append_of_notMem hP', List.idxOf_cons_self, Nat.add_zero]
  have hlen : r.length = P.length + 1 + S.length := by
    rw [hram, List.length_append, List.length_cons]
    omega
  unfold nextEl
  have hidxlast : r.idxOf r1 = r.length - 1 := by
    rw [hidx, hlen, hS, List.length_nil]
    omega
  rw [if_pos hidxlast, hram, hS]
  obtain ⟨b, p, hp⟩ := List.exists_cons_of_ne_nil hPne
  rw [hp]
  rfl

/-! ### §1 split_at 复合族（DANGEYJ.hl:365-:456） -/

/-- **HOL `APPEND_FST_SPLIT`**（DANGEYJ.hl:365）：
`!l u v. FST (split_at_rec r1 (APPEND u v) l) =
APPEND u (FST (split_at_rec r1 v l))`。对 l 归纳，累加器按 `++` 结合律换装。 -/
theorem APPEND_FST_SPLIT [BEq α] [LawfulBEq α] {r1 : α} (l u v : List α) :
    (splitAtRec r1 (u ++ v) l).1 = u ++ (splitAtRec r1 v l).1 := by
  induction l generalizing u v with
  | nil => rfl
  | cons a t ih =>
    by_cases ha : a = r1
    · subst ha
      simp [splitAtRec]
    · have hb : (a == r1) = false := beq_eq_false_iff_ne.mpr ha
      simp only [splitAtRec, hb, Bool.false_eq_true, ↓reduceIte]
      rw [List.append_assoc]
      exact ih u (v := v ++ [a])

/-- **HOL `sym_fst_snd_in_betwn`**（DANGEYJ.hl:372）：
`!l. MEM r2 l /\ ~(MEM r3 u) /\ MEM r3 (FST (split_at_rec r2 u l))
==> MEM r2 (SND (split_at_rec r3 u l))`。
`FST (split_at_rec r2 u l) = u ++ FST (split_at r2 l)`（`fstSplitAtAcc`），
r3 ∉ u 故 r3 落在 r2 前段；再对 r3 切分 r2 前段，r2 留在后缀。 -/
theorem sym_fst_snd_in_betwn [BEq α] [LawfulBEq α] {r2 r3 : α} {u l : List α}
    (h2 : r2 ∈ l) (h3u : r3 ∉ u) (h3 : r3 ∈ (splitAtRec r2 u l).1) :
    r2 ∈ (splitAtRec r3 u l).2 := by
  set P2 := (splitAt r2 l).1 with hP2def
  set S2 := (splitAt r2 l).2 with hS2def
  have hram2 : l = P2 ++ r2 :: S2 := by
    rw [hP2def, hS2def]
    exact splitAt_ram h2
  have h3' : r3 ∈ u ++ P2 := by
    have hh := h3
    rw [← fstSplitAtAcc l r2 u] at hh
    simpa [hP2def, splitAt] using hh
  have h3P2 : r3 ∈ P2 := by
    rcases List.mem_append.mp h3' with h | h
    · exact absurd h h3u
    · exact h
  set A := (splitAt r3 P2).1 with hAdef
  set B := (splitAt r3 P2).2 with hBdef
  have hram3 : P2 = A ++ r3 :: B := by
    rw [hAdef, hBdef]
    exact splitAt_ram h3P2
  have hA : r3 ∉ A := by
    rw [hAdef]
    exact notMemFstSplitAt
  have hl : l = A ++ r3 :: (B ++ r2 :: S2) := by
    rw [hram2, hram3, List.append_assoc]
    rfl
  rw [sndSplitAtAcc l r3 u]
  show r2 ∈ (splitAt r3 l).2
  rw [hl, splitAt_append_of_not_mem hA]
  simp [splitAt, splitAtRec]

/-- **HOL `sym_fst_snd_in_split`**（DANGEYJ.hl:392）：
`!l. MEM r2 l /\ MEM r3 (FST (split_at r2 l))
==> MEM r2 (SND (split_at r3 l))`。`sym_fst_snd_in_betwn` 取 u = [] 直投。 -/
theorem sym_fst_snd_in_split [BEq α] [LawfulBEq α] {r2 r3 : α} {l : List α}
    (h2 : r2 ∈ l) (h3 : r3 ∈ (splitAt r2 l).1) :
    r2 ∈ (splitAt r3 l).2 := by
  have h := sym_fst_snd_in_betwn (r2 := r2) (r3 := r3) (u := []) (l := l)
    h2 (by simp) (by simpa [splitAt] using h3)
  simpa [splitAt] using h

/-- **HOL `SND_TWO_SPLIT`**（DANGEYJ.hl:397）：
`!r u. uniq r /\ MEM r3 (SND (split_at_rec r1 u r))
==> SND (split_at_rec r3 u (SND (split_at_rec r1 u r))) = SND (split_at_rec r3 u r)`。
累加器经 `sndSplitAtAcc` 全消，Nodup 下 `splitAt_dist_ram_all` 给出
`(B,C) = splitAt r3 (SND (splitAt r1 r))` 与 `C = SND (splitAt r3 r)`。 -/
theorem SND_TWO_SPLIT [BEq α] [LawfulBEq α] {r1 r3 : α} {u r : List α}
    (hnd : r.Nodup) (h3 : r3 ∈ (splitAtRec r1 u r).2) :
    (splitAtRec r3 u (splitAtRec r1 u r).2).2 = (splitAtRec r3 u r).2 := by
  have h3' : r3 ∈ (splitAt r1 r).2 := by
    have hh := h3
    rw [sndSplitAtAcc r r1 u] at hh
    simpa [splitAt] using hh
  have hr1 : r1 ∈ r := by
    by_contra hc
    rw [splitAt_no_ram hc] at h3'
    exact absurd h3' (by simp)
  set P := (splitAt r1 r).1 with hPdef
  set S := (splitAt r1 r).2 with hSdef
  have hram : r = P ++ r1 :: S := by
    rw [hPdef, hSdef]
    exact splitAt_ram hr1
  have hSmem : r3 ∈ S := by rwa [hSdef]
  obtain ⟨B, C, hBC⟩ := List.append_of_mem hSmem
  have ht : r = P ++ r1 :: B ++ r3 :: C := by
    rw [hram, hBC, List.append_assoc]
    rfl
  obtain ⟨_, _, _, hBCsplit, hC, _⟩ := splitAt_dist_ram_all (vs := r) hnd ht
  rw [sndSplitAtAcc r r1 u, sndSplitAtAcc (splitAtRec r1 [] r).2 r3 u,
    sndSplitAtAcc r r3 u]
  simpa [splitAt] using (congrArg Prod.snd hBCsplit).symm.trans hC

/-- **HOL `split_at_rec_hd_fst`**（DANGEYJ.hl:410）：
`!l. HD l = a ==> FST (split_at_rec a u l) = u`。l 分空/非空；
非空时 `HD l = a` 即表头命中，split_at_rec 首步即返累加器。 -/
theorem split_at_rec_hd_fst [Inhabited α] [BEq α] [LawfulBEq α] {a : α} {u l : List α}
    (h : l.head! = a) : (splitAtRec a u l).1 = u := by
  cases l with
  | nil => rfl
  | cons b t =>
    simp only [List.head!_cons] at h
    subst h
    simp [splitAtRec]

/-- **HOL `FST_SND_SYM_SPLIT`**（DANGEYJ.hl:418）：
`!t. uniq t /\ MEM r2 t /\ MEM r3 t /\ MEM r3 (FST (split_at_rec r2 [] t))
==> SND (split_at_rec r3 [] (FST (split_at_rec r2 [] t)))
  = FST (split_at_rec r2 [] (SND (split_at_rec r3 [] t)))`。
Nodup 下把 t 表成 `A ++ r3 :: B ++ r2 :: C`，`splitAt_dist_ram_all` 双发收。 -/
theorem FST_SND_SYM_SPLIT [BEq α] [LawfulBEq α] {r2 r3 : α} {t : List α}
    (hnd : t.Nodup) (h2 : r2 ∈ t) (_h3 : r3 ∈ t)
    (h3f : r3 ∈ (splitAtRec r2 [] t).1) :
    (splitAtRec r3 [] (splitAtRec r2 [] t).1).2 =
      (splitAtRec r2 [] (splitAtRec r3 [] t).2).1 := by
  set P2 := (splitAt r2 t).1 with hP2def
  set S2 := (splitAt r2 t).2 with hS2def
  have hram2 : t = P2 ++ r2 :: S2 := by
    rw [hP2def, hS2def]
    exact splitAt_ram h2
  have h3P2 : r3 ∈ P2 := by simpa [hP2def, splitAt] using h3f
  set A := (splitAt r3 P2).1 with hAdef
  set B := (splitAt r3 P2).2 with hBdef
  have hram3 : P2 = A ++ r3 :: B := by
    rw [hAdef, hBdef]
    exact splitAt_ram h3P2
  have ht : t = A ++ r3 :: B ++ r2 :: S2 := by
    rw [hram2, hram3]
  obtain ⟨hAB, _, _, hBC, _, _⟩ := splitAt_dist_ram_all (vs := t) hnd ht
  show (splitAt r3 (splitAt r2 t).1).2 = (splitAt r2 (splitAt r3 t).2).1
  exact (congrArg Prod.snd hAB).symm.trans (congrArg Prod.fst hBC)

/-- **HOL `uniq_snd_split`**（DANGEYJ.hl:447）：
`!r. uniq r ==> uniq (SND (split_at_rec r1 u r))`。
`sndSplitAtAcc` 消累加器后即 `splitAt_distinct_snd`。 -/
theorem uniq_snd_split [BEq α] [LawfulBEq α] {r1 : α} {u r : List α}
    (hnd : r.Nodup) : (splitAtRec r1 u r).2.Nodup := by
  rw [sndSplitAtAcc r r1 u]
  exact splitAt_distinct_snd hnd

/-! ### §2 嵌套 split 的 MEM 族（DANGEYJ.hl:460-:539） -/

/-- **HOL `MEM_FST_FST_SPLIT`**（DANGEYJ.hl:460）：
`!r. MEM r3 (FST (split_at r2 (FST (split_at r1 r))))
==> MEM r3 (FST (split_at r2 r))`。
`FST (split_at r1 r)` 是 r 的前缀，前缀单调性 `mem_fst_splitAt_append_mem` 直投。 -/
theorem MEM_FST_FST_SPLIT [BEq α] [LawfulBEq α] {r1 r2 r3 : α} {r : List α}
    (h : r3 ∈ (splitAt r2 (splitAt r1 r).1).1) :
    r3 ∈ (splitAt r2 r).1 := by
  by_cases h1 : r1 ∈ r
  · rw [splitAt_ram h1]
    exact mem_fst_splitAt_append_mem (s := r1 :: (splitAt r1 r).2) h
  · rw [splitAt_no_ram h1] at h
    simpa using h

/-- **HOL `MEM_SND_FST_FST_SPLIT`**（DANGEYJ.hl:481）：
`!r. MEM x (SND (split_at r3 (FST (split_at r2 (FST (split_at r1 r))))))
==> MEM x (SND (split_at r3 (FST (split_at r2 r))))`。
先证 `FST (split_at r2 r)` 以 `FST (split_at r2 (FST (split_at r1 r)))` 为前缀
（`fst_splitAt_prefix`），再用后缀单调性。 -/
theorem MEM_SND_FST_FST_SPLIT [BEq α] [LawfulBEq α] {r1 r2 r3 x : α} {r : List α}
    (h : x ∈ (splitAt r3 (splitAt r2 (splitAt r1 r).1).1).2) :
    x ∈ (splitAt r3 (splitAt r2 r).1).2 := by
  by_cases h1 : r1 ∈ r
  · rw [splitAt_ram h1]
    obtain ⟨w, hw⟩ := fst_splitAt_prefix (c := r2) (p := (splitAt r1 r).1)
      (s := r1 :: (splitAt r1 r).2)
    rw [hw]
    exact snd_splitAt_append_mem h
  · rw [splitAt_no_ram h1] at h
    simpa using h

/-- **HOL `MEM_SND_FST_FST_SPLIT2`**（DANGEYJ.hl:516）：
`!r. uniq r /\ MEM r3 (SND (split_at r1 r))
/\ MEM x (FST (split_at r2 (FST (split_at r1 r))))
==> MEM x (FST (split_at r2 (FST (split_at r3 r))))`。
Nodup 下 `r = (P ++ r1 :: A) ++ r3 :: B`，`splitAt_dist_ram` 定出
`FST (split_at r3 r) = P ++ r1 :: A`，再前缀单调性收。 -/
theorem MEM_SND_FST_FST_SPLIT2 [BEq α] [LawfulBEq α] {r1 r2 r3 x : α} {r : List α}
    (hnd : r.Nodup) (h3 : r3 ∈ (splitAt r1 r).2)
    (hx : x ∈ (splitAt r2 (splitAt r1 r).1).1) :
    x ∈ (splitAt r2 (splitAt r3 r).1).1 := by
  have hr1 : r1 ∈ r := by
    by_contra hc
    rw [splitAt_no_ram hc] at h3
    exact absurd h3 (by simp)
  set P := (splitAt r1 r).1 with hPdef
  set S := (splitAt r1 r).2 with hSdef
  have hram1 : r = P ++ r1 :: S := by
    rw [hPdef, hSdef]
    exact splitAt_ram hr1
  have hS3 : r3 ∈ S := by rwa [hSdef]
  set A := (splitAt r3 S).1 with hAdef
  set B := (splitAt r3 S).2 with hBdef
  have hram3 : S = A ++ r3 :: B := by
    rw [hAdef, hBdef]
    exact splitAt_ram hS3
  have hdec : r = (P ++ r1 :: A) ++ r3 :: B := by
    rw [hram1, hram3, List.append_assoc]
    rfl
  have hQ := splitAt_dist_ram hnd hdec
  have hQfst : (splitAt r3 r).1 = P ++ (r1 :: A) := (congrArg Prod.fst hQ).symm
  have hmem : x ∈ (splitAt r2 (P ++ (r1 :: A))).1 :=
    mem_fst_splitAt_append_mem hx
  rw [← hQfst] at hmem
  exact hmem

/-! ### §3 betwn 交叠与 HD-nth 桥（DANGEYJ.hl:542-:736） -/

/-- **HOL `BETWN_TWO_MEM`**（DANGEYJ.hl:542）：
`!r. uniq r /\ MEM r1 r /\ MEM r2 r /\ MEM r3 (betwn r r1 r2)
/\ HD (betwn r r1 r2) = r3 /\ MEM x (betwn (betwn r r1 r2) r3 r2)
==> MEM x (betwn r r3 r2)`。
`split_between` 把 betwn r r1 r2 在 r3 处劈开；HD = r3 迫使前段为空，
betwn 退化为 `r3 :: betwn r r3 r2`，内层 betwn 再按端点 r2 不出现化简。 -/
theorem BETWN_TWO_MEM [Inhabited α] [BEq α] [LawfulBEq α] {r1 r2 r3 x : α} {r : List α}
    (hnd : r.Nodup) (h1 : r1 ∈ r) (h2 : r2 ∈ r) (h3 : r3 ∈ between r r1 r2)
    (hd : (between r r1 r2).head! = r3)
    (hx : x ∈ between (between r r1 r2) r3 r2) :
    x ∈ between r r3 r2 := by
  classical
  have hne13 : r1 ≠ r3 := by
    intro e
    subst e
    exact notBetwn1 hnd h2 h3
  have hsb := split_between (vs := r) (r := r1) (v := r2) (u := r3) hnd h1 h2 h3
  rw [if_neg hne13] at hsb
  have hX : between r r1 r3 = [] := by
    by_contra hXne
    have hhead : (between r r1 r2).head! = (between r r1 r3).head! := by
      rw [hsb, List.head!_append _ (by simp [hXne]), List.head!_append _ hXne]
    rw [hd] at hhead
    have hmem : (between r r1 r3).head! ∈ between r r1 r3 :=
      List.head!_mem_self hXne
    rw [← hhead] at hmem
    exact notBetwn2 hnd hmem
  have hB : between r r1 r2 = r3 :: between r r3 r2 := by
    rw [hsb, hX]
    rfl
  have hN : r2 ∉ between r r3 r2 := notBetwn2 hnd
  have hbetween : between (between r r1 r2) r3 r2 = between r r3 r2 := by
    rw [hB, between_def]
    simp only [splitAt, splitAtRec, beq_self_eq_true, ↓reduceIte, List.append_nil]
    rw [if_neg (mt List.contains_iff_mem.mp hN)]
  rw [hbetween] at hx
  exact hx

/-- **HOL `mem_imp_not_nil`**（DANGEYJ.hl:616）：`!s x. MEM x s ==> ~(s = [])`。 -/
theorem mem_imp_not_nil {s : List α} {x : α} (h : x ∈ s) : s ≠ [] :=
  List.ne_nil_of_mem h

/-- **HOL `HD_FST_SPLIT`**（DANGEYJ.hl:621）：
`!t. ~(FST (split_at r2 t) = []) ==> HD (FST (split_at r2 t)) = HD t`。
前缀非空时 take/drop 分解定头。 -/
theorem HD_FST_SPLIT [Inhabited α] [BEq α] [LawfulBEq α] {r2 : α} {t : List α}
    (h : (splitAt r2 t).1 ≠ []) : (splitAt r2 t).1.head! = t.head! := by
  have hfst : (splitAt r2 t).1 = t.take (t.idxOf r2) := by
    simp only [splitAt]
    rw [fstSplitAtTake t r2 []]
    simp
  rw [hfst] at h ⊢
  calc (t.take (t.idxOf r2)).head!
      = (t.take (t.idxOf r2) ++ t.drop (t.idxOf r2)).head! :=
        (List.head!_append (t.drop (t.idxOf r2)) h).symm
    _ = t.head! := by rw [List.take_append_drop]

/-- **HOL `HD_NTH_FST_SND_SPLIT`**（DANGEYJ.hl:629）：
`!r. MEM r1 r /\ MEM r2 r /\ uniq r /\ ~(r1=r2)
/\ MEM r2 (SND (split_at r1 r)) /\ ~(FST (split_at r2 (SND (split_at r1 r))) = [])
==> HD (FST (split_at r2 (SND (split_at r1 r)))) = nth r1 r (indexl r1 r + 1)`。
`HD_FST_SPLIT` 两次把左端推到 `HD (SND (split_at r1 r))`，再按
`r = P ++ r1 :: S` 的 getD 位移收。 -/
theorem HD_NTH_FST_SND_SPLIT [Inhabited α] [BEq α] [LawfulBEq α] {r1 r2 : α}
    {r : List α} (h1 : r1 ∈ r) (_h2 : r2 ∈ r) (_hnd : r.Nodup) (_hne : r1 ≠ r2)
    (_h2s : r2 ∈ (splitAt r1 r).2)
    (hf : (splitAt r2 (splitAt r1 r).2).1 ≠ []) :
    (splitAt r2 (splitAt r1 r).2).1.head! = r.getD (r.idxOf r1 + 1) r1 := by
  set P := (splitAt r1 r).1 with hPdef
  set S := (splitAt r1 r).2 with hSdef
  have hSne : S ≠ [] := by
    intro hs
    have hf' : (splitAt r2 S).1 ≠ [] := hf
    apply hf'
    rw [hs]
    simp [splitAt, splitAtRec]
  have hram : r = P ++ r1 :: S := by
    rw [hPdef, hSdef]
    exact splitAt_ram h1
  have hP : r1 ∉ P := by
    rw [hPdef]
    exact notMemFstSplitAt
  have hidx : r.idxOf r1 = P.length := by
    rw [hram, List.idxOf_append_of_notMem hP, List.idxOf_cons_self, Nat.add_zero]
  have hhead : S.head! = r.getD (r.idxOf r1 + 1) r1 := by
    rw [hidx, hram]
    rw [List.getD_append_right (l := P) (l' := r1 :: S) (d := r1)
      (n := P.length + 1) (by omega)]
    rw [show P.length + 1 - P.length = 1 from by omega]
    obtain ⟨b, p, hp⟩ := List.exists_cons_of_ne_nil hSne
    rw [hp]
    rfl
  have hf' : (splitAt r2 S).1 ≠ [] := hf
  calc (splitAt r2 S).1.head!
      = S.head! := HD_FST_SPLIT hf'
    _ = r.getD (r.idxOf r1 + 1) r1 := hhead

/-- **HOL `HD_SND_NTH_SPLIT_AT`**（DANGEYJ.hl:673）：
`!r. ~(SND (split_at r1 r) = [])
==> HD (SND (split_at r1 r)) = nth r1 r (indexl r1 r + 1)`。
HOL 无 uniq 前提；`notMemFstSplitAt` 免 Nodup 定 idxOf = 前缀长。 -/
theorem HD_SND_NTH_SPLIT_AT [Inhabited α] [BEq α] [LawfulBEq α] {r1 : α} {r : List α}
    (h : (splitAt r1 r).2 ≠ []) :
    (splitAt r1 r).2.head! = r.getD (r.idxOf r1 + 1) r1 := by
  have h1 : r1 ∈ r := by
    by_contra hc
    rw [splitAt_no_ram hc] at h
    exact h rfl
  set P := (splitAt r1 r).1 with hPdef
  set S := (splitAt r1 r).2 with hSdef
  have hSne : S ≠ [] := by rwa [hSdef]
  have hram : r = P ++ r1 :: S := by
    rw [hPdef, hSdef]
    exact splitAt_ram h1
  have hP : r1 ∉ P := by
    rw [hPdef]
    exact notMemFstSplitAt
  have hidx : r.idxOf r1 = P.length := by
    rw [hram, List.idxOf_append_of_notMem hP, List.idxOf_cons_self, Nat.add_zero]
  rw [hidx, hram]
  rw [List.getD_append_right (l := P) (l' := r1 :: S) (d := r1)
    (n := P.length + 1) (by omega)]
  rw [show P.length + 1 - P.length = 1 from by omega]
  obtain ⟨b, p, hp⟩ := List.exists_cons_of_ne_nil hSne
  rw [hp]
  rfl

/-- **HOL `FST_NOT_IMP_NOT_SLPLIT`**（DANGEYJ.hl:689）：
`~(FST (split_at r2 r) = []) ==> ~(r = [])`。空表 split 必返空前缀。 -/
theorem FST_NOT_IMP_NOT_SLPLIT [BEq α] [LawfulBEq α] {r2 : α} {r : List α}
    (h : (splitAt r2 r).1 ≠ []) : r ≠ [] := by
  rintro rfl
  exact h (by simp [splitAt, splitAtRec])

/-- **HOL `HD_FST_FST_SPLIT`**（DANGEYJ.hl:696）：
`!r. ~(FST (split_at r2 (FST (split_at r1 r))) = [])
==> HD (FST (split_at r2 (FST (split_at r1 r)))) = headl r1 r`。
`HD_FST_SPLIT` 两次 + `FST_NOT_IMP_NOT_SLPLIT` 保非空，`headl r1 r ↦ r.headD r1`。 -/
theorem HD_FST_FST_SPLIT [Inhabited α] [BEq α] [LawfulBEq α] {r1 r2 : α} {r : List α}
    (h : (splitAt r2 (splitAt r1 r).1).1 ≠ []) :
    (splitAt r2 (splitAt r1 r).1).1.head! = r.headD r1 := by
  have hP : (splitAt r1 r).1 ≠ [] := by
    intro hp
    apply h
    rw [hp]
    simp [splitAt, splitAtRec]
  have hr : r ≠ [] := FST_NOT_IMP_NOT_SLPLIT (r2 := r1) hP
  have hhead : r.headD r1 = r.head! := by
    obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hr
    rfl
  rw [hhead]
  exact (HD_FST_SPLIT h).trans (HD_FST_SPLIT hP)

/-- **HOL `HD_BETWN2`**（DANGEYJ.hl:709）：
`!r. MEM r1 r /\ MEM r2 r /\ ~(r1=r2) /\ uniq r /\ ~(betwn r r1 r2 = [])
==> HD (betwn r r1 r2) = next_el r r1`。
`between_def` 分 forward / wrap 两支：前者 `HD_FST_SPLIT` 把 HD 推到后缀头
（`nextEl_splitAt_snd`），后者按 `SND (split_at r1 r)` 空否再分
（非空同前，空则 `nextEl_splitAt_fst` 回绕到前缀头）。 -/
theorem HD_BETWN2 [Inhabited α] [BEq α] [LawfulBEq α] {r1 r2 : α} {r : List α}
    (h1 : r1 ∈ r) (_h2 : r2 ∈ r) (_hne : r1 ≠ r2) (_hnd : r.Nodup)
    (hB : between r r1 r2 ≠ []) :
    (between r r1 r2).head! = nextEl r r1 := by
  set P := (splitAt r1 r).1 with hPdef
  set S := (splitAt r1 r).2 with hSdef
  have hBdef : between r r1 r2 =
      if S.contains r2 then (splitAt r2 S).1 else S ++ (splitAt r2 P).1 := by
    have hsplit : splitAt r1 r = (P, S) := by rw [hPdef, hSdef]
    exact between_of_splitAt hsplit
  by_cases hc : S.contains r2
  · have h2S : r2 ∈ S := List.contains_iff_mem.mp hc
    have hSne : S ≠ [] := List.ne_nil_of_mem h2S
    have hB' : (splitAt r2 S).1 ≠ [] := by
      rw [hBdef, if_pos hc] at hB
      exact hB
    rw [hBdef, if_pos hc, HD_FST_SPLIT hB']
    exact (nextEl_splitAt_snd h1 (by rwa [← hSdef])).symm
  · by_cases hS : S = []
    · have hB' : (splitAt r2 P).1 ≠ [] := by
        rw [hBdef, if_neg hc, hS, List.nil_append] at hB
        exact hB
      have hPne : (splitAt r1 r).1 ≠ [] := FST_NOT_IMP_NOT_SLPLIT (r2 := r2) hB'
      rw [hBdef, if_neg hc, hS, List.nil_append, HD_FST_SPLIT hB']
      exact (nextEl_splitAt_fst h1 (by rwa [← hSdef]) hPne).symm
    · rw [hBdef, if_neg hc, List.head!_append _ hS]
      exact (nextEl_splitAt_snd h1 (by rwa [← hSdef])).symm

end Kepler.Text.TameSpine
