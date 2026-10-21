/-
  Kepler.Text.TameSpine.TameList68 — B3 D 链第九批：RXOKSKC 章末收口
  （重发批次；前驱 14:11 死于上游 API 故障，本批第一优先为 salvage 验证 + 缺陷修复）。
  接续批 67 = TameList67.lean（73f14f76）。HOL 对账段：RXOKSKC.hl :523-:1105。

  ┌─ 本批战绩小结 ────────────────────────────────────────────────
  │ salvage 终稿：466 行 / 30 声明（13 §0' 私桥 + RxOkData 结构 + L + 15 公开件），
  │ 零 sorry、零 axiom 声明；`lake build` 9500 jobs 全绿（本机实测 4-14s）。
  │ axiom 探针 17/17 全件仅 [propext, Classical.choice, Quot.sound]，零 sorryAx。
  │ 到达：HOL :527-:532 的 RxOkData 构造数据（f/S/L + 五项前件）与 f 面枚举
  │ 原子件（L/mem_L/L_nodup、f_len/f_nodup/f_ne_nil/f_pair/f_card_pos/
  │ f_card_three/f_getElem/f_mem_iff/len_listPairs_f/f_pair_getElem?/
  │ f_pair_mem/f_next/f_prev_pair）。
  │ **未到达 RXOKSKC 本体（:523）**：剩余五槽（uniq s / good_list /
  │ good_list_nodes / iso e/n/f 三槽）未开工；本章逐字对账留批 69。
  │ 前驱半成品修复 9 处验证性缺陷（签名 2 + 战术 7，命题语义未改）：
  │ 见雷区 #172-#177。
  └──────────────────────────────────────────────────────────────

  新雷区（本批实测记档，编号承 TameList67 实际最高 #171）：
  - #172 idxOf 的 BEq 实例固化：TameList67 `prevEl_eq_getD_idxOf` 在泛型 α 上
    把 `l.idxOf x` 的实例固定为 `instBEqOfDecidableEq`；本文件重述同一表达式时
    TC 会选 `instBEqProd`，导致 getD→getElem 迁移与 `idxOf_getElem` 应用全部
    类型不匹配。对策：`@List.idxOf (Set α × Set α) instBEqOfDecidableEq ...`
    与 `@TameLp.idxOf_getElem (Set α × Set α) instBEqOfDecidableEq _ _ ...`
    显式指定实例。
  - #173 getElem 指标改写 motive 不合法：对 `l[j]'hj` 直接 `rw [hidx]`（j 含
    idxOf）会因 proof 依赖指标报 "motive is not type correct"。对策：先在 ℕ 层
    证 j₁ = j₂，再用 `getElemConN68 ha hb h` 原子迁移（proof-irrelevant）。
  - #174 section 变量自动绑定丢参：命题不引用 D 时 Lean 不把
    `variable (D : RxOkData H)` 纳入上下文，`D.f_len`/`D.hr.three_le_ncard_face`
    报 Unknown identifier（并非 API 缺失）。对策：声明显式写
    `(D : RxOkData H)` binder。
  - #175 `pow_mod_eq` 方向：TameList67 的 `pow_mod_eq` 是 `F^(k%m) = F^k`；
    `(k%C+1)` 指标按 `← pow_mod_eq (k%C+1)` → `mod_succ_mod68` →
    `← pow_mod_eq (k+1)` 三步收，勿按 `F^k → F^(k%m)` 直觉反向使用。
  - #176 `congr 1` 自动关子目标：pair 两分量中一分量 defeq 时 `congr 1` 会自动
    关闭该目标，后续 `· rfl` 报 "No goals to be solved"；直接续写剩余目标。
  - #177 `Nat.add_mod` 嵌套：`a + C - 1` 与 `a + (C-1)` 非 defeq，omega 不能
    直接收 `(k%C + C - 1)%C = (k+C-1)%C`；先 omega 化归再
    `conv_rhs => rw [Nat.add_mod]` + `Nat.mod_eq_of_lt`。

  批 69 接续点（精确）：
  - 文件末尾 `end RxOkData` 之后即 RXOKSKC 主证。从 `D : RxOkData H`（HOL
    :527-:532 五前件）与 `L := D.L` 出发，按 HOL 顺序推进：
    (a) `uniq s` 槽（ONE_TO_ONE_DART，批 66 在册）+ `good_list` 槽
        （rxUniqListOfDarts + SYM_LIST_DART）；
    (b) `good_list_nodes` 槽（FST-fiber 集计算；TameList67
        `rxGoodListNodes` / `good_list_nodes` 泛型形在册）；
    (c) iso 之 e/n/f 三槽（HOL :906-:923 / :928-:1065 / :1073-:1089；
        :928-:1065 为全章最重段）；
    (d) `RXOKSKC`（:523）全件落地 = `iso H (hypermap_of_list L)`（A9 接口）。
  - 可用底座（TameList67，全件已绿）：`hypermapOfListG` 四槽
    （darts/edgeMap/nodeMap/faceMap_hypermapOfListG）、`bijOn_rxESwap`/
    `bijOn_rxFList`/`bijOn_rxNList`、`rxGoodListNodes`、
    `darts_eq_iUnion_setOfOrbits`/`darts_eq_iUnion_faceSet/nodeSet/edgeSet`、
    `iterateMapValuation`、`pow_mod_eq`、`face_eq_orbit_range`、`hypMapsInvs`、
    `prevEl_eq_getD_idxOf`、`nextElListPairsG`/`prevElListPairs`、
    `getElem_rot1'`/`getElemListPairs`。
  - 本文件供给：`RxOkData.L` 与 `f_*` 原子件（node/face 枚举；next/prev 槽直接
    消费 `f_mem_iff`/`f_next`/`f_prev_pair`）。
  - 诚实分期：本批只交付已验证的 RxOkData 段；RXOKSKC 及五槽零 sorry 未动，
    不存在半成品 sorry 债务。
-/
import Kepler.Text.TameSpine.TameList67

namespace Kepler.Text.TameSpine

variable {α : Type*} [DecidableEq α]

open Kepler.Assembly (listPairs nextEl prevEl)


/-! ### §0 本地私桥（TameList66/67 private 件跨模块不可见，按批 63 §0'
体例逐字本地复制，文本取已构建绿实库 TameList67.lean:31-76 + TameList66
§1 私件） -/

omit [DecidableEq α] in
/-- zip 表取元（TameList67 getElem_zip' 同体复制）。 -/
private theorem getElem_zip68 {l₁ l₂ : List α} {i : ℕ} (h : i < (l₁.zip l₂).length)
    (h1 : i < l₁.length) (h2 : i < l₂.length) :
    (l₁.zip l₂)[i]'h = (l₁[i]'h1, l₂[i]'h2) := by
  induction l₁ generalizing l₂ i with
  | nil => cases l₂ <;> simp at h
  | cons a t ih =>
    cases l₂ with
    | nil => simp at h2
    | cons b t' =>
      cases i with
      | zero => simp
      | succ i' =>
        rw [List.zip_cons_cons] at h
        show ((a, b) :: (t.zip t'))[i' + 1]'h
            = ((a :: t)[i' + 1]'(by simpa using h1), (b :: t')[i' + 1]'(by simpa using h2))
        rw [List.getElem_cons, List.getElem_cons, List.getElem_cons]
        exact ih (by simpa using h) (by simpa using h1) (by simpa using h2)

omit [DecidableEq α] in
/-- list_pairs 专用 zip 取元（TameList67 getElemListPairs 同体复制）。 -/
private theorem getElemListPairs68 {s : List α} {j : ℕ} (h1 : j < s.length)
    (h2 : j < (s.drop 1 ++ s.take 1).length) :
    (listPairs s)[j]'(by
      show j < (s.zip (s.drop 1 ++ s.take 1)).length
      rw [List.length_zip]
      exact lt_min_iff.mpr ⟨h1, h2⟩)
      = (s[j]'h1, (s.drop 1 ++ s.take 1)[j]'h2) :=
  getElem_zip68 (by
    show j < (s.zip (s.drop 1 ++ s.take 1)).length
    rw [List.length_zip]
    exact lt_min_iff.mpr ⟨h1, h2⟩) h1 h2

omit [DecidableEq α] in
/-- zip 表成员的取元构造型（TameList67 mem_zip_of 同体复制）。 -/
private theorem mem_zip_of68 {l₁ l₂ : List α} {p : α × α} {i : ℕ}
    (h1 : i < l₁.length) (h2 : i < l₂.length) (e1 : l₁[i]'h1 = p.1) (e2 : l₂[i]'h2 = p.2) :
    p ∈ l₁.zip l₂ := by
  have hk := getElem_zip68 (by rw [List.length_zip]; omega) h1 h2
  have hp : p = (l₁[i]'h1, l₂[i]'h2) :=
    Prod.ext (y := (l₁[i]'h1, l₂[i]'h2)) e1.symm e2.symm
  rw [hp, ← hk]
  have hlen : i < (l₁.zip l₂).length := by
    rw [List.length_zip]
    omega
  exact List.getElem_mem hlen

omit [DecidableEq α] in
/-- 同表两下标相等则取元相等（TameList67 getElemConN67 同体复制）。 -/
private theorem getElemConN68 {α : Type*} {l : List α} {a b : ℕ} (ha : a < l.length)
    (hb : b < l.length) (hab : a = b) : l[a]'ha = l[b]'hb := by
  subst hab; rfl

omit [DecidableEq α] in
/-- rot1 列长度 = 原列长度（TameList67 rot1_length 同体复制）。 -/
private theorem rot1_length68 (L : List α) :
    (L.drop 1 ++ L.take 1).length = L.length := by
  cases L with
  | nil => simp
  | cons a t => simp

omit [DecidableEq α] in
/-- rot1 下标折算 `?`-形（TameList66 getElem_rot1 同体复制）。 -/
private theorem getElem_rot1_68_aux (L : List α) (i : ℕ) (hi : i < L.length) :
    (L.drop 1 ++ L.take 1)[i]? = L[(i + 1) % L.length]? := by
  rcases Nat.lt_or_ge i (L.length - 1) with hlt | hge
  · have h1 : i < (L.drop 1).length := by
      simp only [List.length_drop]; omega
    rw [List.getElem?_append_left h1, List.getElem?_drop,
      show (i + 1) % L.length = i + 1 from Nat.mod_eq_of_lt (by omega),
      Nat.add_comm 1 i]
  · have hilen : i = L.length - 1 := by omega
    have h2 : (L.drop 1).length ≤ i := by
      simp only [List.length_drop]; omega
    rw [List.getElem?_append_right h2,
      show i - (L.drop 1).length = 0 by simp only [List.length_drop]; omega,
      List.getElem?_take_of_lt (by omega),
      show (i + 1) % L.length = 0 from by
        rw [show i + 1 = L.length from by omega]
        exact Nat.mod_self (L.length)]

omit [DecidableEq α] in
/-- rot1 下标折算的 `'h` 形（TameList67 getElem_rot1' 同体复制）。 -/
private theorem getElem_rot1_68 (L : List α) {i : ℕ}
    (hi : i < (L.drop 1 ++ L.take 1).length) :
    (L.drop 1 ++ L.take 1)[i]'hi
      = L[(i + 1) % L.length]'(by
          have hi' : i < L.length := by rw [← rot1_length68]; exact hi
          exact Nat.mod_lt _ (by omega : 0 < L.length)) := by
  have hilen : i < L.length := by rw [← rot1_length68]; exact hi
  have hpos : 0 < L.length := by omega
  have hmod : (i + 1) % L.length < L.length := Nat.mod_lt _ hpos
  have h1 : (L.drop 1 ++ L.take 1)[i]? = some ((L.drop 1 ++ L.take 1)[i]'hi) :=
    List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩
  have h2 : L[(i + 1) % L.length]? = some (L[(i + 1) % L.length]'hmod) :=
    List.getElem?_eq_some_iff.mpr ⟨hmod, rfl⟩
  have h3 := getElem_rot1_68_aux L i hilen
  rw [h1, h2] at h3
  exact Option.some.inj h3

omit [DecidableEq α] in
/-- zip 表左投影成员件（TameList66 mem_zip_fst 同体复制）。 -/
private theorem mem_zip_fst68 {l₁ l₂ : List α} {p : α × α} (h : p ∈ l₁.zip l₂) :
    p.1 ∈ l₁ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp at h
  | cons a t ih =>
    cases l₂ with
    | nil => simp at h
    | cons b t' =>
      rw [List.zip_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (ih h)

omit [DecidableEq α] in
/-- zip 表的右投影成员件（Mathlib 无现成 mem_zip，mem_zip_fst 对偶）。 -/
private theorem mem_zip_snd68 {l₁ l₂ : List α} {p : α × α} (h : p ∈ l₁.zip l₂) :
    p.2 ∈ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp at h
  | cons a t ih =>
    cases l₂ with
    | nil => simp at h
    | cons b t' =>
      rw [List.zip_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (ih h)

omit [DecidableEq α] in
/-- left 列无重 ⟹ zip 表无重（TameList66 nodup_zip_of_nodup_left 同体复制）。 -/
private theorem nodup_zip68 {l₁ l₂ : List α} (h : l₁.Nodup) :
    (l₁.zip l₂).Nodup := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a t ih =>
    cases l₂ with
    | nil => simp
    | cons b t' =>
      rw [List.zip_cons_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, ih (List.nodup_cons.mp h).2⟩
      exact List.nodup_cons.mp h |>.1 (mem_zip_fst68 hm)

omit [DecidableEq α] in
/-- listPairs s 无重（左列无重 ⟹ zip 无重）。 -/
private theorem nodup_listPairs68 {s : List α} (h : s.Nodup) :
    (listPairs s).Nodup :=
  nodup_zip68 h

omit [DecidableEq α] in
/-- `(a % n + 1) % n = (a + 1) % n`（n > 0；`n = 1` 支由 simp 收）。 -/
private theorem mod_succ_mod68 (a n : ℕ) (hn : 0 < n) :
    (a % n + 1) % n = (a + 1) % n := by
  rcases Nat.lt_or_ge 1 n with h2 | h2
  · rw [Nat.add_mod a 1 n, Nat.mod_eq_of_lt h2]
  · have hn1 : n = 1 := by omega
    subst hn1
    simp

omit [DecidableEq α] in
/-- `((a + n - 1) % n + 1) % n = a % n`（n > 0）。 -/
private theorem mod_pred_succ68 (a n : ℕ) (hn : 0 < n) :
    ((a + n - 1) % n + 1) % n = a % n := by
  rw [mod_succ_mod68 _ _ hn]
  have hk : a + n - 1 + 1 = a + n := by omega
  rw [hk, Nat.add_mod a n n, Nat.mod_self, Nat.add_zero, Nat.mod_mod]

/-! ### §1 构造数据（HOL :527-:532：EXISTS_LIST_FACE_NODE_FUNC 的 Skolem f +
LIST_COR_FACE_SET1 的代表集 S + L := list_of_set (f '' S)） -/

/-- RXOKSKC 构造数据。`hr` 与 `hf/hSd/hScov/hSinj` 逐条对应 HOL :527-:532
的 MRESA 前件（EXISTS_LIST_FACE_NODE_FUNC 五合取 + LIST_COR_FACE_SET1 的
dart 覆盖 / face 单射两项——`hScard`/`hSfaces` 两槽本证明零消费不携）。 -/
structure RxOkData (H : Hypermap α) where
  hr : H.IsRestricted
  f : α → List (Set α)
  S : Finset α
  hf : ∀ x ∈ H.darts,
    (∀ i < (H.face x).ncard, (f x)[i]? = some (H.node ((H.faceMap ^ i) x))) ∧
    (f x).length = (H.face x).ncard ∧ (f x).Nodup ∧ (f x) ≠ [] ∧
    (∀ e ∈ listPairs (f x), ∃ i < (H.face x).ncard,
      e = (H.node ((H.faceMap ^ i) x), H.node ((H.faceMap ^ (i + 1)) x)))
  hSd : ∀ x ∈ S, x ∈ H.darts
  hScov : ∀ x ∈ H.darts, ∃ y ∈ S, x ∈ H.face y
  hSinj : ∀ x ∈ S, ∀ y ∈ S, H.face x = H.face y → x = y

namespace RxOkData

variable {H : Hypermap α} (D : RxOkData H)

/-- `L := list_of_set (f '' S)`（HOL :531；Finset.image + toList 的
无重枚举形）。 -/
noncomputable def L : List (List (Set α)) := by
  classical
  exact (D.S.image D.f).toList

theorem mem_L {l : List (Set α)} : l ∈ D.L ↔ ∃ x ∈ D.S, D.f x = l := by
  classical
  simp [L, Finset.mem_image]

theorem L_nodup : D.L.Nodup := by
  classical
  exact Finset.nodup_toList _

theorem f_len {x : α} (hx : x ∈ H.darts) :
    (D.f x).length = (H.face x).ncard :=
  (D.hf x hx).2.1

theorem f_nodup {x : α} (hx : x ∈ H.darts) : (D.f x).Nodup :=
  (D.hf x hx).2.2.1

theorem f_ne_nil {x : α} (hx : x ∈ H.darts) : D.f x ≠ [] :=
  (D.hf x hx).2.2.2.1

theorem f_pair {x : α} (hx : x ∈ H.darts) {e : Set α × Set α}
    (he : e ∈ listPairs (D.f x)) :
    ∃ i < (H.face x).ncard,
      e = (H.node ((H.faceMap ^ i) x), H.node ((H.faceMap ^ (i + 1)) x)) :=
  (D.hf x hx).2.2.2.2 e he

theorem f_card_pos (D : RxOkData H) {x : α} (hx : x ∈ H.darts) :
    0 < (H.face x).ncard := by
  rw [← D.f_len hx]
  exact List.length_pos_iff_ne_nil.mpr (D.f_ne_nil hx)

theorem f_card_three (D : RxOkData H) {x : α} (hx : x ∈ H.darts) :
    3 ≤ (H.face x).ncard :=
  D.hr.three_le_ncard_face hx

theorem f_getElem {x : α} (hx : x ∈ H.darts) {i : ℕ}
    (hi : i < (H.face x).ncard) (hlt : i < (D.f x).length) :
    (D.f x)[i]'hlt = H.node ((H.faceMap ^ i) x) :=
  (List.getElem?_eq_some_iff.mp ((D.hf x hx).1 i hi)).2

/-- `f x` 的元素恰是面轨道上的节点（HOL :542-:554 `all uniq L` 与
:723-:783 node 覆盖两处消费）。 -/
theorem f_mem_iff {x : α} (hx : x ∈ H.darts) {a : Set α} :
    a ∈ D.f x ↔ ∃ i < (H.face x).ncard, a = H.node ((H.faceMap ^ i) x) := by
  constructor
  · intro ha
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp ha
    refine ⟨i, by rwa [D.f_len hx] at hi, ?_⟩
    rw [← he]
    exact D.f_getElem hx (by rwa [D.f_len hx] at hi) hi
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp ((D.hf x hx).1 i hi)
    rw [← he]
    exact List.getElem_mem hlt

theorem len_listPairs_f {x : α} (hx : x ∈ H.darts) :
    (listPairs (D.f x)).length = (H.face x).ncard := by
  show ((D.f x).zip ((D.f x).drop 1 ++ (D.f x).take 1)).length = (H.face x).ncard
  rw [List.length_zip, rot1_length68, Nat.min_self, D.f_len hx]

/-- list_pairs (f x) 的第 i 位（i < CARD (face x)）取元形。 -/
theorem f_pair_getElem? {x : α} (hx : x ∈ H.darts) {i : ℕ}
    (hi : i < (H.face x).ncard) :
    (listPairs (D.f x))[i]? =
      some (H.node ((H.faceMap ^ i) x), H.node ((H.faceMap ^ (i + 1)) x)) := by
  have hlen := D.f_len hx
  have hlt : i < (listPairs (D.f x)).length := by
    rw [D.len_listPairs_f hx]; exact hi
  rw [List.getElem?_eq_getElem hlt]
  have h1 : i < (D.f x).length := by rw [hlen]; exact hi
  have h2 : i < ((D.f x).drop 1 ++ (D.f x).take 1).length := by
    rw [rot1_length68, hlen]; exact hi
  rw [show (listPairs (D.f x))[i]'hlt
      = ((D.f x)[i]'h1, ((D.f x).drop 1 ++ (D.f x).take 1)[i]'h2) from
    getElemListPairs68 h1 h2]
  rw [D.f_getElem hx hi h1, getElem_rot1_68 (D.f x) h2]
  congr 1
  have hCpos := D.f_card_pos hx
  have hC0 : (H.face x).ncard ≠ 0 := Nat.ne_of_gt hCpos
  have hidx : (i + 1) % (D.f x).length = (i + 1) % (H.face x).ncard := by rw [hlen]
  have hnew : (i + 1) % (H.face x).ncard < (D.f x).length := by
    rw [hlen]; exact Nat.mod_lt _ hCpos
  have hold : (i + 1) % (D.f x).length < (D.f x).length :=
    Nat.mod_lt _ (by rw [hlen]; exact hCpos)
  rw [getElemConN68 hold hnew hidx]
  rw [D.f_getElem hx (Nat.mod_lt _ hCpos) hnew]
  rw [pow_mod_eq hC0 (H.pow_card_face_apply_self x) (i + 1)]

/-- 面轨道第 k 步的节点对落 `list_pairs (f x)`（k 任意，经 k % CARD 折算）。 -/
theorem f_pair_mem {x : α} (hx : x ∈ H.darts) (k : ℕ) :
    (H.node ((H.faceMap ^ k) x), H.node ((H.faceMap ^ (k + 1)) x)) ∈
      listPairs (D.f x) := by
  have hCpos := D.f_card_pos hx
  have hC0 : (H.face x).ncard ≠ 0 := Nat.ne_of_gt hCpos
  have hi : k % (H.face x).ncard < (H.face x).ncard := Nat.mod_lt _ hCpos
  obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp (D.f_pair_getElem? hx hi)
  have hval : (H.node ((H.faceMap ^ (k % (H.face x).ncard)) x),
      H.node ((H.faceMap ^ (k % (H.face x).ncard + 1)) x))
      = (H.node ((H.faceMap ^ k) x), H.node ((H.faceMap ^ (k + 1)) x)) := by
    rw [pow_mod_eq hC0 (H.pow_card_face_apply_self x) k]
    congr 1
    rw [← pow_mod_eq hC0 (H.pow_card_face_apply_self x) (k % (H.face x).ncard + 1),
      mod_succ_mod68 k (H.face x).ncard hCpos,
      ← pow_mod_eq hC0 (H.pow_card_face_apply_self x) (k + 1)]
  rw [hval] at he
  rw [← he]
  exact List.getElem_mem hlt

/-- `nextEl (f x) (node (F^k x)) = node (F^(k+1) x)`（f 面枚举的周期
继元；iso f 槽消费）。 -/
theorem f_next {x : α} (hx : x ∈ H.darts) (k : ℕ) :
    nextEl (D.f x) (H.node ((H.faceMap ^ k) x)) =
      H.node ((H.faceMap ^ (k + 1)) x) := by
  have hlen := D.f_len hx
  have hCpos := D.f_card_pos hx
  have hC0 : (H.face x).ncard ≠ 0 := Nat.ne_of_gt hCpos
  have hnod := D.f_nodup hx
  have hpos : 0 < (D.f x).length := by rw [hlen]; exact hCpos
  have hi : k % (H.face x).ncard < (H.face x).ncard := Nat.mod_lt _ hCpos
  have hmem : H.node ((H.faceMap ^ k) x) ∈ D.f x := by
    rw [D.f_mem_iff hx]
    exact ⟨k % (H.face x).ncard, hi, by
      rw [pow_mod_eq hC0 (H.pow_card_face_apply_self x) k]⟩
  rw [TameLp.nextEl_eq_getD hmem, TameLp.getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]
  have h1 : k % (H.face x).ncard < (D.f x).length := by rw [hlen]; exact hi
  have hidx : (D.f x).idxOf (H.node ((H.faceMap ^ k) x)) =
      k % (H.face x).ncard := by
    have hget : (D.f x)[k % (H.face x).ncard]'h1 =
        H.node ((H.faceMap ^ k) x) := by
      rw [D.f_getElem hx hi h1,
        pow_mod_eq hC0 (H.pow_card_face_apply_self x) k]
    rw [← hget]
    exact TameLp.idxOf_getElem hnod h1
  rw [hidx]
  have hidxEq : (k % (H.face x).ncard + 1) % (D.f x).length =
      (k + 1) % (H.face x).ncard := by
    rw [hlen, mod_succ_mod68 _ _ hCpos]
  have hnew : (k + 1) % (H.face x).ncard < (D.f x).length := by
    rw [hlen]; exact Nat.mod_lt _ hCpos
  have hold : (k % (H.face x).ncard + 1) % (D.f x).length < (D.f x).length :=
    Nat.mod_lt _ hpos
  rw [getElemConN68 hold hnew hidxEq]
  rw [D.f_getElem hx (Nat.mod_lt _ hCpos) hnew,
    pow_mod_eq hC0 (H.pow_card_face_apply_self x) (k + 1)]

/-- `prevEl (list_pairs (f x)) (node F^k x, node F^(k+1) x)` 的取元形
（iso n 槽消费；上一对 = 指标 (k + CARD - 1) % CARD）。 -/
theorem f_prev_pair {x : α} (hx : x ∈ H.darts) (k : ℕ) :
    prevEl (listPairs (D.f x))
      (H.node ((H.faceMap ^ k) x), H.node ((H.faceMap ^ (k + 1)) x)) =
      (H.node ((H.faceMap ^ ((k + (H.face x).ncard - 1) % (H.face x).ncard)) x),
        H.node ((H.faceMap ^ k) x)) := by
  have hlen := D.f_len hx
  have hCpos := D.f_card_pos hx
  have hC0 : (H.face x).ncard ≠ 0 := Nat.ne_of_gt hCpos
  have hlenP := D.len_listPairs_f hx
  have hmem := D.f_pair_mem hx k
  rw [prevEl_eq_getD_idxOf hmem]
  -- 雷区 #172：`prevEl_eq_getD_idxOf`（TameList67）把 `idxOf` 的 BEq 实例
  -- 固化为 `instBEqOfDecidableEq`；本地重述同一表达式时 TC 会误选
  -- `instBEqProd`，故显式指定实例，否则 getD→getElem 迁移不匹配。
  have hmodlt : (@List.idxOf (Set α × Set α) instBEqOfDecidableEq
      (H.node ((H.faceMap ^ k) x), H.node ((H.faceMap ^ (k + 1)) x))
      (listPairs (D.f x)) + (listPairs (D.f x)).length - 1) %
      (listPairs (D.f x)).length < (listPairs (D.f x)).length :=
    Nat.mod_lt _ (by rw [hlenP]; exact hCpos)
  trans (listPairs (D.f x))[(@List.idxOf (Set α × Set α) instBEqOfDecidableEq
      (H.node ((H.faceMap ^ k) x), H.node ((H.faceMap ^ (k + 1)) x))
      (listPairs (D.f x)) + (listPairs (D.f x)).length - 1) %
      (listPairs (D.f x)).length]'hmodlt
  · exact TameLp.getD_eq_getElem_of_lt hmodlt _
  have hnodP : (listPairs (D.f x)).Nodup := nodup_listPairs68 (D.f_nodup hx)
  have hi : k % (H.face x).ncard < (H.face x).ncard := Nat.mod_lt _ hCpos
  have hltp : k % (H.face x).ncard < (listPairs (D.f x)).length := by
    rw [hlenP]; exact hi
  have hget : (listPairs (D.f x))[k % (H.face x).ncard]'hltp =
      (H.node ((H.faceMap ^ k) x), H.node ((H.faceMap ^ (k + 1)) x)) := by
    obtain ⟨hlt', he⟩ := List.getElem?_eq_some_iff.mp (D.f_pair_getElem? hx hi)
    rw [he]
    congr 1
    · rw [pow_mod_eq hC0 (H.pow_card_face_apply_self x) k]
    · rw [← pow_mod_eq hC0 (H.pow_card_face_apply_self x)
          (k % (H.face x).ncard + 1),
        mod_succ_mod68 k (H.face x).ncard hCpos,
        ← pow_mod_eq hC0 (H.pow_card_face_apply_self x) (k + 1)]
  have hidx : (@List.idxOf (Set α × Set α) instBEqOfDecidableEq
      (H.node ((H.faceMap ^ k) x), H.node ((H.faceMap ^ (k + 1)) x))
      (listPairs (D.f x))) = k % (H.face x).ncard := by
    rw [← hget]
    exact @TameLp.idxOf_getElem (Set α × Set α) instBEqOfDecidableEq _ _
      (listPairs (D.f x)) hnodP (k % (H.face x).ncard) hltp
  -- 桥 1：idxOf 原子 → k % C。先在 ℕ 层证指标等式，再用 getElemConN68
  -- 一次性迁移，避开依赖 proof 的 motive 雷区 #173。
  have hidxEq : (@List.idxOf (Set α × Set α) instBEqOfDecidableEq
      (H.node ((H.faceMap ^ k) x), H.node ((H.faceMap ^ (k + 1)) x))
      (listPairs (D.f x)) + (listPairs (D.f x)).length - 1) %
      (listPairs (D.f x)).length
      = (k % (H.face x).ncard + (listPairs (D.f x)).length - 1) %
        (listPairs (D.f x)).length := by
    rw [hidx]
  have h1lt : (k % (H.face x).ncard + (listPairs (D.f x)).length - 1) %
      (listPairs (D.f x)).length < (listPairs (D.f x)).length :=
    Nat.mod_lt _ (by rw [hlenP]; exact hCpos)
  rw [getElemConN68 hmodlt h1lt hidxEq]
  -- 指标折算：(k % C + C - 1) % C = (k + C - 1) % C
  have hpidx : (k % (H.face x).ncard + (H.face x).ncard - 1) % (H.face x).ncard =
      (k + (H.face x).ncard - 1) % (H.face x).ncard := by
    have hb : (H.face x).ncard - 1 < (H.face x).ncard := by omega
    have h1 : k % (H.face x).ncard + (H.face x).ncard - 1
        = k % (H.face x).ncard + ((H.face x).ncard - 1) := by omega
    have h2 : k + (H.face x).ncard - 1
        = k + ((H.face x).ncard - 1) := by omega
    rw [h1, h2]
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.mod_eq_of_lt hb]
  have hlenEq : (k % (H.face x).ncard + (listPairs (D.f x)).length - 1) %
      (listPairs (D.f x)).length
      = (k % (H.face x).ncard + (H.face x).ncard - 1) % (H.face x).ncard := by
    rw [hlenP]
  have hfinal : (k % (H.face x).ncard + (listPairs (D.f x)).length - 1) %
      (listPairs (D.f x)).length
      = (k + (H.face x).ncard - 1) % (H.face x).ncard := hlenEq.trans hpidx
  have hp_lt : (k + (H.face x).ncard - 1) % (H.face x).ncard <
      (H.face x).ncard := Nat.mod_lt _ hCpos
  have hp_ltP : (k + (H.face x).ncard - 1) % (H.face x).ncard <
      (listPairs (D.f x)).length := by rw [hlenP]; exact hp_lt
  have hold2 : (k % (H.face x).ncard + (listPairs (D.f x)).length - 1) %
      (listPairs (D.f x)).length < (listPairs (D.f x)).length := h1lt
  rw [getElemConN68 hold2 hp_ltP hfinal]
  obtain ⟨hlt2, he2⟩ := List.getElem?_eq_some_iff.mp (D.f_pair_getElem? hx hp_lt)
  rw [he2]
  congr 1
  -- 第二坐标 (p+1)%C = k%C
  have hstep : (((k + (H.face x).ncard - 1) % (H.face x).ncard) + 1) %
      (H.face x).ncard = k % (H.face x).ncard :=
    mod_pred_succ68 k (H.face x).ncard hCpos
  rw [← pow_mod_eq hC0 (H.pow_card_face_apply_self x)
      (((k + (H.face x).ncard - 1) % (H.face x).ncard) + 1),
    hstep, pow_mod_eq hC0 (H.pow_card_face_apply_self x) k]

end RxOkData

end Kepler.Text.TameSpine
