/-
  Kepler.Text.TameSpine.Reduction3KbwpbhqNtrans2 — tame-corr N-B 段第二波
  （nb2）：KBWPBHQ0（变换塔终止性）spine 形 + transform_count 消费双件 +
  PBFLHET 前端叶 + NCVIBWU 成员性半通用 i 塔层形。

  ┌─ 归属对账 ────────────────────────────────────────────────────
  │ §0 私有小件：replaceSpine 单件替换长度保持、flatten 长度账、
  │    fList 轨道两向（面内不出 face；final 态不出 r）。
  │ §1 `kbwpbhq0Spine`（HOL KBWPBHQ.hl:44 `KBWPBHQ0`）：
  │    `∃ i, finalListSpine (rtransSpine L N r x i)`。
  │    **DIFFERS（证体路线）**：HOL 证体 = 有界 indexf（bounded_index_
  │    find_face 消费 DIOWAAS/RYIUUVK）+ PNXVWFS2 反证；本证 = **纯计数
  │    论证**：¬final 每步 ntrans 长度恰增 1（replaceSpine 单件替换
  │    ++ 单件），而 AQIUNPP3 给状态 i 的 normal_list，其 flatten
  │    Nodup 且 ⊆ listOfDarts L，故 |ntrans i| ≤ |listOfDarts L|，
  │    取 i = |listOfDarts L| + 1 得矛盾。同一陈述、机器可核、且
  │    **不消费 PNXVWFS2**（即不经过 N-A 主塔）——nb1 冻结表中
  │    final_list_transform_count 的"非空性论证"卡点由此解锁。
  │ §2 `finalListTransformCountSpine`（HOL KBWPBHQ.hl:352
  │    `final_list_transform_count`）：kbwpbhq0Spine 非空 + `sInf`
  │    极小性一步（即 HOL Nuxcoea.MIN_LEAST 消费面）。
  │ §3 `sizelFinalListEqF`（HOL KBWPBHQ.hl:884 `sizel_final_list_eq_f`）：
  │    final 态 t 的 |rtrans t| = |find_face x|。DIFFERS（证体路线）：
  │    HOL 用 final_list_power/final_list_rot（rot 存在性）；本证 =
  │    轨道双向包含：rtrans t ⊆ face（final 态 fList 幂 = nextEl 幂，
  │    fList 轨道不出 face）与 face ⊆ rtrans t（final 态 fList 轨道
  │    不出 r），两向 Nodup 子列长度账收口。
  │ §4 `ztransInSucSpine`（HOL PBFLHET.hl:617 `ztrans_in_suc` 的塔层 i
  │    形）：l'z(i) ∈ rtrans(i+1)。证 = rtransSuccSpine（塔层折叠）
  │    + rtransCat（rtrans_cat 的 spine 形，其 ram2' = z 一步内嵌
  │    Seq2.next_prev_id）+ 头元成员。
  │ §5 PBFLHET 叶两件：`inductRev`（HOL PBFLHET.hl:35 `INDUCT_REV`，
  │    平凡算术翻转）+ `finalListInduct1Spine`（HOL PBFLHET.hl:44
  │    `FINAL_LIST_INDUCT1`：¬final@i ⇒ ∀ j ≤ i ¬final@j；证 = 逆向
  │    链式 finalListInductSpine（nb1 件）逐级下传）。
  │ §6（本轮会话期间已迁出）：NCVIBWU 通用 i 塔层形初版（成员性半薄包装）
  │    在本轮 c1–c3 编绿（logs/nb2_build_c3.log）；会话中期编排者续 822
  │    落库 `deebb37e`（aq13 V0 九槽全闭 + `ncvibwuV0FullSpine` 双半装配），
  │    通用 i **双半主件**随之可由薄包装直接闭——见姊妹文件
  │    `Reduction3NcvibwuTower.lean`（ncvibwuTowerSpine 等，编译基线
  │    ≥ `deebb37e`）。本文件保持对 `1a057cfb` 基线可编（零消费该落库）。
  └────────────────────────────────────────────────────────────────

  ┌─ 查重记账（工单 (a)3：Seq2.next_prev_id 公开形）───────────────
  │ 零重落：四形已在库——
  │ · `Kepler.Text.Reduction5.nextPrevId`（Reduction5BetwnBase:498，
  │   泛 α 纯 Nodup，免实例：next_el (prev_el x) = x，正是 Seq2.
  │   next_prev_id 方向）与 `prevNextId`（:445，反向 prev_next_id）；
  │ · `Kepler.Text.TameSpine.nextElPrevElUniq`（JcajyduRed2Trans:94，
  │   [BEq][LawfulBEq][DecidableEq] 公开形，spine 岛同库）；
  │ · `Kepler.Text.TameSpine.changeNextPrev`（Reduction3CoreSplitNormal
  │   :2293，泛 α [DecidableEq]，prev_next_id 方向）。
  │ 本文件经 rtransCat（内嵌 nextElPrevElUniq）消费，零新落。
  └────────────────────────────────────────────────────────────────

  ┌─ 世界选择记账（R1）────────────────────────────────────────────
  │ 全件 spine 世界（ℕ × ℕ，MarkedListSpineFull 载体）；泛 α 小件
  │ （replaceSpine/flatten 长度账）无 BEq 接触面。ncvibwuMemSpine
  │ 消费 ohcgkfuSpineV0 同为 spine 世界，零混合；本文件零 Dart 载体
  │ 件，R1 的 BEq 实例碰撞不触发。
  └────────────────────────────────────────────────────────────────

  纪律：零禁词（无公理、零占位证明、零反射式判定）；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3KbwpbhqNtrans
import Kepler.Text.TameSpine.Reduction3LnrxInductionSpine
import Kepler.Text.TameSpine.JcajyduRed2Trans
import Kepler.Text.TameSpine.JcajyduAqZIndexf
import Kepler.Text.TameSpine.TameList57
import Kepler.Text.TameSpine.TameList6

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl dart_in_face findFaceDarts_nodup
  findFaceDarts_congr_of_mem mem_darts_of_mem_findFace nextEl_mem_of_mem)

/-! ## §0 私有小件 -/

/-- `replaceSpine x [y]`（单件替换，tame_defs.hl `replace` 的 spine 载体）
保持表长：首处命中整段替换为 `[y] ++ zs`，长 = 1 + |zs| = 原长。 -/
private theorem lengthReplaceSpineSingleton {α : Type*} [DecidableEq α] (x y : α) :
    ∀ s : List α, (replaceSpine x [y] s).length = s.length := by
  intro s
  induction s with
  | nil => rfl
  | cons a t ih =>
    rw [show replaceSpine x [y] (a :: t)
        = if a = x then [y] ++ t else a :: replaceSpine x [y] t from rfl]
    split
    · rw [List.length_append, List.length_singleton, List.length_cons]
      omega
    · rw [List.length_cons, List.length_cons, ih]

/-- 全体成员非空的表族的 flatten 长度下界：|s| ≤ |s.flatten|。 -/
private theorem lengthLeFlattenOfAllNeNil {α : Type*} (s : List (List α))
    (h : ∀ t ∈ s, t ≠ []) : s.length ≤ s.flatten.length := by
  induction s with
  | nil => simp
  | cons t rest ih =>
    have h1 : t.length ≠ 0 := by
      have hmem := h t (List.mem_cons_self (a := t) (l := rest))
      rwa [Ne, List.length_eq_zero_iff]
    have h2 : rest.length ≤ rest.flatten.length :=
      ih (fun u hu => h u (List.mem_cons_of_mem _ hu))
    rw [List.flatten_cons, List.length_cons, List.length_append]
    omega

/-- fList 幂轨道不出面：`v ∈ list_of_darts` ⇒ `(fList)^k v ∈ find_face v`。
（face 表沿 congr 逐步换元 + fList 定义 = face 表上的 nextEl 一步。） -/
private theorem fListPowMemFace (L : fgraph ℕ) (hL : GoodList L) {v : ℕ × ℕ}
    (hvl : v ∈ listOfDarts L) (k : ℕ) :
    (fList L)^[k] v ∈ findFaceDarts L v := by
  induction k with
  | zero => exact (dart_in_face L v).mpr hvl
  | succ k ih =>
    have hcong : findFaceDarts L ((fList L)^[k] v) = findFaceDarts L v :=
      findFaceDarts_congr_of_mem hL.1 hvl ih
    rw [Function.iterate_succ_apply']
    show nextEl (findFaceDarts L ((fList L)^[k] v)) ((fList L)^[k] v)
      ∈ findFaceDarts L v
    rw [hcong]
    exact nextEl_mem_of_mem ih

/-- final 态 fList 幂轨道不出环：`final s`、`v ∈ s` ⇒ `(fList)^k v ∈ s`。
（final 定义 fList = nextEl on s 逐步代入。） -/
private theorem fListPowMemFinal (L : fgraph ℕ) {s : List (ℕ × ℕ)}
    (hfin : finalListSpine L s) {v : ℕ × ℕ} (hv : v ∈ s) (k : ℕ) :
    (fList L)^[k] v ∈ s := by
  induction k with
  | zero => exact hv
  | succ k ih =>
    rw [Function.iterate_succ_apply', hfin _ ih]
    exact nextEl_mem_of_mem ih

/-! ## §1 KBWPBHQ0（HOL KBWPBHQ.hl:44）spine 形：变换塔终止性 -/

/-- ¬final 态的长度增长一步：|ntrans(i+1)| = |ntrans(i)| + 1。
（ntransSuccSpine 塔层折叠 + ntrans1 展开一步 + §0 首件收口；
替换列表为单件 [split.2]，附加尾单件 [split.1]。） -/
private theorem ntransSuccLen (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (x : ℕ × ℕ) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i)) :
    (ntransSpine L N r x (i + 1)).length = (ntransSpine L N r x i).length + 1 := by
  rw [ntransSuccSpine L N r x i,
    ntrans1 L (ntransSpine L N r x i) (rtransSpine L N r x i) x hf,
    List.length_append, lengthReplaceSpineSingleton, List.length_singleton]

/-- **HOL `KBWPBHQ0`**（KBWPBHQ.hl:44）spine 形：
`marked_list ⇒ ∃ i, final_list (rtrans i)`——变换塔必达终态。
证体路线 DIFFERS（纯计数，见文件头）：¬final 每步 |N'| 增 1，
而 AQIUNPP3 给状态 K+1 的 normal_list：|N'| ≤ |flatten N'| ≤
|list_of_darts L|（记 K），取 i = K + 1 得 |N| + K + 1 ≤ K，矛盾。
**零消费 PNXVWFS2**（HOL 路线的主卡点），不经 N-A 主塔。 -/
theorem kbwpbhq0Spine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) :
    ∃ i : ℕ, finalListSpine L (rtransSpine L N r x i) := by
  by_contra h
  -- h : ¬∃ i, final@i ⟹ 全程 ¬final（手工换位，零 push_neg 依赖）
  have h' : ∀ i : ℕ, ¬ finalListSpine L (rtransSpine L N r x i) := fun i hi =>
    h ⟨i, hi⟩
  -- 长度账：¬final 全程，|ntrans i| = |N| + i
  have grow : ∀ i : ℕ, (ntransSpine L N r x i).length = N.length + i := by
    intro i
    induction i with
    | zero => rfl
    | succ k ih =>
      rw [ntransSuccLen L N r x k (h' k), ih]
      omega
  -- 状态 K+1 的 normal_list（AQIUNPP3）
  have hmr := aqiunpp3 L hL ((listOfDarts L).length + 1) hta hgn hm
  have hn : NormalListSpine hL
      (ntransSpine L N r x ((listOfDarts L).length + 1)) := hmr.1.2.1
  -- (a) 全员非空 ⇒ |N'| ≤ |flatten N'|
  have h1 : (ntransSpine L N r x ((listOfDarts L).length + 1)).length
      ≤ (ntransSpine L N r x ((listOfDarts L).length + 1)).flatten.length :=
    lengthLeFlattenOfAllNeNil _ hn.2.1
  -- (b) flatten N' Nodup 且 ⊆ list_of_darts ⇒ |flatten N'| ≤ K
  have h2 : (ntransSpine L N r x ((listOfDarts L).length + 1)).flatten.length
      ≤ (listOfDarts L).length :=
    List.Subperm.length_le
      (hn.1.subperm fun d hd => normalListListOfDarts hn d hd)
  have hg := grow ((listOfDarts L).length + 1)
  omega

/-! ## §2 final_list_transform_count（KBWPBHQ.hl:352）spine 镜像 -/

/-- **HOL `final_list_transform_count`**（KBWPBHQ.hl:352）：
`transform_count = t ⇒ final_list (rtrans t)`。
证 = kbwpbhq0Spine 供非空 + `sInf` 极小性成员一步
（HOL Nuxcoea.MIN_LEAST 消费面的 spine 形，minNumSpine = sInf）。 -/
theorem finalListTransformCountSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) {t : ℕ}
    (ht : transformCountSpine L N r x = t) :
    finalListSpine L (rtransSpine L N r x t) := by
  obtain ⟨i, hi⟩ := kbwpbhq0Spine L hL hta hgn hm
  have hmem : sInf {i : ℕ | finalListSpine L (rtransSpine L N r x i)}
      ∈ {i : ℕ | finalListSpine L (rtransSpine L N r x i)} :=
    Nat.sInf_mem ⟨i, hi⟩
  rw [← ht]
  exact hmem

/-! ## §3 sizel_final_list_eq_f（KBWPBHQ.hl:884）spine 镜像 -/

/-- **HOL `sizel_final_list_eq_f`**（KBWPBHQ.hl:884）：
`transform_count = t ⇒ |rtrans t| = |find_face x|`。
证体路线 DIFFERS（见文件头）：两向轨道包含——
⊆：d ∈ rtrans t ⇒ d = (nextEl (rtrans t))^k w = (fList)^k w ∈ face w = face x
（final 态 fList 幂 = nextEl 幂；fList 轨道不出 face，§0 件三）；
⊇：n ∈ face x ⇒ n = (fList)^k w ∈ rtrans t（final 态 fList 轨道不出 r，
§0 件四）。两向 Nodup 子列长度账收口。前提子集：HOL 的
`find_face L x = f` 换元件在陈述中直接代入（零收窄）。 -/
theorem sizelFinalListEqF (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) {t : ℕ}
    (ht : transformCountSpine L N r x = t) :
    (rtransSpine L N r x t).length = (findFaceDarts L x).length := by
  have hfin : finalListSpine L (rtransSpine L N r x t) :=
    finalListTransformCountSpine L hL hta hgn hm ht
  have hmt := aqiunpp3 L hL t hta hgn hm
  have hrnd : (rtransSpine L N r x t).Nodup :=
    (normalListUniqNonnil hmt.1.2.1 hmt.1.2.2.1).1
  have hxl : x ∈ listOfDarts L :=
    normalListListOfDarts hm.1.2.1 x
      (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hm.1.2.2.2.1⟩)
  -- w := next_el (find_face x) x 的两侧成员性
  have hw2 : nextEl (findFaceDarts L x) x ∈ findFaceDarts L x :=
    aq10_memNextMarkInface L hL hgn hm
  have hw1 : nextEl (findFaceDarts L x) x ∈ rtransSpine L N r x t :=
    nextMarkMemRTransSpine L hL hgn hta hm t
  have hwl : nextEl (findFaceDarts L x) x ∈ listOfDarts L :=
    mem_darts_of_mem_findFace L hw2
  have hcongW : findFaceDarts L (nextEl (findFaceDarts L x) x)
      = findFaceDarts L x :=
    findFaceDarts_congr_of_mem hL.1 hxl hw2
  have hfnd : (findFaceDarts L x).Nodup := findFaceDarts_nodup hL.1 x
  -- ⊆：d ∈ rtrans t ⇒ d ∈ face x
  have hsub1 : ∀ d ∈ rtransSpine L N r x t, d ∈ findFaceDarts L x := by
    intro d hd
    have hk := indexfN hw1 hd hrnd
    have hfp := finalListPowerFn
      (indexf (nextEl (findFaceDarts L x) x) d (rtransSpine L N r x t)) L
      (rtransSpine L N r x t) hfin _ hw1
    rw [← hfp] at hk
    have hface := fListPowMemFace L hL hwl
      (indexf (nextEl (findFaceDarts L x) x) d (rtransSpine L N r x t))
    rw [hcongW, hk] at hface
    exact hface
  -- ⊇：n ∈ face x ⇒ n ∈ rtrans t
  have hsub2 : ∀ n ∈ findFaceDarts L x, n ∈ rtransSpine L N r x t := by
    intro n hn
    have hk := indexfN hw2 hn hfnd
    have hww : nextEl (findFaceDarts L x) x
        ∈ findFaceDarts L (nextEl (findFaceDarts L x) x) := by
      rw [hcongW]
      exact hw2
    have hfe := fListPowEqNextElPow L hL _ hww
      (indexf (nextEl (findFaceDarts L x) x) n (findFaceDarts L x))
    rw [hcongW, hk] at hfe
    have hmem := fListPowMemFinal L hfin hw1
      (indexf (nextEl (findFaceDarts L x) x) n (findFaceDarts L x))
    rw [hfe] at hmem
    exact hmem
  -- Nodup 子列长度账收口
  exact le_antisymm (List.Subperm.length_le (hrnd.subperm hsub1))
    (List.Subperm.length_le (hfnd.subperm hsub2))

/-! ## §4 ztrans_in_suc（PBFLHET.hl:617）spine 镜像（塔层 i 形） -/

/-- **HOL `Pbflhet.ztrans_in_suc`**（PBFLHET.hl:617）塔层 i 形：
`¬final (rtrans i) ⇒ MEM (l'z(i)) (rtrans (SUC i))`。
证 = 塔层折叠 rtransSuccSpine（在库）+ rtransCat（rtrans_cat 的
spine 形；其 ram2' = z 一步内嵌 Seq2.next_prev_id，经
nextElPrevElUniq，见文件头查重记账）+ 头元成员。前提子集：
HOL 的 find_face/next_el 数据件在证体中零消费，免携（更强形）。 -/
theorem ztransInSucSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i)) :
    ztransSpine L N r x i ∈ rtransSpine L N r x (i + 1) := by
  rw [rtransSuccSpine L N r x i]
  have hmr := aqiunpp3 L hL i hta hgn hm
  have hrnd : (rtransSpine L N r x i).Nodup :=
    (normalListUniqNonnil hmr.1.2.1 hmr.1.2.2.1).1
  have hcat := rtransCat L (ntransSpine L N r x i) (rtransSpine L N r x i) x
    hf hrnd
  rw [show ztransSpine L N r x i
      = lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x from rfl, hcat]
  simp

/-! ## §5 PBFLHET 前端叶：INDUCT_REV + FINAL_LIST_INDUCT1 -/

/-- **HOL `Pbflhet.INDUCT_REV`**（PBFLHET.hl:35）：`∀ i ≤ j, P i` ↔
`∀ i ≤ j, P (j - i)`——逆向归纳翻转（纯算术）。 -/
theorem inductRev (j : ℕ) (P : ℕ → Prop) :
    (∀ i, i ≤ j → P i) ↔ (∀ i, i ≤ j → P (j - i)) := by
  constructor
  · intro h i hi
    exact h (j - i) (by omega)
  · intro h i hi
    have hm := h (j - i) (by omega)
    rwa [Nat.sub_sub_self hi] at hm

/-- **HOL `Pbflhet.FINAL_LIST_INDUCT1`**（PBFLHET.hl:44）：`¬final@i ⇒
∀ j ≤ i, ¬final@j`。证 = 逆向链式：从 i 出发沿 finalListInductSpine
（nb1 件：¬final@(k+1) ⇒ ¬final@k）逐级下传——即 HOL 证体的
INDUCT_REV 翻转 + 归纳，Lean 侧直接对差值 m = i - j 归纳。前提子集
（更强形，免 TAV2/marked，与 finalListInductSpine 同口径）。 -/
theorem finalListInduct1Spine (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (x : ℕ × ℕ) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i)) :
    ∀ j, j ≤ i → ¬ finalListSpine L (rtransSpine L N r x j) := by
  have key : ∀ m, m ≤ i → ¬ finalListSpine L (rtransSpine L N r x (i - m)) := by
    intro m
    induction m with
    | zero => exact fun _ => hf
    | succ m ih =>
      intro hm
      have him := ih (by omega)
      have heq : i - m = (i - (m + 1)) + 1 := by omega
      rw [heq] at him
      exact finalListInductSpine L N r x (i - (m + 1)) him
  intro j hj
  have hm := key (i - j) (by omega)
  rwa [Nat.sub_sub_self hj] at hm

/-! ## §6（迁出：见文件头）NCVIBWU 通用 i 塔层形 → Reduction3NcvibwuTower.lean -/

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.kbwpbhq0Spine
#print axioms Kepler.Text.TameSpine.finalListTransformCountSpine
#print axioms Kepler.Text.TameSpine.sizelFinalListEqF
#print axioms Kepler.Text.TameSpine.ztransInSucSpine
#print axioms Kepler.Text.TameSpine.inductRev
#print axioms Kepler.Text.TameSpine.finalListInduct1Spine
