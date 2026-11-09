/-
  Kepler.Text.TameSpine.JcajyduAqTowerBase — jcajydu J2 批 E（w2）第一口：
  HOL AQ1–13 章（reduction2.hl:806 `transform_assumption_v2_lemma` 的证词塔）
  的**塔底自含切片** + 塔顶 13 陈述槽 + 装配胶水 + 第一个 AQ 叶（AQ6）。

  ┌─ 考古锚（AGENTS §8；详见 lane DELIVERY.md）─────────────────────
  │ 塔对象 = AQ1/AQ23/AQ4/AQ56/AQ7/AQ8/AQ9/AQ10/AQ11/AQ12/AQ13.hl
  │ （11 文件 17,585 HOL 行 / 214 定理；AQ2/AQ3 在 AQ23，AQ5/AQ6 在
  │ AQ56）。13 条主定理**同构前提** `good_list L ∧ good_list_nodes L ∧
  │ marked_list L N r x`，结论恰好逐一补全 marked_list 9 合取块在
  │ (N', r') = (ntrans…1, rtrans…1) 处的槽位：
  │   AQ1–AQ5 = normal_list 的 5 合取（tame_defs2.hl:93-:100），
  │   AQ6 = MEM r' N'、AQ7 = MEM x r'、AQ8/AQ9 = quotient_list 双件、
  │   AQ10 = next_el r' x = f_list L x、AQ11 = final_list (find_list N'…)、
  │   AQ12/AQ13 = flag/s_flag 双分支——与树内 TameList5 NormalListSpine、
  │   TameList7 MarkedListSpine、TameList13 FlagListSpine/SFlagListSpine
  │   的合取序**逐一对应**（本文件 §3 的 13 个纯 def : Prop 槽即该对账）。
  │ 文件级依赖分层（grep 跨文件引用普查，详 DELIVERY §1.2）：
  │   L2 零跨AQ依赖：AQ23/AQ56/AQ7/AQ1；L3: AQ4←(AQ1,AQ23)、AQ10←(AQ7,AQ4)；
  │   L4: AQ8←(AQ1,AQ23,AQ4,AQ56)、AQ9←AQ8；L5: AQ11←(AQ1,AQ9)、
  │   AQ13←(AQ7,AQ8,AQ9,AQ10)；L6: AQ12←几乎全部；塔顶打包 :806。
  └────────────────────────────────────────────────────────────────

  ┌─ 本批（塔底三组 + 第一叶）────────────────────────────────────
  │ ① replaceSpine 成员三元组（tame_list.hl:546-:600 MEM_replace /
  │   MEM2_replace / MEM3_replace，泛型 α）——AQ2/AQ3/AQ6 与批 E2 的
  │   消费马；② min 幂引擎（PWSSRAT.hl:44/:79 min_not_eq_imp_eq /
  │   min_not_eq_imp_eq_at，纯函数泛型）→ l'y 幂表示（PWSSRAT.hl:263
  │   l_y_rep_power：f_list L x = next_el r x ⇒ l'y = (next_el r)^
  │   [SUC l'm] x）；③ ytrans 成员双件（HOJODCM.hl:49/:152
  │   ytrans_mem_rtrans_v0 / mem_ytrans_list_of_darts_v0）——Hojodcm
  │   四件中的两件干净落地；④ 塔顶 13 陈述槽（纯 def : Prop）+ 装配
  │   定理（HOL :806-:848 装配结构的 Lean 孪生：9 合取逐槽重组合）；
  │   ⑤ **AQ6 第一叶真证**（AQ56.hl:648-:696：final 支 = ntransId/
  │   rtransId + MEM r N；¬final 支 = ntrans1 展开 + MEM2_replace；
  │   HOL 证明装载的 uniq_find_face/marked_list_of_dart/PPLHULJ_v0/
  │   z_not_eq_ytrans 上下文在 Lean 直达路线中零消费）。
  └────────────────────────────────────────────────────────────────

  ┌─ 债务隔离与雷区 ───────────────────────────────────────────────
  │ 零消费 TameList16:1109 `markedListIsNodeNondegenerate` 在案 sorry
  │ 债链（markedListMarked/markedTranslate/hqymrtx1-3List 携带
  │ sorryAx）——Hojodcm 四件中 **z 侧两件**（mem_ztrans_rtrans_v0 /
  │ z_not_eq_ytrans_v0）的 HOL 证词吃 HQYMRTX1_list，在本树干净路线
  │ 需先闭该债，本批**绕行不落地**（UNRESOLVED，见 DELIVERY §1.4）。
  │ TameList17:93 splitNormalListSpine.nd off-by-one（续411 在案）：
  │ 本批 aq6 只涉 split.2/new2 支（ntrans1/rtrans 形），对该偏差不敏
  │ 感，照 j2w1 批 A 先例在现有载体上陈述；off-by-one 本体归 DEF-FIX。
  │ 泛型 binder 雷区（j2w1/c2 实测）：memPowerNextEl 沿 TameLp 三例
  │ [BEq α][LawfulBEq α][DecidableEq α] 随形；min 幂引擎是纯函数层
  │ （无 BEq 面），零实例参。
  └────────────────────────────────────────────────────────────────

  纪律：零 sorry/admit/native_decide/axiom 声明；既有文件零触碰；主仓
  tracked 零改动（本文件经 patch 交付）。
-/

import Kepler.Text.TameSpine.TameList17
import Kepler.Text.TameLp
import Kepler.Text.TameSpine.JcajyduBetwnBase
import Kepler.Text.TameSpine.JcajyduRed2Trans

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl prevEl eList fList GoodList findFaceDarts nList
  listOfDarts)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)

/-! ## §0 replaceSpine 成员三元组（tame_list.hl:546-:600）

`replaceSpine f xs g`（TameList17:75，HOL `replace` tame_defs.hl:317 逐句
镜像）= 把 `g` 中**首个** `f` 段替换为 `xs`。HOL 三件成员引理逐条镜像
（泛型 α，AQ 塔各文件共享的消费马）。 -/

/-- **HOL `MEM2_replace`**（tame_list.hl:566-:581）
`MEM f g /\ MEM x xs ==> MEM x (replace f xs g)`——AQ6 ¬final 支的直接
证词（`r ∈ N`（marked_list 合取 3）+ `x ∈ [new2]` ⇒ 新 r' 落在 replace 段）。 -/
theorem memReplaceFstMem {α : Type*} [DecidableEq α] {f x : α} {xs g : List α}
    (hf : f ∈ g) (hx : x ∈ xs) : x ∈ replaceSpine f xs g := by
  induction g with
  | nil => simp at hf
  | cons z zs ih =>
    by_cases hzx : z = f
    · simp only [replaceSpine, if_pos hzx]
      exact List.mem_append.mpr (Or.inl hx)
    · simp only [replaceSpine, if_neg hzx]
      rcases List.mem_cons.mp hf with hfl | hfr
      · exact absurd hfl.symm hzx
      · exact List.mem_cons_of_mem _ (ih hfr)

/-- **HOL `MEM3_replace`**（tame_list.hl:583-:598）
`~(x = f) /\ MEM x g ==> MEM x (replace f xs g)`——非命中位原样保留。 -/
theorem memReplaceOfNeMem {α : Type*} [DecidableEq α] {f x : α} {xs g : List α}
    (hxf : x ≠ f) (hxg : x ∈ g) : x ∈ replaceSpine f xs g := by
  induction g with
  | nil => simp at hxg
  | cons z zs ih =>
    by_cases hzx : z = f
    · simp only [replaceSpine, if_pos hzx]
      rcases List.mem_cons.mp hxg with hxl | hxr
      · exact absurd (hxl.trans hzx) hxf
      · exact List.mem_append.mpr (Or.inr hxr)
    · simp only [replaceSpine, if_neg hzx]
      rcases List.mem_cons.mp hxg with hxl | hxr
      · rw [hxl]; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih hxr)

/-- **HOL `MEM_replace`**（tame_list.hl:546-:564）的反向形
`MEM x (replace f xs g) ==> MEM x g \/ (MEM f g /\ MEM x xs)`——替换表
成员的两源分解（AQ2/AQ3 的消费形，批 E2 主用）。 -/
theorem memReplaceCases {α : Type*} [DecidableEq α] {f x : α} {xs g : List α}
    (h : x ∈ replaceSpine f xs g) : x ∈ g ∨ f ∈ g ∧ x ∈ xs := by
  induction g with
  | nil => simp [replaceSpine] at h
  | cons z zs ih =>
    by_cases hzx : z = f
    · simp only [replaceSpine, if_pos hzx] at h
      rcases List.mem_append.mp h with hx1 | hx2
      · exact Or.inr ⟨by rw [hzx]; exact List.mem_cons_self .., hx1⟩
      · exact Or.inl (List.mem_cons_of_mem _ hx2)
    · simp only [replaceSpine, if_neg hzx] at h
      rcases List.mem_cons.mp h with hxl | hxr
      · exact Or.inl (by rw [hxl]; exact List.mem_cons_self ..)
      · rcases ih hxr with hcase | ⟨hfz, hxs⟩
        · exact Or.inl (List.mem_cons_of_mem _ hcase)
        · exact Or.inr ⟨List.mem_cons_of_mem _ hfz, hxs⟩

/-! ## §1 min 幂引擎（PWSSRAT.hl:44-:84）

HOL `min_num`（空集 junk 0）↦ `minNumSpine = sInf`（TameList12:91 公开
载体）。命题无 BEq 面（纯函数迭代），零实例参——泛型 binder 雷区不适用。 -/

/-- **HOL `min_not_eq_imp_eq`**（PWSSRAT.hl:44-:75）
`min_num {m | ¬((f POWER SUC SUC m) x = g ((f POWER SUC m) x))} = n ==>
∀ i ≤ n. (f POWER SUC i) x = (g POWER i) (f x)`——l'm 极小性的逐点展开
（i 归纳；i < n 时 i 落集合 ⇒ n ≤ i 矛盾，故等式链逐段成立）。 -/
theorem minNotEqImpEq {α : Type*} (f g : α → α) (x : α) (n : ℕ)
    (h : minNumSpine {m : ℕ | f^[m + 2] x ≠ g (f^[m + 1] x)} = n) :
    ∀ i : ℕ, i ≤ n → f^[i + 1] x = (g)^[i] (f x) := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hkk : k ≤ n := by omega
    have hIH := ih hkk
    have hmem : ¬ (k ∈ {m : ℕ | f^[m + 2] x ≠ g (f^[m + 1] x)}) := by
      intro hm
      have hle : minNumSpine {m : ℕ | f^[m + 2] x ≠ g (f^[m + 1] x)} ≤ k :=
        Nat.sInf_le hm
      rw [h] at hle
      omega
    simp only [Set.mem_setOf_eq, not_not] at hmem
    rw [hmem, hIH, Function.iterate_succ_apply']

/-- **HOL `min_not_eq_imp_eq_at`**（PWSSRAT.hl:79-:84）：i := n 特例
`(f POWER SUC n) x = (g POWER n) (f x)`。 -/
theorem minNotEqImpEqAt {α : Type*} (f g : α → α) (x : α) (n : ℕ)
    (h : minNumSpine {m : ℕ | f^[m + 2] x ≠ g (f^[m + 1] x)} = n) :
    f^[n + 1] x = (g)^[n] (f x) :=
  minNotEqImpEq f g x n h n (Nat.le_refl n)

/-! ## §2 l'y 幂表示与 ytrans 成员双件（Hojodcm 四件的干净两件）

载体记账：HOL `ytrans L N r x 0 = l'y L r x`（trans0 第三合取，j2w1
trans0 同注），故本节陈述以 `lYSpine L r x` 直接承载 ytrans₀；
`l'm L r x = min_num {m | ¬(ITER (SUC SUC m) (next_el r) x =
f_list L (ITER (SUC m) (next_el r) x))}`（tame_defs2.hl:440）↦
`lMSpine`（TameList12:136）。 -/

/-- **HOL `l_y_rep_power`**（PWSSRAT.hl:263-:272）
`f_list L x = next_el r x ==> l'y L r x = ITER (SUC (l'm L r x)) (next_el r) x`
——l_y 定义展开 + min_not_eq_imp_eq_at 的 g-迭代重排（f x = f_list L x
桥接）。 -/
theorem lYRepPower (L : fgraph ℕ) (r : List (ℕ × ℕ)) (x : ℕ × ℕ)
    (hf : fList L x = nextEl r x) :
    lYSpine L r x = (nextEl r)^[lMSpine L r x + 1] x := by
  have hmin := minNotEqImpEq (nextEl r) (fList L) x (lMSpine L r x) rfl
  unfold lYSpine
  rw [Function.iterate_succ_apply, hf, ← hmin (lMSpine L r x) (Nat.le_refl _)]

/-- **HOL `Hojodcm.ytrans_mem_rtrans_v0`**（HOJODCM.hl:49-:64）
`good_list L /\ good_list_nodes L /\ marked_list L N r x /\
~(final_list L r) ==> MEM (ytrans L N r x 0) r`——l_y_rep_power 给
next_el 幂形后 `MEM_POWER_NEXT_EL`（Aq8 形免 uniq，JcajyduBetwnBase
memPowerNextEl）直投。载体记账：`next_el r x = f_list L x` 是
marked_list 合取 6（MarkedListSpine 第 6 槽），HOL 经
f_eq_next_el_x_v0 绕 rotate_to 的路线在本树免 rotate_to 直达；
¬final 前提 HOL 证明未消费，逐字保留（j2w1 rtransFinalProp 同例）。 -/
theorem ytransMemRtrans (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    lYSpine L r x ∈ r := by
  rw [lYRepPower L r x (hm.1.2.2.2.2.2.1).symm]
  exact memPowerNextEl hm.1.2.2.2.1 _

/-- **HOL `Hojodcm.mem_ytrans_list_of_darts_v0`**（HOJODCM.hl:152-:176）
`good_list L /\ good_list_nodes L /\ marked_list L N r x /\
~(final_list L r) ==> MEM (ytrans L N r x 0) (list_of_darts L)`——
y ∈ r + r ∈ N ⇒ y ∈ flatten N，normal_list 的 loop_list 合取（批 5
normalListListOfDarts 的 flatten 提升）直投；HOL 的 loop_list 双层
THAYTHE 展开（:168-:176）在 Lean 由合取投影替换。 -/
theorem memYtransListOfDarts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    lYSpine L r x ∈ listOfDarts L :=
  normalListListOfDarts hm.1.2.1 (lYSpine L r x)
    (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, ytransMemRtrans L hL hgn hm hf⟩)

/-! ## §3 塔顶 13 陈述槽（纯 `def : Prop`，零证明义务）

13 槽 = AQ1–AQ13 主定理结论的 Lean 孪生（HOL 各 `_concl` 逐字折算），
合取槽位对账见模块头考古锚；签名沿 `transformAssumptionSpine`
（TameList17:135）的 ∀ 形：GoodList L 由证人 hL 入参承载，
GoodListNodesTl + MarkedListSpineFull 在 ∀ 内（HOL good_list_nodes /
marked_list 前提槽）。**只立陈述**——各叶证明属批 E2+。 -/

/-- **HOL `AQ1_concl`**（AQ1.hl:2147）：`uniq (flatten (ntrans L N r x 1))`
——marked_list 新 N' 的 normal_list 合取 1。 -/
def aq1Concl (L : fgraph ℕ) (hL : GoodList L) : Prop :=
  ∀ (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ)) (x : ℕ × ℕ),
    GoodListNodesTl L hL → MarkedListSpineFull hL N r x →
    (ntransSpine L N r x 1).flatten.Nodup

/-- **HOL `AQ2_concl`**（AQ23.hl:39）：`all (\s. ~(s = [])) (ntrans … 1)`
——normal_list 合取 2。 -/
def aq2Concl (L : fgraph ℕ) (hL : GoodList L) : Prop :=
  ∀ (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ)) (x : ℕ × ℕ),
    GoodListNodesTl L hL → MarkedListSpineFull hL N r x →
    ∀ s ∈ ntransSpine L N r x 1, s ≠ []

/-- **HOL `AQ3_concl`**（AQ23.hl:263）：`all (f_last L) (ntrans … 1)`
——normal_list 合取 3。 -/
def aq3Concl (L : fgraph ℕ) (hL : GoodList L) : Prop :=
  ∀ (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ)) (x : ℕ × ℕ),
    GoodListNodesTl L hL → MarkedListSpineFull hL N r x →
    ∀ s ∈ ntransSpine L N r x 1, fLastSpine L s

/-- **HOL `AQ4_concl`**（AQ4.hl:692）：`all (loop_list L) (ntrans … 1)`
——normal_list 合取 4。 -/
def aq4Concl (L : fgraph ℕ) (hL : GoodList L) : Prop :=
  ∀ (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ)) (x : ℕ × ℕ),
    GoodListNodesTl L hL → MarkedListSpineFull hL N r x →
    ∀ s ∈ ntransSpine L N r x 1, loopListSpine L s

/-- **HOL `AQ5_concl`**（AQ56.hl:129）：node 闭包——normal_list 合取 5
（HOL 的 `MEM d (flatten (ntrans …))` 前提即逐点 ∀ 形）。 -/
def aq5Concl (L : fgraph ℕ) (hL : GoodList L) : Prop :=
  ∀ (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ)) (x : ℕ × ℕ),
    GoodListNodesTl L hL → MarkedListSpineFull hL N r x →
    ∀ d ∈ (ntransSpine L N r x 1).flatten,
      (hypermapOfList L hL).node d ⊆ {d' | d' ∈ (ntransSpine L N r x 1).flatten}

/-- **HOL `AQ6_concl`**（AQ56.hl:648）：`MEM (rtrans L N r x 1)
(ntrans L N r x 1)`——marked_list 合取 3（MEM r N）。**本批 §5 真证**。 -/
def aq6Concl (L : fgraph ℕ) (hL : GoodList L) : Prop :=
  ∀ (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ)) (x : ℕ × ℕ),
    GoodListNodesTl L hL → MarkedListSpineFull hL N r x →
    rtransSpine L N r x 1 ∈ ntransSpine L N r x 1

/-- **HOL `AQ7_concl`**（AQ7.hl:206）：`MEM x (rtrans L N r x 1)`
——marked_list 合取 4（MEM x r）。 -/
def aq7Concl (L : fgraph ℕ) (hL : GoodList L) : Prop :=
  ∀ (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ)) (x : ℕ × ℕ),
    GoodListNodesTl L hL → MarkedListSpineFull hL N r x →
    x ∈ rtransSpine L N r x 1

/-- **HOL `AQ8_concl`**（AQ8.hl:3341）：`all uniq (quotient_list L N')`
——marked_list 合取 5 前件。 -/
def aq8Concl (L : fgraph ℕ) (hL : GoodList L) : Prop :=
  ∀ (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ)) (x : ℕ × ℕ),
    GoodListNodesTl L hL → MarkedListSpineFull hL N r x →
    ∀ q ∈ quotientListSpine L (ntransSpine L N r x 1), q.Nodup

/-- **HOL `AQ9_concl`**（AQ9.hl:1368）：quotient 非退化（sizel > 1）
——marked_list 合取 5 后件。 -/
def aq9Concl (L : fgraph ℕ) (hL : GoodList L) : Prop :=
  ∀ (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ)) (x : ℕ × ℕ),
    GoodListNodesTl L hL → MarkedListSpineFull hL N r x →
    ∀ v ∈ (quotientListSpine L (ntransSpine L N r x 1)).flatten,
      1 < ((quotientListSpine L (ntransSpine L N r x 1)).filter
        (fun q => decide (v ∈ q))).length

/-- **HOL `AQ10_concl`**（AQ10.hl:102）：`next_el (rtrans … 1) x =
f_list L x`——marked_list 合取 6。 -/
def aq10Concl (L : fgraph ℕ) (hL : GoodList L) : Prop :=
  ∀ (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ)) (x : ℕ × ℕ),
    GoodListNodesTl L hL → MarkedListSpineFull hL N r x →
    nextEl (rtransSpine L N r x 1) x = fList L x

/-- **HOL `AQ11_concl`**（AQ11.hl:229）：`final_list L (find_list N'
(e_list x))`——marked_list 合取 7。 -/
def aq11Concl (L : fgraph ℕ) (hL : GoodList L) : Prop :=
  ∀ (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ)) (x : ℕ × ℕ),
    GoodListNodesTl L hL → MarkedListSpineFull hL N r x →
    finalListSpine L (findListSpine (ntransSpine L N r x 1) (eList x))

/-- **HOL `AQ12_concl`**（AQ12.hl:3643）：`final_list L r' ==>
flag_list L N'`——marked_list 合取 8。 -/
def aq12Concl (L : fgraph ℕ) (hL : GoodList L) : Prop :=
  ∀ (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ)) (x : ℕ × ℕ),
    GoodListNodesTl L hL → MarkedListSpineFull hL N r x →
    finalListSpine L (rtransSpine L N r x 1) →
    FlagListSpine L (ntransSpine L N r x 1)

/-- **HOL `AQ13_concl`**（AQ13.hl:965）：`~final_list L r' ==>
s_flag_list L N' r' x`——marked_list 合取 9。 -/
def aq13Concl (L : fgraph ℕ) (hL : GoodList L) : Prop :=
  ∀ (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ)) (x : ℕ × ℕ),
    GoodListNodesTl L hL → MarkedListSpineFull hL N r x →
    ¬finalListSpine L (rtransSpine L N r x 1) →
    SFlagListSpine L (ntransSpine L N r x 1) (rtransSpine L N r x 1) x

/-- **塔顶装配定理**——HOL `transform_assumption_v2_lemma`
（reduction2.hl:806-:848）装配结构的 Lean 孪生：13 叶在案 ⇒
`transformAssumptionSpine L hL` 无条件成立。HOL 证明的 SUBCONJ 链
（is_restricted 由旧 marked_list 重用；normal_list 五合取由 AQ1–AQ5
闭合；其余由 AQ6–AQ13 逐槽 ASM_SIMP_TAC）= 本定理的 9 槽逐项
recombination（纯命题组合，零债务、零新增证词）。13 叶全部真证后
本定理即给出 77 处消费的无条件形（j2w1 §4 建议的升级路径）。 -/
theorem transformAssumptionOfAq (L : fgraph ℕ) (hL : GoodList L)
    (h1 : aq1Concl L hL) (h2 : aq2Concl L hL) (h3 : aq3Concl L hL)
    (h4 : aq4Concl L hL) (h5 : aq5Concl L hL) (h6 : aq6Concl L hL)
    (h7 : aq7Concl L hL) (h8 : aq8Concl L hL) (h9 : aq9Concl L hL)
    (h10 : aq10Concl L hL) (h11 : aq11Concl L hL) (h12 : aq12Concl L hL)
    (h13 : aq13Concl L hL) : transformAssumptionSpine L hL := by
  intro N r x hgn hm
  exact ⟨⟨hm.1.1,
    ⟨h1 N r x hgn hm, h2 N r x hgn hm, h3 N r x hgn hm, h4 N r x hgn hm,
      h5 N r x hgn hm⟩,
    h6 N r x hgn hm, h7 N r x hgn hm,
    ⟨h8 N r x hgn hm, h9 N r x hgn hm⟩,
    h10 N r x hgn hm, h11 N r x hgn hm⟩,
    fun hfin => h12 N r x hgn hm hfin,
    fun hfin => h13 N r x hgn hm hfin⟩

/-! ## §4 第一 AQ 叶真证：AQ6（AQ56.hl:648-:696）

HOL 证明结构（:653-:696）：final 支（`DICH_TAC(28-14)` 后
`SET_RULE !A. A\/~A` case split）= ntrans_id/rtrans_id 退化为
`MEM r N`（marked_list 合取 3）；¬final 支 = `MATCH_MP_TAC(SET_RULE
A==> A\/B)` 取左支 + `Tame_list.MEM2_replace`（本文件 §0
memReplaceFstMem）。HOL 装载的 uniq_find_face/marked_list_of_dart/
mem_ztrans_rtrans_v0/z_not_eq_ytrans_v0/PPLHULJ_v0 上下文（:663-:693）
为 ASM_REWRITE 消解展开形服务，Lean 直达路线零消费。 -/
theorem aq6 (L : fgraph ℕ) (hL : GoodList L) : aq6Concl L hL := by
  intro N r x _hgn hm
  by_cases hfin : finalListSpine L r
  · -- final 支：单步恒等（j2w1 ntransId/rtransId）退化 MEM r N
    rw [ntransId L N r x hfin, rtransId L N r x hfin]
    exact hm.1.2.2.1
  · -- ¬final 支：ntrans1 展开 + r' = split.2 + MEM2_replace 左支
    have hr' : rtransSpine L N r x 1 = (splitNormalListSpine L r
        (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).2 := by
      show ((transformListSpine L x)^[1] (N, r)).2 = _
      rw [Function.iterate_one]
      simp only [transformListSpine, if_neg hfin]
    rw [ntrans1 L N r x hfin, hr']
    exact List.mem_append.mpr (Or.inl
      (memReplaceFstMem hm.1.2.2.1 (List.mem_singleton_self _)))

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三 `[propext, Classical.choice,
Quot.sound]`，零 sorryAx——本批九件证明零消费 TameList16:1109 在案债链。
落库时编排者可整体注释本节，不影响任何声明。） -/
#print axioms Kepler.Text.TameSpine.memReplaceFstMem
#print axioms Kepler.Text.TameSpine.memReplaceOfNeMem
#print axioms Kepler.Text.TameSpine.memReplaceCases
#print axioms Kepler.Text.TameSpine.minNotEqImpEq
#print axioms Kepler.Text.TameSpine.minNotEqImpEqAt
#print axioms Kepler.Text.TameSpine.lYRepPower
#print axioms Kepler.Text.TameSpine.ytransMemRtrans
#print axioms Kepler.Text.TameSpine.memYtransListOfDarts
#print axioms Kepler.Text.TameSpine.transformAssumptionOfAq
#print axioms Kepler.Text.TameSpine.aq6
