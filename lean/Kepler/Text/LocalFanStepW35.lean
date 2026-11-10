/-
Kepler/Text/LocalFanStepW35.lean — wave W35：w 侧单一归纳总装（**归纳骨架 + th3 溯源**）。

## th3 溯源结论（工单第 1 步，决定归纳单元形态）
* `grep -n "th3" NKEZBFC.hl` → 仅 8 处**应用**（:132/:135/:187/:190/:296/:538:
  早期三倍组；:2385–2388: H 段 union 步进的 h4 供给），**全文件无绑定**；
* `grep -rn "th3" reference/flyspeck/` → 快照内无定义（仅 tame/ssreflect 与 trig1
  的同名局部 let，无关）⇒ **th3 是未入库 HOL 库文件的全局件**（按 opened 模块
  名单，最可能 = `local/local_lemmas.hl` 的 w 侧 1_2 族）；
* 应用面语义（机器推断）：`th3[x; v; w]` + DISJOINT/非共线前提 ⇒ 落在
  **w 侧 1_2 族**（H 步 h4 = `ITER(k-j-1) v ∈ affGt{0}{v, ITER(k-j-1-1) v}`
  = `hprev` 的在案内容）与互异/非共线助手。
**推论（止损依据）**：H/J 单一归纳的 h4 = th3 内容 = **hprev 1_2 族本身**；
而 hprev ⟺ C1 ∧ C2（`pW20_hprev_iff_21`），C2 = WindingSlot 内容 ⇒
**「WindingSlot 真证」需要 th3 的 Lean 对件，而 th3 的证明体不在快照内**
——归纳单元不能在自身内部闭环（h4 与目标同源）。按工单止损口径交付骨架：

## 本件（骨架，以 1_2 族为显式接口 `hfam`；接口 = th3 的 Lean 对件签名）
* §1 `pW35_union_of_family`：H 段 union 望远镜等式（成员形，`∀j` 归纳；
  基 = 周期回卷 `vv k = v` + pair_comm，步 = `AFF_GE_EQ_AFF_GE_UNION_p9`
  + hfam 供 h4）——**归纳结构本身已证明**。
* §2 `pW35_slot_of_family`：J 段收尾（`ρ(vv(i+1)) ∈ affGe{0}{v, vv(i+1)}`）
  = 平凡对成员 + §1 在 `j := k-i-2` 的实例。
⇒ 一旦 `hfam`（th3 对件）到位，本件 + W30 C1 供给 + W33 排除 + W34 边界即
总装出 hslot_w/hprev 的真证；WindingSlot 退位条件 = th3 对件。
-/
import Kepler.Text.LocalFanStepW32
import Kepler.Text.LocalFanStepW33
import Kepler.Text.LocalFanStepW34

set_option maxHeartbeats 4000000

namespace Kepler.Text

open Kepler.Geom Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §1 H 段 union 望远镜等式（归纳骨架） -/

/-- **w 侧 union 望远镜（成员形，归纳骨架）**：给定 1_2 族 `hfam`
（= th3 内容的 Lean 接口）⇒
`z ∈ affGe{0}{v, vv(k-j-1)} ↔ ∃ j1 ≤ j, z ∈ affGe{0}{vv(k-j1-1), vv(k-j1)}`
（`j < k-2`）。基：`vv k = v` 周期回卷 + `Set.pair_comm`；
步：`AFF_GE_EQ_AFF_GE_UNION_p9`（h4 ← `hfam`）。 -/
theorem pW35_union_of_family (hcl : convexLocalFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {vv : ℕ → V3} {k : ℕ} (hk : V.ncard = k)
    (hiter : ∀ n, (rhoNode1_p2 FF)^[n] v = vv n)
    (hfam : ∀ n : ℕ, 2 ≤ n → n ≤ k - 1 → vv n ∈ affGt ({0} : Set V3) {v, vv (n - 1)}) :
    ∀ j : ℕ, j < k - 2 → ∀ z : V3,
      z ∈ affGe ({0} : Set V3) {v, vv (k - j - 1)} ↔
        ∃ j1, j1 ≤ j ∧ z ∈ affGe ({0} : Set V3) {vv (k - j1 - 1), vv (k - j1)} := by
  have hlf : localFan_p2 V E FF := hcl.1
  have h0V : (0 : V3) ∉ V := (CVLF_LF_F hcl).2.2.2.2.1
  have hvvV : ∀ n : ℕ, vv n ∈ V := fun n => by
    rw [← hiter n]
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hv n
  -- 周期回卷：vv k = v
  have hk1 : vv k = v := by
    rw [← hiter k, show k = V.ncard from hk.symm]
    exact LOFA_IMP_ITER_RHO_NODE_ID hlf hv
  -- 单点-对 的互斥（供 AFF_GE_EQ_AFF_GE_UNION_p9 的 Disjoint 前提）
  have hdisj : ∀ a b : V3, a ∈ V → b ∈ V → Disjoint ({0} : Set V3) {a, b} := by
    intro a b ha hb
    rw [Set.disjoint_singleton_left]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => h0V (h ▸ ha), fun h => h0V (h ▸ hb)⟩
  intro j
  induction j with
  | zero =>
    intro _ z
    constructor
    · intro hz
      exact ⟨0, Nat.zero_le 0, by
        have hz' : z ∈ affGe ({0} : Set V3) {v, vv (k - 1)} := by
          simpa using hz
        simpa [hk1, Set.pair_comm] using hz'⟩
    · rintro ⟨j1, hj1, hz⟩
      have hj0 : j1 = 0 := by omega
      subst hj0
      have hz' : z ∈ affGe ({0} : Set V3) {vv (k - 1), v} := by
        simpa [Nat.sub_zero, hk1] using hz
      rw [Set.pair_comm] at hz'
      simpa [Nat.sub_zero, hk1] using hz'
  | succ j ih =>
    intro hj z
    -- 归纳步：h4 ← hfam（指数 k-j-1）
    have hU := AFF_GE_EQ_AFF_GE_UNION_p9 (x := (0 : V3)) (v := v)
      (u := vv (k - (j + 1) - 1)) (v1 := vv (k - j - 1))
      (h1 := hdisj v (vv (k - (j + 1) - 1)) hv (hvvV (k - (j + 1) - 1)))
      (h2 := hdisj v (vv (k - j - 1)) hv (hvvV (k - j - 1)))
      (h3 := hdisj (vv (k - j - 1)) (vv (k - (j + 1) - 1))
        (hvvV (k - j - 1)) (hvvV (k - (j + 1) - 1)))
      (h4 := hfam (k - j - 1) (by omega) (by omega))
    have hj' : j < k - 2 := by omega
    rw [hU, Set.mem_union]
    constructor
    · rintro (hz | hz)
      · obtain ⟨j1, hj1, hz'⟩ := (ih hj' z).mp hz
        exact ⟨j1, by omega, hz'⟩
      · refine ⟨j + 1, by omega, ?_⟩
        simpa [Set.pair_comm, show k - (j + 1) - 1 = k - j - 2 from by omega,
          show k - (j + 1) = k - j - 1 from by omega] using hz
    · rintro ⟨j1, hj1, hz⟩
      rcases Nat.lt_or_ge j1 (j + 1) with h | h
      · exact Or.inl ((ih hj' z).mpr ⟨j1, by omega, hz⟩)
      · have hj1e : j1 = j + 1 := by omega
        subst hj1e
        exact Or.inr (by
          simpa [Set.pair_comm, show k - (j + 1) - 1 = k - j - 2 from by omega,
            show k - (j + 1) = k - j - 1 from by omega] using hz)

/-! ## §2 备注（止损切除） -/

/-! J 段收尾 `pW35_slot_of_family`（1_2 族 ⇒ `ρ(vv(i+1)) ∈ affGe{0}{v, vv(i+1)}`）
在 2 轮 + 心跳 4M 内不可收敛：`pW35_union_of_family` 在 `j := k-i-2` 的实例化
触发 whnf 超时（Nat 减法下标 `k - (k-i-2) - 1` 与 ∃-绑定项统一时的归约爆炸，
非逻辑卡点）。骨架证明思路见 DELIVERY_W35 §2；机械化方案 = 先把
`∀ i, k - (k - i - 2) = i + 2` 等下标引理化为具名 `have`（避免 rw-in-∃）。 -/

end Kepler.Text

/-! ## 探针 -/
#print axioms Kepler.Text.pW35_union_of_family
