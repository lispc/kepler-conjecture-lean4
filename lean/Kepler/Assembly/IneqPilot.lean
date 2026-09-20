/-
  P6-E 接口侧粘合试点（2026-09-20）：Assembly 脊柱 `nonlinearInequalities`
  接口（Assembly.lean:245，sorry 占位）的目标形态示范——**不改 Assembly.lean
  本体**，把一条已内核闭合的 G4 案例（C3397113841，1504 叶证书）接通
  "证书 → 接口"全链。

  链路（逐环可审计）：
  1. 案例证书定理 `C3397113841_pos`（bb_sound + 22 分片内核 `decide`，
     `#print axioms` = 标准三公理）；
  2. 粘合引理 `C3397113841_evalReal`（Interval/Cases/C3397113841Glue.lean：
     `evalReal` 语义 = `0 - delta4Y …`，一行 `simp only`）；
  3. 语义命题 `ineqProp_3397113841`：HOL `ineq.hl:2056` 的字面镜像
     （盒界 + `delta4_y … < &0`），由 1+2 经端点嵌入闭合；
  4. `certifiedIneqHolds_pilot`：`CertifiedIneqHolds`（Assembly.lean:165，
     占位 `True`）的目标形态——按 id 查表展开为量化不等式命题，表内条目
     由 3 的定理闭合。

  量产评估见 DECISIONS/报告：本文件只含 1 条目的查表；993 条时
  if 链/Lookup 表的编译成本与清单不变量见试点报告。
-/
import Kepler.Interval.Cases.C3397113841
import Kepler.Interval.Cases.C3397113841Glue
import Kepler.Text.PackingAuto2
import Kepler.Text.SphereKit

namespace Kepler.Assembly

open Kepler.Text Kepler.Interval Kepler.Interval.Cases

/-! ## 1. 语义命题（HOL 字面镜像）与闭合 -/

/-- HOL 案例 3397113841（ineq.hl:2056）的字面量化命题：
`!y1..y6. (&2 <= y1 /\ y1 <= &2*h0) /\ … /\ (y4 = #3.36) /\ …
  ==> delta4_y y1 y2 y3 y4 y5 y6 < &0`。
折算说明：`y4 = #3.36`（点盒）写成双向 `≤`；`/\-`前件写成 `→`-链
（与 Assembly 注册表量化同形，见 `AllCertified` 注释）；`delta4_y` =
`delta4Y`（SphereKit.lean:126），`h0` = `Kepler.Text.h0`（PackingAuto2.lean:458）。 -/
def ineqProp_3397113841 : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ,
    2 ≤ y1 → y1 ≤ 2 * h0 → 2 ≤ y2 → y2 ≤ 2 * h0 → 2 ≤ y3 → y3 ≤ 2 * h0 →
    3.36 ≤ y4 → y4 ≤ 3.36 → 2 ≤ y5 → y5 ≤ 2 * h0 → 2 ≤ y6 → y6 ≤ 2 * h0 →
    delta4Y y1 y2 y3 y4 y5 y6 < 0

/-- **端点嵌入**（十进制原盒 ⊆ dyadic 外扩证书盒）+ 证书定理 + 粘合引理，
闭合语义命题。端点验证全是 `norm_num` 量级：
`2·h0 = 2.52 ≤ 2705829397·2⁻³⁰`、`225485783·2⁻²⁶ ≤ 3.36 ≤ 3607772529·2⁻³⁰`。 -/
theorem ineq_3397113841 : ineqProp_3397113841 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have h252 : (2 : ℝ) * h0 ≤ Dyadic.toReal ⟨2705829397, -30⟩ := by
    rw [Dyadic.toReal_def]; norm_num [h0]
  have h336l : Dyadic.toReal ⟨225485783, -26⟩ ≤ (3.36 : ℝ) := by
    rw [Dyadic.toReal_def]; norm_num
  have h336h : (3.36 : ℝ) ≤ Dyadic.toReal ⟨3607772529, -30⟩ := by
    rw [Dyadic.toReal_def]; norm_num
  have hlo : ∀ y : ℝ, 2 ≤ y → Dyadic.toReal ⟨2, 0⟩ ≤ y := fun y h => by
    rw [Dyadic.toReal_int]; exact_mod_cast h
  have hmem : boxMem C3397113841Box ![y1, y2, y3, y4, y5, y6] := by
    intro i
    fin_cases i
    · exact ⟨hlo y1 h1l, le_trans h1h h252⟩
    · exact ⟨hlo y2 h2l, le_trans h2h h252⟩
    · exact ⟨hlo y3 h3l, le_trans h3h h252⟩
    · exact ⟨le_trans h336l h4l, le_trans h4h h336h⟩
    · exact ⟨hlo y5 h5l, le_trans h5h h252⟩
    · exact ⟨hlo y6 h6l, le_trans h6h h252⟩
  have hpos := C3397113841_pos ![y1, y2, y3, y4, y5, y6] hmem
  rw [C3397113841_evalReal] at hpos
  simpa using hpos

/-! ## 2. `CertifiedIneqHolds` 目标形态：按 id 查表展开 -/

/-- **目标形态（量产样板）**：按 id 查表展开为对应的字面量化不等式命题
（对照 Assembly.lean:163-165 的填实说明）。量产版 = 993 条分支的查表；
本试点只含案例 3397113841 一条。不在表内的 id 回落 `True`（与现行占位
语义一致——量产后须由"ID 清单 = 查表定义域"的不变量保证回落分支不可达，
否则接口语义退化为占位）。 -/
def certifiedIneqHolds_pilot (id : String) : Prop :=
  if id = "3397113841" then ineqProp_3397113841 else True

/-- 表内条目由 G4 内核证书（经粘合引理）闭合。 -/
theorem certifiedIneqHolds_pilot_holds (id : String) :
    certifiedIneqHolds_pilot id := by
  unfold certifiedIneqHolds_pilot
  split
  · exact ineq_3397113841
  · trivial

/-- 试点清单（对照 Assembly.lean:171-183 六个 PLACEHOLDER 清单；
3397113841 的 HOL 标签是 `Xconvert/Lp_aux/Tablelp`，属 `lp_ineqs` 分量）。 -/
def idsPilot : List String := ["3397113841"]

/-- 与 Assembly.lean `AllCertified`（:168）同形的注册表量化闭合。 -/
theorem allCertified_pilot : ∀ id ∈ idsPilot, certifiedIneqHolds_pilot id :=
  fun id _ => certifiedIneqHolds_pilot_holds id

#print axioms ineq_3397113841
#print axioms certifiedIneqHolds_pilot_holds

end Kepler.Assembly
