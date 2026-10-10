/-
  Kepler.Text.TameSpine.Keystone — W0 keystone 批 1：S1 规格桥 + S3 Iso 孪生桥。

  立项：`docs/tamespine-port-plan.md` §4 W0 批（tame 章 A7/A8/A9 三接口共同前置）。
  深侦：`docs/tame-chapter-scout.md` §3.3（S1/S3 行）+ §6-R3/R4/R9。

  镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353）：
  - `formal_lp/hypermap/ssreflect/list_hypermap-compiled.hl:60`
    （`hypermap_of_list` 规格级语义，经 `IsHypermapOfList` 钉死）；
  - `hypermap/hypermap.hl:9614`（`iso`，`HypermapIso` 孪生桥）。

  结构（scout §6-R3 纪律：**TameSpine 侧只留桥引理**——`hypermapOfList` 构造本体
  与其四字段 permutes/comp_eq_one 证明留在 TameLp W1 keystone（9d775467，全部真
  证明），本模块不复制任何构造机器）：

  - **S3 孪生桥**：`Assembly.HypermapIso`（Assembly.lean:98-104）与
    `Hypermap.Iso`（Text/Hypermap.lean:8254）逐字同体（scout "近乎白捡"）——
    `Iff.rfl` 互推 + refl/symm/trans 三件以 `Hypermap.Iso` 家族为单一真源
    （Assembly 侧 trans 已有 `hypermapIsoTrans:957`，本模块补 refl/symm 并以
    桥件统一，后续 S4 iso 不变家族按 R3 纪律落 Hypermap.lean 家族后经此桥消费）。
  - **S1 规格桥**：`Assembly.IsHypermapOfList`（Assembly.lean:116-124）↔
    `TameLp.IsHypermapOfListTl`（TameLp.lean:3485-3493）匿名构造器四槽一步
    ——这就是 f2bf7db8 记账的"Assembly 四字段一步折算转发计划"落地，
    import 方向裁决为**第三模块双向桥**：TameLp 不 import Assembly（环），
    Assembly 不 import TameLp（签名零触碰），两者由本模块同时 import 折算。

  W0 验收锚（立项批次表）：`IsHypermapOfList L (hypermapOfList L)`
  —— `isHypermapOfList_hypermapOfList`。至此 A7（∃Hy witness）/A9（∃H'
  witness）的证人机器在 **Assembly 谓词层**可用；A8 的 def 层（GoodListNodes
  忠实化）见姊妹模块 `Kepler.Text.TameSpine.GoodGraph`（W0 批 2）。

  红线遵守：本模块零 sorry、零 Assembly/TameLp 签名触碰；公理面预期 = 标准三
  （propext/Classical.choice/Quot.sound）——桥件只做字段转发与 defeq 折算，
  不引入任何接口 sorry 污染（配 `#print axioms` 审计锚，见文件尾注释）。
-/
import Kepler.Assembly
import Kepler.Text.TameLp

namespace Kepler.Text.TameSpine

open Kepler.Text (Hypermap)
open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList)

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-! ### S3：`HypermapIso` ↔ `Hypermap.Iso` 孪生桥（scout §3.3-S3） -/

/-- **S3 孪生桥**：`Assembly.HypermapIso`（hypermap.hl:9614 `iso` 的 Assembly §1b
镜像，Assembly.lean:98-104）与 `Hypermap.Iso`（Hypermap.lean:8254）def 体逐字
同体，`Iff.rfl` 互推。消费纪律（scout §6-R3）：新移植一律落 `Hypermap.Iso`
家族，Assembly 侧经本桥折算，不复制孪生定理群。 -/
theorem hypermapIso_iff {H : Hypermap α} {G : Hypermap β} :
    Kepler.Assembly.HypermapIso H G ↔ Hypermap.Iso H G := Iff.rfl

/-- 孪生桥正向运输：`Hypermap.Iso` 件 ⟹ Assembly 谓词形（A7/A9 装配出口用）。 -/
theorem hypermapIso_of_iso {H : Hypermap α} {G : Hypermap β}
    (h : Hypermap.Iso H G) : Kepler.Assembly.HypermapIso H G := h

/-- 孪生桥反向运输：Assembly 谓词形 ⟹ `Hypermap.Iso` 件（S4 iso 不变家族
入口；落 Hypermap.lean 家族的前提形）。 -/
theorem iso_of_hypermapIso {H : Hypermap α} {G : Hypermap β}
    (h : Kepler.Assembly.HypermapIso H G) : Hypermap.Iso H G := h

/-- HOL `I_BIJ`（hypermap.hl:9612）的 Assembly 谓词形：`HypermapIso` 自反
（经 `Hypermap.Iso.refl`，Hypermap.lean:8266）。 -/
theorem hypermapIso_refl (H : Hypermap α) : Kepler.Assembly.HypermapIso H H :=
  Hypermap.Iso.refl H

/-- HOL `iso_sym`（hypermap.hl:9617）的 Assembly 谓词形：对称性
（经 `Hypermap.Iso.symm`，`Nonempty α` 为 HOL 类型恒非空的 Lean 折算）。
ℕ×ℕ 消费形自动满足。 -/
theorem hypermapIso_symm {H : Hypermap α} {G : Hypermap β} [Nonempty α]
    (h : Kepler.Assembly.HypermapIso H G) : Kepler.Assembly.HypermapIso G H :=
  Hypermap.Iso.symm h

/-- HOL `iso_trans`（hypermap.hl:9660）的 Assembly 谓词形：传递性
（经 `Hypermap.Iso.trans`；与 Assembly.lean:957 `hypermapIsoTrans` 同体，
此处以孪生桥统一真源，A9 的 JCAJYDU1/JCAJYDU 两次 iso_trans 折叠消费）。 -/
theorem hypermapIso_trans {H : Hypermap α} {G : Hypermap β} {W : Hypermap γ}
    (h1 : Kepler.Assembly.HypermapIso H G) (h2 : Kepler.Assembly.HypermapIso G W) :
    Kepler.Assembly.HypermapIso H W :=
  Hypermap.Iso.trans h1 h2

/-- S1 构造件的自反 Iso（Assembly 谓词形，A7 witness 侧消费形；
`Hypermap.Iso` 版孪生在 TameLp.lean:2616）。 -/
theorem hypermapOfList_iso_refl {L : fgraph ℕ} {hL : GoodList L} :
    Kepler.Assembly.HypermapIso
      (Kepler.Text.TameLp.hypermapOfList L hL) (Kepler.Text.TameLp.hypermapOfList L hL) :=
  Hypermap.Iso.refl _

/-! ### S1：`IsHypermapOfList` ↔ `IsHypermapOfListTl` 规格桥 + W0 验收锚 -/

/-- **S1 孪生桥**：`Assembly.IsHypermapOfList`（Assembly.lean:116-124，
list_hypermap-compiled.hl:60 `hypermap_of_list` 的规格级镜像）与
`TameLp.IsHypermapOfListTl`（TameLp.lean:3485-3493）四槽逐字同体——
匿名构造器一步互转，无新证明义务（R4 纪律：两侧均不在规格之外重复加
合取项，"dart 集外恒等"由 `Hypermap` 的 `PermutesOn` 字段内置）。 -/
theorem isHypermapOfList_iff (L : fgraph ℕ) (H : Hypermap (ℕ × ℕ)) :
    Kepler.Assembly.IsHypermapOfList L H ↔ Kepler.Text.TameLp.IsHypermapOfListTl L H :=
  ⟨fun h => ⟨h.darts_eq, h.edgeMap_eq, h.nodeMap_eq, h.faceMap_eq⟩,
   fun h => ⟨h.darts_eq, h.edgeMap_eq, h.nodeMap_eq, h.faceMap_eq⟩⟩

/-- 孪生桥反向具名形：Assembly 规格形 ⟹ TameLp 孪生形（TameLp 侧定理族
`hypermapOfList_isHypermapOfListTl` 之后的 REVERSE/MAP 运输束直接消费）。 -/
theorem isHypermapOfListTl_of_isHypermapOfList {L : fgraph ℕ} {H : Hypermap (ℕ × ℕ)}
    (h : Kepler.Assembly.IsHypermapOfList L H) : Kepler.Text.TameLp.IsHypermapOfListTl L H :=
  (isHypermapOfList_iff L H).mp h

/-- **W0 验收锚**（立项批次表 `IsHypermapOfList L (hypermapOfList L)`）：
S1 构造（TameLp W1 keystone 9d775467 真落地）满足 **Assembly §1b 规格谓词**
——A7 的 `∃ Hy`/A9 的 `∃ H'` 证人自此在 Assembly 谓词层可用（witness 必须
就是 canonical `hypermapOfList` 构造本身，scout §5 阻塞关系）。

证明 = 孪生桥正向 + TameLp 规格实例定理 `hypermapOfList_isHypermapOfListTl`
（TameLp.lean:3498，四槽 = 构造四定理组装，全真证明零 sorry）。 -/
theorem isHypermapOfList_hypermapOfList {L : fgraph ℕ} {hL : GoodList L} :
    Kepler.Assembly.IsHypermapOfList L (Kepler.Text.TameLp.hypermapOfList L hL) :=
  (isHypermapOfList_iff L _).mpr (Kepler.Text.TameLp.hypermapOfList_isHypermapOfListTl L hL)

/-- 验收锚的具名前提形（A9 装配 lane 直接引用形）。 -/
theorem isHypermapOfList_hypermapOfList' (L : fgraph ℕ) (hL : GoodList L) :
    Kepler.Assembly.IsHypermapOfList L (Kepler.Text.TameLp.hypermapOfList L hL) :=
  isHypermapOfList_hypermapOfList

end Kepler.Text.TameSpine

/-! 公理审计锚（收口时在探针中执行，预期输出 `"[propext, Classical.choice, Quot.sound]"`）：
#print axioms Kepler.Text.TameSpine.isHypermapOfList_hypermapOfList
#print axioms Kepler.Text.TameSpine.hypermapIso_trans
-/
