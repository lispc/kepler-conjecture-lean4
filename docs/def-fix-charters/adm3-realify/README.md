# DEF-FIX 章程：`Adm3` 真化（Assembly 侧）

> 依据：`tamecorr-iso-scout`（2026-11-06，只读侦察）报告 B + 用户 2026-11-06 裁决「做」。
> 影响面：hTC 第三件 `tameCorrespondenceIso` 的前提 `TamePlanarHypermap`。

## 0. 一句话

`Assembly.Adm3` 的结论子句原为 `True`（形状占位，**严格弱于** HOL `adm_3`），
现抄回 `Kepler.Text.TameLp.Adm3` 的真结论；抄回后 Assembly 与 TameLp 两份
`TamePlanarHypermap` 的 12 个槽**全部 defeq**，整 def 退化为 `rfl` 级相等。

## 1. 对象与 HOL 锚

- HOL `adm_3`：`reference/flyspeck/text_formalization/tame/tame_defs.hl:124-127`
  （`a_tame = 0.63` 内联为 `Kepler.Text.TameLp.aTame`，定义在 `TameLp.lean:412`）。
- Lean 真形独占源：`lean/Kepler/Text/TameLp.lean:443-446`。
- 被改件：`lean/Kepler/Assembly.lean:2101-2103`（`def Adm3`）。

## 2. 改动

1. `Assembly.Adm3` 尾：`True` → `Kepler.Text.TameLp.aTame ≤ setSum (setOfTrianglesMeetingNode H x) w`
   （逐字对齐 HOL；`aTame` 需全限定，Assembly 无 `open Kepler.Text.TameLp`）。
2. 私有桥 `b3_tamePlanarHypermap`（`Assembly.lean:2373-2381` 区）：`Adm3` 槽由
   `fun x _ _ => trivial` 改为直接交 `ha3`（TameLp 的真见证；两版 `Adm3` 现 defeq）。

## 3. 验收（岛协议，Assembly 级 `lake build` 永久禁止）

| 项 | 实测 |
|---|---|
| `lean -o /tmp/asm_defix/Kepler/Assembly.olean Kepler/Assembly.lean` | **RC=0 / 0 error**（~35 s） |
| `example : Assembly.Adm3 H w ↔ TameLp.Adm3 H w := Iff.rfl` | **通过**（12 槽全 defeq 的直接证据） |
| `#print axioms Kepler.Assembly.the_kepler_conjecture_from_interfaces` | **628**（624 shard + 标准三 + `sorryAx`）—— 与基线**逐项一致** |

## 4. 风险与残留

- 本改动把 `tameCorrespondenceIso` 的**前提变强**（`True` → 真 `adm_3`）：这与 HOL 一致，
  但意味着将来填证时必须真的供出 `adm_3`。属"恢复保真度"，不是弱化。
- 若将来有人依赖 `Adm3` 的平凡性（`trivial` 构造），会编译失败——本仓无此消费者（全树 grep 仅
  `b3_tamePlanarHypermap` 一处，已同步改）。
