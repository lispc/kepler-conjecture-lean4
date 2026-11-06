# DEF-FIX 章程 · `hygiene-probe-axiom`（2026-11-06 卫生波）

用户 2026-11-06 裁决：「三项小裁决，都按你的建议来」。本目录装其中第 1、2 项，
两项各自一个 gate 文件（`auto_gate.sh` 一次只吃一个 `$FILE`）。

| gate 文件 | 目标文件 | 内容 |
|---|---|---|
| `gate-PackingAuto20.md` | `lean/Kepler/Text/PackingAuto20.lean` | 全树唯一一条真 `axiom` → 一行转发定理 |
| `gate-IdLists.md` | `lean/Kepler/Assembly/IdLists.lean` | 删除 `True` 镜像假闭合四件 + 一条 example |

裁决 3（`idsLpIneqs := []` → 真 127 条）**不做**：`CertifiedIneqHolds` 的
`else True` 回落使任意 `AllCertified` 恒真，换清单只是把「空量化的假」换成
「127 条量化的假」。真修法 = 993 分支查表 + 删回落，属 hLP/P6-E 本体。

两条共同依据：AGENTS §2「禁 `axiom`」与「最危险的不是 sorry，是看起来证完了」。

裁决 3 附带的零风险动作（在 `Assembly:281` 与 `allCertified_pilot` 上方钉
``-- 红线：不许用它闭任何 nLI 件``）**推迟到 `fcdjdot` 落库之后**再做 ——
目前有车道正基于 `Assembly.lean` 的副本施工，先动会产生 patch 基点漂移。
