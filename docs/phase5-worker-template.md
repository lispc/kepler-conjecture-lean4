# Phase 5 工人 agent 任务模板（opencode + GLM）

> 主 agent（Kimi）用这个模板派活给 opencode（GLM coding plan）。
> 主 agent 职责：切分任务、验收（build + grep sorry + #print axioms）、commit。
> 工人职责：单文件、零 sorry、编译到绿、不碰 git。

## 调用方式

```bash
cd lean && nohup timeout 3600 opencode run -m zhipuai-coding-plan/glm-5.3-flash "<PROMPT>" \
  > /tmp/phase5_<task>.log 2>&1 &
# 难 block 换满血模型：-m zhipuai-coding-plan/glm-5.3
```

## PROMPT 模板

````
You are working in the lean/ directory of a Lean 4 + Mathlib project
(toolchain via elan; build as: export PATH="$HOME/.elan/bin:$PATH" && lake env lean <file>).

TASK: <具体任务，含目标文件与要证的定理清单>

Context:
- 3D type is Kepler.Geom.V3 (see Kepler/Geom/Azim.lean); use `open Kepler.Geom`.
- Existing geometry layers: Kepler/Geom/{Azim,AzimLemmas,Aff,Coplanar}.lean,
  Kepler/Text/{Hypermap,Fan,TopologyFan,Planarity}.lean — read before proving,
  reuse existing lemmas (e.g. collinear3_iff_mem_affineSpan, vectorAngle).
- HOL sources: reference/flyspeck/text_formalization/**.hl and
  ~/hol-light-ref/*.ml (paths relative to repo root /home/scroll/repos/kepler-conjecture-lean4).
- Hint: Mathlib's InnerProductGeometry.angle may coincide with vectorAngle;
  check before reinventing.
- Style: match existing files — namespace Kepler.Text or Kepler.Geom,
  HOL source line header comments, Chinese comments OK.

HARD RULES:
1. Only create/modify the files listed in TASK. Never touch other files. Never use git.
2. Zero sorry/admit/native_decide. Every theorem fully proved.
3. Iterate `lake env lean <file>` until exit 0.
4. If stuck on a lemma for >~25 minutes, replace it with a TODO comment in your
   report (NOT in the code — code must stay sorry-free; omit the lemma instead)
   and continue with the rest.
5. Final report: file list, theorem list, compile iteration count, skipped items.
````

## 验收清单（主 agent 执行）

1. `lake build Kepler` 全绿（不能只看单文件，防连带破坏）
2. `grep -nE '\b(sorry|admit|native_decide)\b' <新文件>` 零命中
3. 新定理 `#print axioms` 仅 `[propext, Classical.choice, Quot.sound]`
4. 快速读一遍 diff：证明风格、无投机性定义改动
5. 全部通过才 commit + push（身份 Zhang Zhuo <mycinbrin@gmail.com>）

## 难度升级策略

- glm-5.3-flash 卡壳（>3 轮无进展或报 skip）→ 同一任务重派 glm-5.3
- glm-5.3 也卡 → 主 agent（Kimi k3）接手或进一步切小
