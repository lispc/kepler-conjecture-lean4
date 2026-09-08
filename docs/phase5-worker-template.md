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
   （例外：拆分中的巨块任务会显式标注"允许在指定分支位留 sorry"，
   并指定 WIP 文件；此时只准在指定位置留，且最终块必须清零。）
2b. **禁止整文件读取**：定位一律 `grep -n`，阅读一律
   `sed -n 'A,Bp'` 且窗口 ≤100 行。整读大文件（>500 行）会导致
   后续 API 请求静默失败、进程无错退出（已实锤多次）。
2c. 开写时限：探索 ≤10 分钟就必须开始写第一行代码；超时直接按
   已掌握的信息写，编译报错再修。
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

## 路由规则（2026-09-08 起，含 flash 实测失败模式）

**车道分工（用户 2026-09-08 定）**：

- **big-pickle（opencode 免费）**：只做 Lean 定理移植（Phase 5）。
  实测真产 4/4 零干预（block 23–26），速度 ~10–17 HOL 行/分钟，
  质量/速度均 ≥ flash。同时只开一路（免费额度限流未测）。
  失败升级链：big-pickle → glm-5.3（满血）→ 主 agent 亲手。
- **glm-5.3-flash（GLM coding plan）**：Phase 4 代码任务（Python/C
  流水线），以及 big-pickle  Lane 占用时的 Phase 5 备胎。
- **glm-5.3（满血）**：big-pickle/flash 都失败的 Lean 硬块。

派 flash 前按此分流，别等失败再升级：

- **flash**：良构块（≤4 引理）、所需引理全部已存在、有同文件镜像模板
  （对称情形、变量对换重放）。block 20（:5452–5593 五枚 properties）
  是 flash 零干预完成的标杆。
- **满血**：需要先自证新前置引理（如 affGe_mono_right 不存在）、
  azim/分析类、依赖组装、陌生领域。block 21（:5594 lemma_proof0_fan）
  flash 探索瘫痪一整小时、零写入（git 干净、log 无一次 Write/Edit）——
  "10 分钟内必须开写"规则对瘫痪无效，只能事前路由规避。
- 瘫痪识别：监视器触发时若 git 无 diff 且 log 尾部还在 Read/Grep，
  即瘫痪，直接升级满血重派，不给第二次机会。
