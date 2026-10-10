# docs/

分类规则（2026-10-10 重组；落位规程见 PLAN.md §7.9）：按**生命周期**分层，
不按主题。引用路径一律用仓库根相对路径。

- **根层 = 常住参考**：被 PLAN/STATUS 长期引用、持续更新的文档才放这里，
  并在本文件登记。
- `scouts/` — 侦察报告。写完即历史记录；结论应吸收进 PLAN/STATUS/playbook。
- `handoffs/` — lane 交接与班次日志。日期性记录，内部旧链接不回溯修复。
- `projects/` — 专项设计与路线图（一个 lane/项目一册）；收官后整册归档。
- `assets/` — 产物与草稿（探针、日志、`.lean.txt`、wip 补丁、公理探针输出）。
- `statement-fix-proposals-patches/` — SF 通道执行版补丁存档（活跃，
  `auto_gate.sh` 直接引用，勿移）。

## 常住文档

- `statement-fidelity.md` — Phase 1 交付：与 Flyspeck `the_kepler_conjecture` 逐条对照
- `module-map.md` — Phase 5 交付：《Dense Sphere Packings》章节 → Lean 模块映射与进度表
- `hard-cases.md` — 卡壳记录（PLAN.md §7.6）
- `architecture.md` — Phase 6 交付：证书格式与流水线架构
- `phase6-spine.md` — 装配脊柱设计与 M5′ 路线
- `e2e-debt-map.md` — 主定理可达债务度量（每波收工由编排者更新）
- `fill-worker-playbook.md` / `phase5-worker-template.md` — 填证工人手册与模板
- `local-manifest.md` / `packing-manifest.md` — 章节移植清单与约定
- `statement-fix-proposals.md` — SF 通道提案账本
