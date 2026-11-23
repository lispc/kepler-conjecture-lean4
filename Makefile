# Kepler 猜想 Lean 4 形式化项目 — Makefile
#
# ⚠ 全树构建被 AGENTS §4 永久禁止（lake 全核扇出实测 12 路并发 → 内存枯竭 →
#   内核事故；且 defaultTargets 闭包不含根定理，build 成功不构成验收）。
#   下方 build/check/reprove 已改为闸门：打印指引并 exit 1（P0-2，
#   eng-acceptance-gate-w1，2026-11-23 用户明批）。原命令保留为
#   *-legacy-unsafe 目标，仅供考古对照，不要运行。
#
# 验收 root = Kepler.Final（P0-1，2026-11-23 用户明批）：
#   唯一验收语言 = `#print axioms Kepler.the_kepler_conjecture_e2e`
#   （lean/Kepler/Final.lean 文末；lean/scripts/AxiomAudit.lean 含同一探针）。
#   lakefile 命名验收 target = KeplerAcceptance（roots = ["Kepler.Final"]）。
#   静态自检（零编译、零 lake）：make acceptance-check
#
# 常用目标：
#   make build / check / reprove   —— 全树构建闸（打印指引并 exit 1，见上）
#   make acceptance-check          —— 静态验收自检：lakefile 断言 + sorry census 对账
#   make compute                   —— 重跑不受信任的生成器/求解器（Phase 2+ 填充）

.PHONY: build check reprove compute cache acceptance-check \
	build-legacy-unsafe check-legacy-unsafe reprove-legacy-unsafe

export PATH := $(HOME)/.elan/bin:$(PATH)

# P0-2：遗留全树入口隔离（AGENTS §4）。多目标共用同一配方。
build check reprove:
	@echo "ERROR: 禁止全树构建（lake build / rm -rf .lake/build）—— AGENTS.md §4。"
	@echo "  验收 root = Kepler.Final；验收走编排者岛协议（单文件 lean -o）+ #print axioms。"
	@echo "  零编译静态自检：make acceptance-check；考古对照：* -legacy-unsafe（勿跑）。"
	@exit 1

build-legacy-unsafe:
	cd lean && lake build

# 旧公理审计（2026-09 旧口径 4 探针 + 现已并入的根面探针，见 lean/scripts/AxiomAudit.lean）。
check-legacy-unsafe: build-legacy-unsafe
	cd lean && lake env lean scripts/AxiomAudit.lean

reprove-legacy-unsafe:
	cd lean && rm -rf .lake/build && lake build
	$(MAKE) check-legacy-unsafe

# P0-1/P0-3 静态验收自检：不触发任何编译与 lake。
acceptance-check:
	python3 scripts/check_acceptance_targets.py
	python3 scripts/sorry_census.py --check --no-tsv

cache:
	cd lean && lake exe cache get

compute:
	@echo "TODO: pipeline 生成器尚未实现（Phase 2+）"
