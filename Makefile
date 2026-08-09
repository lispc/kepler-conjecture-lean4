# Kepler 猜想 Lean 4 形式化项目 — Makefile
# 常用目标：
#   make build    构建 Lean 项目
#   make check    构建 + 公理审计（确认无自引入公理、无 sorry）
#   make reprove  从零重建（干净机器上的 Definition of Done，G6）
#   make compute  重跑不受信任的生成器/求解器（Phase 2+ 填充）

.PHONY: build check reprove compute cache

export PATH := $(HOME)/.elan/bin:$(PATH)

build:
	cd lean && lake build

# 公理审计：主定理/各验收定理的 #print axioms 输出只允许标准公理
# （propext / Classical.choice / Quot.sound），不得出现 sorryAx 或自引入 axiom。
check: build
	cd lean && lake env lean scripts/AxiomAudit.lean

cache:
	cd lean && lake exe cache get

reprove:
	cd lean && rm -rf .lake/build && lake build
	$(MAKE) check

compute:
	@echo "TODO: pipeline 生成器尚未实现（Phase 2+）"
