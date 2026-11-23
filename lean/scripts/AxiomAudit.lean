import Kepler.Statement
import Kepler.LP.HelloChecker
import Kepler.Graphs.TameClassification
-- P0-2（eng-acceptance-gate-w1，2026-11-23 用户明批）：根面探针。
-- 下方前 4 条探针是 2026-09 旧口径；验收 root = Kepler.Final（AGENTS §1/§5，
-- P0-1），根定理的唯一验收输出在文末新增行。
import Kepler.Final

-- Axiom audit: must print only the standard axioms (or none).
-- Any `sorryAx` (except on the explicitly allowed Phase-1 placeholder
-- `the_kepler_conjecture`) or project-introduced axiom fails the audit.
#print axioms Kepler.LP.example_bound
#print axioms Kepler.Packing.finite_inter_ball
-- Phase 1: the proof body of the main statement is a sanctioned `sorry`
-- (PLAN.md §4 Phase 1); this line documents that fact in CI output.
#print axioms Kepler.the_kepler_conjecture
-- G2: standard axioms + the scoped native_decide trust axioms
-- (DECISIONS.md 2026-08-10; per-seed counts recorded in
-- docs/architecture.md "建成状态"); no sorryAx allowed here.
#print axioms Kepler.Graphs.tame_classification
-- 根面验收（AGENTS §1）：期望输出 = [propext, Classical.choice, Quot.sound]
-- ∪ 恰 585 条地面 native_decide 公理 + 当前锥内 sorry 债的 sorryAx
-- （2026-11-23 账本口径 49 = 48 nli* + 1 hLP；唯一实时账本 docs/priority-queue.md）。
-- 编译本文件需要 KeplerAcceptance 的完整 import 闭包（8,869 模块）——由编排者
-- 按岛协议执行，不属于车道可跑范围。
#print axioms Kepler.the_kepler_conjecture_e2e
