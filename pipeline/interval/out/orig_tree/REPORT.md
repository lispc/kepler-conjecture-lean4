# 原始分割树导入 × pinned-rung 裸区间判定 — 实验报告

2026-09-21。对象:prep-BIXPCGW 7274157868 a split(0/2) / split(1/2)。
问题:Flyspeck 原始自适应分割树的叶盒,我们的 pinned-rung(12,-64)裸区间
判定通过率多少?"原始分割树 + 裸区间"路线够不够?

## 结论(先行)

**不够,且差得远:原始树 9 叶全军覆没(0/9 PASS)。**
- split(0/2)(无 break_case 条目 → 全域单叶):**1/1 FAIL**。
- split(1/2)(原始树 8 叶):**8/8 FAIL**。
- 对照(hminus 从 [1.2,1.3] 全区间钉到 1.26±2⁻¹⁶,贴近原始常数语义):
  仍 **8/8 FAIL** —— 失败不是 hminus 变动引起的,是 x 空间margin vs 裸区间
  过估的内在差距。
- 失败不是 rung 精度问题:同族 y 空间案例(W5 repair 进行中)的 stage-A
  chunk 在 rung 12/16/20 上失败数不变(5/3544),margin 型失败爬梯子无效。

## 原始树导入

- 源:`reference/flyspeck/text_formalization/nonlinear/break_case_log.hl:757`
  (split(1/2);split(0/2) 无条目 = 原始验证未再分割)。
- 语义(`break_case_exec.hl` mk_rec / 头部注释):`Iarg_facet ((i,side),frac,msec,sub)`
  单侧分割——side=false:cut=lo+frac·(hi−lo),左半是已验证叶(msec=C++毫秒),
  递归右半;side=true 镜像。`Iarg_leaf n` 收尾。变量 0-based,指 x1..x6
  (x 空间 = 平方变量,bounds 如 [#4.0, x2, (2hminus)²])。
- 初始域:prep.hl 条目 bounds,hminus 按常数 1.26 计(与 split 边界
  (2·1.26)²=6.3504 一致;注:hminus 实为 choice 常数 ≈1.2618,这里取 1.26
  是重建近似,±0.002 的差异不影响结论量级)。
- split(1/2) 树:7 层嵌套 facet(依次切 x2,x3,x5,x6,x4,x1,x2,比例
  0.7846/0.8514/0.8970/0.9055/0.7783/0.6160/0.6813,全为非中点自适应)→ **8 叶**,
  原始 C++ 运行时合计 ~8.1s(779+747+1200+1147+985+1151+763+1339 msec)。
- split(0/2):**1 叶**(全域 x1∈[5.76,6.3504],x4∈[7.0267,8],余 [4,6.3504])。

## 我们的判定设置

- 案例 JSON:emit_rpn 链(parse 中间件复用 bb-cert-rerun 的
  ineq_prep_ast/defs_prep)生成到 `pipeline/interval/out/cases_prep/`:
  split(0/2) 21168 ops / 57 ite, split(1/2) 27374 ops / 75 ite,各带 1 个
  disj 备选(`dih_x + unit6·(−2.3) < 0`)。
- 判定器:FillParams data-mode disj 驱动(runMainFileDisj),pinned rung
  **N=12, out=-64**(梯子第一级)。原始 6 维叶盒嵌入 7 维 case(hminus∈
  [6/5,13/10] 为 dim0),端点外扩到 2⁻³⁰ dyadic 网格。
- 脚本:`pipeline/interval/orig_tree_probe.py`(树解析/叶盒展开/驱动生成)、
  `orig_tree_analyze.py`( verdict 统计)、`out/orig_tree/run_probe.sh`
  (setsid + 状态文件 + nice 19)。

## 判定结果

| 实验 | 叶数 | PASS | FAIL | 备注 |
|---|---|---|---|---|
| split(0/2) 全域 | 1 | 0 | 1 | 整个子案盒裸判定就不成立 |
| split(1/2) 原始树 | 8 | 0 | 8 | hminus∈[1.2,1.3] 全区间 |
| split(1/2) 原始树 | 8 | 0 | 8 | hminus 钉 1.26±2⁻¹⁶(对照) |

FAIL 分布:9/9 全部贴原始域边界——但这是树太粗的平凡结果(7 刀切 6 维,
每叶必然贴多个边界面),不构成"边界形态"证据。真正的对照数字:
原始 Taylor 验证器 ~8.1s 闭合的 8 个盒,我们的裸区间在 rung 12/-64 下
0/8;而我们自己的 bb_arb 直跑这两个 case(27K ops,~7K 节点/s)600s
内连 4M 节点都跑不完;同族 y 空间案例闭合证书 90,017 叶且仍需 W1–W5
repair 轮修 pinned-rung 失败叶。

## 回答

1. **"原始分割树 + 裸区间"够不够?** 不够。原始树是给 Taylor 模型+导数
   验证器设计的:导数把过估压到 O(w²),8 刀就够;裸区间过估 O(w),
   同样 margin 需要再细化几个数量级(参照:y 空间姊妹案例 9 万叶)。
   直接嫁接原始树到我们的判定层没有捷径。
2. **FAIL 叶是否集中在 Taylor 能治的形态?** 是——失败是全局性的
   margin/过估失败(钉死 hminus 后不变,爬 rung 无效),正是
   Multivariate_taylor 一阶模型针对的形态。这与 MKFKQWU 原型结论一致:
   出路在求值器(前向 AD/均值形式),不在分割策略。原始树的增量价值是
   提供**非中点切点先验**(贴在真实 margin 脊线上),可与 AD 求值器组合
   使用,但不能替代它。

## 产物

- `pipeline/interval/orig_tree_probe.py`、`orig_tree_analyze.py`(未 commit)
- `pipeline/interval/out/cases_prep/prep-BIXPCGW_7274157868_a_split_{0,1}_2.json`
- `pipeline/interval/out/orig_tree/`:leaves.json ×2、probe*.d/(driver+boxes)、
  probe*.run.log(判定输出)、probe*.status、run_probe.sh、本报告
- 驱动部署件:`lean/Kepler/Interval/Cases/Repair/Probe7274157868s{0,1,1hmpin}.lean`
- bb_arb 直跑探针日志:`/tmp/prep-reproto/logs/prep-BIXPCGW_7274157868_a_split_*`
  (均 FAIL_TIMEOUT 600s/4M 预算)
- g4e worktree 新增符号链接 `reference/flyspeck/.../ineq.hl`(emit_rpn 的
  darts 表依赖;未 commit)

纪律:全程 nice 19、并发 ≤2(我的部分)、setsid + 状态文件;未动在跑进程;
主仓只读;worktree 无 commit。
