# 585 信任基座内核化 —— 结论文档（供独立 agent 评审）

> 生成：`trust585-research-w1`（2026-11-20，用户批「侦查吧」）+ 编排者亲验。
> 本文档**自包含**：不依赖任何会话上下文；全部断言带出处；供任何 agent 独立复核与挑战。
> 主报告全文：`~/c17_backup/lane_snapshots/trust585-research-w1/RESEARCH.md`（含探针脚本与日志）。

---

## 0. TL;DR

**混合判定**：
- **tri 5 件 GO**（基座 585→580，本机 1–2 天级；用户已记下、**暂不开工**）；
- **580 件 shard-range NO-GO**（带明确翻案条件，见 §5）；
- **明确否决的伪选项**：用 core `bv_decide` 换 `native_decide`（§4——同公理类换皮，信任洗白）。

585 = 根面验收式中的地面枚举公理基座（`AGENTS.md` §1：589 = 585 native + 标准三 + sorryAx；
2026-11-06 用户终局裁决「不比 Flyspeck/Isabelle 更差」；基线定格 `52275a1c` 2026-11-09）。
用户 2026-11-20 新问题：「最终想做到纯标准三」——本报告回答这条路的事实底。

## 1. 585 解剖（全部本地实查）

- 构成：**580 shard-range + 5 tri-single-seed，仅 2 种陈述形状**；分布 Hex 290 / Pent 198 /
  Quad 92 / Tri 5；与 `docs/trust-base.tsv` 逐行对账（RESEARCH §1）。
- 两形状逐字摘录：`QuadR/K053.lean:10-14`（shard-range 形）与 `CertTri.lean:88-106`
  （tri-single-seed 形）。
- 本体 = tame 图枚举的**可达性闭包**：搜索树 ~**1.87e9 结点**（AFP 锚）终证 ~数千 tame 类；
  worklist **零重复 pop**（去重=不需要，`Worklist.lean` 注释印证）——对称去重捷径不存在。
- 文件极小（全 CertShards 共 13.3k 行）——成本 100% 在 native 求值运行时，无代码缩减面。
- 编译期行为：native_decide 在 elaboration 期跑完该范围的枚举求值——实测 Pent p50 ~200 s、
  稀疏巨件 K005 = 6,774 s；历史记录 DECISIONS.md:359「Phase 2 分片 ~7 天重建成本」。

## 2. NO-GO 证据链（580 shard-range，四条独立死因）

1. **工具端死（铁证）**：core `bv_decide` 与 `native_decide` **同公理类**——toolchain 源码
   `Lean/Meta/Native.lean:32-35` 原文「…add an **axiom** asserting `e = true`…It is the basis
   for `native_decide` and `bv_decide`」（Lean 4.32.2，Breitner 2025；编排者亲读亲验）。
   ⇒ SAT/BV 证书重建路线（原以为的路线 B）**零信任削减**。
2. **成本端死（旧判决勘误后更死）**：内核重放真实区间 **2.2e4–6.8e6 核时**——原
   「4,450–6,550 核时」系单片外推、较 AFP 1.87e9 结点锚**低估 ~5×**（AGENTS §1 的旧数字
   按此勘误理解）。
3. **内存墙**：单根 >14 GB 实测（heavy-scout）；36 GB 本机下并行不可行。
4. **先例规模差**：FCT-Lean（corun1024/4ct，2026，AI 生成、非权威）以 reducibility 重设计把
   90 核时压到 3.5（≈26×）——但 FCT 是 633 构型 vs 我们 1.87e9 结点，**差 6 个数量级**，
   26× 不构成翻案。

## 3. GO 部分（tri 5 件；pilot 已具草案、用户暂不开工）

- tri_shard_3/4：各 **1 pop**，直 `decide` 即可（分钟级编译，陈述零动）。
- tri_shard_0/1/2：逐节点证书走查（certgen.py 设计 + `TopReplayTriAll` 的 `decide+kernel`
  批定理手法 + ~150–250 行仿真引理；≈26 核时 EST、内存批间有界、**非 farm**）。
- 探针已离线全量走完五根 = **312,764 pops，与 AFP ArchStat 官方 Tri 计数逐位吻合**
  （`probe_tri_root0.py` + `logs/probe_root*.log`）。
- 5 条全换 = **基座 585→580**（基座第一次真减）。执行草案：RESEARCH §7。

## 4. 明确否决的伪选项：bv_decide 换皮（用户问「至少看起来更官方可靠？」）

**判：不换，方向性错误。**
- 同公理类：`#print axioms` 里照样一条条 axiom（同一 native_eq_true 通道），585 一条不少——
  「看起来官方」是门面差异，信任零变化；
- **更不可审计**：现行基座逐条列名、进 manifest、可 replay、注明数据源与生成器版本
  （AGENTS §1 验收条款）；bv_decide 的 per-use 隐式公理反而**更暗**；
- 精神违和：AGENTS §2 禁造假定理的精神延伸 = 禁把明示信任挪进暗处；Isabelle 自己的
  `by eval` 同样不进内核——我们现有形态已是对等里**最可见**的；
- 换皮代价真实：585 的 manifest/信任基座文档/三波对账（trust-base.md §2–4）全部要重做，
  换来零实质。

## 5. 未来潜在方向（翻案条件——按可信度排序，均未开工）

1. **死子树证书叠加**（唯一未测量的结构性问题）：1.87e9 结点里 99%+ 是早死分支；若死因
   集中于少数可形式化的简单界，可在分支点放小证书替代整棵子树枚举——求值与重编时间
   可能砍 1–2 个数量级。**关键：死因分布从未被测量**。便宜探针设计已就绪（trust585 的
   离线管线走一个中等 Pent 范围，量死支占比/死因分布/深度）——用户 2026-11-20 裁「先不发」。
2. **数学级枚举压缩**：把可达性闭包换成结构不变量的证明（分支剪枝可证化）——研究级，
   Hales/Isabelle 均未做过；成功则同时解 580 内核化与重编时长两个问题。
3. **内核求值代际跃迁**：Lean 内核 ByteArray/大整数加速网络端 **UNRESOLVED**（如实标注，
   未承重）；若未来内核原生支持高效字节数组求值，反射检查器路线成本需重估。
4. **Mathlib `lrat_proof`（kernel-as-LRAT-checker，Carneiro 2022）**：本机 mathlib 包已建
   （8,264 oleans——「本仓无 Mathlib」folklore 仅指本仓代码不 import，包体在场）；
   当前 585 无靶（组合可达性 ≠ 命题重言式），但未来小件可考虑。

## 6. 指针索引

| 件 | 位置 |
|---|---|
| 主报告（含 §7 pilot 草案、§8 580 全量成本模型） | `~/c17_backup/lane_snapshots/trust585-research-w1/RESEARCH.md` |
| 探针脚本与日志 | 同目录 `probe_tri_root0.py` + `logs/` |
| 信任基座账本 | `docs/trust-base.md`（§1.1 已同步本判定） |
| 基座逐行清单 | `docs/trust-base.tsv` + `docs/trust-base.md` §4 |
| 验收式与禁造边 | `AGENTS.md` §1/§2 |
| 历史成本记录 | `DECISIONS.md:359`（~7 天重建）、`DECISIONS.md:515-529` |
| 编排者勘误记录 | `docs/priority-queue.md` §8 续1320（旧判决 5× 勘误） |

> 评审请求：本报告的核心可挑战点是 §2-1（bv_decide 同公理类——请独立读 toolchain 源码
> 复核）、§2-2（5× 勘误的结点锚外推）、§5-1（死支结构的可证书性——**这是整条路线唯一
> 没有数字的地方**，也是唯一可能改写结论的地方）。
