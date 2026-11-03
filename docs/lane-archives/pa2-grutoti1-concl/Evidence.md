# Evidence — lane `pa2-grutoti1-concl`（2026-11-03，Lane-draft）

HEAD = f8b3e46f。基线按 `git show HEAD:lean/Kepler/Text/PackingAuto2.lean` 冻结快照
（编排者 T0 闸对 `LocalAuto1.lean` 的在途改动与 PA2 链无关；期间未读未写共享
`.lake`；收尾时该在途件已被编排者收走，`git status --porcelain` 为空 = 本车道
tracked 零改动自证）。

## 1. 基线（logs/baseline.log）
- RC=0，0 error；`declaration uses sorry` **26** 条；总 warning **61**
  （26 sorry + 35 linter/deprecation）。

## 2. 勘察结论（工单"先勘"项作答）
- PA2 内**无**非 `_concl` 的 GRUTOTI，**无** edgeX/dihX 求和同义件；
  `GRUTOTI1_concl` 在 PA2 内无消费者（下游 PA16:1617 `KIZHLTL4` 经 import 消费）。
- `PackingConcl` 接口已有同形件：`GRUTOTI1_concl_discharged`（:809）与 PA24 私拷
  `GRUTOTI1_concl_p24(_pub)`，均消费 PA2 的 sorried 本体——**plumbing 缺口不在
  接口层，而在 PA2 本体的证明**。
- PA23（import PA2）含 statement 同形**真证** `GRUTOTI`（GRUTOTI.hl:60-8001 移植
  capstone）；章体零裸 sorry。反向 import 成环 ⇒ 链复制是唯一路线，且为 PA2 既有
  纪律（§0-§6.5 `p2g_*` 先例）。

## 3. 落地形态（Kit-draft = HEAD PA2 + 插入块，diff +28362/−1）
- 插入点：`GRUTOTI1_concl` docstring 前（首个消费者之前），`namespace Kepler.Text` 内。
- A：PA23 GRUTOTI 章（PA23:218-6385 相邻整段逐字，private 名不变，含块间
  docstring/set_option——复制粒度为 [pre_i, pre_{i+1}) 精确切分，见 §7 坑 1）。
- B：外部 Kepler 依赖 **628 件**（13 模块），逐件 `private` 化 + `p2e_` 改名，
  跨文件引用同步改名；构建由编译器 unknown-identifier 驱动 10 轮收敛
  （logs/slice5-8、final1-3）。
- C：`GRUTOTI1_concl` 体 = `PackingAuto23.GRUTOTI` capstone 证体逐字
  （`intro … exact grutoti_concl_arith …`）。

## 4. 上游 sorried 件核查（新证据）
| 件 | 原产地 | 状态 | 进链? |
|---|---|---|---|
| `AJRIPQN` | PA17:931 | **已闭合**（体 = `exact p17_ajripqn_of_tailfix …`） | 是（净版） |
| `QZKSYKG1/2` | PA14:1936/3034 | **已闭合** | 是（净版） |
| `PROJECTION_ORTHOGONAL` | PA5:106 | 已知误移植、陈述为假、sorry 保真 | **否**（代码零引用） |
| `U0_NOT_IN_CONVEX_HULL_FROM_ROGERS` | PA12:1060 | sorried | **否**（代码零引用） |
- 被拷 628 件的构建期 sorry 审计：0 命中（审计正则已含 bare 形态；PA15 存在
  内联 `:= sorry` 形态 4 处 :465/:470/:2074/:5867/:5888，对应 twin 均未进链或
  未触发警告——final3 全谱仅 3 条伪影警告，见 §5）。

## 5. 终验读数（logs/final3.log，WorkAx=Work+4 条 #print，34253 行）
- **未达 RC=0**：82 error = 45 unknown identifier + 12 unsolved goals + 级联
  （rcases/rewrite 对错误恢复 metavariable 的二阶失败）。
- 45 个残余 unknown 精确清单：`ext_final3.txt`（含 40 个 `p2e_*` ——均为已拷但
  依赖块尚未齐的连锁件；`ext_master.txt`=164 根已含其大部分裸名依赖）。
- `#print axioms` 实验读数（**错误恢复态，不作最终 axiom 面**）：
  `GRUTOTI1_concl depends on axioms: [propext, sorryAx, choice, Quot.sound]`；
  三条 `p23_*` 同面——其 "declaration uses sorry" 警告为依赖块失败导致的
  恢复伪影（三件本体在 PA23 为真证 tactic 块，依赖的 SMALLEST_ANGLE 链已核查
  为 PA15 净版）。下波清零 unknown 后重读，预期 axiom 面脱离 sorryAx。
- warning 谱面：28 sorry 警告 = 25（PA2 原有 26 − 本体）+ 3 伪影；其余 linter
  警告未逐条比对（闸在 RC=0 后才有效，linter 开关处方见 DELIVERY 工单 3）。

## 6. kit 闸逐项（对当前 kit 重生成后）
- `git apply --check`（HEAD，check-only）：**PASS**
- 陈述逐字冻结（docstring+5 行陈述+`:= by` 逐字节等价）：**True**
- 零新 import：**是**（PA2 原 5 条 import 不动）
- 新增行禁词：tactic 级 0；注释文字 48 处（史志 docstring 逐字携带，与 HEAD
  既有注释口径一致，如 PA2:1113"PA5 正本 sorry"）

## 7. 方法坑与处方（下波复用）
1. 复制块切分必须用 [pre_i, pre_{i+1})（pre=含 docstring 的预起点）；右端取
   decl 行会吞下一件 docstring ⇒ docstring 重复 = `unexpected token '/--'` 解析错。
2. 块尾可达原文件 EOF，须剥 `end /namespace` 行——否则在插入点把
   `Kepler.Text` 关闭，其后全部名字解析失败（round 6-7 的 37 个幽灵 unknown 主因）。
3. 闭包扫描只扫代码区 [decl, 下一件 pre-start)：docstring 英文词会误拖
   sorried 占位件（PROJECTION_ORTHOGONAL/U0_NOT_IN… 即此）。
4. 跨文件引用一层一轮：编译器驱动的 unknown 清单是唯一真值；`maxErrors` 须用
   CLI `lean -D maxErrors=8000`（文件内 `set_option maxErrors` 不生效，`-K` 非法）。
5. 上游状态以**当前源码**为准：PA17/PA23 文件头的 "sorried" 注记多已过时。
