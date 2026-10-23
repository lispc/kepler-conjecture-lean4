# BIXPCGW 紧致化原型：诚实 no-go（2026-10-24，Lane K 交付）

> 快照：`lane_snapshots/bixpcgw-tighten/`（patch ~1.6k 行、mpmath 对拍电池、全部日志）。
> **结论**：centered form / 逐 op 仿射 / 整 prog 区间 AD 三架构全部与 stock 逐盒零差异——
> 根盒宽 2^-4..2^-6 × 中间量 ~1e4 下二阶余项 ±1e7 压倒真值，包络紧致化无判定增量。
> **维持挂起**；若续攻唯一实证方向 = 紧致化与二分耦合（gsplit 强化），另 cw div 倒数路径
> SEGV（sub_081 可复现）需独立 r-record 槽重写。sound 电池有战功（抓出 ite 槽位假闭合一次）。

---

# TIGHTEN — BIXPCGW 残叶多项式子式紧致化（Lane K 交付）

日期: 2026-10-24。基座: 主仓 HEAD `pipeline/interval/bb_arb.c`
（md5 `2225a8c6cf8417b092931b5a8734e61f`，与 Lane E 核对值一致，主仓只读未动）。
工作目录 `/tmp/bixtight`；交付 patch = `patches/bb_arb_tighten.patch`
（纯新增、0 删行；无 `--tighten` 时与 stock 逐字节一致，见 §5）。

## 0. 结论先行

**验收线（resid336 前 100 盒：20k 节点内叶数 ≥3× 削减且 100/100 闭合）未达成。**

最终 sound 版实测（§3 全表）：

| 样本 | stock/bare | `--tighten`（sound 最终版） |
|---|---|---|
| resid336 前 100 盒 | 94/100，68,410 叶，35 s | **94/100，68,410 叶（逐盒零差异）** |
| artifact2000 抽样 40 根盒 | 0/40 闭合 | 0/40 闭合（一致） |
| pending21 根盒 | 3/21 闭合 | 3/21 闭合（一致） |

即：**最终版 `--tighten` 在本案全部固定样本上与 stock 行为完全一致
（sound 性成立、无收益）**。诚实的 no-go 边界与机理见 §4：
centered form / 一阶仿射在 2^-4..2^-6 盒宽 × 中间量 ~1e4 的本题参数下，
数学上就到不了判定所需的紧度；这不是实现质量问题（三种架构 + 一个
假闭合 bug 都被逐一定位并留档）。

## 1. 最终实现（v3.1，`--tighten` 旗标）

- **主路径 `try_centered_whole`**：整 prog 一次性 centered form
  `f(box) ⊆ f(c) + ∇f(c)·δ ± ½Σ_ij |H_ij| w_i w_j`。双记录并行：
  - 点记录 {f0 = f(c) 球, gf[n] = ∇f(c) 球}（中点精确点求值 + 点 AD）；
  - 区间记录 {V, G[n], Hh[n²]} = {f/∂f/∂²f 在盒上的区间}
    （二阶区间 AD：mul 积法则；一元 sqrt/atan/log 链式）。
  - ite guard / sqrt / log / abs 的域判定用**槽的 centered 包络**
    （cw_slot_hull：f0 ± Σ|gf|half + ½Σ|Hh|half²，比裸区间紧）。
- **回退**：cw 放弃（含 div 的 prog、guard/abs/sqrt/log 跨 0）→ 原裸区间
  求值器。**绝不比 stock 差**。含自适应退避（连续放弃后指数拉长重试间隔）。
- 全部系数/余项经 FLINT arb/mag 外向舍入；包络由构造包含真值域
  （逐 op 公式注释见 patch）。
- 审计旗标 `--tighten-stats`：打印根盒 bare/tight 区间对拍 + cw 命中/放弃计数。

## 2. 架构演进（过程全部留档，含失败与假闭合）

| 版本 | 思路 | 实测 | 判定 |
|---|---|---|---|
| v0 | 逐 op 一阶仿射全 prog | box0 20k 节点 **0 闭合**；余项经嵌套 mul 几何复合 | NO-GO |
| v1 | run 级 centered form（mag B/D/H 传播）+ 逐 op 仿射胶水 | box25 叶数 5504 vs bare ~684（**8× 恶化**），wall 40× | NO-GO |
| v2a | 整 prog centered form（mag B/D/H 递推） | 曾报 100/100 + 100 叶 → **假闭合**（ite 槽位 d--/d++ bug，被 soundness 电池抓出：sub_099 hull [4,4] vs 真值 ≥2701） | 作废 |
| v2b | 修复后（含 div 倒数 in-place 别名 bug → SEGV） | sub_099 hull ±3e7（sound 但极肥）；sub_081 SEGV | 换思路 |
| v3/v3.1 | cw 快路径（div 禁用）+ 裸区间回退 + 退避 | §3：与 stock 完全一致 | 交付 |

v3.1 已知未修缺陷：cw 的 div 路径（r=1/g 的区间倒数记录）存在未解的
别名/时序 SEGV（sub_081 复现），本波以"含 div 即放弃 cw"规避。故
`--tighten` 当前只对**不含 div** 的 prog 有实际作用（本案主 prog 全含 div）。

## 3. 矩阵实测（nice -n 19 单进程；复现 `scripts/run100.sh`）

| 配置（每盒 --max-nodes 20000） | pass | 总叶数 | wall |
|---|---|---|---|
| A `bb_arb_stock` | 94/100 | 68,410 | 35 s |
| B `--tighten`（v3.1） | 94/100 | 68,410 | 36 s |
| C `--tm --ite-hull2 --gsplit2` | 95/100 | 48,936 | 172 s |
| D = C + `--tighten` | 未单跑：v3.1 的 cw 在含 div prog 上必然放弃，行为 ≡ C（机制见 §4；B≡A 的逐盒零差异已直接证实该等价性） | — | — |

A、C 与 Lane E 的历史数字逐位一致（94/100、68,410；95/100、48,936）——
基线复现可信。

## 4. 为什么到不了 ≥3×（机理，供下一波）

1. **逐 op 仿射/Taylor 余项经嵌套乘法几何复合**（r_new ⊇ Rf·Rg）：
   150+ 指令的表达式上余项达 ±3e7（真值仅 ~1e4）。方法上界，非实现问题。
2. **二阶区间 AD 的 Hessian 不复合但被中间量污染**：中间 sub-产品 的
   naive 区间肥胖度（~18×，如 sub_099 bare ±81k vs 真值 7.7k）乘进
   H 的 V·H 项。区间 AD ≠ mag 递推，但同受此限。
3. **线性项下限**：梯度 × half 在 2^-4 盒宽、量级 1e4 下已 ~±8e3，
   与真值域同量级——centered form 的线性部分收益上限被盒宽锁死。
   E 预演的 D 因子 66→42 只对单个因子成立，且仍未定号。
4. **闭合机制错配**：stock 的 263/336 盒靠 disj/naive 正性闭合；
   cw 的紧值域只在 guard 可判盒上才有机会出手，而 guard 可判 ⟹
   naive 大多也能走通 → cw 无增量。guard 跨 0 盒（73/336）在根宽下
   centered guard 包络仍跨 0 → abort → 与 stock 同步 bisect。

## 5. Sound 性论证与对拍（通过）

1. **构造论证**：每 op 包络 ⊇ 真值域（arb/mag 外向舍入；公式逐条注释）；
   centered 装配 = Taylor-Lagrange 余项 + 球失配余量，恒为超集。
2. **点采样电池** `scripts/point_battery.py`（mpmath 60 dps；盒角点 2^n +
   中心）：
   - 116 敏感子式 mini-case（48 ite guard / 36 div 分母 / 18 sqrt 底 /
     14 abs 参数）：**10,578 点，0 违例、0 假闭合**；71 例 NOT-SUBSET
     （sound 但肥：div-free 纯多项式 case 的 cw 包络 ±1e7，已知 §4.2）。
   - resid minicase 13 例：1,419 点，0 违例、0 假闭合。
   - 电池曾抓出 v2a 假闭合（sub_099）—— soundness 审计有效的直接证据。
3. **默认路径逐字节回归**：每轮修改后 `bb_arb_tight CASE --max-nodes 2000`
   （无旗标）out md5 `629e4dfe00dfb7076f6117cdb2d1f89a`、
   err md5 `b4551758229dbea5ee4763b2fe723df7`（= E 的 stock 基线）。

## 6. 与 gsplit2 的交互（任务 5）

- 机制：gsplit2 只在 TM guard 跨 0 触发 hull 时改选切分维；`--tighten`
  不触碰 TM 路径的 guard 判定 → gsplit2 选维行为不受影响（源码事实）。
- 实测：v3.1 的 cw 在含 div prog 上必然放弃 → B ≡ A 逐盒零差异
  → D ≡ C（未单跑 30 盒，等价性由 B≡A 直接推出）。即本波形态下
  gsplit2 的 1.40× 杠杆完整保留、不受 tighten 干扰。
- 下一波若把 cw 的紧致 guard 判定接入 TM 的 guard 判定（本波未做），
  guard 跨 0 事件减少 → hull 触发减少 → gsplit2 作用面自动收缩
  （"守卫面消失"的预期成立的前提是 cw 的 guard 包络足够紧——
  见 §4.3，根盒宽下并不成立）。

## 7. no-go 边界与下一波建议（诚实）

- **验收线 no-go**：centered form / 一阶仿射（三种架构）在本案
  2^-4..2^-6 盒宽 × 1e4 中间量级下无收益；单纯更强的包络算法不解决
  盒宽×量级的线性项下限。
- v3.1 遗留缺陷：cw 的 div 倒数路径 SEGV（已规避为"含 div 即放弃"），
  下一波若继续应以独立 r-record 槽重写（不复用除数槽）。
- 若继续本方向，唯一有实证支撑的路径：**紧致化与二分耦合**
  （先按 guard 面切 1-2 刀再 centered 判定，即 gsplit 强化而非包络强化）；
  否则建议维持诊断线的判断：挂起本 case 等更强机器/算法。

## 8. 交付物清单（本快照）

```
TIGHTEN.md                    本文件
PROGRESS.md                   滚动进度（含全部过程数据与作废标记）
patches/bb_arb_tighten.patch  对 HEAD bb_arb.c 的完整 diff（纯新增 ~1.6k 行）
bb_arb_tight_source.c         修改后完整源码副本（对照用）
scripts/run100.sh             100 盒矩阵 runner
scripts/run30.sh              30 盒子集 runner
scripts/point_battery.py      mpmath 点采样 soundness 电池
scripts/synth_roots.py        artifact/pending21 → 单盒 case 合成
scripts/resid336.json 等      样本清单副本（与 bixpcgw 快照一致）
logs/resA_bare.perbox         A 基线逐盒（94/100, 68,410）
logs/resBfinal_tight.perbox   B 最终版逐盒（与 A 逐盒零差异）
logs/resC_gs2.perbox          C 逐盒（95/100, 48,936）
logs/battery_sub116.log       116 子式电池（10,578 点 0 违例）
logs/battery_minicase13.log   minicase 采样电池（1,419 点 0 违例）
logs/resBfinal.log            B 运行日志
MD5SUMS                       全部交付文件校验
```

## 9. 诚实性声明

实测：§3 全部数字；电池数字；回归 md5；A/C 与 E 历史数字逐位一致。
推断：D ≡ C 的等价性（由 B≡A + cw 含 div 必放弃的源码事实推出，未单跑）。
未跑：全量 336 盒的 tighten 矩阵（A 的 336 盒基线 E 已有：313/336、
179,629 叶；v3.1 行为=stock，可推断一致）；Lean 端到端（无权限，纪律）；
pending21 的 Lean 重放。
