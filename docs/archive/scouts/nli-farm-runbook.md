# FARM-RUNBOOK — nli rest 单条「证书就绪 → 落库」命令序列 + 批次建议（nli-glue-template-w1）

> 读者预设：不了解本波上下文，照做即可。上游依据 = a2-rest9-w1/RUNBOOK-G4.md
> （G4 发射/分段构建/回灌/落库全流程，A1+A2 两轮实测）、A1 雷区册、本目录
> rest-params.tsv / GlueTemplate.lean.draft。
> **模板状态**：A1 单点实证草案，A2 落地后校准（见 GlueTemplate 头注）。

## 0. 前置事实（先读，能省一天）

- 构建锁与流水线脚本已固化：跨车道锁 `/tmp/kepler_build_lock.sh`
  （`source` 后 `lock_build nice -n 19 lake build <target>`；30min TTL +
  内存闸 + 1h 获取超时），落库走 `scripts/integrate_lane.sh`
  （manifest 映射 + pathspec 提交 + THM 闸；rc 码表见脚本头注）。
- **两档实测标定点**（构建时长外推用）：FWGKMBZ 605 分片/205,418 叶 =
  7h02m；QITNPEAx3725403817 2,775 分片/964,984 叶 = 外推 38-45h。
  分片构建速率 ≈ 86 分片/小时（本机 12 核 38.6 GB，nice 19）。
- harness 60 min 杀后台：单次 Bash 调用别指望跑完全程，**到点被杀后重跑
  同一条命令**即可（lake 按 olean 缓存断点续跑；A1 即此法 8 段零失败）。
- lake 大致按 Shard 编号**降序**先建，完成顺序不代表缺件；进度只看
  `.olean` 计数（雷区 #389）。
- G4 发射通路不在本机（无 ssh 主机条目，RUNBOOK-G4 §6）：cert.json 层面的
  发射由编排者/持机人执行；本机职责面 = 补丁核查 → 段建 → 回灌 → 粘合
  → 落库。

## 1. 单条 rest 流程（从证书就绪到落库）

记 `NAME` = rest 的 HOL 名去空格（如 `GCKBQEA`、`QITNPEA5653753305`）、
`CASE` = case JSON 文件基名、`C<NAME>` = 证书模块名（模块名 = 发射
out.lean basename，无 `--name` 选项）。工作克隆约定
`/tmp/<lane>/repo/lean`（APFS 克隆，**不动任何 tracked 文件**）。

### 步 1 — 就绪核查（人工，~15 min）
```bash
# 1a. case JSON 在盘且 id 对桩（PEMKWU↔PEMKWKU 型漂移在此拦截）
ls pipeline/interval/out/cases/<CASE>.json
python3 -c "import json;print(json.load(open('pipeline/interval/out/cases/<CASE>.json'))['id'])"
# 1b. rest-params.tsv 该行 → 桥类（S3）与盒端点清单（S1）核对
# 1c. MISSING case JSON 的 tmpl 族（QITNPEA1×6 / ZTGIJCF4×16）：走 §4 例外通道，本步不可跳过检查
```

### 步 2 — G4 发射（仅编排者/持机人；证书已在库则整段跳过）
```
python3 pipeline/interval/emit_lean.py <CASE>.json <cert.json> C<NAME>.lean --bbg --params=<G4 params>
```
产物应与 case JSON 逐项一致（box 逐端点、叶数 ± 小容差）；移植在库旧证书
时以「库内分片 = 本 case 证书」四条证据链为准（RUNBOOK-G4 §0）。

### 步 3 — CertG 核查（一次性质检；A2 落地前必做）
```bash
cd /tmp/<lane>/repo/lean && source /tmp/kepler_build_lock.sh
lock_build nice -n 19 lake build Kepler.Interval.CertG   # 期望 exit 0
```
若复现 `CertG.lean:248/:420 decide=false`（TM demo 债），按 RUNBOOK-G4 §1
选项 A（重烤 mantissa，先例 C549Mono）或 B（删 8 个 demo 声明，抄送记档）
处理——该债挡所有经 Base→CertG 依赖链的 rest（bb_arb 分片链）。

### 步 4 — 分段构建（机器时；分段 = 每段重复同一条命令）
```bash
cd /tmp/<lane>/repo/lean && source /tmp/kepler_build_lock.sh
lock_build nice -n 19 lake build Kepler.Interval.Cases.C<NAME>
# 进度（每段末）：
ls .lake/build/lib/lean/Kepler/Interval/Cases/C<NAME>/ | grep -c '\.olean$'
```
段长 ~90 min；期望计数涨到 分片数+1（含 Base）。**不要同时 build
Kepler.Assembly**（163 MB PA21 olean 内存叠加会顶爆包络，雷区 #399）。
磁盘预算：全树 olean ≈ 源目录 965 MB 量级 × 15-16（按 A2 外推），开工前
`df -h` 确认余量。

### 步 5 — 完工自证（干净探针）
```bash
cat > /tmp/<lane>/probe.lean <<'EOF'
import Kepler.Interval.Cases.C<NAME>
#print axioms Kepler.Interval.Cases.C<NAME>_pos
EOF
cd /tmp/<lane>/repo/lean && lake env lean /tmp/<lane>/probe.lean
# 期望：depends on axioms: [propext, Classical.choice, Quot.sound]
```

### 步 6 — olean 回灌主仓（A1 模式）
```bash
SRC=/tmp/<lane>/repo/lean/.lake/build/lib/lean/Kepler/Interval/Cases
DST=/Users/zhangzhuo/repos/kepler-conjecture-lean4/lean/.lake/build/lib/lean/Kepler/Interval/Cases
mkdir -p "$DST/C<NAME>"
cp "$SRC"/C<NAME>.olean "$SRC"/C<NAME>.ilean "$DST"/
cp "$SRC"/C<NAME>.olean.hash "$SRC"/C<NAME>.ilean.hash "$DST"/ 2>/dev/null || true
cp "$SRC"/C<NAME>.trace "$DST"/ 2>/dev/null || true
cp "$SRC"/C<NAME>/*.olean "$SRC"/C<NAME>/*.ilean "$DST/C<NAME>"/
cp "$SRC"/C<NAME>/*.hash "$SRC"/C<NAME>/*.trace "$DST/C<NAME>"/ 2>/dev/null || true
```
回灌前先核主仓与克隆该批源 md5 一致；回灌后以 `lake build` 真实重放为准
（SF-42 雷区：`cp -Rc` 后可能假绿，必要时先删目标 `{olean,ilean,trace,hash}`）。

### 步 7 — 粘合件撰写（人工； GlueTemplate 实例化）
- 按 GlueTemplate §CHECKLIST 1-7 填 ⟪…⟫（数据源：rest-params.tsv 行 +
  证书顶模块头注释 + case JSON）；
- 同族共享桥只在族首例新写，后续 import 复用；
- 车道草稿构建验证（步 4 同法 build 该 glue 目标）+ 探针标准三；
- 单条人工工时：同构/单桥类 2-4 h；例外类（首例带族桥）+4-8 h；
  tmpl 族（桥齐后）1.5-2.5 h/条。

### 步 8 — 落库（integrate_lane.sh，路径限定提交）
```bash
# 快照目录内备齐：glue 文件 + Assembly.lean 两处编辑的落库文本
cat > /tmp/<lane>/manifest.tsv <<EOF
A<批次><NAME>Glue.lean	lean/Kepler/A<批次><NAME>Glue.lean
Assembly.patched.lean	lean/Kepler/Assembly.lean
EOF
INTEGRATE_REPO=/Users/zhangzhuo/repos/kepler-conjecture-lean4 \
  /Users/zhangzhuo/repos/kepler-conjecture-lean4/scripts/integrate_lane.sh \
  --snapshot /tmp/<lane>/snapshot \
  --manifest /tmp/<lane>/manifest.tsv \
  --lane-files lean/Kepler/A<批次><NAME>Glue.lean,lean/Kepler/Assembly.lean \
  --thm nliRest<NAME> \
  --commit-msg "nli farm 批<批次>: <NAME> 粘合落库 (C<NAME> 证书回灌)"
# 落库后主仓验收：
cd /Users/zhangzhuo/repos/kepler-conjecture-lean4/lean
lake build Kepler.Assembly          # olean 就位时期望分钟级（A1 实测 ~1min12s）
echo 'import Kepler.Assembly
#print axioms Kepler.Assembly.nliRest<NAME>' > /tmp/<lane>/probe2.lean
lake env lean /tmp/<lane>/probe2.lean   # 期望标准三（注册全名，雷区 #391）
```
（细则照 a2-rest9-w1/APPLY-DRAFT.md：Assembly 侧编辑 = import 区加一行 +
sorry 骨架替换为 `nliRest<NAME> : bank_<NAME> := <NliGlue>.nliGlue<NAME>`
或具名前提槽一行代入。）

### 步 9 — 地图重扫 + 记账
```bash
grep -c 'nliRest.*:= sorry' lean/Kepler/Assembly.lean   # 计数应 −1（当前 57）
```
- `docs/e2e-reachability-map.tsv` 该 rest 位次状态更新（A1 落库后做法）；
- `docs/priority-queue.md` 销账 −1；
- rest-params.tsv 该行加「已闭 @commit」注记（本快照目录内维护，不动主仓）。

## 2. 批次建议

- **批次粒度 4-6 条，按 S3 桥族分组**（同批共享一座桥，验证成本摊薄）。
  建议批序（风险递进）：
  1. **B0 校准批**：MKFKQWUhalfwt、MKFKQWU（+QITNPEA4003532128a、BIXPCGWb
     备选）——验证 A1 签名直配与 simp only 集合，校准模板；
  2. **B1 首例批**：GCKBQEA、BIXPCGW1738910218a2、BIXPCGW7080972881a2、
     BIXPCGW6652007036a2（A2 落地后桥可直接抄）；
  3. **B3 首例批**：BIXPCGW9455898160 + 4 条 QITNPEA 线性 spine 单目标族
     （3848804089/5814748276/6206775865/5653753305）——同模板 5 连发；
  4. **B4 批**：TEWNSCJ、TXQTPVC、QITNPEAv24003532128、IXPOTPA、PEMKWU；
  5. **tmpl 批 ×2**：QITNPEA1×6、ZTGIJCF4×16（16 条分 3 小批；桥 3+4 齐
     后为纯机械实例化；case JSON MISSING 走 §4 例外通道前置）；
  6. **杂项收尾批**：FHBVYXZ×3、GLFVCVK4×5、MKFKQWU 余量、JSPEVYT、
     RQWUDDU、QITNPEA5400790175×2、QITNPEA2134082733、QITNPEA9939613598、
     1965189142a（B6 单件）。
- **闸序**：每批 = 全批证书回灌完成 → 全批 glue 构建绿 + 探针标准三 →
  逐条 integrate_lane 落库（每条独立 commit，pathspec 限定）→ 一次地图
  重扫 + 批记账。批内任何一条红线（证书性失败/闸未过）→ 该条退回步 1，
  其余照常（分片相互独立，无批内耦合）。
- **回滚点**：①回灌前——源 md5 核对（不一致即回炉，禁止只拷 olean）；
  ②落库前——glue 草稿 + Assembly 补丁全在快照目录，主仓零脏；③落库后
  ——每条独立 commit，`git revert` 单条可逆；④批末——地图重扫计数对账
  （sorry 计数、map 位次、priority-queue 三处一致）。
- **并发**：构建锁一次只允许一个 lake 进程；批内证书段建与上一批落库/
  记账（人工）可流水并行。

## 3. 单条工时预估（人工净时，不含机器构建等待）

| 桥类 | 首例（含族桥） | 后续同族 |
|---|---|---|
| B0 同构 | 3-4 h（校准批） | 1.5-2 h |
| B1 dihY | 2 h（桥 A2 已写） | 1.5-2 h |
| B2 eta_y | 4-6 h | 1.5-2 h |
| B3 gamma4 | 6-10 h（风险项） | 2-3 h |
| B4 gamma23/spine | 3-4 h（P25 先例复制） | 2-3 h |
| B6 asnFnhk | 3-4 h（在库先例抄改） | —（单件） |
| tmpl 族 | 桥齐后 1.5-2.5 h/条 | 同左 |

机器构建等待另计：小证书（百叶级）≈1 h，A2 量级 ≈38-45 h——**排队不阻塞
人工**，批内证书可提前串行发射段建。57 条全周期粗估：人工 ≈ 110-150 h +
机器 ≈ 6-8 个 A2 量级周期（批内共享段建窗口）。

## 4. 例外通道（非常规件）

- **case JSON MISSING 22 条**（QITNPEA1×6 + ZTGIJCF4×16）：均系
  make_F4/add_QITNPEA1 循环生成（ineq.hl:845-862 / 486-499），需生成器式
  case 产出（编排者/G4 侧）；禁止手猜路径与参数。补齐前该 22 条冻结。
- **PEMKWU ↔ PEMKWKU id 漂移**：步 1a 拦截，一行核对后放行。
- **P25 桥 private**（p25_gamma23Full8X_yOfX_eq）：B4 首例批前决定
  「复制入 glue」或「主仓提级 public」（后者是 tracked 改动，走编排者）。
- **CertG demo 债**：步 3 拦截；A2 落地即自然验证该补丁。
- **A2 未完工边界**：本 RUNBOOK 的 B1 桥与具名前提槽代入形以 A2 落地
  实测为准校准；A2 落地前 B1 批次不得先发。
