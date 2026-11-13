# DEF-FIX 章程（草案）：tau_x kit 真身化 —— `taumX_p19`/`tauResidualX_p19` 及 LA38 孪生（2026-11-14，tauxkit-w1 拟）

> **状态：APPROVED（用户 2026-11-14 批；侦察车道 tauxkit-w1 产出，编排者正式化）。** 依据：AGENTS §2「定义改动只走
> DEF-FIX 通道」+ 先例 `docs/def-fix-charters/p21-anchor/`（锚点重编码）与
> `docs/def-fix-charters/vas-cluster-move/`（纯搬运、保陈述逐字节）。
> 证据全件：`~/c17_backup/lane_snapshots/tauxkit-w1/DELIVERY.md` + `logs/`（探针均标准三 axioms）。
> 闸模式 = `GATE_MODE=DEF-FIX`；`DF_PATCH=` 落库时由编排者将本草案落入
> `docs/def-fix-charters/tauxkit-realify/gate-<file>.md` 后引用。

## 0. 一句话

把 LA19 的两个**零常量假桩** `taumX_p19`/`tauResidualX_p19`（`fun _ => 0`，致存量陈述
`tau_x_tau_residual_x_general_p19` **按字为假**——探针 `probe_a_stub_literal_false` 以标准三
axioms 否定之）与 LA38 的四个 **`:= sorry` 不透明桩**（`taumXP38`/`tauResidualXP38`/
`taudXP38`/`flatTermXP38`）的体，改成**树内已存在的逐字 HOL 同体真身**（`LocalAuto1` 的
`_t11` kit）；另将 LA38:174 `taudP38`（`OWZLKVY4` 陈述所消费）指到 `taud_t11` 同体。
**不改任何陈述、sorry 数零净增减、零新 import、零 axiom/native_decide 增删**；
后续 7 件消费者的证明义务由后续车道按本章程 §3 的处置表领取。

## 1. 对象与 HOL 锚

- HOL 定义（行段全文见 DELIVERY.md §1.1）：
  - `taum_x` = `reference/flyspeck/text_formalization/general/sphere.hl:827-829`
    （`rhazim_x + rhazim2_x + rhazim3_x − (&1+const1)·pi`）。
  - `tau_residual_x` = `reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:181-185`
    （`rhazim{,2,3}_x_div_sqrtdelta_posbranch` 三旋转和，:169-179 与 `dih_x_div_sqrtdelta_posbranch`
    :138-142、`matan` sphere.hl:728-731）。
  - `flat_term_x` = sphere.hl:825；`taud_x` = nonlin_def.hl:413-416。
- Lean 真身（**已存在于树**，逐字同体，本修只"指过去"）：
  - `Kepler.Text.LocalAuto1.lean:1243` `taumX_t11` ≡ HOL `taum_x`（逐字核对）；
  - `Kepler.Text.LocalAuto1.lean:1237` `tauResidualX_t11` ≡ HOL `tau_residual_x`（逐字核对）；
  - `LocalAuto1.lean:1124` `taudX_t11` ≡ HOL `taud_x`（展开形）；
  - `LocalAuto1.lean:1117` `flatTermX_t11` ≡ HOL `flat_term_x`；
  - `LocalAuto1.lean:1120` `taud_t11` ≡ HOL `taud`。
  - `_t11` 后缀来由（LA1:980-987）：ICD 与 Text 根 `sqrt3` 撞名，故 LA1 以 `_t11` 复制全套体。
- 改前假桩（本修对象）：
  - `LocalAuto19.lean:128` `taumX_p19 : … := fun _ _ _ _ _ _ => (0 : ℝ)`（EXTERNAL-ANCHOR 注记）；
  - `LocalAuto19.lean:132` `tauResidualX_p19 : … := fun _ _ _ _ _ _ => (0 : ℝ)`；
  - `LocalAuto38.lean:182` `taumXP38 : … := sorry`；`:185` `tauResidualXP38 : … := sorry`；
  - `LocalAuto38.lean:178` `taudXP38 : … := sorry`；`:188` `flatTermXP38 : … := sorry`；
  - `LocalAuto38.lean:174` `taudP38 : … := sorry`（OWZLKVY4 陈述消费；`= taud_t11` 同体）。
- 语义差（改前 → 改后）：
  - LA19 侧：改前 `taumX_p19 ≡ 0`、`tauResidualX_p19 ≡ 0` ⇒ C1 陈述
    `taumX_p19 x = √deltaX·tauResidualX_p19 x + flatTermX_p19 x1` 在平坦点 (4,4,4,12,4,4) 处
    化为 `0 = −sol0`（sol0Pos_p19：`sol0 > 0`），**按字为假**。改后为真陈述（HOL 同证 +
    数值 6/6 + delta=0 分支符号探针）。
  - LA38 侧：改前 4+1 桩为不透明常量 ⇒ 消费者陈述**不可证也不为假**；改后全部转为真陈述。

## 2. 改动范围（7 个声明 / 各 1 行定义体 + 7 行 docstring 注记）

| 文件 | 声明 | 改行 | 性质 |
|---|---|---|---|
| `LocalAuto19.lean` | `taumX_p19` (:128) | 1 | ANCHOR：`fun _ => 0` → `taumX_t11`（别名） |
| `LocalAuto19.lean` | `tauResidualX_p19` (:132) | 1 | ANCHOR：同上 → `tauResidualX_t11` |
| `LocalAuto38.lean` | `taumXP38` (:182) | 1 | ANCHOR：`sorry` → `taumX_t11`（孪生） |
| `LocalAuto38.lean` | `tauResidualXP38` (:185) | 1 | ANCHOR：`sorry` → `tauResidualX_t11` |
| `LocalAuto38.lean` | `taudXP38` (:178) | 1 | ANCHOR：`sorry` → `taudX_t11`（套件附带，C7 需要） |
| `LocalAuto38.lean` | `flatTermXP38` (:188) | 1 | ANCHOR：`sorry` → `flatTermX_t11`（套件附带，C4 需要） |
| `LocalAuto38.lean` | `taudP38` (:174) | 1 | ANCHOR：`sorry` → `taud_t11`（附带，C8 的 OWZLKVY4 陈述需要；`taudP38` 与 `taudXP38` 是两个不同桩，勿混） |

- **零新 import**：LA38:127 已 `import Kepler.Text.LocalAuto1`；LA19 的闭包已含 LA1
  （LA19:1157 已消费 `taudX_t11` 并编译过——本修前即有的事实）。
- **不改任何陈述**（7 件消费者的 statement 逐字节不动）；**不新增/删除 `sorry`**
  （7 件消费者仍是 `sorry`，债务从"假/不可判陈述的 sorry"变为"真陈述的 sorry"）；
  净 sorry = 0。
- docstring 7 行注记改为"DEF-FIX 别名真身，见 `docs/def-fix-charters/tauxkit-realify/`"
  （去掉 "EXTERNAL-ANCHOR / NEEDS: tau_x kit" 措辞）。
- **显式不做**（留后续 charter/车道）：SphereKit 归并（`taumX`/`tauResidualX` canonical 化，
  LA38:214-216 注记的计划 §1.2）——本案不动 SphereKit，避免 `_t11`/ICD/SphereKit 三方孪生
  在本案内交叉；`rhazimP38`/`tauqP38`/`eulerAXP38`/`cayleyR*`/`enclosedP38` 等其余
  LA38 Section 0 桩——非 tau_x kit 消费链，留原 lane。

### 2.1 逐文件 diff 围栏（与实际 `git diff` 逐字一致；正式化时拆入 gate-<file>.md）

`lean/Kepler/Text/LocalAuto19.lean`：

```diff
-/-- EXTERNAL-ANCHOR: HOL `taum_x` (sphere.hl:827) = `rhazim_x`-sum minus
-`(1+const1)*pi`. The `rhazim_x_div_sqrtdelta_posbranch` kit of nonlin_def.hl
-is unported; carried as a stub with the honest signature. NEEDS: tau_x kit. -/
-noncomputable def taumX_p19 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := fun _ _ _ _ _ _ => (0 : ℝ)
+/-- HOL `taum_x` (sphere.hl:827): **alias of `LocalAuto1.taumX_t11`** (the
+verbatim body, already in-tree), per DEF-FIX charter
+`docs/def-fix-charters/tauxkit-realify/`. -/
+noncomputable def taumX_p19 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := taumX_t11
```

```diff
-/-- EXTERNAL-ANCHOR: HOL `tau_residual_x` (nonlin_def.hl:181), the sum of the
-three rotated `rhazim_x_div_sqrtdelta_posbranch`. Stub. NEEDS: tau_x kit. -/
-noncomputable def tauResidualX_p19 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := fun _ _ _ _ _ _ => (0 : ℝ)
+/-- HOL `tau_residual_x` (nonlin_def.hl:181): **alias of
+`LocalAuto1.tauResidualX_t11`** (verbatim body, already in-tree), per DEF-FIX
+charter `docs/def-fix-charters/tauxkit-realify/`. -/
+noncomputable def tauResidualX_p19 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := tauResidualX_t11
```

`lean/Kepler/Text/LocalAuto38.lean`（5 桩同模式；示例 2 个，正式化时 5 份齐全）：

```diff
-/-- NEEDS: nonlin_def.hl `taum_x` (EXTERNAL-ANCHOR; cf. the sibling stubs
-`tauResidualX_p19`/`taumX_p19`, not built in this checkout). -/
-noncomputable def taumXP38 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ := sorry
+/-- HOL `taum_x` (sphere.hl:827): **alias of `LocalAuto1.taumX_t11`** (verbatim
+body, already in-tree), per DEF-FIX charter
+`docs/def-fix-charters/tauxkit-realify/`. -/
+noncomputable def taumXP38 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ := taumX_t11 x1 x2 x3 x4 x5 x6
```

```diff
-/-- NEEDS: pent_hex lane `taud` (y-space taud; the `_p19` twin is not built
-in this checkout). -/
-noncomputable def taudP38 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ := sorry
+/-- HOL `taud` (nonlin_def.hl:406; the `_p19` twin `taudP19` is built at
+LocalAuto19:122): **alias of `LocalAuto1.taud_t11`** (verbatim body), per
+DEF-FIX charter `docs/def-fix-charters/tauxkit-realify/`. -/
+noncomputable def taudP38 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ := taud_t11 y1 y2 y3 y4 y5 y6
```

（`taudXP38 := fun … => taudX_t11 …`、`tauResidualXP38 := … tauResidualX_t11 …`、
`flatTermXP38 x := flatTermX_t11 x` 同模式，正式化时逐字补全；原注记的
"the `_p19` twin is not built in this checkout" 系 stale——`taudP19` 在 LA19:122
已是真身，一并由新注记纠正。）

## 3. 破坏面与验收

### 3.1 下游逐件处置表（本修后的证明义务分配；陈述全部不动）

| # | 件 | 位置 | 换后状态 | 领取方 | 验收 |
|---|---|---|---|---|---|
| C1 | `tau_x_tau_residual_x_general_p19` | LA19:433 | 真陈述 + sorry | taukit 证明车道 W1 | 标准三；路线 = HOL pent_hex.hl:136 双分支（pos/negbranch 桥 + rho_alt + sol0_const1（= `la22_const1_eq`×π，已证））；delta=0 分支模板 = 探针 `probe_a_flat_identity` |
| C2 | OWZLKVY4/hex/pent 塔 | LA19:445+ | 陈述不受影响 | OWZLKVY4 原 lane | C1 + DB "2314572187"/"7796879304" + EAR_DELTA_X4（"8346775862"/"8631418063"） |
| C3 | `taum_taum_x` | LA38:378 | 真陈述 + sorry | taukit 证明车道 W2 | 标准三；路线 = `taum_123` 形 + `sqrtxx`（顺手可收 #5） |
| C4 | `tau_x_tau_residual_x_general` | LA38:3462 | 真陈述 + sorry | 同 W1（与 C1 同一 HOL 证明） | 标准三 |
| C5 | `quad_4680581274_a` | LA38:3662 | 真陈述 + sorry | quad 原 lane | 标准三（DB+LP 级，仍 NEEDS-DB） |
| C6 | `taum_x_sym` | LA38:3693 | 真陈述 + sorry | taukit 证明车道 W2 | 标准三；路线 = `dih_y_sym`（顺手可收 #2） |
| C7 | `taud_x_taum_x` | LA38:3698 | 真陈述 + sorry | 同 C2 线（OWZLKVY4 下游） | 标准三（经 OWZLKVY4） |
| C8 | `OWZLKVY4` | LA38:3475 | 真陈述 + sorry | OWZLKVY4 原 lane | 标准三（DB+LP 级，仍 NEEDS-DB） |

**SF 通道：本修及上表全程零 SF**（7/7 陈述与 HOL 逐字同形，`probe_b` 6/6 形状编译 +
数值验证全绿）。若后续证明中发现某件陈述与 HOL 有未预见的出入，**停线回编排者**，走
`docs/statement-fix-proposals.md`，不许在证明车道内微调。

### 3.2 验收清单（本修 commit 的闸）

1. `LocalAuto19.lean` / `LocalAuto38.lean` 模块级 `lake build` RC=0、**error 计数 0**；
2. 7 件消费者陈述 `git diff` 零触碰（闸门 `DF_PATCH` 围栏外无 statement 行）；
3. 全库 `#print axioms Kepler.the_kepler_conjecture_e2e` 根面与基线逐字节一致
   （sorry 数不变；假桩不是 axiom，换真身不增减 axiom 面）；
4. 换后探针复跑：`probe_a_stub_literal_false` 在 `taumX_p19` 新体上**编译失败**
   （旧假陈述已不存在——同 p21-anchor 的"旧命题消失验证"）；`probe_b` 6 形状以
   `_t11` 名代桩的 example 在新体下可直接 `exact` 实例化（形状同一性）；
5. docstring 注记与 `docs/priority-queue.md` §1/§8 同步（账本层记"假陈述"类债清除）。

### 3.3 风险与回滚

- **回滚**：单 commit `git revert`（7 行 def 体 + 7 行 docstring，无结构性改动）。
- **风险 1（孪生误配，§7.1-25）**：`_t11`/`ICD`/SphereKit 三方孪生并存；本修一律指向
  `LocalAuto1` 的 `_t11` 真身（唯一、已被 LA1 registry 消费、负载最重），不允许在
  证明车道里"顺手"换指 ICD 名或新建第 N 个孪生。
- **风险 2（rho 语义等价不同 def）**：`LocalAuto1:186 rho`（rho_fun 形）与 `rhoICD_t11`
  语义相等（经 `sol0 = π·const1`）但非同一 def；真身体内的 `rhoICD_t11` 不得与 LA1:186 `rho`
  混用，否则 rfl 级步骤卡壳（已在探针中以 `rhoICD_t11` 全程一致规避）。
- **风险 3（债务表述）**：本修不减少根面数字（7 件仍 sorry）；它消除的是"**按字为假**"的
  陈述债（AGENTS §2 的隐性违例面）。pq §8 落日志时写明这一性质，避免"数字没动=白做"的误读。
- **风险 4（DB 依赖）**：C2/C5/C7/C8 的完全证明仍挂 NEEDS-DB（4 条 DB 引理）；本修不承诺
  它们落地，只解除 tau_x kit 这道前置锁。
- **风险 5（后续归并）**：SphereKit canonical 化（`taumX`/`tauResidualX` 宿主迁移）是
  后续独立 DEF-FIX；届时本修引入的 7 个别名行一次性改指——已在 §2 "显式不做"钉死边界。

## 4. 逐文件闸门（草案；正式化时按 p21-anchor 拆 gate-<file>.md）

```sh
cd lean
# LocalAuto19（一个 $FILE 一份围栏；DF_PATCH 按仓库根解析）
GATE_MODE=DEF-FIX DF_PATCH=docs/def-fix-charters/tauxkit-realify/gate-LocalAuto19.md \
  DF_ANCHORS="sphere.hl:827;nonlin_def.hl:181" \
  DF_NAMES="taumX_p19,tauResidualX_p19" DF_SORRY_NET=0 \
  LANE_FILES="Kepler/Text/LocalAuto19.lean,Kepler/Text/LocalAuto38.lean" \
  bash scripts/auto_gate.sh Kepler/Text/LocalAuto19.lean taumX_p19

# LocalAuto38
GATE_MODE=DEF-FIX DF_PATCH=docs/def-fix-charters/tauxkit-realify/gate-LocalAuto38.md \
  DF_ANCHORS="nonlin_def.hl:181;nonlin_def.hl:413;sphere.hl:825" \
  DF_NAMES="taudP38,taudXP38,taumXP38,tauResidualXP38,flatTermXP38" DF_SORRY_NET=0 \
  LANE_FILES="Kepler/Text/LocalAuto19.lean,Kepler/Text/LocalAuto38.lean" \
  bash scripts/auto_gate.sh Kepler/Text/LocalAuto38.lean taumXP38
```
（`LANE_FILES` 按当轮实际脏文件补齐；闸 roots 全量构建步按 AGENTS §4 禁用，认
模块 build + 岛协议 + 编排者亲跑 `#print axioms` 三件套。）
