# e2e 定理树可视化

> 2026-11-03 建立。页面是**本地 web app**（HTML/JS + SQLite），不在仓内运行；
> 本文件记录数据口径、设计选择与重建方式。

## 1. 位置与启动

当前会话的页面目录（durable）：

```
~/.zcode/v2/visualizations/571e2f5484263141668294a63494107b5f37ee99532a11d2a7d3d625ceaa225b/e2e-tree/
  index.html  app.js  style.css  server.py  build_db.py  tree.db  export_math.lean
```

```bash
cd <上面这个目录>
python3 server.py . 8790
# 浏览器打开 http://127.0.0.1:8790/
```

页面已用浏览器实测：树展开、DAG/BFS 切换、模块下钻、129 条债务路径、搜索与聚焦均正常。

### 1.1 当前 NLI 源树（2026-11-22，`SOURCE_STATIC`，无 olean）

**当前页面：`http://127.0.0.1:8791/`（已实测展开全部 49 债与当前源码）。** 页面目录：

```
~/.zcode/v2/visualizations/571e2f5484263141668294a63494107b5f37ee99532a11d2a7d3d625ceaa225b/nli-current-tree/
  index.html  app.js  style.css  server.py  build_db.py  build_current_nli.py
  current_nli.tsv  manifest.json  tree.db
```

重建与启动：

```bash
cd <上面这个目录>
PYTHONDONTWRITEBYTECODE=1 python3 -I build_current_nli.py
python3 server.py . 8791
```

- 快照：HEAD `c8b26e16`；**55 节点 = 1 源根 + 5 分族 + 49 当前债**，54 条分族边，
  `missing_parent=0`、`missing_edge=0`。S2a/fat1 在飞与 wt1 Gate 1 状态标在节点类型里。
- 名单方法：最后正式根面 AQ 的 51 债，扣除已经小模块亲验闭合的 sqrt8/wt2A；
  随后逐项回查当前 `lean/Kepler/Assembly.lean`，**49/49 声明仍含 sorry**。
  `manifest.json` 保存 HEAD、49 行号、输入/生成器 SHA256 与 DB 计数。
- 全程不需要 olean，不注释 Graphs、不改 Assembly/585，也不复用旧 DB 冒充现状。
  浏览器实测：根与五个分族展开、49 债全显、`/api/debt` count=49、wt1 的
  `/api/source` 返回当前 `Assembly.lean:431` 的 `:= sorry`。
- **口径边界**：这是当前 NLI 的**源码静态债务/分族树**，边不是 proof-term DAG，
  不能替代 `e2e_reach_map` 或 `#print axioms`。重建当前完整 proof-term 树仍须 import
  `Kepler.Assembly` 并遍历环境，因此仍需相应 olean。
- 旧 `e2e-tree/tree.db`（18,884 节点 / 208 模块 / 134 债源）只是历史快照，旧 8790
  服务已停止，避免与当前 8791 混淆；不得仅改 meta 冒充新树。

### 1.2 当前 Text 模块/声明源图（2026-11-22，`SOURCE_STATIC`，无 olean）

**Text 页面：`http://127.0.0.1:8792/`（已实测分族、import DAG 与模块源码）。** 页面目录：

```
~/.zcode/v2/visualizations/571e2f5484263141668294a63494107b5f37ee99532a11d2a7d3d625ceaa225b/text-current-tree/
  index.html  app.js  style.css  server.py  build_db.py  build_current_text.py
  current_text.tsv  manifest.json  tree.db
```

重建与启动：

```bash
cd <上面这个目录>
PYTHONDONTWRITEBYTECODE=1 python3 -I build_current_text.py
python3 server.py . 8792
```

- 快照：HEAD `072a0d0c`；**1,097 个 tracked Text 模块 / 83,265 条声明**，
  页面共 1,110 节点（加源根与 12 分族）与 **4,730** 条分族/Text 内部 import 边，
  `missing_parent=0`、`missing_edge=0`。
- 全目录源码扫描得 **43,367 处直接 `sorry`，分布于 206 个模块**：
  **42,889** 是 `Text/LP` 的 bound 骨架（hold），另有 **478** 条其它锥外 Text 占位。
  账本 **Text 0 是 e2e 锥内口径**，不能误写为整个 `Text/` 目录零 sorry；这些节点也不
  自动属于当前根面 49 债。页面顶部与债务提示均明确分开。
- `manifest.json` 保存 HEAD、模块/声明/sorry 计数、分族计数、输入清单与生成器 SHA256。
  `/api/source` 对模块节点返回当前文件开头，例如 `Text/LP/LPLeafRoot75.lean` 的
  真实骨架，不伪造 proof-term 或闭合状态。
- 全程不需要 olean，不改 Assembly/Graphs/585。此页用于**模块/声明导航和 import DAG**，
  不替代 proof-term 可达图、`e2e_reach_map` 或 `#print axioms`。

## 2. 数据快照

> **快照（2026-11-03 深夜已重建到基线 E）**：页面 `tree.db` = 主仓当前 HEAD
> （S1 接线 `ebe0d0b7` + QZYZMJC `2dea72f0` 后）：**16,885** 数学层节点 /
> **203** 模块 / **135** 债源 / **87,543** DAG 边 / 全树 K_REACH 2,079,707。
> 下表 15,480/129 为 c1 时代旧读数，仅供对照重建口径。源码查看（§3）显示
> 的代码与节点表现在同代。

- 主仓 `a31177c9`（PackingConcl c1 Stage 1 落库后）。
- 全树 `K_REACH = 2,078,302`（`5384f11d` 时为 2,078,095；c1 后 +207）。
- `SORRIED = 129`（`5384f11d` 为 123；c1 把 `UPFZBZM_concl` 假债换成 7 真源：
  PA15×5 / PA16 `QZYZMJC` / PA2 `GRUTOTI1_concl`）。
- `K_AXIOM = 624`；`K_MODULES = 4,171`；`COVERAGE ≈ 99.25%`。
- ORPHANS：e2e 单根 ≈15,752；154/156 根 union 14,824（见 `docs/global-reachability-map.md`）。

### 页面里的“数学层”

全树 2.08M 节点的绝大多数是机械证书层（`Interval.Cases` / `Graphs.CertShards` /
`Shard` / `CertTri/Quad/Pent/Hex`）。页面按以下口径折叠：

| 指标 | 数值 |
|---|---:|
| 数学层节点 | 15,480 |
| 模块 / 组 | 195 / 7 |
| 直接 sorryAx 源 | 129 |
| 最大深度 | 31 |
| DAG 边 | 79,965 |
| 折叠的机械模块叶子 | 36 |

页头同时标注“全树 K_REACH ≈ 2.08M”，避免把数学层误读为全树。

## 3. 设计选择

- **默认 DAG 直接子节点**：每个节点显示其 proof term 直接引用的全部 Kepler 子节点；
  同一节点可出现在多个父下。工具栏可切到 **BFS 生成树**（每个节点一个父，严格树）。
- **源码查看**（2026-11-03 晚新增）：详情面板「查看源码」→ 弹出只读代码窗。服务端
  `/api/source?name=&module=` 把节点名（含 `_private.<mod>.<idx>.` 乱名还原）映射到
  仓库 `lean/` 下对应模块文件，定位声明（含前置 docstring/`@[...]`），按"下一个列 0
  声明/注释/属性"取声明体（>600 行截断提示）；**直接子节点在代码中的引用全部高亮，
  点击高亮跳转到该子节点**——例如根定理的 4 个子节点（`assembly` /
  `linearProgrammingResults` / `nonlinearInequalities` / `textCapstone`）在
  `Assembly.lean:7131` 的证明里逐一看得见。生成/合成节点（机械证书层 `native_decide`
  公理等）在源里不存在，如实报错。快照 stale 时注意：代码显示的是**仓库当前 HEAD**
  的源，节点表可能是旧快照（当前 DB = `a31177c9`/129，HEAD 已到基线 C `a522078c`/123）。
- **面包屑用首次 BFS 父边**：BFS 路径只用于定位/“返回全树”，不与 DAG 子节点混为一谈。
- **懒加载 + 虚拟滚动 + 每节点 100 子节点分页**：不一次性渲染全树；展开
  `textCapstone`（60 子节点）、搜索 2M 名字、模块下钻都实测不卡。
- **模块视图**：组概览（log 尺度条形）+ Top 模块 + 模块内声明列表；模块名可筛选。
- **债务视图**：129 个直接 `sorryAx` 源按模块分组，点击聚焦到树。
- **搜索**：全局名子串，最多 100 条；点击聚焦并展示面包屑。

## 4. 重建

导出器在仓内：`lean/scripts/export_e2e_tree.lean`（数学层 + DAG 边；机械模块折叠为叶子）。

```bash
cd <repo>/lean
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) \
  lean scripts/export_e2e_tree.lean > /tmp/e2e-tree-math.tsv

cd <viz>/e2e-tree
python3 build_db.py /tmp/e2e-tree-math.tsv tree.db
python3 server.py . 8790
```

`build_db.py` 读取 TSV（`name/module/kind/directSorryAx/parent/childCount/...` 节点行
+ `E\tparent\tchild` 边行），生成 `nodes` / `edges` / `modules` / `groups` / `meta`。

## 5. 已知限制

- 机械证书层只折叠为模块叶子；若要逐一看 2M 证书，需要另开“证书层”视图/数据库。
- 树是证明项可达图，不是 import 闭包；DAG 模式会出现重复节点（多父）。
- 当前数据快照是 c1 后的 129；重新生成时须用对应 HEAD 的源/olean 重编（
  `.lake` 共享 olean 可能被 REWIRE 闸测试污染，见 `docs/e2e-reachability-map.md` 的仪器校准节）。
