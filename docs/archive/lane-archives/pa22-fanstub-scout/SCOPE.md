# SCOPE — `pa22-fanstub-scout`（只读侦察车道）

## 任务

把 `lean/Kepler/Text/PackingAuto22.lean` 的 14 条 `sorry` 逐个判死
（PROVABLE / BLOCKED-FAKESTUB / NEEDS-MATH / FALSE-AS-STATED），
并给 `fcdjdot` 柱③（`DLWCHEM`/`XULJEPR`）的最短可通路径。

## 边界（严格遵守）

- 主仓 tracked 文件**零改动**：`git status --short` 在本车道结束时为空。
- 探针只写 `/tmp/pa22fan/`；交付在
  `~/c17_backup/lane_snapshots/pa22-fanstub-scout/`。
- 只跑 `nice -n 19 lake env lean <单文件>`；未跑 `lake build` / `auto_gate.sh` / 地图仪器。
- 未 commit。

## 做了什么

1. 逐条读 14 条 sorry 的陈述 + 其依赖的定义层（`hypermap1OfFanxP22` 等 7 个 `_p22` 桩）。
2. 对 14 条 + 30 余条上游件实测 `#print axioms`（`logs/probe_axioms.log`）。
3. 写机器探针证伪 #4/#5/#6/#7/#8（`logs/probe_false.lean`、`logs/probe_easy.lean`，
   RC=0，全部标准三），探针里含一个自造的具体有界多面体 `bx`。
4. 写探针证明 #2（3 行，RC=0）。
5. 清点 fan/conforming 上游移植状态（`logs/probe_fankit.log`、`probe_fan2.log`、`probe_conf.log`），
   全部标准三。
6. 用源级调用行 + 逐 callee `#print axioms` 定位柱子③ 的 sorryAx 根。

## 关键限制（诚实记账）

- olean 不保留 theorem 的 proof term（`ConstantInfo.value? = none`），
  所以无法对证明项做传递闭包；依赖根集是"逐 callee `#print axioms` + 源级调用行"合成。
  诊断见 `logs/probe_dbg*.lean`。
- #3 的 `dihV` 数值反例是手算（结构性事实 `volSolidTriangleP22 ≡ 0` 是定义即得）。
- #11 的 `arcLengthICD` ↔ `acs` 桥在树内不存在（`LocalAuto22.arclength_xrr_p22` 同为 sorry），
  故 #11 判 NEEDS-MATH 而非 PROVABLE。
- #1 的 111 行 HOL 移植未做，判 NEEDS-MATH。

## 判决分布

| 判决 | 条数 | 编号 |
|---|---:|---|
| PROVABLE | 1 | #2 |
| BLOCKED-FAKESTUB | 2 | #9, #14 |
| NEEDS-MATH | 5 | #1, #10, #11, #12, #13 |
| FALSE-AS-STATED | 6 | #3, #4, #5, #6, #7, #8 |

（#3 属 DEF 桩致假，不是 AGENTS §2 明列的两条假桩；同样需要 DEF-FIX。）

## 一句话（G）

**GO（定向）**：先开 DEF-FIX 章程把 `verticesP22/edgesP22/hypermap1OfFanxP22/eFanP22/
dartsetLeadsIntoFanP22/topologicalComponentYfanP22` 接到已在树内的真 Fan API
（`FAN`/`hypermapOfFan`/`dartsetLeadsIntoFan`/`POLYHEDRON_FAN`，全部标准三），
补 12 行 `WBLARHH_BIJ`，即可把 #4/#5/#7/#8 从 FALSE 转真（~130 行）；
柱③ 的标准三则必须另做 #10（~400）+ #9（~60）+ #14（~50）+ #13（~30），
**只做 #11/#12/#13 是死路**（对柱③ 零影响）。
