# Evidence — la11-mksimplex-cont-w1

基线 HEAD `b89ee8b45bc9ecbe197dd9e0551423326a9e8873`。
编译仪器（全部单进程串行、`nice -n 19`、无 `lake`）：

```
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 script -q <log> lean <file>
```

## 1. `#print axioms` 原文（WorkCheck.lean 文件末，`end Kepler.Text` 之后）

探针尾（已从 `Work.lean` 剥离，只存在于 `WorkCheck.lean`）：

```lean
#print axioms Kepler.Text.CONTINUOUS_MK_SIMPLEX_WITHINREAL_p11
#print axioms Kepler.Text.PQCSXWG2_WITHINREAL_p11
#print axioms Kepler.Text.PQCSXWG2_ATREAL_p11
#print axioms Kepler.Text.PQCSXWG2_p11
#print axioms Kepler.Text.PQCSXWG2_concl_p11
#print axioms Kepler.Text.MK_SIMPLEX_TRANSLATION_p11
#print axioms Kepler.Text.CONTINUOUS_WITHIN_SQRT_COMPOSE_p11
```

输出（`logs/work2.log`，逐字）：

```
'Kepler.Text.CONTINUOUS_MK_SIMPLEX_WITHINREAL_p11' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.PQCSXWG2_WITHINREAL_p11' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.PQCSXWG2_ATREAL_p11' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.PQCSXWG2_p11' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.PQCSXWG2_concl_p11' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.MK_SIMPLEX_TRANSLATION_p11' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.CONTINUOUS_WITHIN_SQRT_COMPOSE_p11' depends on axioms: [propext, Classical.choice, Quot.sound]
```

零 `sorryAx`。注：本文件头部有遗留 `open … Classical`（:152），故
`Classical.choice` 未被打印成 `choice`（本 Lean 4.32 在 `open Classical` 下会打印成 `choice`）；
本 lane **未新增**任何 `open Classical` / `open Classical in`。

## 2. 整文件 RC / 错误数 / sorry 声明计数

### 基线（`Base.lean` = `git show HEAD:lean/Kepler/Text/LocalAuto11.lean`）

```
$ LEAN_PATH=… lean Base.lean ; echo RC=$?
RC=0
$ tr -d '\r' < logs/base.log | grep -c ': error:'
0
$ tr -d '\r' < logs/base.log | grep -c 'declaration uses `sorry`'
24
$ tr -d '\r' < logs/base.log | grep -c 'warning:'
29
```

### 交付（`Work.lean` = Base + kit）

```
$ LEAN_PATH=… lean Work.lean ; echo RC=$?
RC=0
$ tr -d '\r' < logs/work_final.log | grep -c ': error:'
0
$ tr -d '\r' < logs/work_final.log | grep -c 'declaration uses `sorry`'
22
$ tr -d '\r' < logs/work_final.log | grep -c 'warning:'
27
```

**sorry 声明计数：24 → 22**（总 `declaration uses sorry` warning 口径）。

口径说明：车道 brief 的「own-sorry 22」= 上述 24 减去两条 opaque `def … := sorry`
（`dartStd4_p11` :192、`tauq_p11` :197，二者是 HOL 未在语料中的 `dart_std4`/`tauq` 的
opaque 占位，非定理债）。故：

| 口径 | HEAD | 交付 |
|---|---|---|
| `declaration uses sorry` warning 总数 | 24 | **22** |
| own-sorry（剔除 2 条 opaque def 占位） | 22 | **20** ✅ |

### warning 谱面（逐条）

基线 29 条 = 24 条 `declaration uses sorry` + 5 条其它
（`hx1` unused :724、`hy1` unused :808、`simp argument deltaX` :1541、:1546、`hk` unused :1768）。

交付 27 条 = **22 条 `declaration uses sorry`**（恰好少了 :1629 / :1646 两条）+ **同样 5 条其它**
（`hx1` :724、`hy1` :808、`deltaX` :1541、:1546、`hk` :1934——行号因插入助件整体后移 166 行）。

**唯一差异 = 两条目标件的 `sorry` warning 消失**；无新增 warning。

> 注意点：`sorry` 体不会触发 `linter.unusedVariables`。`CONTINUOUS_MK_SIMPLEX_WITHINREAL_p11`
> 的 `hd`（`0 < deltaX …`，HOL 证明里也未用）在换成真证后会新增一条 unused 警告；
> 为保持谱面不变，证明开头写了
> `have hdne : deltaX (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) ≠ 0 := ne_of_gt hd`
> 显式消费该 binder（不影响陈述，陈述逐字冻结）。

## 3. kit 与 `git apply` 校验

```
$ cd /Users/zhangzhuo/repos/kepler-conjecture-lean4
$ git apply --stat /Users/zhangzhuo/c17_backup/lane_snapshots/la11-mksimplex-cont-w1/kit-la11-mksimplex-cont-w1.diff
 lean/Kepler/Text/LocalAuto11.lean |  170 +++++++++++++++++++++++++++++++++++++
 1 file changed, 168 insertions(+), 2 deletions(-)

$ git apply --check /Users/zhangzhuo/c17_backup/lane_snapshots/la11-mksimplex-cont-w1/kit-la11-mksimplex-cont-w1.diff
（无输出）→ APPLY-CHECK PASS

$ git status --porcelain
（无输出）→ 主仓源码 tracked 零改动
```

kit 头形（逐字）：

```
diff --git a/lean/Kepler/Text/LocalAuto11.lean b/lean/Kepler/Text/LocalAuto11.lean
--- a/lean/Kepler/Text/LocalAuto11.lean
+++ b/lean/Kepler/Text/LocalAuto11.lean
```

3 个 hunk：`@@ -1623,6 +1623,122 @@`（助件块）、`@@ -1638,7 +1754,56 @@`（:1629 证明体）、
`@@ -1658,7 +1823,8 @@`（:1646 证明体）。删除行仅 2 条 `-  sorry`。

## 4. 探针（probe）留痕

`pA.lean`（API 侦察）/ `pB.lean`（首版，命名冲突 + 2 处 API 修正）/ `pC.lean`（改名重跑）/
`pD.lean`（最终证法，RC=0，`#print axioms` 两件均 `[propext, Classical.choice, Quot.sound]`）。
日志：`logs/pA.log`、`logs/pB.log`、`logs/pC.log`、`logs/pD.log`、`logs/pD2.log`、`logs/pD3.log`。
