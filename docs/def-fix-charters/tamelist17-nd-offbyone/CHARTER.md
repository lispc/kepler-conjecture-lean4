# DEF-FIX 章程 · `TameList17:93` splitNormalListSpine.nd off-by-one（续411 挂账项结案）

立案：2026-11-09。立案人：编排者。触发：`j2w2` 的 E4 普查确证该 off-by-one 是 `aq3Concl` split.1 支的**内容级前置**（LAST 取值直接依赖 nd），且续411 早已判"批 C 消费 split.1 前必须先修"。

---

## 1. 缺陷（三源比对，续411 已实锤）

- Lean `lean/Kepler/Text/TameSpine/TameList17.lean:93`：
  `nd x = (List.range' 1 (sz x.1)).map (fun i => (nList L)^[i] x)` —— `range' 1 k = [1..k]`（闭，k 项）。
- HOL `tame_defs2.hl:172`：`map (λi. (n_list L POWER i) x) (upt 1 (sz (FST x)))`，`upt i j = iota i (j − i)` ⇒ `upt 1 sz = [1 .. sz−1]`（**少一项**）。
- 故 Lean 多跑一步 `i = sz` 的 node 迭代：`nd x` 末元 = `nList^{sz} x = x`（node 圈恒等），HOL 为 `nList^{sz−1} x`。
- **树内一错一对**：`Reduction5Base:149` 的链侧 `splitNormalList` 已正确带 `-1`。

影响面：`splitNormalListSpine` 的 `.1`（`new1`）——其 `LAST new1` 决定 split.1 支的 f_last；对 split.2/`new2` 无影响。

## 2. 修复（一行）

```diff
-    fun x => (List.range' 1 (sz x.1)).map fun i => (nList L)^[i] x
+    fun x => (List.range' 1 (sz x.1 - 1)).map fun i => (nList L)^[i] x
```

## 3. 消费方审计（j2w2 实测，编排者采信，2026-11-09 22:2x）

在 `/tmp/jcajydu-j2w2/audit17/` 补丁副本 + symlink farm 上编译：

| 文件 | 结果 |
|---|---|
| `TameList17`（补丁版本体） | RC=0 |
| `TameList72` / `JcajyduRed2Trans` / `JcajyduAqTowerBase` / `JcajyduAqSnd` | 全 RC=0 |
| 追加全树 grep 命中件：`JcajyduAqTowerE2` / `JcajyduAqZIndexf` / `JcajyduAqZUnlock` / `TameList18` / `ChainMarkedQ` / `Reduction3Defs` | 全 RC=0 |

**逐处坏因：零处**——10 件对 `splitNormalListSpine` 只做外层结构操作（append 形状、cons 头、mem 分解），从不吃 `nd`/`range'` 的具体值；无任何定理需改陈述或降级为条件形。
**两侧同式核实** ✓：补丁后与 `Reduction5Base:149` 链侧定义同式（仅语法括号差异，`audit17/diffs/nd_side_by_side.txt`）。

## 4. 禁止与闸门

- 禁止：任何其它改动（本项**只改这一行**）；新增 axiom/sorry/native_decide；改任何定理陈述；顺带修别的 off-by-one。
- 闸门：岛协议编译 `TameList17` RC=0；消费者抽验 ≥3 件 RC=0（`TameList72`/`JcajyduAqSnd`/`JcajyduAqTowerBase`）；`print axioms` 抽验既有件不新增 `sorryAx`；comment-depth 0。
- 回滚：单 commit，revert 即恢复。

## 5. 结案与后续

- 本项落地即注销续411 挂账；`j2w2` 的 E4（`aq3Concl` split.1 支 + `JcajyduAqSplit1.lean`）随即开工。
- 语义影响：修复后 `splitNormalListSpine` 与 HOL 逐项对齐；`Reduction5Base` 链侧无需改。
