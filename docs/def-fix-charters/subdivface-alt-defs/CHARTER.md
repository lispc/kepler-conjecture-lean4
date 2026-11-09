# DEF-FIX 章程 · subdiv 定义层补两件（`subdivFace0Alt` / `subdivFace0Alt2`）

立案：2026-11-09。立案人：编排者。触发：`j3-t6d` 的 T5B 普查——`reduction3.hl:1454/:1560/:1572` 三件直接引用 `subdiv_face0_alt` / `subdiv_face0_alt2`，而树内零命中；车道按"不许自造定义"停手上报。

---

## 1. 对象与 HOL 锚

| Lean 目标 | HOL | 位置 |
|---|---|---|
| `subdivFace0Alt` | `subdiv_face0_alt` | `tame_defs2.hl:368-381`（`list_RECURSION`） |
| `subdivFace0Alt2` | `subdiv_face0_alt2` | `tame_defs2.hl:389-397`（`list_RECURSION`） |

HOL 逐字（两件都是递归定义，返回 `(face × graph)`）：

```
subdivFace0_alt g f u n [] = (f,g)
subdivFace0_alt g f u n (vo :: vos) =
  if vo = NONE then subdivFace0_alt g f u (SUC n) vos
  else let v = the vo in
    if nextVertex f u = v /\ n = 0 then subdivFace0_alt g f v 0 vos
    else let ws = upt (countVertices g) (countVertices g + n) in
         let (f1,f2,g') = splitFace g u v f ws in
         subdivFace0_alt g' f2 v 0 vos

subdivFace0_alt2 g f n0 [] = (f,g)
subdivFace0_alt2 g f n0 (uvn :: uvnos) =
  let (u,v,n) = uvn in
  let ws = upt n0 (n0 + n) in
  let (f1,f2,g') = splitFace g u v f ws in
  subdivFace0_alt2 g' f2 (n + n0) uvnos
```

## 2. 缺陷（机器核实）

- 树内 `subdivFace0Alt` / `subdivFace0Alt2` **零命中**（`grep --include='*.lean'`）。
- 消费件（`table147.md` T5 段）：`subdivFace0_alt2_foldl_steps`(:1560)、`_alt`(:1572)、`subdivFace0_beta_subdivFace0_alt`(:1454)，以及 `b_nfgtransk`(:4442) 的缺口清单。
- 同名族在树内已有 **`subdivFace0Beta`**（`Reduction3DefsLayer.lean:81`，D2 落库）——它是 `subdiv_face0_beta` 的余态形（返回 `((uo,n),f,g)`），与本两件的 `(f,g)` 返回值不同，**不可互相定义**（D2 文件头已预警）。

## 3. 裁定

**批准新增两件纯定义**，放在新文件 `lean/Kepler/Text/Reduction3DefsSubdivAlt.lean`（namespace `Kepler.Text.Reduction3`）：

- 逐字对齐 §1 两段 HOL 体；类型按树内既有折算：`graph ↦ Graph`、`face ↦ Face`、`countVertices ↦ Graph.countVertices`、`nextVertex ↦ Face.nextVertex`、`upt a b ↦ List.range' a (b - a)`（截断减恒等）、`the vo ↦ vo.getD 0`（与 D2 先例同口径，`vo = NONE` 分支已排除）；
- 允许附带"定义即引理"式平凡事实（nil 基例 `rfl`、`vo = NONE` 支展开），但**不得**借机证 T5B 的定理；
- **零既有陈述改动、零 axiom/sorry/admit/native_decide**；`DF_SORRY_NET = 0`。

## 4. 禁止与闸门

- 禁止：改 `subdivFace0Beta`/`subdivSingleStep`/`subdivTripleStep`；改任何既有定理陈述；import `Kepler.Assembly` 伞模块或 TameSpine（保持 Reduction3 岛纪律）。
- 闸门：岛协议编译 RC=0；`#check` 打印两件签名并与 §1 逐行比对（DIFFERS 记档：`Option`/`getD` 折算、`range'` 截断、HOL `/\` ↔ Lean `∧`）；附带的平凡引理 `#print axioms` ⊆ 标准三；comment-depth = 0；pit10 零禁词。
- 回滚：本定义批与后续 T5B 定理批**各自独立 commit**。

## 5. 顺序

本定义批（patch A）→ T5B 6 件自由件 + 3 件由本批解锁的定理（patch B）→ `b_nfgtransk` 待 `subdiv_single_step_betwn`（Aq12/J2）落库后收口。
