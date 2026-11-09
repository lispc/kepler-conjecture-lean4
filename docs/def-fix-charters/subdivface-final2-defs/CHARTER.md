# 章程 · `subdivFaceFinal2`（纯定义一件）

立案：2026-11-10。立案人：编排者。触发：j3-t6d 的 T7E 交付回报——`subdivFaceFinal2`
在 `lean/Kepler` 零命中（T7E 件2 BLOCKED）。
上游章程：`docs/def-fix-charters/subdivface-alt-defs/CHARTER.md`（同族两 def，`3e02ca96` 已落）。

---

## 1. 对象与 HOL 锚

HOL `tame_defs2.hl:397-400`：

```
let subdivFaceFinal2 = new_definition'
  `subdivFaceFinal2 g f uvns =
  (let (f,g) = subdivFace0_alt2 g f (countVertices g) uvns in
     makeFaceFinal f g)`;;
```

Lean 目标（`Kepler.Text.Reduction3` 命名空间，与 `subdivFace0Alt2` 同处）：

```
def subdivFaceFinal2 (g : Graph) (f : Face) (uvns : List (Nat × Nat × Nat)) : Graph :=
  let p := subdivFace0Alt2 g f g.countVertices uvns
  makeFaceFinal p.1 p.2
```

## 2. 机器核实（编排者 2026-11-10 独立验证）

- `subdivFace0Alt2 : Graph → Face → Nat → List (Nat × Nat × Nat) → Face × Graph`
  已在库（`Reduction3DefsSubdivAlt.lean:59`，`3e02ca96`）。
- `makeFaceFinal (f : Face) (g : Graph) : Graph` 已在库（`Kepler/Graphs/FaceDivision.lean:28`）。
- HOL `let (f,g) = …` 的绑定序 = `(Face, Graph)`，与 Lean 侧 `p.1 : Face` / `p.2 : Graph` 逐位对应。
- 消费者：`reduction3.hl:456`（`subdiv_face0_alt2_finals`，**不吃**本 def）与
  `reduction3.hl:488`（`subdiv_faceFinal2_finals`，**吃**本 def）。全树零其它消费者。

## 3. 裁定

**批准新增一件纯定义，零定理改动、零既有文件触碰。**
允许附带 nil 方程（`subdivFaceFinal2Nil`，`rfl` 级）与定义展开引理；
**不证** `subdiv_faceFinal2_finals` 本体（那归 J3 定理层，另批）。

## 4. 禁止与闸门

- 禁止：新增 `axiom`/`sorry`/`admit`/`native_decide`；改任何既有陈述；import `Kepler.Assembly` 伞模块。
- 闸门：岛协议编译 RC=0；`#print axioms` 对附带引理 ⊆ 标准三；pit10 零禁词；comment-depth 0。

## 5. 归属

DEF-FIX 章程已批 ⇒ j3-t6d 可在 `Reduction3DefsSubdivAlt.lean` 追加（**同文件追加，
不新建文件**，保持同族两 def 在同一模块），独立 commit。
