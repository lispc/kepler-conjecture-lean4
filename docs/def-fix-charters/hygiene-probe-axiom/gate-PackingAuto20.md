# DEF-FIX 闸门章程 · `lean/Kepler/Text/PackingAuto20.lean`
## （卫生波 1：全树唯一一条 `axiom` → 一行转发定理）

编排者直接施工，2026-11-06。基线 HEAD `33821f6f`。
用户 2026-11-06 裁决「三项小裁决，都按你的建议来」⇒ 裁决 1。

## 1. 对象与依据

- 改前 `:1412`：`axiom SOL_SOLID_TRIANGLE_probe …`。实测
  `grep -rn '^axiom [A-Za-z_]' lean/Kepler/` **唯一命中**就是它
  ⇒ 全树唯一一条真 `axiom`（AGENTS §2 明令禁止）。
- 真证明**已在同文件** `:272` `theorem SOL_SOLID_TRIANGLE`，
  10 行签名 + 结论与 probe 版**逐字相同**（逐字节比对过）。
- 零消费者：`grep -rn SOL_SOLID_TRIANGLE_probe lean/Kepler/` 只有声明行自己。
- HOL 锚：`packing/TSKAJXY1.hl:111`（`let SOL_SOLID_TRIANGLE = prove_by_refinement`）。
- 改后：`grep -rn '^axiom [A-Za-z_]' lean/Kepler/` 为空（其余 `^axiom` 命中
  全是 docstring 散文，如 `axiom face on the axprobe sample)`）。
- 选择「改转发」而非「删除」：名字保留，任何隐藏消费者都不会断。

## 2. 应用围栏

### 2.1 改动围栏

```diff
 
 
 
-/-- PROBE-ONLY stub of the hub's SOL_SOLID_TRIANGLE (the real proved
-theorem lives in PackingAuto20.lean:265; this probe validates only the
-SOL_SOL_Y_EXPLICIT assembly). -/
-axiom SOL_SOLID_TRIANGLE_probe {a b c : ℝ} (v0 v1 v2 v3 : V3)
+/-- PROBE-ONLY alias of the hub's `SOL_SOLID_TRIANGLE`（真证明在同文件 `:272`）。
+2026-11-06 卫生波：本条原为 `axiom`（**全树唯一一条**），改为一行转发 ——
+公理面清零，名字保留供探针复用。HOL 锚 `TSKAJXY1.hl:111`。 -/
+theorem SOL_SOLID_TRIANGLE_probe {a b c : ℝ} (v0 v1 v2 v3 : V3)
     (hnc : ¬ Coplanar ({v0, v1, v2, v3} : Set V3))
     (ha : a = dihV v0 v1 v2 v3) (hb : b = dihV v0 v2 v3 v1)
     (hc : c = dihV v0 v3 v1 v2) :
-    sol v0 (convexHull ℝ ({v0, v1, v2, v3} : Set V3)) = a + b + c - Real.pi
+    sol v0 (convexHull ℝ ({v0, v1, v2, v3} : Set V3)) = a + b + c - Real.pi :=
+  SOL_SOLID_TRIANGLE v0 v1 v2 v3 hnc ha hb hc
 
 /-- HOL `SOL_SOL_Y_EXPLICIT` (TSKAJXY1.hl:2995): the four vertex solid
 angles of a 4-cell are the `sol_y` values of the edge six-tuple.
```

### 2.2 验收

- `lake env lean -o <olean> Kepler/Text/PackingAuto20.lean` ⇒ **RC=0 / 0 error /
  0 `declaration uses sorry`**（编排者实测 67.8 s）。
- `#print axioms Kepler.Text.SOL_SOLID_TRIANGLE_probe` = `[propext, Classical.choice, Quot.sound]`。
- 零删除面：除旧 docstring 与 `axiom` 关键字外无内容删除；陈述逐字不动。
