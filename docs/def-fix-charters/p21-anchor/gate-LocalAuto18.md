# DEF-FIX 闸门章程 · `LocalAuto18.lean`（LA18 终端锚点重编码）

HOL 锚：`reference/flyspeck/text_formalization/local/terminal.hl:37`
（`main_nonlinear_terminal_v11`，109 条 `Main_estimate` 的合取）。

对象：`mainNonlinearTerminalV11_p18`（`LocalAuto18.lean:212`，改前 206）。
只改定义体：`∀ y : Fin 6 → ℝ, MainNonlinearTerminalV11_p18 y` →
`main_nonlinear_terminal_v11`（`LocalAuto1.lean:2139` 的 registry 合取）。
盒谓词 `MainNonlinearTerminalV11_p18`（LA18:199）原样保留，不是锚点。

### 2.1 改动围栏

```diff
-    `mainNonlinearTerminalV11_p18 := ∀ y, MainNonlinearTerminalV11 y`.
+    `mainNonlinearTerminalV11_p18 := main_nonlinear_terminal_v11` (alias of the
+    `LocalAuto1` 109-entry registry conjunction; DEF-FIX charter
+    `docs/def-fix-charters/p21-anchor/`).
-/-- HOL `main_nonlinear_terminal_v11` (terminal.hl:37) as a bare Prop;
-opaque in scripts/local (164 uses). -/
-def mainNonlinearTerminalV11_p18 : Prop := ∀ y : Fin 6 → ℝ, MainNonlinearTerminalV11_p18 y
+/-- HOL `main_nonlinear_terminal_v11` (terminal.hl:37) as a bare Prop:
+**alias of `LocalAuto1.main_nonlinear_terminal_v11`** (the closed conjunction of
+the 109 registry entries), per DEF-FIX charter
+`docs/def-fix-charters/p21-anchor/`. The box predicate
+`MainNonlinearTerminalV11_p18` above stays a plain predicate (it is no longer
+the anchor). -/
+def mainNonlinearTerminalV11_p18 : Prop := main_nonlinear_terminal_v11
```

### 2.2 白名单与范围外

- `DF_NAMES="mainNonlinearTerminalV11_p18"`；`DF_SORRY_NET=0`。
- 本文件其余行零改动；孪生 `LocalAuto21.lean` 见 `gate-LocalAuto21.md`。
