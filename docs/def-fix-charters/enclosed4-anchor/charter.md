# DEF-FIX 章程（草案）：LA38 `_p38` 锚桩 enclosed/cayleyR 填体（2026-11-14，enclosed4-w1 车道拟；**待用户批准**）

> 依据：AGENTS §2（定义改动走 DEF-FIX 通道；假桩不得绕证）+ enclosed4-w1 侦察
> （`~/c17_backup/lane_snapshots/enclosed4-w1/DELIVERY.md` §1/§3/§4）+ shadow 实证
> （同目录 `logs/shadow_final.lean`、`logs/probe_shadow.log`，RC=0、三探针恰标准三）。
> 草案模式比照 `docs/def-fix-charters/p21-anchor/`；闸模式建议
> `GATE_MODE=DEF-FIX`，`DF_PATCH=` 本目录 `gate-LocalAuto38.md`。

## 0. 一句话

把 LA38 的两个 EXTERNAL-ANCHOR 假桩 `cayleyRP38`（LA38:193-195）与
`enclosedP38`（LA38:165-167）填成 HOL 真身（`leg/cayleyR_def.hl:32`、
`leg/enclosed_def.hl:22-24`；canonical 真身已在树内
`IneqClosureDefs.cayleyR`/`enclosed`），解锁 enclosed 集群 4 件
（`enclosed4_lemma`/`vv_enclosed4`/`enclosed_sym`/`enclosed_sym2`，其中 sym 两件
证明已随本草案 shadow 验证，逐字稿见 DELIVERY §4.3）。

## 1. 对象与 HOL 锚

| 声明 | 位置 | 现体 | 新体（HOL 锚） |
|---|---|---|---|
| `cayleyRP38` | LA38:193-195 | `:= sorry` | `leg/cayleyR_def.hl:32` 5 顶点 Cayley-Menger 多项式（逐字源：`IneqClosureDefs.lean:780` 的 `cayleyR` 体） |
| `enclosedP38` | LA38:165-167 | `:= sorry` | `leg/enclosed_def.hl:22-24`：`sqrt (quadratic_root_plus (abc_of_quadratic (muR …)))`，`_p38` 词汇展开形（孪生：`IneqClosureDefs.enclosed` :878、LA38 `quadCrossDiag2XP38` :238） |

- `enclosedP38` 新体引用 `abcOfQuadraticP38`（LA38:226）与 `muRP38`（LA38:231），
  Lean 无前向引用 ⇒ **声明块整体下移到 `muRP38` 之后、`quadCrossDiag2XP38` 之前**
  （名字/签名/文档串一字不动，仅位置与体）。
- 文档串「NEEDS: …unported enclosed lane」改为「DEF-FIX charter
  `docs/def-fix-charters/enclosed4-anchor/`」式注记。

## 2. 改动围栏（与将被批准的 `git diff` 逐字一致）

`lean/Kepler/Text/LocalAuto38.lean`（体移植的多项式行略，逐字抄
IneqClosureDefs:780-836 的 `cayleyR` 体）：

```diff
-/-- NEEDS: sphere.hl `enclosed` (9-arg enclosed-arc length; body lives in
-the unported enclosed lane). -/
-noncomputable def enclosedP38 (y1 y2 y3 y4 y5 y6 y7 y8 y9 : ℝ) : ℝ := sorry
+/-- HOL `enclosed` (leg/enclosed_def.hl:22-24): sqrt of the +root of the
+quadratic interpolant of `muR`.  DEF-FIX charter
+`docs/def-fix-charters/enclosed4-anchor/`. -/
+noncomputable def enclosedP38 (y1 y2 y3 y4 y5 y6 y7 y8 y9 : ℝ) : ℝ :=
+  Real.sqrt (quadraticRootPlus
+    (abcOfQuadraticP38 (muRP38 y1 y2 y3 y4 y5 y6 y7 y8 y9)).1
+    (abcOfQuadraticP38 (muRP38 y1 y2 y3 y4 y5 y6 y7 y8 y9)).2.1
+    (abcOfQuadraticP38 (muRP38 y1 y2 y3 y4 y5 y6 y7 y8 y9)).2.2)
```
（该块物理下移到 :233 区；`cayleyRP38` 同式：docstring 改注记，体 :=
`cayleyR` 多项式逐字移植。）

**替代变体**（审批时可二选一，shadow 已验证此变体等价）：`cayleyRP38` 体 :=
`cayleyR x12 … x35`（别名）、`enclosedP38` 体 := 同形用 canonical
`abcOfQuadratic (muR …)` + LA38 `+import Kepler.Text.IneqClosureDefs`（闭包
SphereKit+PackingAuto2，零环）。零新 import，零新 sorry；`muR_ALT`/`muR_alt`/
`quad_cross_diag2_x_cayleyR` 保持 `rfl`（shadow 实测）。

## 3. 白名单与范围外

- `DF_NAMES="cayleyRP38 enclosedP38"`；`DF_SORRY_NET=-4`（2 桩体 + 本波同 patch
  落库的 `enclosed_sym`/`enclosed_sym2` 两条真证明；每删一笔有真证明在场）。
- 范围外（不属本波）：`abc_of_quadratic_cayleyR`/`cayleyR_disc`（LA38:3546/:3555，
  陈述过 `cayleytrP38` 桩，树内无 `cayleytr` 真身，rg 零命中——须单独立项）；
  `enclosed4_lemma`/`vv_enclosed4`（各自缺件见 DELIVERY §3.2/§3.3）；
  `taumXP38`/`tauqP38` 等其余 `_p38` 锚桩原样不动。
- 本波 patch 内不含任何 LP / nli / native_decide 内容；四件目标件的陈述逐字节不动。

## 4. 验证要点（shadow 实证，非转述）

- 填体后 LA38 全文件直编 RC=0、error 0（`logs/shadow2/3/4.log`；机械坑：
  sym 证明需 `set_option maxRecDepth 65536 in`，默认 512 在深嵌套多项式上爆
  recursion depth）。
- 两 sym 件落位后 `#print axioms` 恰 `[propext, choice, Quot.sound]`
  （`logs/probe_shadow.log` 原文三行）。
- 若采用替代变体：LA38 `+import Kepler.Text.IneqClosureDefs` 后全名 `cayleyR`/`muR`/
  `abcOfQuadratic` 在 `Kepler.Text` 命名空间直解析，LA38 无同名冲突（shadow
  实测）。
