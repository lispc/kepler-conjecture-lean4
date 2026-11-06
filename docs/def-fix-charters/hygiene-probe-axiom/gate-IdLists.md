# DEF-FIX 闸门章程 · `lean/Kepler/Assembly/IdLists.lean`
## （卫生波 2：删除 `True` 镜像假闭合四件 + 一条 `example`）

编排者直接施工，2026-11-06。基线 HEAD `33821f6f`。
用户 2026-11-06 裁决「三项小裁决，都按你的建议来」⇒ 裁决 2。

## 1. 对象与依据

改前 `:664-697` 五件（全部零外部消费者）：

| 件 | 问题 |
|---|---|
| `CertifiedIneqHoldsMirror (_id) : Prop := True` | 把 `True` 硬编码进 `CertifiedIneqHolds` 的本地镜像 |
| `AllCertifiedMirror ids := ∀ id ∈ ids, CertifiedIneqHoldsMirror id` | 由上一件导出，恒真 |
| `TheNonlinearInequalitiesFilled` = 六分量 `AllCertifiedMirror` 合取 | "填入后展开形态"，实际恒真 |
| `example : AllCertifiedMirror lpIneqsIds ↔ …` | 只为上一件服务的 `Iff.rfl` |
| `theNonlinearInequalitiesFilled_placeholder : TheNonlinearInequalitiesFilled` | **`exact True.intro` "证完" 六分量接口合取** |

- 病灶与原型 `weaklySaturatedP22 := True` **完全同型**：桩 + 由桩导出的"已证"
  定理。AGENTS §2 与 `docs/handoff-2026-11-06.md` §5 红旗清单都点名这一类。
- 零消费者：全树 grep 只在文件内部自引（删除后仅剩本章程引用）。
- 保留：六个 id 清单、`*_length` 钉子（`rfl` 可判）、`certLookupDomain`、
  文件尾三条位置式成员 `example` —— 那些是**数据与生成期校验**，不是假闭合。
- HOL 锚：`general/the_main_statement.hl:55-59`（六分量合取的真形）。

## 2. 应用围栏

### 2.1 改动围栏

```diff
 set_option maxRecDepth 2048 in
 theorem kcblrqcIneqDefIds_length : kcblrqcIneqDefIds.length = 28 := rfl
 
-/-! ## 接线示范（P6-E 接口侧；**不改 Assembly.lean 本体**）
+/-! ## 接线说明（P6-E 接口侧；**不改 Assembly.lean 本体**）
 
 `TheNonlinearInequalities`（Assembly.lean:190-193）填入六清单后的展开形态。
-按 IneqPilot.lean 先例，本数据文件不 import `Kepler.Assembly`
-（避免为纯数据拉起整条装配链构建）；下面两个定义是 Assembly.lean:165-168
-`CertifiedIneqHolds` / `AllCertified` 的逐字镜像，仅用于展示展开形态。
 接线时（G4 粘合量产）把六个清单常量代入 Assembly.lean:171-183 的对应
 PLACEHOLDER 字段，并将 `CertifiedIneqHolds` 填实为按 id 查表展开
-（量产样板 = IneqPilot.lean `certifiedIneqHolds_pilot`）。 -/
+（量产样板 = IneqPilot.lean `certifiedIneqHolds_pilot`）。
 
-/-- Assembly.lean:165 占位语义的本地镜像（填实后按 id 查表展开为字面量化
-不等式命题，由 G4 内核证书闭合）。 -/
-def CertifiedIneqHoldsMirror (_id : String) : Prop := True
-
-/-- Assembly.lean:168 注册表量化的本地镜像。 -/
-def AllCertifiedMirror (ids : List String) : Prop :=
-  ∀ id ∈ ids, CertifiedIneqHoldsMirror id
-
-/-- **填入后展开形态**：`TheNonlinearInequalities` = 六分量 `AllCertified` 合取
-（Assembly.lean:190-193；`LpIneqs` = 第四分量，Assembly.lean:186）。 -/
-def TheNonlinearInequalitiesFilled : Prop :=
-  AllCertifiedMirror packNonlinearNonOx3q1hIds ∧ AllCertifiedMirror ox3q1hIds ∧
-    AllCertifiedMirror mainNonlinearTerminalV11Ids ∧ AllCertifiedMirror lpIneqsIds ∧
-    AllCertifiedMirror packIneqDefAIds ∧ AllCertifiedMirror kcblrqcIneqDefIds
-
-/-- 清单上的量化逐点展开（注册表量化的定义等价值）。 -/
-example : AllCertifiedMirror lpIneqsIds ↔
-    ∀ id ∈ lpIneqsIds, CertifiedIneqHoldsMirror id := Iff.rfl
-
-/-- 占位语义下填入形态可闭合（`True` 占位逐点平凡）；`CertifiedIneqHolds`
-填实后此定理由 G4 证书逐条替换。 -/
-theorem theNonlinearInequalitiesFilled_placeholder :
-    TheNonlinearInequalitiesFilled := by
-  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro _ _ <;> exact True.intro
+**2026-11-06 卫生波删除（不要再加回来）**：此处原有
+`CertifiedIneqHoldsMirror (_id) := True` / `AllCertifiedMirror` /
+`TheNonlinearInequalitiesFilled` 三件，以及一条
+`theNonlinearInequalitiesFilled_placeholder`（用 `exact True.intro`
+"证完"六分量合取）。它们与原型 `weaklySaturatedP22 := True` 属同一类假绿：
+把 `True` 硬编码进镜像定义，再"证明"它。零消费者、零收益，走 DEF-FIX
+章程 `docs/def-fix-charters/hygiene-probe-axiom/` 删除。
+接口的展开形态应当直接讨论 Assembly 侧的真定义，不做本地 `True` 镜像。 -/
 
 /-- **清单 = 查表定义域** 不变量（IneqPilot.lean:72-76 警告的 else-True 静默
 退化防线）：查表定义域 = 六清单并集；`CertifiedIneqHolds` 填实时其查表分支
```

### 2.2 验收

- `lake env lean -o <olean> Kepler/Assembly/IdLists.lean` ⇒ **RC=0 / 0 error /
  0 sorry**（编排者实测 0.9 s）。
- 删除面全部是上表五件；新增面只有解释性 docstring。
- `certLookupDomain` 与六个 `*_length` 钉子保留且仍可编译（本文件 RC=0 即证）。
