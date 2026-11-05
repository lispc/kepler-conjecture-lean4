# Evidence — pa22-eusotyp2-assembly-w1

## 1. 编译命令（standalone，无 lake）

```
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 script -q <log> lean <file>
```

- 基线：`lean Work.lean`（Work.lean = 仓 HEAD 文件，sha256 `1397802c…85ed0`）
- 新件：`lean Work2.lean`（14,769 行）
- 公理：`lean Work2_ax.lean`（Work2 + 尾行 `#print axioms Kepler.Text.EUSOTYP2_general`）

## 2. 读数

| 项 | 基线 Work.lean | 新件 Work2.lean |
|---|---|---|
| 退出码 RC | 0 | 0 |
| `grep -c ': error:'` | 0 | 0 |
| `grep -c 'declaration uses \`sorry\`'` | 17 | 16 |
| `grep -cE '^\s*sorry\s*$'` | 16 | 15 |
| 行数 | 14,434 | 14,769 |

命令原文（读日志先 `tr -d '\r'`）：

```
tr -d '\r' < logs_base.log | grep -c ': error:'          # 0
tr -d '\r' < logs_base.log | grep -c 'declaration uses `sorry`'  # 17
tr -d '\r' < logs_w2.log   | grep -c ': error:'          # 0
tr -d '\r' < logs_w2.log   | grep -c 'declaration uses `sorry`'  # 16
grep -cE '^\s*sorry\s*$' Work.lean    # 16
grep -cE '^\s*sorry\s*$' Work2.lean   # 15
```

注意：本文件 `error` 行格式为 `error(lean.unknownIdentifier):` 时不含 `': error:'`
（首轮诊断中曾出现 1 条该形式，修复后为 0）。基线/新件警告谱面除
`sorry` 计数 17→16 外逐条一致（`diff warn_base.txt warn_new.txt` 仅此一行差异）。

## 3. 公理面（原文）

```
'Kepler.Text.EUSOTYP2_general' depends on axioms: [propext, Classical.choice, Quot.sound]
```

（本 Lean 4.32 在 `open Classical` 下把 `Classical.choice` 打印为 `choice`；
本文件头部的 `open Kepler.Geom Set Classical` 为既有行，未改动。）

## 4. 陈述冻结

```
sed -n '10826,10851p' Work.lean  > stmt_base.txt
sed -n '10929,10954p' Work2.lean > stmt_new.txt
cmp stmt_base.txt stmt_new.txt   # 无输出 = 逐字节相同
shasum -a 256 stmt_base.txt stmt_new.txt
# 55a82de19ea8942802a36c12f58dce2f1e563560e695325dc12b46ff4aabf80d  两文件一致
```

全文件反向重建核（删除新增 103+233 行、目标体恢复 `  sorry`）：

```
{ sed -n '1,10825p' Work2.lean; sed -n '10929,10954p' Work2.lean; echo '  sorry'; sed -n '11188,$p' Work2.lean; } > Recon.lean
cmp Recon.lean Work.lean   # 无输出 = RECON_IDENTICAL
```

## 5. patch 与 apply

```
git apply --stat patch-pa22-eusotyp2-assembly-w1.diff
#  lean/Kepler/Text/PackingAuto22.lean |  337 +++++++++++++++++++++++++++++++++++
#  1 file changed, 336 insertions(+), 1 deletion(-)
git apply --check patch-pa22-eusotyp2-assembly-w1.diff   # PASS
```

patch 头：

```
diff --git a/lean/Kepler/Text/PackingAuto22.lean b/lean/Kepler/Text/PackingAuto22.lean
index 769f071..ee8eda0 100644
--- a/lean/Kepler/Text/PackingAuto22.lean
+++ b/lean/Kepler/Text/PackingAuto22.lean
```

往返核：在临时 git 仓（base = HEAD 文件）上 `git apply` 后 `cmp` 与 Work2.lean
逐字节相同（`PATCH_ROUNDTRIP_IDENTICAL`）。

## 6. 新增块自检

```
sed -n '10826,11187p' Work2.lean | grep -c 'import'                      # 0
sed -n '10826,11187p' Work2.lean | grep -c 'open'                        # 0
sed -n '10826,11187p' Work2.lean | grep -cE 'sorry|admit|native_decide'  # 0
```

## 7. 日志清单（$S/logs/）

- `logs_base.log` — 基线整文件编译（RC=0）
- `logs_w2.log` — 新件整文件编译（RC=0）
- `logs_ax.log` — 新件 + `#print axioms`（RC=0）
- `logs_probe.log` / `logs_ph.log` / `logs_t1.log` — 探针迭代（probe 全绿）
