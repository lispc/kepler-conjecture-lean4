# PA2 存量 stub/concl 桩地图（只读，2026-10-10 归档）

> PA2（5412 行，全链底层）standalone sorry 恰 **46 处**，全部位于 `*_concl`
> 接口块（:4668-5410）；块外零 sorry。`_concl` 共 53 + TSKAJXY_statement（def）。
> 真证 6 + 纯转发 1（GLTVHUM/DUUNHOR/OAPVION1-3/RDWKARC/RHWVGNP）。

## 组 1：twin 已真证且干净（A 类，20 根，可收割）

MHFTTZN1/2/3(PA6)、WAUFCHE1(PA7:598)、WQPRRDY(PA7:1072 CAPSTONE)、EMNWUUS1/2
(PA9)、SLTSTLO1(PA13:595)、HDTFNFZ(PA10:257)、URRPHBZ1/3(PA10/PA17)、
KIZHLTL1/2(PA16)、TIWWFYQ(PA5:663)、VORONOI_BALL2/INTER_BIS_LE/POLYHEDRON
(PA5:739/777/872——INTER_BIS_LE 的 "twin sorried" 注记已过期)、DRUQUFE、
KHEJKCI(PA6:203)。删桩后 PackingConcl `_discharged` 条目零影响（不引用 PA2 名）。
例外：QXSKIIT（PA6 体是它的转发，删则 PA6 断）不进 A 波。

## 组 2：twin 亦 sorry（活债流转）

XNHPWAB1/4（**PA8 全文件 0 sorry 的唯一 taint 源**）、XNHPWAB2/3、WAUFCHE2、
YIFVQDV、KSOQKWL、SLTSTLO2、URRPHBZ2、QZYZMJC、KIZHLTL3（HOL 侧本就无
general-f 证明）、UPFZBZM（PA19 真证但 taint 回流 PA2.GRUTOTI1_concl 桩 →
PA2 内 RDWKARC）、QXSKIIT。

## 组 3：twin 缺失/mismatch/自环（C 类）

- `MXI_EXISTS_concl`（:4902）**自环根债**：PA12.MXI_EXPLICIT 的证明就吃本接口；
  消费者 PA11:457+PA12:1949（LEPJBDJ k=2/3 残链与 PA13 URRPHBZ2 的根债）。
- `RVFXZBU1/2`：**无 twin 全仓**；`RVFXZBU3`：twin PA10:197 限 i≤4 且 i=2,3 sorry。
- `XYOFCGX`（twin 需 Packing 接口无）、`IVFICRK`（twin 严格弱）、
  `GOTCJAH`（PA22 不同编码且故意不 import）。
- `DUUNHOR`：PackingConcl:137 弱接口版（barV-only）全仓无消费者；PA2/PA6 已是
  r2 加宽形真证——统一方案 = 接口升级 r2 形并 wire，-1 sorry。
- `GRUTOTI1_concl`：wired 经 PA24 `_p24`+`_pub` shim（合并时删）；真 twin =
  PA23.GRUTOTI（剩 hcov+pivot 两 sorry）；消费者 PA16:1617+PA24。
- `OXLZLEZ_concl`：wired PA25 但注入两枚 bank 叶 sorry（PA21 pack_nonlinear_rest、
  PA25 ox3q1hP25）。

## 波拆分建议

- **波 1（~30 行，低风险）**：PackingConcl:137 DUUNHOR 弱接口升级 r2 形 + 过期
  注释清理（PA4:1370-1487、PA17:276/278、PA13:53-54、PackingConcl 台账
  "52 sorried"→46 自相矛盾差 1）。
- **波 2（A 类收割，~150-200 行）**：删组 1 的 20 根桩（执行时逐名重新 grep——
  并行线可能新增消费者）；净效果 -20 桩（卫生，不减 reachable sorryAx）。
- **波 3（B/C 真证 bite，按杠杆）**：3a PA7.XNHPWAB1+4（→PA8 全文件转清洁，最高
  杠杆）；3b MXI_EXISTS 自环根债（解锁 PA11/12/13 链）；3c GRUTOTI 收口联动
  （删 _p24 shim、改 PackingConcl:605 与 PA16:1617 指向，注意 PA16 反向 import
  成环检查）；3d PA19.RDWKARC 填证（docstring 已有全证明架构，PA2:5199 有整份
  in-place 真证可移植）；3e PA24 残件；3f PA7 其余；3g SLTSTLO2/URRPHBZ2/QZYZMJC
  /AJRIPQN；3h C 类接口修正。

## 注意

- PA23/PA24 活跃并行线：波 2 不得含 GRUTOTI1/REUHADY 三根桩（已登记 merge 时删）。
- `TSKAJXY_statement`（PA2:5043 def）被 PA18/19/21/25 消费，非桩勿动。
- PA2 concl 块外零 sorry（p2g 复制 kit 已全真证）。
