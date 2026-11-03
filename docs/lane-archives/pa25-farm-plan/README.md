# pa25-farm-plan — PA25 30 e2e 直源排产/备料波（归档 · B0 已消费）

> **状态更新（2026-11-03 晚）**：B0 replay 已按下方消费条件走完并落库——
> `pa25-b0-replay` 验证车道判决 GO（整文件 RC=0、16 必查件 + 13 新私件全标准三、
> 14 件漂移 0、sorry 56→40），编排者在干净 HEAD 过闸后落库（queue 续 258）。
> 本归档保留原排产表与 kit 供追溯；B1–B5 的 go/no-go 判定仍然有效。

**基线**：任务书 `1c0b328f`；交付时主仓 `a34cb699`（并发 pa19-rdwkarc 落库）。
`PackingAuto25.lean` 在两处 blob 逐字相同（`1ce617cc…`），行号/计数不受影响。

**为什么不落库（2026-11-03）**

1. 本波是**排产/备料波**，不是填充波；主交付是 30 源全表 + 6 批 go/no-go，不是可落库的证明。
2. `kit-pa25-replay-w4w5w6.diff`（11 直源 + 5 kit，`+841/−16`，删除面恰 16 行裸
   `sorry`）只在**旧基线 `76771f7e`** 上编译验证过（21/21 标准三），**未在 HEAD 编译**。
   按「kit 只含 RC=0」政策，未在目标 HEAD 验证的 kit 不得落库。
3. 四条非/半 farm 件中：`cc_prep_model_data` 只交 API/证法映射（未交 diff）；
   `pkLeafRank*` 是搬债；`ox3q1hP25` NO-GO（`Oxl_def.hl` 不在仓内）。

**消费条件（B0 replay，满足后才可落库）**

1. 在 HEAD 应用本 kit（`git apply --check` 当前 PASS）。
2. 整文件 standalone `RC=0` / 0 error；`logs/count_sorries.py` 口径 56 → 40。
3. 对 11 直源 + 5 kit（及 `real_model_3a/3b` 所在的 `cell3_from_ineq_thm` 链）逐件
   `#print axioms`，必须标准三；`PACKING_CHAPTER_MAIN_CONCLUSION_discharged` 的
   sorryAx 面必须相应收缩。
4. 过标准闸（`LANE_FILES=Kepler/Text/PackingAuto25.lean`，`THM` 取一件填充直源）后落库。

**不要做的事**：不要把旧基线 76771f7e 的 21/21 探针读数当成 HEAD 读数；不要据本 kit
声称任何 `real_model_*` 已关闭；不要在冻结期跑 G4/发射（B4 `gamma8b` 需要新 bank/证书，
NO-GO）。

**对应 queue 条目**：`docs/priority-queue.md` §8 续 256。

**工件哈希（sha256）**

```
b6adfe9490615888aec991841edd6279c0fa2f88570cef09bd6eb59adc12d6f8  DELIVERY.md
13b08365ab9bdf2edd9b857bd05a5d930193af54d58b3b50bae6313c647fcc4e  Evidence.md
acd3a32d300aad542d322677a05ae5e98ac268c36f6cdaec426c3fb4f9fa49c5  kit-pa25-replay-w4w5w6.diff
```
