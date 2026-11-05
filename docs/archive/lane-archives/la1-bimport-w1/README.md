# la1-bimport-w1 — 归档说明

- 基线 HEAD：`8635c297`（车道运行中主干推进到 `873d2a2c`；两件目标源文件在两版
  HEAD 逐字相同，md5 `a224d342…` / `78b3088c…`，本目录读数对两版均有效）。
- 落库内容：本目录（审计 + 残件）由编排者随 `010f79a6` 入库；两行 import
  （LA16→LA33、LA26→LA28）的源码改动以工作区补丁 `kit-la1-bimport-w1.diff`
  交付，对 HEAD `873d2a2c` 的干净树 `git apply --check` 通过，尚未提交。
- 未落库件：`Kit-draft-la26-rrcwnsj-w1.lean`（上一车道 `la26-rrcwnsj-w1` 的已验证
  降维件，md5 `d718a8d4…`）。不落库原因：`RRCWNSJ_p26` 仍未闭合，该件若现在插入
  `LocalAuto26.lean` 是死代码；待 `hnoLunar` 证明落地时随目标体一起消费。
- 消费条件：`LocalAuto26.lean` 的 `RRCWNSJ_p26` 证明波启动时，把该降维件与
  `ODXLSTCv2_p28` / `IMJXPHRv2_p28` 装配（后者已由本车道的 import 解锁）。
- `LKGRQUI` 桥：**不建**。请求的桥形（bridge 内 `import LocalAuto27`，LA20 再
  import bridge）成环：`LA27 → LA24 → LA20`；且 LA20 已用 `LkgrquiKernel.LKGRQUI_krnl`
  闭合消费件，`LocalConcl.LKGRQUI_discharged` 已是标准三。论证见 `BRIDGE.md`。
- queue §8：无对应条目（本车道记录）。
