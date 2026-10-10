# PA2 DUUNHOR 移交文档（2026-09-30 第二轮收尾，接 docs/pa2-duu-handoff.md）

## 本轮结果（正本已落库：lean/Kepler/Text/PackingAuto2.lean，全文件编译零错误，git modified 未提交）

### 已落库（本轮新增，全部编译通过）
| 件 | 状态 |
|---|---|
| §6.6 kit：p2g_span_image_le_ncard | ✅ 真证（Finset 覆盖 + finrank_span_le_card + ncard 桥） |
| §6.6 kit：p2g_affDim_convexHull | ✅ 真证（vectorSpan_mono 双向 + convexHull_subset_affineSpan） |
| §6.6 kit：p2g_coplanar_of_affDim_le | ✅ 真证（root-Coplanar，Set.Elem coesort 形式） |
| §6.6 kit：p2g_mem_convexHull_finset | ✅ 真证（Finset.coemass 形式） |
| p2g_AFF_DIM_FINITE_UNION_LE | ⚠️ 语句已冻结（PA6:1552 镜像），证明体移至 WIP 文件，见下 |
| DUUNHOR_concl | sorry 保持（47 冻结集之一，未变） |

sorry 计数：正本 60（与落库前持平，净零新增；GLTVHUM 的 −1 与
p2g_AFF_DIM_FINITE_UNION_LE 语句冻结的 +1 相抵）。

### WIP 文件（下一轮的主战场）
/tmp/pa2duu_duunhor_wip.lean（91k 字符）＝ DUUNHOR 波全部工作体的原样保存：
- p2g_AFF_DIM_FINITE_UNION_LE 全证明体（case-1/case-2 完整计数桥 + hcnt_gen 泛化引理）
- DUUNHOR_concl 主装配体（hA/hB/hsubXX hull 覆盖段 + hcnt 桥 + endgame）

### 剩余 4 处 elaboration 错误（全部在 WIP 块内，数学内容已对，纯 Lean 4 形式问题）
1. p2g_AFF_DIM_FINITE_UNION_LE case-1 t=∅ 端局 omega：
   CharZero ?m.988 卡死。原因：`Nat.card ↥(s \ Set.singleton p0)` 的 ↥ coesort
   token 在 have TYPE 位置触发 mvar 实例搜索死循环。
   方向：hle/hcnt 的 Nat.cast_le.2/rw 前先把 ↥(...) 参数换成
   `(s \ Set.singleton p0 : Set V3)` 双重 ascription 形式（pa2_work.lean 其他位置
   已验证可编译），或者干脆用 hb 桥把 Nat.card 全部改写成 ncard 后再 omega/linarith。
2. case-2 hchain 步5 内层 le_trans (p2g...) (by omega)：
   `Nat.card ↥(s \ Set.singleton p0) ≤ Nat.card ↑(s \ Set.singleton p0)` 的
   ↥/↑ coesort 形式不一致导致Application type mismatch。
   方向：步5 target 的 `(Nat.card ↑(s \ Set.singleton p0) : ℕ)` 已是 ↑ 形式，
   把 p2g 结论/hcardle/hb 的参数全部改成同一 ↑ 形式，或全部改成 ↥ 形式。
   注意：↥ 与 ↑ 在 Nat.card 参数位置不是同一个常量（Set.Elem vs CoeSort.coe），
   不是 defeq（isDefEq 会 5M/20M 心跳超时）。
3. case-2 endgame linarith 失败：
   依赖第 2 条修好后的 hchain（hcardle/hcnt 原子一致后 linarith/omega 可闭）。
4. DUUNHOR_concl case-2 hull 覆盖段 show tactic failed：
   `convexHull ℝ ↑(Yfin ∪ {PP})` vs `convexHull ℝ ((↑Yfin-coe).union {PP})`
   的 Finset.coe_union / Set.union 两种形式 defeq 检查失败（同样是 coe 路径问题）。
   方向：hsubXX 的 ∀∈ 形式（build67 已验证可 elaborat）+ 终段的
   `Set.union` applied 形式（build70 已验证可 elaborat）之间需要一个
   `convert` 或 `Finset.coe_union` 的显式桥。或者用 hb0/Fintype.card 桥绕过
   p2g_mem_convexHull_finset 的 ↑s hull 形式（参考 hYcard' 的写法）。

### 调试经验（下一轮必读）
- `Nat.card ↥X`（↥ token）与 `Nat.card ↑X`（↑ token）在 Nat.card 参数位置
  elaborat 出不同 coesort 证明项，二者 defEq 检查会心跳超时或直接失败。
  同一文件内必须统一用一种；本波 ↥ 在 have TYPE 位置、↑ 在 rw 规则位置
  各自触发过死循环。最稳的是 hb 桥（Nat.card_coe_set_eq）+ ncard 全程。
- `Set.singleton p0` 与 `{p0}`（Singleton.singleton p0）同理不是同一个常量，
  rw 规则匹配会失败；`Set.mem_sdiff` 的 mp/mpr 用法见 hmem'/hx'。
- `Set.union` applied 形式（Set.union A B）在 have := RHS 位置可编译，
  在 have TYPE 位置会卡 Module 实例搜索（hsubXX 第一次尝试失败）；
  `∀ z ∈ Set.union A B, ...` 的 ∀∈ 形式可编译（build67 验证）。
- `Finset.coe_union` / `Set.union` 的 defeq 检查在 convexHull 参数位置失败
  （DUUNHOR case-2 hull 段），需要 `convert` 或 Finset.coe_union 显式桥。
