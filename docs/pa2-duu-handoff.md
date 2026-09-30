# PA2 DUUNHOR 移植波 handoff（2026-09-30，本波两阶段：阶段 1 完成落盘；阶段 2 GIANT 进行中）

## 已落盘（阶段 1：PA2 三桩 + 两顺路件，repo/lean/Kepler/Text/PackingAuto2.lean 已更新，全文件编译零错误）

| 件 | 现状 |
|---|---|
| p2g_VORONOI_LIST_CANONICAL | ✅ 真证（PA5:1638 正本证明体链复制 + 依赖闭包 §3.5 段） |
| p2g_POLYHEDRON_VORONOI_LIST | ✅ 真证（PA5:1689 链复制） |
| p2g_POLYTOPE_VORONOI_LIST | ✅ 真证（PA5:1979 链复制 + polytope kit §4.5 段） |
| p2g_HALFSPACE_EQ | ✅ 真证（PA6:247 正本 5aa56729 链复制，+p2g_REAL_LINE_BOUNDED 依赖件） |
| p2g_BARV_EXISTS | ✅ 真证（PA6:885 正本链复制；上游 PA5 侧桩已随本波闭合） |

### 阶段 1 依赖闭包（全部真证，`private` + p2g_ 前缀，正本行号在注释）
- §3.5 段：p2g_INTERS_UNIV / p2g_INTERS_INTER_INTERS / p2g_MID_POINT_EXISTS /
  p2g_KIUMVTC / p2g_VORONOI_BALL2 / p2g_VORONOI_INTER_BIS_LE /
  p2g_VORONOI_CLOSED_EQ_FINITE_INTERS_BIS_LE / p2g_polyhedron_bisLe /
  p2g_VORONOI_POLYHEDRON / p2g_INTER_AFFINE_HULL / p2g_minimal_inters_aux /
  p2g_MINIMAL_INTER_INTERS_EXISTS / p2g_LIST_SUBSET / p2g_VORONOI_LIST_BIS_LE
- §4.5 段（polytope kit，PA5:1706-1995 链复制；三件自文件下方上移）：
  p2g_sSup_mem_closed / p2g_mem_hull_insert_facet / p2g_convexHull_union_hull /
  p2g_affDim_of_nonempty / p2g_polytope_of_compact_polyhedron_aux /
  p2g_polytope_of_compact_polyhedron / p2g_HD_IN_SET_OF_LIST /
  p2g_isClosed_voronoiList / p2g_bounded_voronoiList_of_len / p2g_LENGTH_IMP_CONS

### sorry 变化：52 → 47（-5，即本波闭合的五件；无新增 sorry）

## 进行中（阶段 2：DUUNHOR_concl GIANT，全部在 /tmp/pa2_work.lean，未落盘——文件尚有错误+3 处 sorry，不可直接落盘）

### 已完成并编译通过（/tmp/pa2_work.lean 行 ~2860-3710）
- §6.5 段 DUUNHOR kit（PA6 正本 5aa56729 链复制，全真证零 sorry）：
  p2g_LENGTH_TRUNCATE_SIMPLEX / p2g_INTER_VORONOI_SUBSET_BISECTOR（自证，bis 展开式）/
  p2g_VORONOI_CLOSED_EQ_LEMMA / p2g_CLOSEST_POINT_MEM / p2g_OMEGA_LIST_N_EQ /
  p2g_ODIGPXU_LEMMA / p2g_ODIGPXU / p2g_VORONOI_SET_SUBSET /
  p2g_initialSublist_truncate_truncate / p2g_voronoiList_initialSublist_mono /
  p2g_OMEGA_LIST_N_IN_FACET / p2g_OMEGA_LIST_N_IN_VORONOI_LIST_GEN /
  p2g_OMEGA_LIST_N_EQ_GEN / p2g_SET_OF_LIST_TRUNCATE_SIMPLEX_SUBSET /
  p2g_VORONOI_LIST_AFF_DIM / p2g_ROGERS_AFF_DIM_FULL（PA6:1479 真证链复制）
- §6.6 段（本波自证，探针 /tmp/pa2_duu_probe.lean 全绿后移植）：
  p2g_coplanar_of_affDim_le（root-Coplanar！见下"关键发现"）/
  p2g_mem_convexHull_finset / p2g_affineSpan_subset / p2g_finrank_sup_le /
  p2g_span_two_of_finrank / p2g_AFF_DIM_LE_2_IMP_COPLANAR（Geom 版，现未用可删）/
  p2g_AFF_DIM_FINITE_UNION_LE（PA6:1552 的 sorry 之真证补位！）
- DUUNHOR_concl 主装配已写入：§0 最小分歧指标 k（hleast 强归纳，避开 Nat.findX）✅
  hvk（vor-list 在 k 处分歧）✅；hcover 的两支"早期完备"情形 ✅（全证）；
  主情形 hcovneg1/2 + hss_tt 强归纳骨架 ✅；hkey' 核心的全部前置件
  （hPsub/hPpoly/hp0P/hp0not/hsubLu/hsubLv2/hpIn/hqIn/面配置 hFacU/hFacV/
  hneA/hneB/hsumLu/hsumLv2/hlt1/hlt1'）✅

### 关键发现（下波必读）
1. **DUUNHOR_concl 的 `Coplanar` 是 Mathlib 根命名空间 `Coplanar ℝ S`**
   （= Module.rank (vectorSpan ℝ S) ≤ 2，双显式参数），不是 Kepler.Geom.Coplanar
   （affineSpan 三点存在，单参数）——与 PA24 `coplanarAzimEq` 的"按元数分辨"同款。
   终步用 `p2g_coplanar_of_affDim_le`（kit 内）：coplanar_iff_finrank_le_two + affDim 展开。
2. `Finset.sum_subset` 的 h₀ 消没引理里 `rw [if_neg hx2]` 会因 lambda 未 beta 而失败；
   用 `show (if ... then ss x else 0) • x = 0` 强制 beta，或 `simp [if_neg hx2]`。
3. `Finset.mem_union` 的 rintro/提供须走 Iff（`Finset.mem_union.2 (Or.inl ...)`），
   直接对 raw Mem 用 ⟨⟩ 匿名构造会报 And.intro 元数错。
4. `Finset.range_subset.2` 的 RHS 是 ∀ x < m 形（非 m ≤ n）。

### 余下工作（完整配方，按此施工；全部设计已定）
1. hkey' 尾部（现文件 ~3730 起，hsumDEL 残件为坏占位须删）：
   a. hDELv（erase-和相等）：∑ (Lv.erase p0) ss = ∑ (Lv.erase p0) tt，
      sum_congr + mem_image.1(mem_erase.1 hx).1 + x≠p0→j≠n→j<n→ih j hjn hjk；
      注意 ih 形为 `∀ m < n, m < k → ss (ωu m) = tt (ωv m)`（三参）；
      元素改写：`rw [hjx, ← (hpre j hjk).1, ih-式, (hpre j hjk).1]`。
   b. hDELv-数字版（∑erase ss = ∑erase tt，无 •x）供 a-b 算术。
   c. hDELv'-vsum 版（•x 版）供 heq。
   d. hLuEq : ∑ Lu (ss•x) = ∑ Lv2 (tt•x) + (tt p0 - ss p0) • p0：
      linear_combination (norm := module) hsplit_w - hsplit'_w - hDELv'，
      其中 hsplit_w/hsplit'_w：hsplit/hsplit' 与 hssw/httw 合成的 w-等式
      （∑ Li (ss•x) + ∑ Lu (ss•x) = w 等，Finset.sum_erase_add 拆 p0 项 +
      hLiLv/hDELv 运输 + E3'：∑ Li (ss•x) - ∑ Lv (tt•x) = (ss p0 - tt p0) • p0，
      由 erase-拆分 + hDELv' 线性合成）。
   e. heq : (1-(1-a)) • p0 + (1-a) • p = (1-(1-b)) • p0 + (1-b) • q：
      先 e1 : (1-a) • p = ∑ Lu (ss•x)（hpIn 里已有 h1 同式），
      e2 : (1-b) • q = ∑ Lv2 (tt•x)；linear_combination (norm := module)
      hLuEq + hnum'，hnum' : (a-b) • p0 = (ss p0 - tt p0) • p0（rw hnum，
      hnum : tt p0 - ss p0 = a - b，由 a/b 的 erase-加法拆分 + hDELv-数字版 linarith）。
   f. ODIGPXU 应用：p2g_ODIGPXU (voronoiList V (truncateSimplex n ul))
      (voronoiList V (truncateSimplex (n+1) vl)) (voronoiList V (truncateSimplex (n+1) ul))
      p0 p q t s hPpoly hp0P hp0not hFacV hFacU hqIn hpIn ht hs heq，
      其中 t := 1 - ∑ Li ss、s := 1 - ∑ Lv tt（s = t ⟺ a = b）。
   g. 收口：a = b（linarith，a/b 的 erase-拆分 + hDELv-数字版）→
      ss p0 = tt p0（a-b = ss p0 - tt p0 再 linarith）。
2. hss_tt 之后的覆盖第二段（现文件 "exact hkey' hi" 之后的 sorry）：
   - Y/Lv_lt 等号 + ∑ Lv_lt ss = ∑ Lv_lt tt（hss_tt 逐点）
   - a := ∑ Y tt；1 - a ≠ 0（hcovneg2 (k-1) 的 Lv≤(k-1)=Y 等集论证 + Y 空时 a=0）
   - p := inv(1-a) • ∑ Lv_ge (tt•x) ∈ X（两个 hull-min 经
     p2g_OMEGA_LIST_N_IN_VORONOI_LIST_GEN (k ≤ j < 4) + vsum Lu_ge ss = vsum Lv_ge tt
     ——由 hsplitA/hsplitB 两 w-分解 + vsum Lv_lt ss = vsum Lv_lt tt）
   - p ∉ Lv_lt（p2g_OMEGA_LIST_N_EQ_GEN + hinjv，p ∈ X 的 ul 侧）
   - w ∈ hull (Y ∪ {p})：权重 fun y => if y = p then 1 - a else tt y
     （Finset.sum_union + SUM_SING + 筛选恒等）⊆ hull (Y ∪ X)。
3. §3 维度收尾（最后一个 sorry）：
   - k=0：X = 两闭胞交（TRUNCATE_0_EQ_HEAD + VORONOI_LIST_SING）；hdV ul ≠ hdV vl
     （hvk 反证）；p2g_INTER_VORONOI_SUBSET_BISECTOR + affDim_hyperplane
     （a := 2•(hdV ul - hdV vl) ≠ 0）→ affDim X ≤ 2（X 空时 -1 平凡）。
   - 0<k：Fu/Fv 为 P=vorlist trunc (k-1) vl 的面（p2g_IDBEZAL + hpre(k-1) 运输 +
     p2g_TRUNCATE_SIMPLEX_BARV / p2g_TRUNCATE_TRUNCATE_SIMPLEX）；
     faceOf_inter + faceOf_face → X 是 Fu/Fv 的面；X=Fu∧X=Fv 与 hvk 矛盾；
     FACE_OF_AFF_DIM_LT + p2g_VORONOI_LIST_AFF_DIM（=3-k）→ affDim X ≤ 2-k。
   - 总装：交空则 _root_.coplanar_empty；否则 affDim 交 ≤ affDim hull(Y∪X)
     （affDim_mono）= affDim (Y∪X)（p2g_affDim_convexHull，需新增：
     vectorSpan_mono 两侧 + convexHull_subset_affineSpan，PA6 ROGERS_AFF_DIM_FULL 同法）
     ≤ Nat.card Y + affDim X（p2g_AFF_DIM_FINITE_UNION_LE）≤ k + (2-k) = 2
     （Y.card ≤ k + hdimX）→ p2g_coplanar_of_affDim_le。
4. 修完跑全文件（`~/.elan/bin/lake env lean /tmp/pa2_work.lean`，~3-4 分钟），
   零错误后 cp 落盘 repo PA2，再跑公理审计（#print axioms DUUNHOR_concl 等）。

### 当前 /tmp/pa2_work.lean 已知错误清单（v31 后 ~15 处，全部机械）
- 3319/3321 hleast 内层：hcon2 论证已改为 hjmin (fun i hij => by by_contra hiA; exact
  hcon2 ⟨i, hij, hiA⟩)（v21 已应用，若再现请 grep 核对）
- hPnot 分支：`rw [hp0] at hne` 位置错——应 `rw [hp0] at hcon` 后再取
  p2g_OMEGA_LIST_N_EQ；且 rcases Set.mem_union.1 hcon（v32 已修一半，请核对）
- hpIn/hqIn 的 refine 尾：`convexHull_min hsubLu2 (...) ?_` 的第二参应直接给
  p2g_mem_convexHull_finset.2 ⟨...⟩（v31 已改为 convexHull_min 形，核对 `?_` 数）
- 3700 rw [hp0] at hne 方向、3705/3711 Set.mem_union.1、3719 hpIn refine 结构、
  3724+ Function expected——均随 hkey' 重写一并消解
- hsumDEL 坏占位（"Finset.mem_erase.1 ... |>.elim id" 垃圾文本）——删除重写为 1a

### 纪律提醒
- 阶段 1 已在 repo；阶段 2 的 /tmp/pa2_work.lean 勿直接 cp 落盘。
- 单 lean 进程；探针只在 /tmp；禁止全项目 lake build 与 git 操作。
- 3283/3293 的 "unsolved goals case pos" 是 hle3 与 DUUNHOR 外层尚未闭合的分支
  （DUUNHOR 整体仍有 sorry），修完 sorry 自然消失。
