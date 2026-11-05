# PA22 独立可攻清单波 交接 (2026-09-30)

lane: PA22 填充 (PackingAuto22.lean) — 本轮 "PA22b"
状态: 文件全量 `lake env lean` 单文件检查通过 (0 error, 仅既有 sorry 警告)。
sorry: 41 → 37 (闭合 4)。本轮新增 NEEDS 文档 2 处 (ARG_ORDER / sloc2_ortho)。

## 本轮闭合 (4)
1. `collinear_translate_axis` (:4474 附近) — 双侧化归 `collinear3_iff_smul`,
   退化情形 (u1 = t•u1) 用 `collinear3_of_eq`, 标量恒等式
   `t•u1 = (t/(1-t))•(u1−t•u1)` 一次证好 (module + field_simp)。
2. `azim_axis` — 无条件恒等 (原假设只保证非退化): 私件
   `p22_azim_trans` (AZIM_TRANSLATION 重建) + `p22_azim_axis_shift`
   (沿轴平移被测点; AzimSpec 层 h1→h1±s) + `p22_collinear3_axis_shift`。
3. `card_packing_ball` — n := ⌈(r+1)³⌉; `Set.Finite.exists_finset_coe` +
   `measure_biUnion_finset` + `EuclideanSpace.volume_ball_fin_three`;
   ncard 桥 `Set.ncard_coe_finset` (绕开 toFinset 时代的所有坑)。
4. `card_packing_annulus` — card_packing_ball (2*h0+1) 的直接推论。

## NEEDS (本轮文档化, 陈述冻结)
- `ARG_ORDER` — **陈述在 Complex.arg (值域 (−π,π]) 下为假**。
  反例: u=1, n=3, h1=e^{−iπ/2}, h2=e^{i(π/2−0.1)}, h3=−1, h4=h1:
  假设全成立, 但 (i,j)=(1,3): arg(h2/h1)=π−0.1 > −π/2 = arg(h3/h1)。
  flyspeck 原证用 Ysskqoy Arg ([0,2π)); 需 statement owner 抬升到 holArg
  (同 ARG_INV_ALT 移植注记的缺陷类)。已留完整反例注释。
- `sloc2_ortho` — 球面直角三角恒等式, 数学路线已完全算出并 ~90% 形式化
  (探针 /tmp/pa22b_sloc2_ortho_progress.lean, 0 sorry 但 4 个 unsolved):
  Gram 记号 A,B,C,x,y,z; 右角约束 C·z = x·y; 六条点积/范数展开;
  cos alp = x·√P/√D, sin bet = √(BCP/D), t = x/√(BC)
  (P := AC−y², D := ABC²−x²y²; 全部正性来自投影非零)。
  仅剩最后的平方恒等式装配: (cos alp)² = (1−q_b²)·t² + 符号论证
  (cos·t ≥ 0, 同号于 x)。**坑**: 对含 (√…)⁻¹ 的装配目标 field_simp
  会错清分母产生假子目标; 改用显式 div_mul_eq_mul_div /
  eq_div_iff (pow_ne_zero 2 …) / mul_sub 链或以 k-引理为证书的
  linear_combination。探针中 nondegeneracy/keyd/R/展开/正性/k1–k8/
  hca/hcb/hct/hqbr/hsg 全部已编译, 下一波直接搬。

## 下波地图 (PA22 剩余 sorry 37 个, 独立可攻排序)
- sloc2_ortho (见上, 最接近闭合; 装配仅剩 3–4 个 field_simp 残差)
- UKBRPFE_explicit / BIEFJHU_explicit — 纯数值。路线: asn 泰勒上界
  (α = (1−t²)^{-1/2} 的部分和+尾项, 经 ∫), sin 高阶界 (x−x³/6+x⁵/120−x⁷/5040),
  π ∈ (3.14, 22/7), k∈{3..7} 逐个 (sin(π/3)=√3/2, π/4, π/5=√(10−2√5)/4,
  1/2, π/7 区间), k ≥ 7 单调延拓 (gap'(k) = 0.0331 − 2asn + … > 0,
  需 asn' 界)。BIEFJHU 另需 h∈[1,1.26] 的耦合处理 (最紧 k=5,h=1 余量
  仅 0.0107, 需 ~25 个 h-区间或 gap-单调性论证) — 体量大, 单独一波。
- 2000 行后 GIANT 区 (GOTCJAH/EUSOTYP/POLYHEDRON_CONFORMING_FAN 等) 未动。

## 纪律遵守
- 探针只在 /tmp; 单 lean 进程; 无 git 操作; 未动清单外条目;
  增量落盘 (每闭合一件即写入)。
