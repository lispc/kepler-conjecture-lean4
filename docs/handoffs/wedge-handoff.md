# PA21 楔形 GIANT 工位 handoff（2026-10-08，重启续作 lane，第二次交卷）

## 核心成果（本 lane 已完成）
- **kit1b2 段全绿**（hcone/hslab 数值块 + hlam 点积桥 + p21w_wedge_band + wedge_band 消费）：
  /tmp/wedgeprobe/PA21WKit1b2.olean 已产出，kit1b2.log 0 error。
- 真文件 lean/Kepler/Text/PackingAuto21.lean 的楔形数值块已按修复重写（未落盘失败风险）：
  * hlam 恢复 ascribed 形态 `p ⬝ᵥ ((v - u : V3))`（匹配 rconeGe 体的 WRAPPED 点积 arg2）。
  * hcone 块：`rw [add_sub_cancel_left, dist_eq_norm, add_sub_cancel_left, hlam x] at hcone`，
    h1 经 nlinarith [hcone, hDpos] 闭合（绕开 le_of_mul_le_mul 的 mul 因子对位问题）。
  * hslab 块：`rw [add_sub_cancel_left, ← WithLp.ofLp_sub, hlam x, mul_comm (dist v u)
    (x.ofLp ⬝ᵥ e3.ofLp), ← dist_eq_norm v u] at hslab`，
    h2 经 le_of_mul_le_mul_right hslab hDpos 闭合。
    （关键：slab 体的点积 arg2 是 OPERANDS 形态 `v.ofLp - u.ofLp`，rconeGe 体的是
     WRAPPED 形态 `(v - u).ofLp`——两个 def 的 elaboration 形态不一致，需分别处理。）
  * reverse 分支 hkey：`rw [hlam x]` 桥 + calc，已绿。
  * hval0 括号修复（mul_nonneg 三层嵌套去掉多余的 (by norm_num) 层）。
  * refine 尾部简化为 `rw [hnorm2, mul_comm a ‖x‖]`（h1 形态已含 mul_right_comm）。

## 当前卡点（下一 lane 第一任务）
- **kit1c 段 45 错**：内容 = [5186(kA), 5582(kC)) = p21w_ang_re/im、p21w_ang_lt_pi_of_im_pos、
  p21w_cone_to_band、p21w_band_to_cone、p21w_zOf 系列、p21w_wedgeGe_eq_affGe。
  首错 43:13 `Invalid field symm: True.symm`（p21w_ang_re 的 `simp at h2` 把
  `Complex.exp_re (ang z * I)` 简化成了 True——疑为 ang/I 的 elaboration 形态在
  kit1c 合成头下与真文件不一致）。**尚未诊断**。
- kit3/vol/sol/post 四段未跑（依赖 kit1c）。

## /tmp/wedgeprobe 探针链设施（已验证可用）
- 分段：PA21WPrefix(4582行,含3个p21_*去私有) → PA21WKit1a → PA21WKit1b1 →
  PA21WKit1b2 → PA21WKit1c → PA21WVol → PA21WSol → PA21WPost。
- run_chain.sh：`lake env printenv LEAN_PATH` 取路径 + `lean --root=/tmp/wedgeprobe` 逐段编译，
  .olean + .ok 缓存，kill 后重跑自动跳过绿段。
- chunk 生成脚本见 handoff 上一版的 gen() 模板（import 全量 + set_option + namespace + opens）。
- ⚠️ chunk 的 gen header 与 kit1b2 实测一致即可；kit1c 首错疑似与 elaboration 形态有关，
  可先试在 kit1c 头部补 `open scoped Complex` 或对比真文件 5188 行的 elaboration。

## 关键教训（本 lane 实证）
- V3 点积的 elaboration 形态混乱是本区最大坑：
  * rconeGe 体（PA2 olean）的点积 arg2 = WRAPPED 形态 `ofLp (HSub v u)`（显示 `(v - u).ofLp`）。
  * 残留 S 集合定义（fresh elab）的点积 arg2 = OPERANDS 形态 `v.ofLp - u.ofLp`。
  * 两者对同一语法 `(y - u) ⬝ᵥ (v - u)` 产生不同 term，rw 模式必须逐点核对显示。
  * hlam 需 ascribed 形态（WRAPPED）才能匹配 rconeGe 体；hslab 需 ← ofLp_sub 桥。
- `simp at h2` 可能把假设改写成 True（kit1c 43:13），注意检查 simp 前后的假设形态。
- zsh 空 glob 中断整个命令行：rm 用显式文件名。
- 本机 grep 是 ugrep -G 包装：\b 与 (a|b) 不可靠，查代码用 `command grep`。

## 下波地图
1. kit1c 45 错诊断（首错 43:13 True.symm，建议先在 kit1c 头部逐个补 open 对比）。
2. kit3/vol/sol/post 逐段过链。
3. 全文件 `lake env lean Kepler/Text/PackingAuto21.lean` 终检。
4. PA21 的 MCELL2_VOL_SPLIT_EXPLICIT + MCELL2_SOL 陈述已冻结未动，sorries 仍为 3 处
   （396/973/1335），与记账一致。
