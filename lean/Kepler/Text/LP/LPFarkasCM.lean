/-
  Kepler/Text/LP/LPFarkasCM — Farkas 列主序 → 行主序桥（C3 落地波，2026-10-16）。

  背景：`Kepler.Text.LP.LPFarkas` §3 列主序内核（C1.7，f75c305d）把 189 条
  infeasible 证书的内核检查从行主序 `farkasCheck`（B086 4h22m / B087 内存
  爆炸，求值结构病）降到列主序 `farkasCheckCol`（B086 7m45s）。但叶层冻结
  陈述 `LpTerminalInfeasibleCertified`（LPCert，DEF-FIX 章程 lp-infeas-deffix.md，
  2026-10-12）的见证类型是**行主序** `LpFarkasCore`——闭叶需要行主序核。

  本模块提供唯一的合法换向通道：`rowsFromCols`（列表转置）+ `rowCoreOf`
  （列主序核的行主序像）+ `farkasCheck_rowCoreOf`（列检查通过 ⟹ 行检查
  通过）。全部纯追加，`LPFarkas.lean` 零触碰；正确性 = 纯 List 结构归纳
  （转置不改数学量：每列加权和与 rhs 加权和逐点相同），**不经行主序
  decide**——巨物行主序求值的内存陷阱（C1.7 B087 事故，65.8GB 物理足迹）
  不在本路径。

  消费形态（C3 闭合模块，`gen_farkas.py --land` 发射）：每条 infeasible
  记录一个模块，`core`（列主序字面量）+ `core_farkasCheck`（列主序 decide）
  + `rowCore := rowCoreOf core` + `row_check := farkasCheck_rowCoreOf …`；
  叶转发 `⟨rowCore, row_check⟩` 闭合 `LpTerminalInfeasibleCertified`。
-/
import Kepler.Text.LP.LPFarkas

namespace Kepler.Text.LP

/-! ## §1 List 取项备件（自证，零 API 依赖；LPFarkas §3 同款纪律） -/

/-- cons 头取项（自证备件）。 -/
private theorem getD_cons_zero' {α : Type} {x : α} {l : List α} {d : α} :
    (x :: l).getD 0 d = x := rfl

/-- cons 尾取项（自证备件）。 -/
private theorem getD_cons_succ' {α : Type} {x : α} {l : List α} {k : Nat} {d : α} :
    (x :: l).getD (k + 1) d = l.getD k d := rfl

/-- map 后取项 = 对原位取项映像（i 在界；`a` 仅为内层 getD 默认值占位）。 -/
private theorem map_getD {α β : Type} (f : α → β) (d : β) (a : α) :
    ∀ (l : List α) (i : Nat), i < l.length → (l.map f).getD i d = f (l.getD i a) := by
  intro l
  induction l with
  | nil => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | cons x t ih =>
      intro i hi
      cases i with
      | zero => rfl
      | succ k =>
          simp only [List.length_cons] at hi
          simp only [List.map_cons, getD_cons_succ']
          exact ih k (by omega)

/-- map 后越界取项落默认值。 -/
private theorem map_getD_of_le {α β : Type} (f : α → β) (d : β) :
    ∀ (l : List α) (i : Nat), l.length ≤ i → (l.map f).getD i d = d := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons x t ih =>
      intro i hi
      cases i with
      | zero => simp only [List.length_cons] at hi; omega
      | succ k =>
          simp only [List.length_cons] at hi
          simp only [List.map_cons, getD_cons_succ']
          exact ih k (by omega)

/-- range 映像的 cons 分解：`range (R+1)` 映像 = 首项 :: 尾段右移映像。 -/
private theorem map_range_cons {α : Type} (f : Nat → α) (R : Nat) :
    (List.range (R + 1)).map f = f 0 :: (List.range R).map (fun j => f (j + 1)) := by
  induction R with
  | zero => rfl
  | succ R ih =>
      rw [List.range_succ, List.map_append, ih, List.range_succ, List.map_append]
      simp [List.cons_append]

/-- range 映像取项 = 原位映像（j 在界；f 随归纳右移）。 -/
private theorem map_range_getD {α : Type} (d : α) :
    ∀ (R : Nat) (f : Nat → α) (j : Nat), j < R →
      ((List.range R).map f).getD j d = f j := by
  intro R
  induction R with
  | zero => intro f j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ R ih =>
      intro f j hj
      rw [map_range_cons f R]
      cases j with
      | zero => simp
      | succ k =>
          simp only [getD_cons_succ']
          exact ih (fun j => f (j + 1)) k (by omega)

/-! ## §2 列表转置（列 → 行） -/

/-- **列表转置**：`rowsFromCols cols R` = 行主序行表，第 `j` 行 = 各列的
第 `j` 项（越界读 0）。`R` = 行数（`coreShapeCol` 不变式下 = 每列等长 =
rhs/mults 平行长）；列数 = `cols.length` = 每行项数。 -/
def rowsFromCols (cols : List (List Int)) (R : Nat) : List (List Int) :=
  (List.range R).map (fun j => cols.map (fun c => c.getD j 0))

/-- 转置行长 = 行数。 -/
theorem rowsFromCols_length (cols : List (List Int)) (R : Nat) :
    (rowsFromCols cols R).length = R := by
  simp [rowsFromCols]

/-- 转置单行定位：j < R 时第 j 行 = 各列第 j 项的映像行。 -/
theorem rowsFromCols_getD_row (cols : List (List Int)) (R j : Nat) (hj : j < R) :
    (rowsFromCols cols R).getD j [] = cols.map (fun c => c.getD j 0) := by
  unfold rowsFromCols
  exact map_range_getD [] R (fun k => cols.map (fun c => c.getD k 0)) j hj

/-- 转置取项：第 j 行第 i 项 = 第 i 列第 j 项（双双在界；转置的逐点
恒等式）。 -/
theorem rowsFromCols_getD (cols : List (List Int)) (R j i : Nat) (hj : j < R)
    (hi : i < cols.length) :
    ((rowsFromCols cols R).getD j []).getD i 0 = (cols.getD i []).getD j 0 := by
  rw [rowsFromCols_getD_row cols R j hj,
    map_getD (fun c : List Int => c.getD j 0) 0 [] cols i hi]

/-! ## §3 乘子加权求和的函数化对账（结构递归逐点镜像） -/

/-- 函数形列乘加 `∑_j mⱼ · f j`（f 随归纳右移；与 `coreColDot` 同一
成对直读结构）。 -/
private def colDotF (f : Nat → Int) : List Nat → Int
  | [] => 0
  | m :: ms => f 0 * (m : Int) + colDotF (fun j => f (j + 1)) ms

/-- 零函数求和为零（越界读 0 的对账终点）。 -/
private theorem colDotF_zero : ∀ ms : List Nat, colDotF (fun _ : Nat => (0 : Int)) ms = 0
  | [] => rfl
  | _ :: ms => by simpa [colDotF] using colDotF_zero ms

/-- 函数形与内核列乘加逐点相同（`a` 逐位取项）。 -/
private theorem coreColDot_eq_colDotF (a : List Int) :
    ∀ (ms : List Nat), coreColDot a ms = colDotF (fun j => a.getD j 0) ms
  | [] => by cases a <;> rfl
  | m :: ms => by
      cases a with
      | nil => exact (colDotF_zero (m :: ms)).symm
      | cons x xs =>
          simp only [coreColDot, colDotF, getD_cons_zero', getD_cons_succ']
          rw [coreColDot_eq_colDotF xs ms]

/-- 函数形右移同余：两函数在 `j < ms.length` 上逐点相等则求和相等。 -/
private theorem colDotF_congr (f g : Nat → Int) :
    ∀ (ms : List Nat), (∀ j < ms.length, f j = g j) → colDotF f ms = colDotF g ms
  | [], _ => rfl
  | m :: ms, h => by
      have h0 : f 0 = g 0 := h 0 (by simp)
      have h1 : ∀ j < ms.length, f (j + 1) = g (j + 1) :=
        fun j hj => h (j + 1) (by simpa using hj)
      simp only [colDotF, h0]
      rw [colDotF_congr (fun j => f (j + 1)) (fun j => g (j + 1)) ms h1]

/-- 内核行主序列和 = 函数形乘加（行表长 = 乘子表长时成对直读对账）。 -/
private theorem coreColSum_eq_colDotF :
    ∀ (ms : List Nat) (rows : List (List Int)) (i : Nat), rows.length = ms.length →
      coreColSum rows ms i = colDotF (fun j => (rows.getD j []).getD i 0) ms
  | [], rows, _, h => by
      cases rows with
      | nil => rfl
      | cons r rs => simp at h
  | m :: ms, rows, i, h => by
      cases rows with
      | nil => simp at h
      | cons r rs =>
          simp only [coreColSum, colDotF, getD_cons_zero', getD_cons_succ']
          have hms : rs.length = ms.length := by
            simp only [List.length_cons] at h
            omega
          rw [coreColSum_eq_colDotF ms rs i hms]

/-! ## §4 换向主件 -/

/-- **列主序列和桥**：转置行表上跑行主序每列求和 = 列主序同列一趟乘加
（逐点同数学量；任一侧越界读 0，两侧同落 0）。 -/
theorem coreColSum_rowsFromCols (cols : List (List Int)) (R : Nat) (ms : List Nat) (i : Nat)
    (hms : ms.length = R) :
    coreColSum (rowsFromCols cols R) ms i = coreColSumCol cols ms i := by
  rw [coreColSum_eq_colDotF ms _ i (by rw [hms, rowsFromCols_length])]
  simp only [coreColSumCol, coreColDot_eq_colDotF]
  refine colDotF_congr _ _ ms fun j hj => ?_
  have hjR : j < R := by omega
  by_cases hi : i < cols.length
  · rw [rowsFromCols_getD cols R j i hjR hi]
  · rw [rowsFromCols_getD_row cols R j hjR,
      map_getD_of_le (fun c : List Int => c.getD j 0) 0 cols i (by omega)]
    have hget : cols.getD i [] = [] := by
      cases cols with
      | nil => rfl
      | cons c cs =>
          cases i with
          | zero => simp at hi
          | succ k =>
              have hk : cs.length ≤ k := by
                simp only [List.length_cons] at hi
                omega
              simpa using map_getD_of_le id [] cs k hk
    rw [hget]
    rfl

/-- 转置行主序核形状良好（三表平行 + 每行长 = 列数）。 -/
theorem coreShape_rowsFromCols (cols : List (List Int)) (rhs : List Int) (ms : List Nat)
    (n : Nat) (hc : cols.length = n) (hms : ms.length = rhs.length) :
    coreShape ⟨n, rowsFromCols cols rhs.length, rhs, ms⟩ = true := by
  have hlen : (rowsFromCols cols rhs.length).length = rhs.length := by
    rw [rowsFromCols_length]
  have hall : (rowsFromCols cols rhs.length).all (fun r => r.length == n) = true := by
    refine List.all_eq_true.mpr fun r hr => ?_
    obtain ⟨j, -, hrj⟩ := List.mem_map.mp hr
    subst hrj
    simp [List.length_map, hc]
  simp only [coreShape, hlen]
  exact Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨beq_self_eq_true _, beq_iff_eq.mpr hms.symm⟩, hall⟩

/-- **列→行桥（主件）**：列主序 checker 通过 ⟹ 转置行主序核 checker
通过。行主序核只经本桥闭合，不经行主序 decide（C1.7 B086/B087 实测
巨物行主序求值 = 内存陷阱；本件纯 List 结构归纳，与数据体量无关）。 -/
theorem farkasCheck_rowsFromCols (n : Nat) (cols : List (List Int)) (rhs : List Int)
    (ms : List Nat) (h : farkasCheckCol ⟨n, cols, rhs, ms⟩ = true) :
    farkasCheck ⟨n, rowsFromCols cols rhs.length, rhs, ms⟩ = true := by
  simp only [farkasCheckCol, coreShapeCol, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, beq_iff_eq, List.mem_range] at h
  obtain ⟨⟨⟨hcols, hparallel⟩, -⟩, hcolsum⟩ := h.1
  have hrhs := h.2
  have hshape := coreShape_rowsFromCols cols rhs ms n hcols hparallel.symm
  have hall' : (List.range n).all
      (fun x => coreColSum (rowsFromCols cols rhs.length) ms x == 0) = true := by
    rw [List.all_eq_true]
    intro i hi
    simp only [List.mem_range] at hi
    rw [coreColSum_rowsFromCols cols rhs.length ms i hparallel.symm, hcolsum i hi]
    rfl
  exact Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨hshape, hall'⟩, decide_eq_true_eq.mpr hrhs⟩

/-- 列主序核的**行主序像**（转置重建；闭叶见证的唯一合法行主序核来源
——巨物行主序 decide 不在此路径）。 -/
def rowCoreOf (d : LpFarkasCoreCol) : LpFarkasCore :=
  ⟨d.nvars, rowsFromCols d.cols d.rhs.length, d.rhs, d.mults⟩

/-- **闭叶转发件**：`rowCoreOf` 的行主序 checker 由列检查经桥直推
（叶闭合形 `⟨rowCoreOf core, farkasCheck_rowCoreOf core core_farkasCheck⟩`）。 -/
theorem farkasCheck_rowCoreOf (d : LpFarkasCoreCol) (h : farkasCheckCol d = true) :
    farkasCheck (rowCoreOf d) = true :=
  farkasCheck_rowsFromCols _ _ _ _ h

end Kepler.Text.LP
