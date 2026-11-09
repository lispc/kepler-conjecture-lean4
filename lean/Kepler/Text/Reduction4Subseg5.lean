/-
  Kepler.Text.Reduction4Subseg5 — J 战役 J1 板 F2（`parts_cat` + `core_cat`，岛内自证路线 A）。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/`）──
  │ tame_list.hl:6164 `partition_into_atom0r_cat` → 私有分解链（本文件 §1）
  │ tame_list.hl:6253 `parts_cat`                 → parts_cat
  │ reduction4.hl:3844 `core_cat`                 → core_cat
  └────────────────────────────────────────────────────────────────

  ┌─ 路线（编排者裁定 A：岛内自证，零 TameSpine）──────────────────
  │ `partitionIntoAtom0` 只按「当前 atom 头」`a.headD r` 与来元的键比较，
  │ 故处理 `p ++ q` = 先处理 p、再以 p 的末态为初态处理 q。三层私有件：
  │   ① `pia0_append`（fold：处理 p++q = 先 p 后 q，acc 任意）
  │   ② `pia0_seed`（初态为 `a :: tail` 时，结果 = 以 `[a]` 为初态的结果 ++ tail）
  │   ③ `pia0_spill`（切口断裂 ⇒ 结果 = 从空初态算起 ++ 原初态）
  │   ④ `pia0_atomHead`（末态头 atom 的头 = 输入表末元）
  │ 再用 `nextEl_append_getLast`（`next_el (u++v) (LAST u) = HD v`）把 HOL 的
  │ 切口条件 `~(next_el r x = n x)` 翻成 `n x ≠ HD v`，投 `pia0_spill` 收口。
  │ 该路线**不引入任何 TameSpine 模块**（Reduction5 岛闭包不变量保持）。
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide；本文件全具体载体
  （`Dart = ℕ × ℕ`，无泛型 binder ⇒ 实例烘焙唯一）。
-/

import Kepler.Text.Reduction4Subseg4
import Kepler.Text.Reduction4Subseg

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction4Idx

open Kepler.Graphs (fgraph)
open Kepler.Assembly (nextEl fList eList)
open Kepler.Text.Reduction5 (Dart parts core partitionIntoAtom partitionIntoAtom0
  partitionIntoAtom0r)

/-! ## §0 小件（`getLast!` / `head!` 互译） -/

/-- `getLast! l = l.getLastD default`（`getLast!` 是按构造子定义的，对变量不直接归约）。 -/
private theorem getLast!_eq_getLastD (l : List Dart) :
    l.getLast! = l.getLastD (default : Dart) := by
  cases l with
  | nil => rfl
  | cons a as => rw [List.getLast!_cons_eq_getLastD, List.getLastD_cons]

/-- `getLast!` 的 `concat` 形（任意缺省元）。 -/
private theorem getLast!_concat (l : List Dart) (a : Dart) : (l ++ [a]).getLast! = a := by
  rw [getLast!_eq_getLastD]
  exact List.getLastD_concat

/-- `head! (l.reverse) = l.getLast!`。 -/
private theorem head!_reverse (l : List Dart) : l.reverse.head! = l.getLast! := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    cases as with
    | nil => rfl
    | cons b bs =>
      rw [List.reverse_cons, List.head!_append _ (by simp), ih]
      simp only [List.getLast!_cons_eq_getLastD, List.getLastD_cons]

/-- `(l.reverse).getLast! = l.head!`。 -/
private theorem getLast!_reverse (l : List Dart) : l.reverse.getLast! = l.head! := by
  rw [← head!_reverse l.reverse, List.reverse_reverse]

/-- `l[0] = l.head!`（非空）。 -/
private theorem getElem_zero_eq_head! {l : List Dart} (h : 0 < l.length) :
    l[0]'(h) = l.head! := by
  cases l with
  | nil => simp at h
  | cons a as => rfl

/-- `headD` 与 `head!` 在非空表上同值（`head!` 与 `headD` 对变量都卡住，故需此桥）。 -/
private theorem headD_eq_head! {l : List Dart} (h : l ≠ []) (d : Dart) :
    l.headD d = l.head! := by
  obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil h
  rfl

/-! ## §1 `partitionIntoAtom0` 分解链（HOL `partition_into_atom0r_cat` 的 Lean 版内核） -/

section Pia0

variable (n : Dart → Dart)

/-- `P n acc l` 在 `l ≠ []` 时非空。 -/
private theorem pia0_ne_nil :
    ∀ (l : List Dart) (acc : List (List Dart)), l ≠ [] → partitionIntoAtom0 n acc l ≠ [] := by
  intro l
  induction l with
  | nil => intro acc hl; exact absurd rfl hl
  | cons r rs ih =>
    intro acc hl
    cases rs with
    | nil =>
      cases acc with
      | nil => rw [partitionIntoAtom0.eq_2, partitionIntoAtom0.eq_1]; simp
      | cons a acc' =>
        rw [partitionIntoAtom0.eq_3]
        by_cases h : (n r == a.headD r) = true
        · rw [if_pos h, partitionIntoAtom0.eq_1]; simp
        · rw [if_neg h, partitionIntoAtom0.eq_1]; simp
    | cons q qs =>
      cases acc with
      | nil =>
        rw [partitionIntoAtom0.eq_2]
        exact ih [[r]] (by simp)
      | cons a acc' =>
        rw [partitionIntoAtom0.eq_3]
        by_cases h : (n r == a.headD r) = true
        · rw [if_pos h]; exact ih ((r :: a) :: acc') (by simp)
        · rw [if_neg h]; exact ih ([r] :: a :: acc') (by simp)

/-- **fold**：处理 `p ++ q` = 先处理 `p`、再以 `p` 的末态为初态处理 `q`。 -/
private theorem pia0_append (p q : List Dart) :
    ∀ acc : List (List Dart),
      partitionIntoAtom0 n acc (p ++ q)
        = partitionIntoAtom0 n (partitionIntoAtom0 n acc p) q := by
  induction p with
  | nil => intro acc; rw [List.nil_append, partitionIntoAtom0.eq_1]
  | cons r rs ih =>
    intro acc
    cases acc with
    | nil =>
      rw [List.cons_append, partitionIntoAtom0.eq_2, partitionIntoAtom0.eq_2]
      exact ih [[r]]
    | cons a acc' =>
      rw [List.cons_append, partitionIntoAtom0.eq_3, partitionIntoAtom0.eq_3]
      by_cases h : (n r == a.headD r) = true
      · rw [if_pos h, if_pos h]
        exact ih ((r :: a) :: acc')
      · rw [if_neg h, if_neg h]
        exact ih ([r] :: a :: acc')

/-- **seed**：初态 `a :: tail` 的尾部 `tail` 只是被原样搬到结果末尾。 -/
private theorem pia0_seed (rs : List Dart) :
    ∀ (a : List Dart) (tail : List (List Dart)),
      partitionIntoAtom0 n (a :: tail) rs = partitionIntoAtom0 n [a] rs ++ tail := by
  induction rs with
  | nil =>
    intro a tail
    rw [partitionIntoAtom0.eq_1, partitionIntoAtom0.eq_1]
    rfl
  | cons r rs ih =>
    intro a tail
    rw [partitionIntoAtom0.eq_3, partitionIntoAtom0.eq_3]
    by_cases h : (n r == a.headD r) = true
    · rw [if_pos h, if_pos h, ih (r :: a) tail]
    · rw [if_neg h, if_neg h, ih [r] (a :: tail), ih [r] (a :: []), List.append_assoc]
      rfl

/-- **spill**：切口断裂（来元键 ≠ 当前 atom 头键）⇒ 结果 = 从空初态算起 ++ 原初态。 -/
private theorem pia0_spill {a : List Dart} {r : Dart} {rs : List Dart}
    {tail : List (List Dart)} (hbrk : (n r == a.headD r) = false) :
    partitionIntoAtom0 n (a :: tail) (r :: rs)
      = partitionIntoAtom0 n [] (r :: rs) ++ (a :: tail) := by
  rw [partitionIntoAtom0.eq_3, if_neg (by rw [hbrk]; simp),
    pia0_seed n rs [r] (a :: tail), partitionIntoAtom0.eq_2]

/-- **atomHead**：输入非空时，末态头 atom 的头 = 输入表末元。 -/
private theorem pia0_atomHead (l : List Dart) :
    ∀ (acc : List (List Dart)) (d : Dart), l ≠ [] →
      ((partitionIntoAtom0 n acc l).headD []).headD d = l.getLast! := by
  induction l with
  | nil => intro acc d hl; exact absurd rfl hl
  | cons r rs ih =>
    intro acc d hl
    rw [List.getLast!_cons_eq_getLastD]
    cases rs with
    | nil =>
      cases acc with
      | nil => rw [partitionIntoAtom0.eq_2, partitionIntoAtom0.eq_1]; rfl
      | cons a acc' =>
        rw [partitionIntoAtom0.eq_3]
        by_cases h : (n r == a.headD r) = true
        · rw [if_pos h, partitionIntoAtom0.eq_1]; rfl
        · rw [if_neg h, partitionIntoAtom0.eq_1]; rfl
    | cons q qs =>
      rw [List.getLastD_cons]
      cases acc with
      | nil =>
        rw [partitionIntoAtom0.eq_2]
        rw [ih [[r]] d (by simp), List.getLast!_cons_eq_getLastD]
      | cons a acc' =>
        rw [partitionIntoAtom0.eq_3]
        by_cases h : (n r == a.headD r) = true
        · rw [if_pos h]
          rw [ih ((r :: a) :: acc') d (by simp), List.getLast!_cons_eq_getLastD]
        · rw [if_neg h]
          rw [ih ([r] :: a :: acc') d (by simp), List.getLast!_cons_eq_getLastD]

end Pia0

/-! ## §2 切口件：`next_el (u ++ v) (LAST u) = HD v` -/

/-- **HOL 的 `LAST_cat` / `next_el_cat` 切口形**（`u`、`v` 非空、`u ++ v` 无重）：
`u.getLast!` 在 `u ++ v` 中的环上后继 = `v.head!`。 -/
private theorem nextEl_append_getLast {u v : List Dart} (hu : u ≠ []) (hv : v ≠ [])
    (hnd : (u ++ v).Nodup) : nextEl (u ++ v) u.getLast! = v.head! := by
  have hndu : u.Nodup := (List.nodup_append.mp hnd).1
  have hpos : 0 < u.length := List.length_pos_of_ne_nil hu
  have hlen : u.length < (u ++ v).length := by
    rw [List.length_append]
    have hvpos : 0 < v.length := List.length_pos_of_ne_nil hv
    omega
  have hgl : u.getLast! = u[u.length - 1]'(by omega) := by
    rw [getLast!_eq_getLastD]
    exact Kepler.Text.TameLp.getLastD_eq_getElem_last hpos (default : Dart)
  have hxmem : u.getLast! ∈ u := by
    rw [hgl]
    exact List.getElem_mem (by omega)
  have hidx_u : u.idxOf u.getLast! = u.length - 1 := by
    rw [hgl, Kepler.Text.TameLp.idxOf_getElem hndu (by omega)]
  have hidx : (u ++ v).idxOf u.getLast! = u.length - 1 := by
    rw [List.idxOf_append_of_mem hxmem, hidx_u]
  have hxmem' : u.getLast! ∈ u ++ v := List.mem_append_left _ hxmem
  rw [Kepler.Text.TameLp.nextEl_eq_getD hxmem', hidx]
  have hmod : (u.length - 1 + 1) % (u ++ v).length = u.length := by
    have h0 : u.length - 1 + 1 = u.length := by omega
    rw [h0, Nat.mod_eq_of_lt hlen]
  rw [hmod, Kepler.Text.TameLp.getD_eq_getElem_of_lt hlen,
    List.getElem_append_right (by omega : u.length ≤ u.length)]
  simp only [Nat.sub_self]
  exact getElem_zero_eq_head! (List.length_pos_of_ne_nil hv)

/-! ## §3 `parts_cat`（tame_list.hl:6253） -/

/-- **HOL `parts_cat`**（tame_list.hl:6253-6269）：
`r = cat u v`、`LAST u = x`、`u ≠ []`、`v ≠ []`、
`~(next_el r x = f_list L (e_list x))`、`uniq r`
⇒ `parts L r = cat (parts L u) (parts L v)`。

路线：`parts L r = P n [] r.reverse`（`P = partitionIntoAtom0`，`n = fList L ∘ eList`），
`(u ++ v).reverse = v.reverse ++ u.reverse`；`pia0_append` 先 fold 出
`P n (P n [] v.reverse) u.reverse`，再由 `nextEl_append_getLast` +
`pia0_atomHead` 把 HOL 的切口条件翻成 `n x ≠ HD v`（= 切口断裂），
`pia0_spill` 拆成 `P n [] u.reverse ++ P n [] v.reverse`。 -/
theorem parts_cat (L : fgraph ℕ) {u v : List Dart} {x : Dart}
    (hxr : x ∈ u ++ v) (hbrk : nextEl (u ++ v) x ≠ fList L (eList x))
    (hx : u.getLast! = x) (hu : u ≠ []) (hv : v ≠ []) (hnd : (u ++ v).Nodup) :
    parts L (u ++ v) = parts L u ++ parts L v := by
  -- 切口：`next_el (u++v) x = HD v`，故 `n x ≠ HD v`
  have hjunc : nextEl (u ++ v) x = v.head! := by
    rw [← hx]
    exact nextEl_append_getLast hu hv hnd
  have hvne : fList L (eList x) ≠ v.head! := by
    intro h
    exact hbrk (hjunc.trans h.symm)
  have hbeq : (fList L (eList x) == v.head!) = false := beq_eq_false_iff_ne.mpr hvne
  -- `u.reverse = x :: rest`
  have hune : u.reverse ≠ [] := by simpa using hu
  obtain ⟨y, rest, hrev⟩ := List.exists_cons_of_ne_nil hune
  have hy : y = x := by
    have h1 : u.reverse.head! = y := by rw [hrev]; rfl
    rw [← h1, head!_reverse, hx]
  rw [hy] at hrev
  -- 末态初态非空，取头 atom
  have haccne : Kepler.Text.Reduction5.partitionIntoAtom0 (fun d => fList L (eList d)) []
      v.reverse ≠ [] := pia0_ne_nil (fun d => fList L (eList d)) v.reverse [] (by simpa using hv)
  obtain ⟨Ahd, Atail, hA⟩ := List.exists_cons_of_ne_nil haccne
  -- 头 atom 的头 = `v.head!`
  have hAhd : Ahd.headD x = v.head! := by
    have h2 := pia0_atomHead (fun d => fList L (eList d)) v.reverse [] x (by simpa using hv)
    rw [hA] at h2
    rw [show (Ahd :: Atail).headD ([] : List Dart) = Ahd from rfl] at h2
    rw [getLast!_reverse] at h2
    exact h2
  have hbrk' : (fList L (eList x) == Ahd.headD x) = false := by
    rw [hAhd]
    exact hbeq
  -- 主链
  have hstep1 := pia0_append (fun d => fList L (eList d)) v.reverse u.reverse []
  have hstep2 : partitionIntoAtom0 (fun d => fList L (eList d))
      (partitionIntoAtom0 (fun d => fList L (eList d)) [] v.reverse) u.reverse
      = partitionIntoAtom0 (fun d => fList L (eList d)) [] u.reverse
        ++ partitionIntoAtom0 (fun d => fList L (eList d)) [] v.reverse := by
    rw [hrev, hA]
    exact pia0_spill (fun d => fList L (eList d)) hbrk'
  show (parts L (u ++ v)) = parts L u ++ parts L v
  unfold parts partitionIntoAtom
  rw [List.reverse_append, hstep1, hstep2]

/-! ## §4 `core_cat`（reduction4.hl:3844） -/

/-- **HOL `core_cat`**（reduction4.hl:3844）：
`uniq (cat u v)`、`u ≠ []`、`~(next_el (cat u v) (LAST u) = f_list L (e_list (LAST u)))`
⇒ `core L (cat u v) = cat (core L u) (core L v)`。

路线：`v = []` 走 `core_nil`；否则 `core = map (FST ∘ HD)` 对 `parts_cat` 分配
（`List.map_append`）。 -/
theorem core_cat (L : fgraph ℕ) {u v : List Dart} (hnd : (u ++ v).Nodup) (hu : u ≠ [])
    (hbrk : nextEl (u ++ v) (u.getLast!) ≠ fList L (eList (u.getLast!))) :
    core L (u ++ v) = core L u ++ core L v := by
  by_cases hv : v = []
  · subst hv
    rw [List.append_nil, coreNil, List.append_nil]
  · have hxr : u.getLast! ∈ u ++ v := by
      have hune : u ≠ [] := hu
      have hpos : 0 < u.length := List.length_pos_of_ne_nil hune
      have hgl : u.getLast! = u[u.length - 1]'(by omega) := by
        rw [getLast!_eq_getLastD]
        exact Kepler.Text.TameLp.getLastD_eq_getElem_last hpos (default : Dart)
      rw [hgl]
      exact List.mem_append_left _ (List.getElem_mem (by omega))
    show (parts L (u ++ v)).map (fun l => (l.headD (0, 0)).1)
      = (parts L u).map (fun l => (l.headD (0, 0)).1)
        ++ (parts L v).map (fun l => (l.headD (0, 0)).1)
    rw [parts_cat L hxr hbrk rfl hu hv hnd, List.map_append]

end Kepler.Text.Reduction4Idx

/-! 公理审计锚（本文件编译即执行；预期 ≤ 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.Reduction4Idx.parts_cat
#print axioms Kepler.Text.Reduction4Idx.core_cat
