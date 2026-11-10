/-
  Kepler.Text.TameSpine.Reduction3NcvibwuIndexFirst — NCVIBWU index 半：义务 ① 落机器。
  `idxOf_append_seg`（段位：B 的第 i 元在 P++B++S 的位置 = |P|+i）+
  `indexf_seg`（共享 Nodup 段 ⇒ 两表 `indexf` 相等，= `B.idxOf d - B.idxOf w`）。
  ② ③ ④（B-内偏移归纳 / F-y 位置账 / 拼装）需 betwnTakeDrop 双支 case 分析，
  列下一波（见 DELIVERY_2ncvibwu2 §2）。

  纪律：零禁词；主仓双零写入；既有文件零触碰。
-/
import Kepler.Text.TameSpine.Reduction3NcvibwuGateFirst
import Kepler.Text.TameSpine.JcajyduRed2Trans

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Text.TameLp (getElem_idxOf)

variable {α : Type}

/-- **段位**：`(P ++ B ++ S)` 为 Nodup 时，`B` 的第 i 元在整表的位置 = `|P| + i`。 -/
theorem idxOf_append_seg [BEq α] [LawfulBEq α] [DecidableEq α] {P B S : List α}
    (hs : (P ++ B ++ S).Nodup) {i : ℕ} (hi : i < B.length) :
    (P ++ B ++ S).idxOf (B[i]'hi) = P.length + i := by
  have hmemB : B[i]'hi ∈ B := List.getElem_mem hi
  have hmemPB : B[i]'hi ∈ P ++ B := List.mem_append_right _ hmemB
  have hnd : (P ++ B).Nodup := (List.nodup_append.mp hs).1
  have hdisj : B[i]'hi ∉ P := by
    intro hmemP
    exact ((List.nodup_append.mp hnd).2.2 _ hmemP _ hmemB) rfl
  rw [List.idxOf_append_of_mem (l₁ := P ++ B) (l₂ := S) hmemPB,
    List.idxOf_append_of_notMem (l₁ := P) (l₂ := B) hdisj,
    (List.nodup_append.mp hnd).2.1.idxOf_getElem (i := i) hi]

/-- 单侧：`indexf w d (P ++ B ++ S) = B.idxOf d - B.idxOf w`（w,d ∈ B，Nodup，不绕回）。 -/
theorem indexf_seg_side [BEq α] [LawfulBEq α] [DecidableEq α] {P B S : List α}
    (hnd : (P ++ B ++ S).Nodup) (hB : B.Nodup) {w d : α}
    (hw : w ∈ B) (hd : d ∈ B) (hwd : B.idxOf w ≤ B.idxOf d) :
    indexf w d (P ++ B ++ S) = B.idxOf d - B.idxOf w := by
  have hbw : B.idxOf w < B.length := List.idxOf_lt_length_iff.mpr hw
  have hbd : B.idxOf d < B.length := List.idxOf_lt_length_iff.mpr hd
  have hposw : (P ++ B ++ S).idxOf w = P.length + B.idxOf w :=
    (congrArg (fun e => (P ++ B ++ S).idxOf e) (getElem_idxOf hw)).symm.trans
      (idxOf_append_seg (P := P) (B := B) (S := S) hnd hbw)
  have hposd : (P ++ B ++ S).idxOf d = P.length + B.idxOf d :=
    (congrArg (fun e => (P ++ B ++ S).idxOf e) (getElem_idxOf hd)).symm.trans
      (idxOf_append_seg (P := P) (B := B) (S := S) hnd hbd)
  have hmemw : w ∈ P ++ B ++ S := by
    rw [List.mem_append, List.mem_append]; exact Or.inl (Or.inr hw)
  have hmemd : d ∈ P ++ B ++ S := by
    rw [List.mem_append, List.mem_append]; exact Or.inl (Or.inr hd)
  rw [indexf, if_pos ⟨hmemw, hmemd⟩, hposd, hposw]
  have hlen : (P ++ B ++ S).length = P.length + B.length + S.length := by
    rw [List.length_append, List.length_append]
  rw [hlen]
  have hsub : P.length + B.length + S.length - (P.length + B.idxOf w)
      = B.length + S.length - B.idxOf w := by omega
  rw [hsub]
  have hsplit : (P.length + B.idxOf d) + (B.length + S.length - B.idxOf w)
      = (B.idxOf d - B.idxOf w) + (P.length + (B.length + S.length)) := by omega
  rw [hsplit, show P.length + (B.length + S.length)
      = P.length + B.length + S.length from by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

/-- **义务 ①**：两表共享同一 Nodup 段 `B`（前后缀任意、两表各自 Nodup）且
`w,d ∈ B`、不绕回 ⇒ `indexf w d` 两表相等。 -/
theorem indexf_seg [BEq α] [LawfulBEq α] [DecidableEq α] {P₁ P₂ B S₁ S₂ : List α}
    (hnd1 : (P₁ ++ B ++ S₁).Nodup) (hnd2 : (P₂ ++ B ++ S₂).Nodup)
    (hB : B.Nodup) {w d : α} (hw : w ∈ B) (hd : d ∈ B)
    (hwd : B.idxOf w ≤ B.idxOf d) :
    indexf w d (P₁ ++ B ++ S₁) = indexf w d (P₂ ++ B ++ S₂) := by
  rw [indexf_seg_side hnd1 hB hw hd hwd, indexf_seg_side hnd2 hB hw hd hwd]

end Kepler.Text.TameSpine

-- 公理探针（编译即执行；目标：标准三，零未证占位）
#print axioms Kepler.Text.TameSpine.idxOf_append_seg
#print axioms Kepler.Text.TameSpine.indexf_seg_side
#print axioms Kepler.Text.TameSpine.indexf_seg
