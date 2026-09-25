import Kepler.Interval.Cases.C549Mono
import Kepler.Interval.Cases.C549CertSlimDefs


/-! ## 549 facePos 全量评估（emit_mono.py 生成；勿手改）。

C549MonoBatch17 — rung 128（发射钉死） shard 17/53（20 叶；modes ['then']）
每叶：面叶 + 导数叶 + DerivSafeOn 证书叶 ⇒ 嵌套 DSafe ⇒
checkPosFace*_sound ⇒ 全盒语义正性 0 < evalReal ρ。
本模块层级：['cert', 'der', 'face', 'fold']；decide 战术：decide。 -/


set_option maxHeartbeats 0
set_option maxRecDepth 1000000


namespace Kepler.Interval.C549MonoBatch17

open Kepler.Interval


/-- case 549 表达式（本模块自包含副本）. -/

def E549 : IExpr 6 :=
  (.sub (.div (.const ⟨1893, 0⟩) (.const ⟨1000, 0⟩) (-64)) (.add (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.const ⟨2, 0⟩) (-64)) (.ite (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) (.trans .arctanK (.div (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0) (-64)) 128 (-80)) (.ite (.sub (.const ⟨0, 0⟩) (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sub (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.const ⟨2, 0⟩) (-64)) (.trans .arctanK (.div (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0) (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) (-64)) 128 (-80))) (.ite (.sub (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) (.const ⟨0, 0⟩)) (.sub (.neg (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.const ⟨2, 0⟩) (-64))) (.trans .arctanK (.div (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0) (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) (-64)) 128 (-80))) (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))))))))

/-- 叶 59623（then 支，lo 面）原盒. -/

def B59623 : Fin 6 → DInterval :=
  ![⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩]

/-- 证书叶 59623.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S59623C0P : TMParams :=
  ⟨[⟨251878049815265964014883689953579807384617, 68850918456183022448275755092049701870781, 0, (-80), (-80)⟩], [], []⟩

theorem S59623C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B59623 S59623C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 59623.C0. -/

theorem S59623D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B59623 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S59623C0 ρ hρ

/-- 证书叶 59623.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S59623C1P : TMParams :=
  ⟨[⟨251878049815265964014883689953579807384617, 68850918456183022448275755092049701870781, 0, (-80), (-80)⟩], [], []⟩

theorem S59623C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B59623 S59623C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 59623.C1. -/

theorem S59623D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B59623 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S59623C1 ρ hρ

/-- 证书叶 59623.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S59623C2P : TMParams :=
  ⟨[], [], []⟩

theorem S59623C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B59623 S59623C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 59623.C2. -/

theorem S59623D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B59623 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S59623C2 ρ hρ

/-- 导数叶 59623（+∂x3f，then 支，全盒）. -/

def DP59623 : TMParams :=
  ⟨[⟨6747862877632628952418403917683187545144192, 6747862877632628952418403917683187545144192, 816595469778217410784842878819099475721992863734, (-80), (-80)⟩, ⟨6747862877632628952418403917683187545144192, 6747862877632628952418403917683187545144192, 816595469778217410784842878819099475721992863734, (-80), (-80)⟩, ⟨6747862877632628952418403917683187545144192, 6747862877632628952418403917683187545144192, 816595469778217410784842878819099475721992863734, (-80), (-80)⟩, ⟨6747862877632628952418403917683187545144192, 6747862877632628952418403917683187545144192, 816595469778217410784842878819099475721992863734, (-80), (-80)⟩, ⟨6747862877632628952418403917683187545144192, 6747862877632628952418403917683187545144192, 816595469778217410784842878819099475721992863734, (-80), (-80)⟩, ⟨6747862877632628952418403917683187545144192, 6747862877632628952418403917683187545144192, 816595469778217410784842878819099475721992863734, (-80), (-80)⟩, ⟨6747862877632628952418403917683187545144192, 6747862877632628952418403917683187545144192, 816595469778217410784842878819099475721992863734, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der59623 :
    checkPosTMHull (derivIExpr E549 2) B59623 DP59623
    = true := by
  decide

/-- 面叶 59623（lo 面）. -/

def FB59623 : Fin 6 → DInterval := faceBoxLo B59623 2

def PF59623 : TMParams :=
  ⟨[⟨282887666392803091325214505348899843062920, 32976209407516312774888959905130609437502, 0, (-80), (-80)⟩, ⟨6691864939887226122343668187745359799452634, 6691864939887226122343668187745359799452634, 822023948775246988772766025937351834489812938095, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face59623 :
    checkPosTMHull E549 FB59623 PF59623
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 59623，then 支）. -/

def DSafe59623 : DerivSafeOn B59623 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S59623D2) S59623D1) (Or.inr (Or.inr rfl))) S59623D0)))

/-- mono 折叠组合（叶 59623，两叶引用零重算）. -/

theorem Fold59623 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B59623 2 PF59623 DP59623 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B59623 DP59623 = true := Der59623
  have h2 : checkPosTMHull E549 (faceBoxLo B59623 2) PF59623 = true := Face59623
  show (checkPosTMHull (derivIExpr E549 2) B59623 DP59623
      && checkPosTMHull E549 (faceBoxLo B59623 2) PF59623) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 59623）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem59623 (ρ : Fin 6 → ℝ) (hρ : boxMem B59623 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe59623 Fold59623 hρ

#print axioms Sem59623

/-- 叶 59775（then 支，lo 面）原盒. -/

def B59775 : Fin 6 → DInterval :=
  ![⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨9148280341, -32⟩, ⟨4853313045, -31⟩⟩]

/-- 证书叶 59775.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S59775C0P : TMParams :=
  ⟨[⟨94551873472008100936717896525731440874985, 71838221516254321557251500892587678281815, 0, (-80), (-80)⟩], [], []⟩

theorem S59775C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B59775 S59775C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 59775.C0. -/

theorem S59775D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B59775 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S59775C0 ρ hρ

/-- 证书叶 59775.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S59775C1P : TMParams :=
  ⟨[⟨94551873472008100936717896525731440874985, 71838221516254321557251500892587678281815, 0, (-80), (-80)⟩], [], []⟩

theorem S59775C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B59775 S59775C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 59775.C1. -/

theorem S59775D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B59775 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S59775C1 ρ hρ

/-- 证书叶 59775.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S59775C2P : TMParams :=
  ⟨[], [], []⟩

theorem S59775C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B59775 S59775C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 59775.C2. -/

theorem S59775D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B59775 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S59775C2 ρ hρ

/-- 导数叶 59775（+∂x3f，then 支，全盒）. -/

def DP59775 : TMParams :=
  ⟨[⟨6703721866853984818651811398960785986368031, 6703721866853984818651811398960785986368031, 793435914716114277531686290733260217821852609228, (-80), (-80)⟩, ⟨6703721866853984818651811398960785986368031, 6703721866853984818651811398960785986368031, 793435914716114277531686290733260217821852609228, (-80), (-80)⟩, ⟨6703721866853984818651811398960785986368031, 6703721866853984818651811398960785986368031, 793435914716114277531686290733260217821852609228, (-80), (-80)⟩, ⟨6703721866853984818651811398960785986368031, 6703721866853984818651811398960785986368031, 793435914716114277531686290733260217821852609228, (-80), (-80)⟩, ⟨6703721866853984818651811398960785986368031, 6703721866853984818651811398960785986368031, 793435914716114277531686290733260217821852609228, (-80), (-80)⟩, ⟨6703721866853984818651811398960785986368031, 6703721866853984818651811398960785986368031, 793435914716114277531686290733260217821852609228, (-80), (-80)⟩, ⟨6703721866853984818651811398960785986368031, 6703721866853984818651811398960785986368031, 793435914716114277531686290733260217821852609228, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der59775 :
    checkPosTMHull (derivIExpr E549 2) B59775 DP59775
    = true := by
  decide

/-- 面叶 59775（lo 面）. -/

def FB59775 : Fin 6 → DInterval := faceBoxLo B59775 2

def PF59775 : TMParams :=
  ⟨[⟨115954043282844577761190252089532427099145, 34409813785131682376002897663489481543257, 0, (-80), (-80)⟩, ⟨6649488144669905316499393192354569958687106, 6649488144669905316499393192354569958687106, 800403917710517008140651016876516649549913744578, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face59775 :
    checkPosTMHull E549 FB59775 PF59775
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 59775，then 支）. -/

def DSafe59775 : DerivSafeOn B59775 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S59775D2) S59775D1) (Or.inr (Or.inr rfl))) S59775D0)))

/-- mono 折叠组合（叶 59775，两叶引用零重算）. -/

theorem Fold59775 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B59775 2 PF59775 DP59775 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B59775 DP59775 = true := Der59775
  have h2 : checkPosTMHull E549 (faceBoxLo B59775 2) PF59775 = true := Face59775
  show (checkPosTMHull (derivIExpr E549 2) B59775 DP59775
      && checkPosTMHull E549 (faceBoxLo B59775 2) PF59775) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 59775）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem59775 (ρ : Fin 6 → ℝ) (hρ : boxMem B59775 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe59775 Fold59775 hρ

#print axioms Sem59775

/-- 叶 59927（then 支，lo 面）原盒. -/

def B59927 : Fin 6 → DInterval :=
  ![⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩]

/-- 证书叶 59927.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S59927C0P : TMParams :=
  ⟨[⟨61849376887274746533587469382650522416061, 537684947078241856302170550471227288342384, 0, (-80), (-80)⟩], [], []⟩

theorem S59927C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B59927 S59927C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 59927.C0. -/

theorem S59927D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B59927 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S59927C0 ρ hρ

/-- 证书叶 59927.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S59927C1P : TMParams :=
  ⟨[⟨61849376887274746533587469382650522416061, 537684947078241856302170550471227288342384, 0, (-80), (-80)⟩], [], []⟩

theorem S59927C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B59927 S59927C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 59927.C1. -/

theorem S59927D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B59927 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S59927C1 ρ hρ

/-- 证书叶 59927.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S59927C2P : TMParams :=
  ⟨[], [], []⟩

theorem S59927C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B59927 S59927C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 59927.C2. -/

theorem S59927D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B59927 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S59927C2 ρ hρ

/-- 导数叶 59927（+∂x3f，then 支，全盒）. -/

def DP59927 : TMParams :=
  ⟨[⟨6593570135766559778131606230511785519572974, 6593570135766559778131606230511785519572974, 797764541358778174432389727902426994169589290994, (-80), (-80)⟩, ⟨6593570135766559778131606230511785519572974, 6593570135766559778131606230511785519572974, 797764541358778174432389727902426994169589290994, (-80), (-80)⟩, ⟨6593570135766559778131606230511785519572974, 6593570135766559778131606230511785519572974, 797764541358778174432389727902426994169589290994, (-80), (-80)⟩, ⟨6593570135766559778131606230511785519572974, 6593570135766559778131606230511785519572974, 797764541358778174432389727902426994169589290994, (-80), (-80)⟩, ⟨6593570135766559778131606230511785519572974, 6593570135766559778131606230511785519572974, 797764541358778174432389727902426994169589290994, (-80), (-80)⟩, ⟨6593570135766559778131606230511785519572974, 6593570135766559778131606230511785519572974, 797764541358778174432389727902426994169589290994, (-80), (-80)⟩, ⟨6593570135766559778131606230511785519572974, 6593570135766559778131606230511785519572974, 797764541358778174432389727902426994169589290994, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der59927 :
    checkPosTMHull (derivIExpr E549 2) B59927 DP59927
    = true := by
  decide

/-- 面叶 59927（lo 面）. -/

def FB59927 : Fin 6 → DInterval := faceBoxLo B59927 2

def PF59927 : TMParams :=
  ⟨[⟨69765691272165789311955919625776695148333, 515413266303705014843205613503990413835370, 0, (-80), (-80)⟩, ⟨6550855764974302476212206058713676190062287, 6550855764974302476212206058713676190062287, 802907862598464309950867526149702961380764995321, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face59927 :
    checkPosTMHull E549 FB59927 PF59927
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 59927，then 支）. -/

def DSafe59927 : DerivSafeOn B59927 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S59927D2) S59927D1) (Or.inr (Or.inr rfl))) S59927D0)))

/-- mono 折叠组合（叶 59927，两叶引用零重算）. -/

theorem Fold59927 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B59927 2 PF59927 DP59927 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B59927 DP59927 = true := Der59927
  have h2 : checkPosTMHull E549 (faceBoxLo B59927 2) PF59927 = true := Face59927
  show (checkPosTMHull (derivIExpr E549 2) B59927 DP59927
      && checkPosTMHull E549 (faceBoxLo B59927 2) PF59927) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 59927）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem59927 (ρ : Fin 6 → ℝ) (hρ : boxMem B59927 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe59927 Fold59927 hρ

#print axioms Sem59927

/-- 叶 60079（then 支，lo 面）原盒. -/

def B60079 : Fin 6 → DInterval :=
  ![⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨9148280341, -32⟩, ⟨4853313045, -31⟩⟩]

/-- 证书叶 60079.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S60079C0P : TMParams :=
  ⟨[⟨99312893239211601436647698866902715378075, 72323056349224683521091042209357351044701, 0, (-80), (-80)⟩], [], []⟩

theorem S60079C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B60079 S60079C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 60079.C0. -/

theorem S60079D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B60079 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S60079C0 ρ hρ

/-- 证书叶 60079.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S60079C1P : TMParams :=
  ⟨[⟨99312893239211601436647698866902715378075, 72323056349224683521091042209357351044701, 0, (-80), (-80)⟩], [], []⟩

theorem S60079C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B60079 S60079C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 60079.C1. -/

theorem S60079D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B60079 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S60079C1 ρ hρ

/-- 证书叶 60079.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S60079C2P : TMParams :=
  ⟨[], [], []⟩

theorem S60079C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B60079 S60079C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 60079.C2. -/

theorem S60079D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B60079 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S60079C2 ρ hρ

/-- 导数叶 60079（+∂x3f，then 支，全盒）. -/

def DP60079 : TMParams :=
  ⟨[⟨6782589687587111377534318818690446784198188, 6782589687587111377534318818690446784198188, 803349623233207865111027388786783185184408621872, (-80), (-80)⟩, ⟨6782589687587111377534318818690446784198188, 6782589687587111377534318818690446784198188, 803349623233207865111027388786783185184408621872, (-80), (-80)⟩, ⟨6782589687587111377534318818690446784198188, 6782589687587111377534318818690446784198188, 803349623233207865111027388786783185184408621872, (-80), (-80)⟩, ⟨6782589687587111377534318818690446784198188, 6782589687587111377534318818690446784198188, 803349623233207865111027388786783185184408621872, (-80), (-80)⟩, ⟨6782589687587111377534318818690446784198188, 6782589687587111377534318818690446784198188, 803349623233207865111027388786783185184408621872, (-80), (-80)⟩, ⟨6782589687587111377534318818690446784198188, 6782589687587111377534318818690446784198188, 803349623233207865111027388786783185184408621872, (-80), (-80)⟩, ⟨6782589687587111377534318818690446784198188, 6782589687587111377534318818690446784198188, 803349623233207865111027388786783185184408621872, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der60079 :
    checkPosTMHull (derivIExpr E549 2) B60079 DP60079
    = true := by
  decide

/-- 面叶 60079（lo 面）. -/

def FB60079 : Fin 6 → DInterval := faceBoxLo B60079 2

def PF60079 : TMParams :=
  ⟨[⟨119028532304212994072405452627801248314425, 34640281120830857353122905213764431597123, 0, (-80), (-80)⟩, ⟨6716665886517066205226325504469658567064101, 6716665886517066205226325504469658567064101, 810334115384316162894654660353820709904918821353, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face60079 :
    checkPosTMHull E549 FB60079 PF60079
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 60079，then 支）. -/

def DSafe60079 : DerivSafeOn B60079 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S60079D2) S60079D1) (Or.inr (Or.inr rfl))) S60079D0)))

/-- mono 折叠组合（叶 60079，两叶引用零重算）. -/

theorem Fold60079 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B60079 2 PF60079 DP60079 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B60079 DP60079 = true := Der60079
  have h2 : checkPosTMHull E549 (faceBoxLo B60079 2) PF60079 = true := Face60079
  show (checkPosTMHull (derivIExpr E549 2) B60079 DP60079
      && checkPosTMHull E549 (faceBoxLo B60079 2) PF60079) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 60079）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem60079 (ρ : Fin 6 → ℝ) (hρ : boxMem B60079 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe60079 Fold60079 hρ

#print axioms Sem60079

/-- 叶 60231（then 支，lo 面）原盒. -/

def B60231 : Fin 6 → DInterval :=
  ![⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩]

/-- 证书叶 60231.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S60231C0P : TMParams :=
  ⟨[⟨130423267409741260120940681257875420856076, 549467841518001762509058309198196947791025, 0, (-80), (-80)⟩], [], []⟩

theorem S60231C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B60231 S60231C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 60231.C0. -/

theorem S60231D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B60231 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S60231C0 ρ hρ

/-- 证书叶 60231.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S60231C1P : TMParams :=
  ⟨[⟨130423267409741260120940681257875420856076, 549467841518001762509058309198196947791025, 0, (-80), (-80)⟩], [], []⟩

theorem S60231C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B60231 S60231C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 60231.C1. -/

theorem S60231D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B60231 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S60231C1 ρ hρ

/-- 证书叶 60231.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S60231C2P : TMParams :=
  ⟨[], [], []⟩

theorem S60231C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B60231 S60231C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 60231.C2. -/

theorem S60231D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B60231 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S60231C2 ρ hρ

/-- 导数叶 60231（+∂x3f，then 支，全盒）. -/

def DP60231 : TMParams :=
  ⟨[⟨6779119249760266816253239632154051833699918, 6779119249760266816253239632154051833699918, 821342158531602524211510445512894293210010987507, (-80), (-80)⟩, ⟨6779119249760266816253239632154051833699918, 6779119249760266816253239632154051833699918, 821342158531602524211510445512894293210010987507, (-80), (-80)⟩, ⟨6779119249760266816253239632154051833699918, 6779119249760266816253239632154051833699918, 821342158531602524211510445512894293210010987507, (-80), (-80)⟩, ⟨6779119249760266816253239632154051833699918, 6779119249760266816253239632154051833699918, 821342158531602524211510445512894293210010987507, (-80), (-80)⟩, ⟨6779119249760266816253239632154051833699918, 6779119249760266816253239632154051833699918, 821342158531602524211510445512894293210010987507, (-80), (-80)⟩, ⟨6779119249760266816253239632154051833699918, 6779119249760266816253239632154051833699918, 821342158531602524211510445512894293210010987507, (-80), (-80)⟩, ⟨6779119249760266816253239632154051833699918, 6779119249760266816253239632154051833699918, 821342158531602524211510445512894293210010987507, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der60231 :
    checkPosTMHull (derivIExpr E549 2) B60231 DP60231
    = true := by
  decide

/-- 面叶 60231（lo 面）. -/

def FB60231 : Fin 6 → DInterval := faceBoxLo B60231 2

def PF60231 : TMParams :=
  ⟨[⟨145062142112013279365219736505774743687218, 263585926294955548188953497023818924718186, 0, (-80), (-80)⟩, ⟨6728316634310554482899544996201331118727567, 6728316634310554482899544996201331118727567, 826555434084569202203384604478997825864889630908, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face60231 :
    checkPosTMHull E549 FB60231 PF60231
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 60231，then 支）. -/

def DSafe60231 : DerivSafeOn B60231 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S60231D2) S60231D1) (Or.inr (Or.inr rfl))) S60231D0)))

/-- mono 折叠组合（叶 60231，两叶引用零重算）. -/

theorem Fold60231 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B60231 2 PF60231 DP60231 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B60231 DP60231 = true := Der60231
  have h2 : checkPosTMHull E549 (faceBoxLo B60231 2) PF60231 = true := Face60231
  show (checkPosTMHull (derivIExpr E549 2) B60231 DP60231
      && checkPosTMHull E549 (faceBoxLo B60231 2) PF60231) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 60231）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem60231 (ρ : Fin 6 → ℝ) (hρ : boxMem B60231 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe60231 Fold60231 hρ

#print axioms Sem60231

/-- 叶 60383（then 支，lo 面）原盒. -/

def B60383 : Fin 6 → DInterval :=
  ![⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩]

/-- 证书叶 60383.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S60383C0P : TMParams :=
  ⟨[⟨112002066995007111881793726154289003885331, 506603377015994030259511503270056198293224, 0, (-80), (-80)⟩], [], []⟩

theorem S60383C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B60383 S60383C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 60383.C0. -/

theorem S60383D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B60383 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S60383C0 ρ hρ

/-- 证书叶 60383.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S60383C1P : TMParams :=
  ⟨[⟨112002066995007111881793726154289003885331, 506603377015994030259511503270056198293224, 0, (-80), (-80)⟩], [], []⟩

theorem S60383C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B60383 S60383C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 60383.C1. -/

theorem S60383D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B60383 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S60383C1 ρ hρ

/-- 证书叶 60383.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S60383C2P : TMParams :=
  ⟨[], [], []⟩

theorem S60383C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B60383 S60383C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 60383.C2. -/

theorem S60383D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B60383 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S60383C2 ρ hρ

/-- 导数叶 60383（+∂x3f，then 支，全盒）. -/

def DP60383 : TMParams :=
  ⟨[⟨6166095519742878032142089538519040876719966, 6166095519742878032142089538519040876719966, 744211941258165867114721300415698916227370516279, (-80), (-80)⟩, ⟨6166095519742878032142089538519040876719966, 6166095519742878032142089538519040876719966, 744211941258165867114721300415698916227370516279, (-80), (-80)⟩, ⟨6166095519742878032142089538519040876719966, 6166095519742878032142089538519040876719966, 744211941258165867114721300415698916227370516279, (-80), (-80)⟩, ⟨6166095519742878032142089538519040876719966, 6166095519742878032142089538519040876719966, 744211941258165867114721300415698916227370516279, (-80), (-80)⟩, ⟨6166095519742878032142089538519040876719966, 6166095519742878032142089538519040876719966, 744211941258165867114721300415698916227370516279, (-80), (-80)⟩, ⟨6166095519742878032142089538519040876719966, 6166095519742878032142089538519040876719966, 744211941258165867114721300415698916227370516279, (-80), (-80)⟩, ⟨6166095519742878032142089538519040876719966, 6166095519742878032142089538519040876719966, 744211941258165867114721300415698916227370516279, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der60383 :
    checkPosTMHull (derivIExpr E549 2) B60383 DP60383
    = true := by
  decide

/-- 面叶 60383（lo 面）. -/

def FB60383 : Fin 6 → DInterval := faceBoxLo B60383 2

def PF60383 : TMParams :=
  ⟨[⟨63613226541517244100142593450811854253073, 484863266506538617772055855249882914983841, 0, (-80), (-80)⟩, ⟨6116722457194056843258427602107252341581634, 6116722457194056843258427602107252341581634, 749427036360284006901838117159569642446007318187, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face60383 :
    checkPosTMHull E549 FB60383 PF60383
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 60383，then 支）. -/

def DSafe60383 : DerivSafeOn B60383 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S60383D2) S60383D1) (Or.inr (Or.inr rfl))) S60383D0)))

/-- mono 折叠组合（叶 60383，两叶引用零重算）. -/

theorem Fold60383 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B60383 2 PF60383 DP60383 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B60383 DP60383 = true := Der60383
  have h2 : checkPosTMHull E549 (faceBoxLo B60383 2) PF60383 = true := Face60383
  show (checkPosTMHull (derivIExpr E549 2) B60383 DP60383
      && checkPosTMHull E549 (faceBoxLo B60383 2) PF60383) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 60383）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem60383 (ρ : Fin 6 → ℝ) (hρ : boxMem B60383 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe60383 Fold60383 hρ

#print axioms Sem60383

/-- 叶 60535（then 支，lo 面）原盒. -/

def B60535 : Fin 6 → DInterval :=
  ![⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩]

/-- 证书叶 60535.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S60535C0P : TMParams :=
  ⟨[⟨277691602899481974858102369712677466864153, 283437066043454747192662687632863400136280, 0, (-80), (-80)⟩], [], []⟩

theorem S60535C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B60535 S60535C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 60535.C0. -/

theorem S60535D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B60535 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S60535C0 ρ hρ

/-- 证书叶 60535.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S60535C1P : TMParams :=
  ⟨[⟨277691602899481974858102369712677466864153, 283437066043454747192662687632863400136280, 0, (-80), (-80)⟩], [], []⟩

theorem S60535C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B60535 S60535C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 60535.C1. -/

theorem S60535D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B60535 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S60535C1 ρ hρ

/-- 证书叶 60535.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S60535C2P : TMParams :=
  ⟨[], [], []⟩

theorem S60535C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B60535 S60535C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 60535.C2. -/

theorem S60535D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B60535 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S60535C2 ρ hρ

/-- 导数叶 60535（+∂x3f，then 支，全盒）. -/

def DP60535 : TMParams :=
  ⟨[⟨7038263651419722995755754536596166526944044, 7038263651419722995755754536596166526944044, 854166561241913276744646986108126657150377792554, (-80), (-80)⟩, ⟨7038263651419722995755754536596166526944044, 7038263651419722995755754536596166526944044, 854166561241913276744646986108126657150377792554, (-80), (-80)⟩, ⟨7038263651419722995755754536596166526944044, 7038263651419722995755754536596166526944044, 854166561241913276744646986108126657150377792554, (-80), (-80)⟩, ⟨7038263651419722995755754536596166526944044, 7038263651419722995755754536596166526944044, 854166561241913276744646986108126657150377792554, (-80), (-80)⟩, ⟨7038263651419722995755754536596166526944044, 7038263651419722995755754536596166526944044, 854166561241913276744646986108126657150377792554, (-80), (-80)⟩, ⟨7038263651419722995755754536596166526944044, 7038263651419722995755754536596166526944044, 854166561241913276744646986108126657150377792554, (-80), (-80)⟩, ⟨7038263651419722995755754536596166526944044, 7038263651419722995755754536596166526944044, 854166561241913276744646986108126657150377792554, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der60535 :
    checkPosTMHull (derivIExpr E549 2) B60535 DP60535
    = true := by
  decide

/-- 面叶 60535（lo 面）. -/

def FB60535 : Fin 6 → DInterval := faceBoxLo B60535 2

def PF60535 : TMParams :=
  ⟨[⟨307320469003548577922040912582793530302370, 272359933279068832419945247121564730833457, 0, (-80), (-80)⟩, ⟨6995645569010606157676872631006259666759882, 6995645569010606157676872631006259666759882, 859226199460601990730441102903202797744320794687, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face60535 :
    checkPosTMHull E549 FB60535 PF60535
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 60535，then 支）. -/

def DSafe60535 : DerivSafeOn B60535 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S60535D2) S60535D1) (Or.inr (Or.inr rfl))) S60535D0)))

/-- mono 折叠组合（叶 60535，两叶引用零重算）. -/

theorem Fold60535 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B60535 2 PF60535 DP60535 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B60535 DP60535 = true := Der60535
  have h2 : checkPosTMHull E549 (faceBoxLo B60535 2) PF60535 = true := Face60535
  show (checkPosTMHull (derivIExpr E549 2) B60535 DP60535
      && checkPosTMHull E549 (faceBoxLo B60535 2) PF60535) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 60535）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem60535 (ρ : Fin 6 → ℝ) (hρ : boxMem B60535 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe60535 Fold60535 hρ

#print axioms Sem60535

/-- 叶 60687（then 支，lo 面）原盒. -/

def B60687 : Fin 6 → DInterval :=
  ![⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩]

/-- 证书叶 60687.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S60687C0P : TMParams :=
  ⟨[⟨61053998971967241056126949078875622200970, 523864851320285324686211644750222634340128, 0, (-80), (-80)⟩], [], []⟩

theorem S60687C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B60687 S60687C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 60687.C0. -/

theorem S60687D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B60687 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S60687C0 ρ hρ

/-- 证书叶 60687.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S60687C1P : TMParams :=
  ⟨[⟨61053998971967241056126949078875622200970, 523864851320285324686211644750222634340128, 0, (-80), (-80)⟩], [], []⟩

theorem S60687C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B60687 S60687C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 60687.C1. -/

theorem S60687D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B60687 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S60687C1 ρ hρ

/-- 证书叶 60687.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S60687C2P : TMParams :=
  ⟨[], [], []⟩

theorem S60687C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B60687 S60687C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 60687.C2. -/

theorem S60687D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B60687 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S60687C2 ρ hρ

/-- 导数叶 60687（+∂x3f，then 支，全盒）. -/

def DP60687 : TMParams :=
  ⟨[⟨6437525441023097053584845390482475633358109, 6437525441023097053584845390482475633358109, 778925629174943647668588737569062195948827200902, (-80), (-80)⟩, ⟨6437525441023097053584845390482475633358109, 6437525441023097053584845390482475633358109, 778925629174943647668588737569062195948827200902, (-80), (-80)⟩, ⟨6437525441023097053584845390482475633358109, 6437525441023097053584845390482475633358109, 778925629174943647668588737569062195948827200902, (-80), (-80)⟩, ⟨6437525441023097053584845390482475633358109, 6437525441023097053584845390482475633358109, 778925629174943647668588737569062195948827200902, (-80), (-80)⟩, ⟨6437525441023097053584845390482475633358109, 6437525441023097053584845390482475633358109, 778925629174943647668588737569062195948827200902, (-80), (-80)⟩, ⟨6437525441023097053584845390482475633358109, 6437525441023097053584845390482475633358109, 778925629174943647668588737569062195948827200902, (-80), (-80)⟩, ⟨6437525441023097053584845390482475633358109, 6437525441023097053584845390482475633358109, 778925629174943647668588737569062195948827200902, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der60687 :
    checkPosTMHull (derivIExpr E549 2) B60687 DP60687
    = true := by
  decide

/-- 面叶 60687（lo 面）. -/

def FB60687 : Fin 6 → DInterval := faceBoxLo B60687 2

def PF60687 : TMParams :=
  ⟨[⟨68718755362209671130482665576812615394544, 503299275923190448679103155732347858434224, 0, (-80), (-80)⟩, ⟨6409673691584283504475759609520248906895754, 6409673691584283504475759609520248906895754, 783799088936949489254405027699550443008283831121, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face60687 :
    checkPosTMHull E549 FB60687 PF60687
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 60687，then 支）. -/

def DSafe60687 : DerivSafeOn B60687 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S60687D2) S60687D1) (Or.inr (Or.inr rfl))) S60687D0)))

/-- mono 折叠组合（叶 60687，两叶引用零重算）. -/

theorem Fold60687 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B60687 2 PF60687 DP60687 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B60687 DP60687 = true := Der60687
  have h2 : checkPosTMHull E549 (faceBoxLo B60687 2) PF60687 = true := Face60687
  show (checkPosTMHull (derivIExpr E549 2) B60687 DP60687
      && checkPosTMHull E549 (faceBoxLo B60687 2) PF60687) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 60687）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem60687 (ρ : Fin 6 → ℝ) (hρ : boxMem B60687 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe60687 Fold60687 hρ

#print axioms Sem60687

/-- 叶 60839（then 支，lo 面）原盒. -/

def B60839 : Fin 6 → DInterval :=
  ![⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨2, 0⟩, ⟨9148280341, -32⟩⟩]

/-- 证书叶 60839.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S60839C0P : TMParams :=
  ⟨[⟨51003739961498189111752763040267758795306, 525114624301934540131685315842187843783071, 0, (-80), (-80)⟩], [], []⟩

theorem S60839C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B60839 S60839C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 60839.C0. -/

theorem S60839D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B60839 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S60839C0 ρ hρ

/-- 证书叶 60839.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S60839C1P : TMParams :=
  ⟨[⟨51003739961498189111752763040267758795306, 525114624301934540131685315842187843783071, 0, (-80), (-80)⟩], [], []⟩

theorem S60839C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B60839 S60839C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 60839.C1. -/

theorem S60839D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B60839 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S60839C1 ρ hρ

/-- 证书叶 60839.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S60839C2P : TMParams :=
  ⟨[], [], []⟩

theorem S60839C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B60839 S60839C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 60839.C2. -/

theorem S60839D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B60839 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S60839C2 ρ hρ

/-- 导数叶 60839（+∂x3f，then 支，全盒）. -/

def DP60839 : TMParams :=
  ⟨[⟨6249908999942871029086534242275890113493007, 6249908999942871029086534242275890113493007, 741404738811741415496359135714114403094288223620, (-80), (-80)⟩, ⟨6249908999942871029086534242275890113493007, 6249908999942871029086534242275890113493007, 741404738811741415496359135714114403094288223620, (-80), (-80)⟩, ⟨6249908999942871029086534242275890113493007, 6249908999942871029086534242275890113493007, 741404738811741415496359135714114403094288223620, (-80), (-80)⟩, ⟨6249908999942871029086534242275890113493007, 6249908999942871029086534242275890113493007, 741404738811741415496359135714114403094288223620, (-80), (-80)⟩, ⟨6249908999942871029086534242275890113493007, 6249908999942871029086534242275890113493007, 741404738811741415496359135714114403094288223620, (-80), (-80)⟩, ⟨6249908999942871029086534242275890113493007, 6249908999942871029086534242275890113493007, 741404738811741415496359135714114403094288223620, (-80), (-80)⟩, ⟨6249908999942871029086534242275890113493007, 6249908999942871029086534242275890113493007, 741404738811741415496359135714114403094288223620, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der60839 :
    checkPosTMHull (derivIExpr E549 2) B60839 DP60839
    = true := by
  decide

/-- 面叶 60839（lo 面）. -/

def FB60839 : Fin 6 → DInterval := faceBoxLo B60839 2

def PF60839 : TMParams :=
  ⟨[⟨29457028014790857470109846317237603334471, 504186874365546174298238242183782218971070, 0, (-80), (-80)⟩, ⟨6199314434172029448640627667742610840511084, 6199314434172029448640627667742610840511084, 747397144270474775871774454812999493400277996008, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face60839 :
    checkPosTMHull E549 FB60839 PF60839
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 60839，then 支）. -/

def DSafe60839 : DerivSafeOn B60839 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S60839D2) S60839D1) (Or.inr (Or.inr rfl))) S60839D0)))

/-- mono 折叠组合（叶 60839，两叶引用零重算）. -/

theorem Fold60839 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B60839 2 PF60839 DP60839 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B60839 DP60839 = true := Der60839
  have h2 : checkPosTMHull E549 (faceBoxLo B60839 2) PF60839 = true := Face60839
  show (checkPosTMHull (derivIExpr E549 2) B60839 DP60839
      && checkPosTMHull E549 (faceBoxLo B60839 2) PF60839) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 60839）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem60839 (ρ : Fin 6 → ℝ) (hρ : boxMem B60839 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe60839 Fold60839 hρ

#print axioms Sem60839

/-- 叶 60991（then 支，lo 面）原盒. -/

def B60991 : Fin 6 → DInterval :=
  ![⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩]

/-- 证书叶 60991.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S60991C0P : TMParams :=
  ⟨[⟨61126452088976022403255764386540457587462, 514561300578380048555594398489938304862849, 0, (-80), (-80)⟩], [], []⟩

theorem S60991C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B60991 S60991C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 60991.C0. -/

theorem S60991D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B60991 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S60991C0 ρ hρ

/-- 证书叶 60991.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S60991C1P : TMParams :=
  ⟨[⟨61126452088976022403255764386540457587462, 514561300578380048555594398489938304862849, 0, (-80), (-80)⟩], [], []⟩

theorem S60991C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B60991 S60991C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 60991.C1. -/

theorem S60991D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B60991 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S60991C1 ρ hρ

/-- 证书叶 60991.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S60991C2P : TMParams :=
  ⟨[], [], []⟩

theorem S60991C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B60991 S60991C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 60991.C2. -/

theorem S60991D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B60991 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S60991C2 ρ hρ

/-- 导数叶 60991（+∂x3f，then 支，全盒）. -/

def DP60991 : TMParams :=
  ⟨[⟨6346719082673057253805289243657502960767704, 6346719082673057253805289243657502960767704, 768061390294522825409853964334703222517201764592, (-80), (-80)⟩, ⟨6346719082673057253805289243657502960767704, 6346719082673057253805289243657502960767704, 768061390294522825409853964334703222517201764592, (-80), (-80)⟩, ⟨6346719082673057253805289243657502960767704, 6346719082673057253805289243657502960767704, 768061390294522825409853964334703222517201764592, (-80), (-80)⟩, ⟨6346719082673057253805289243657502960767704, 6346719082673057253805289243657502960767704, 768061390294522825409853964334703222517201764592, (-80), (-80)⟩, ⟨6346719082673057253805289243657502960767704, 6346719082673057253805289243657502960767704, 768061390294522825409853964334703222517201764592, (-80), (-80)⟩, ⟨6346719082673057253805289243657502960767704, 6346719082673057253805289243657502960767704, 768061390294522825409853964334703222517201764592, (-80), (-80)⟩, ⟨6346719082673057253805289243657502960767704, 6346719082673057253805289243657502960767704, 768061390294522825409853964334703222517201764592, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der60991 :
    checkPosTMHull (derivIExpr E549 2) B60991 DP60991
    = true := by
  decide

/-- 面叶 60991（lo 面）. -/

def FB60991 : Fin 6 → DInterval := faceBoxLo B60991 2

def PF60991 : TMParams :=
  ⟨[⟨68149879620409257494383006339675304475270, 493698045423708798553131335381219393347772, 0, (-80), (-80)⟩, ⟨6303257574143378596709646662216937510901808, 6303257574143378596709646662216937510901808, 772912913387365660077174018480644527108094913448, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face60991 :
    checkPosTMHull E549 FB60991 PF60991
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 60991，then 支）. -/

def DSafe60991 : DerivSafeOn B60991 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S60991D2) S60991D1) (Or.inr (Or.inr rfl))) S60991D0)))

/-- mono 折叠组合（叶 60991，两叶引用零重算）. -/

theorem Fold60991 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B60991 2 PF60991 DP60991 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B60991 DP60991 = true := Der60991
  have h2 : checkPosTMHull E549 (faceBoxLo B60991 2) PF60991 = true := Face60991
  show (checkPosTMHull (derivIExpr E549 2) B60991 DP60991
      && checkPosTMHull E549 (faceBoxLo B60991 2) PF60991) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 60991）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem60991 (ρ : Fin 6 → ℝ) (hρ : boxMem B60991 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe60991 Fold60991 hρ

#print axioms Sem60991

/-- 叶 61143（then 支，lo 面）原盒. -/

def B61143 : Fin 6 → DInterval :=
  ![⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨9148280341, -32⟩, ⟨4853313045, -31⟩⟩]

/-- 证书叶 61143.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S61143C0P : TMParams :=
  ⟨[⟨103531407202341314856058328178915264522866, 277653949384329903771117121668257151132713, 0, (-80), (-80)⟩], [], []⟩

theorem S61143C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B61143 S61143C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 61143.C0. -/

theorem S61143D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B61143 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S61143C0 ρ hρ

/-- 证书叶 61143.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S61143C1P : TMParams :=
  ⟨[⟨103531407202341314856058328178915264522866, 277653949384329903771117121668257151132713, 0, (-80), (-80)⟩], [], []⟩

theorem S61143C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B61143 S61143C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 61143.C1. -/

theorem S61143D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B61143 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S61143C1 ρ hρ

/-- 证书叶 61143.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S61143C2P : TMParams :=
  ⟨[], [], []⟩

theorem S61143C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B61143 S61143C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 61143.C2. -/

theorem S61143D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B61143 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S61143C2 ρ hρ

/-- 导数叶 61143（+∂x3f，then 支，全盒）. -/

def DP61143 : TMParams :=
  ⟨[⟨6572727129521995708589916372464286418976119, 6572727129521995708589916372464286418976119, 781102501896381743189920537169947045249410177462, (-80), (-80)⟩, ⟨6572727129521995708589916372464286418976119, 6572727129521995708589916372464286418976119, 781102501896381743189920537169947045249410177462, (-80), (-80)⟩, ⟨6572727129521995708589916372464286418976119, 6572727129521995708589916372464286418976119, 781102501896381743189920537169947045249410177462, (-80), (-80)⟩, ⟨6572727129521995708589916372464286418976119, 6572727129521995708589916372464286418976119, 781102501896381743189920537169947045249410177462, (-80), (-80)⟩, ⟨6572727129521995708589916372464286418976119, 6572727129521995708589916372464286418976119, 781102501896381743189920537169947045249410177462, (-80), (-80)⟩, ⟨6572727129521995708589916372464286418976119, 6572727129521995708589916372464286418976119, 781102501896381743189920537169947045249410177462, (-80), (-80)⟩, ⟨6572727129521995708589916372464286418976119, 6572727129521995708589916372464286418976119, 781102501896381743189920537169947045249410177462, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der61143 :
    checkPosTMHull (derivIExpr E549 2) B61143 DP61143
    = true := by
  decide

/-- 面叶 61143（lo 面）. -/

def FB61143 : Fin 6 → DInterval := faceBoxLo B61143 2

def PF61143 : TMParams :=
  ⟨[⟨121580468603338411229808375161952793146985, 133317625439399793863296670058551460411092, 0, (-80), (-80)⟩, ⟨6528071429786546588634404917896369287037254, 6528071429786546588634404917896369287037254, 787400665594036351822245652173678011318375306378, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face61143 :
    checkPosTMHull E549 FB61143 PF61143
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 61143，then 支）. -/

def DSafe61143 : DerivSafeOn B61143 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S61143D2) S61143D1) (Or.inr (Or.inr rfl))) S61143D0)))

/-- mono 折叠组合（叶 61143，两叶引用零重算）. -/

theorem Fold61143 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B61143 2 PF61143 DP61143 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B61143 DP61143 = true := Der61143
  have h2 : checkPosTMHull E549 (faceBoxLo B61143 2) PF61143 = true := Face61143
  show (checkPosTMHull (derivIExpr E549 2) B61143 DP61143
      && checkPosTMHull E549 (faceBoxLo B61143 2) PF61143) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 61143）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem61143 (ρ : Fin 6 → ℝ) (hρ : boxMem B61143 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe61143 Fold61143 hρ

#print axioms Sem61143

/-- 叶 61295（then 支，lo 面）原盒. -/

def B61295 : Fin 6 → DInterval :=
  ![⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩]

/-- 证书叶 61295.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S61295C0P : TMParams :=
  ⟨[⟨255542156024895086329632193765524640524909, 270321386053179469602187257486663186116271, 0, (-80), (-80)⟩], [], []⟩

theorem S61295C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B61295 S61295C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 61295.C0. -/

theorem S61295D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B61295 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S61295C0 ρ hρ

/-- 证书叶 61295.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S61295C1P : TMParams :=
  ⟨[⟨255542156024895086329632193765524640524909, 270321386053179469602187257486663186116271, 0, (-80), (-80)⟩], [], []⟩

theorem S61295C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B61295 S61295C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 61295.C1. -/

theorem S61295D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B61295 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S61295C1 ρ hρ

/-- 证书叶 61295.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S61295C2P : TMParams :=
  ⟨[], [], []⟩

theorem S61295C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B61295 S61295C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 61295.C2. -/

theorem S61295D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B61295 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S61295C2 ρ hρ

/-- 导数叶 61295（+∂x3f，then 支，全盒）. -/

def DP61295 : TMParams :=
  ⟨[⟨6663343042480235858619375154832576859473598, 6663343042480235858619375154832576859473598, 807033829308908220272701734228582324746447090944, (-80), (-80)⟩, ⟨6663343042480235858619375154832576859473598, 6663343042480235858619375154832576859473598, 807033829308908220272701734228582324746447090944, (-80), (-80)⟩, ⟨6663343042480235858619375154832576859473598, 6663343042480235858619375154832576859473598, 807033829308908220272701734228582324746447090944, (-80), (-80)⟩, ⟨6663343042480235858619375154832576859473598, 6663343042480235858619375154832576859473598, 807033829308908220272701734228582324746447090944, (-80), (-80)⟩, ⟨6663343042480235858619375154832576859473598, 6663343042480235858619375154832576859473598, 807033829308908220272701734228582324746447090944, (-80), (-80)⟩, ⟨6663343042480235858619375154832576859473598, 6663343042480235858619375154832576859473598, 807033829308908220272701734228582324746447090944, (-80), (-80)⟩, ⟨6663343042480235858619375154832576859473598, 6663343042480235858619375154832576859473598, 807033829308908220272701734228582324746447090944, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der61295 :
    checkPosTMHull (derivIExpr E549 2) B61295 DP61295
    = true := by
  decide

/-- 面叶 61295（lo 面）. -/

def FB61295 : Fin 6 → DInterval := faceBoxLo B61295 2

def PF61295 : TMParams :=
  ⟨[⟨286530211793195189769257940658965498905125, 259660832427891506780090689726960165613565, 0, (-80), (-80)⟩, ⟨6631350550025546127729666874457752944266171, 6631350550025546127729666874457752944266171, 812002641814614617956317708110875581604416675260, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face61295 :
    checkPosTMHull E549 FB61295 PF61295
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 61295，then 支）. -/

def DSafe61295 : DerivSafeOn B61295 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S61295D2) S61295D1) (Or.inr (Or.inr rfl))) S61295D0)))

/-- mono 折叠组合（叶 61295，两叶引用零重算）. -/

theorem Fold61295 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B61295 2 PF61295 DP61295 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B61295 DP61295 = true := Der61295
  have h2 : checkPosTMHull E549 (faceBoxLo B61295 2) PF61295 = true := Face61295
  show (checkPosTMHull (derivIExpr E549 2) B61295 DP61295
      && checkPosTMHull E549 (faceBoxLo B61295 2) PF61295) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 61295）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem61295 (ρ : Fin 6 → ℝ) (hρ : boxMem B61295 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe61295 Fold61295 hρ

#print axioms Sem61295

/-- 叶 61447（then 支，lo 面）原盒. -/

def B61447 : Fin 6 → DInterval :=
  ![⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩]

/-- 证书叶 61447.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S61447C0P : TMParams :=
  ⟨[⟨230844609651850603910620278865359388647356, 254502838488759746625707086024479566769769, 0, (-80), (-80)⟩], [], []⟩

theorem S61447C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B61447 S61447C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 61447.C0. -/

theorem S61447D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B61447 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S61447C0 ρ hρ

/-- 证书叶 61447.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S61447C1P : TMParams :=
  ⟨[⟨230844609651850603910620278865359388647356, 254502838488759746625707086024479566769769, 0, (-80), (-80)⟩], [], []⟩

theorem S61447C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B61447 S61447C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 61447.C1. -/

theorem S61447D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B61447 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S61447C1 ρ hρ

/-- 证书叶 61447.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S61447C2P : TMParams :=
  ⟨[], [], []⟩

theorem S61447C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B61447 S61447C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 61447.C2. -/

theorem S61447D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B61447 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S61447C2 ρ hρ

/-- 导数叶 61447（+∂x3f，then 支，全盒）. -/

def DP61447 : TMParams :=
  ⟨[⟨6222923465055708921820080788181261260202355, 6222923465055708921820080788181261260202355, 751849418031832887987033253736972802255725704340, (-80), (-80)⟩, ⟨6222923465055708921820080788181261260202355, 6222923465055708921820080788181261260202355, 751849418031832887987033253736972802255725704340, (-80), (-80)⟩, ⟨6222923465055708921820080788181261260202355, 6222923465055708921820080788181261260202355, 751849418031832887987033253736972802255725704340, (-80), (-80)⟩, ⟨6222923465055708921820080788181261260202355, 6222923465055708921820080788181261260202355, 751849418031832887987033253736972802255725704340, (-80), (-80)⟩, ⟨6222923465055708921820080788181261260202355, 6222923465055708921820080788181261260202355, 751849418031832887987033253736972802255725704340, (-80), (-80)⟩, ⟨6222923465055708921820080788181261260202355, 6222923465055708921820080788181261260202355, 751849418031832887987033253736972802255725704340, (-80), (-80)⟩, ⟨6222923465055708921820080788181261260202355, 6222923465055708921820080788181261260202355, 751849418031832887987033253736972802255725704340, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der61447 :
    checkPosTMHull (derivIExpr E549 2) B61447 DP61447
    = true := by
  decide

/-- 面叶 61447（lo 面）. -/

def FB61447 : Fin 6 → DInterval := faceBoxLo B61447 2

def PF61447 : TMParams :=
  ⟨[⟨130770910822605648328368454610373774210503, 122075005014904171099631733030914215070959, 0, (-80), (-80)⟩, ⟨6189640339409009521626801560128348350393054, 6189640339409009521626801560128348350393054, 756834359873487707479769349828652315046612026553, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face61447 :
    checkPosTMHull E549 FB61447 PF61447
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 61447，then 支）. -/

def DSafe61447 : DerivSafeOn B61447 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S61447D2) S61447D1) (Or.inr (Or.inr rfl))) S61447D0)))

/-- mono 折叠组合（叶 61447，两叶引用零重算）. -/

theorem Fold61447 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B61447 2 PF61447 DP61447 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B61447 DP61447 = true := Der61447
  have h2 : checkPosTMHull E549 (faceBoxLo B61447 2) PF61447 = true := Face61447
  show (checkPosTMHull (derivIExpr E549 2) B61447 DP61447
      && checkPosTMHull E549 (faceBoxLo B61447 2) PF61447) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 61447）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem61447 (ρ : Fin 6 → ℝ) (hρ : boxMem B61447 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe61447 Fold61447 hρ

#print axioms Sem61447

/-- 叶 61599（then 支，lo 面）原盒. -/

def B61599 : Fin 6 → DInterval :=
  ![⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨2, 0⟩, ⟨9148280341, -32⟩⟩]

/-- 证书叶 61599.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S61599C0P : TMParams :=
  ⟨[⟨46688601511717805291223693755969712851272, 256438475508858911052773704252488175475972, 0, (-80), (-80)⟩], [], []⟩

theorem S61599C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B61599 S61599C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 61599.C0. -/

theorem S61599D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B61599 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S61599C0 ρ hρ

/-- 证书叶 61599.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S61599C1P : TMParams :=
  ⟨[⟨46688601511717805291223693755969712851272, 256438475508858911052773704252488175475972, 0, (-80), (-80)⟩], [], []⟩

theorem S61599C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B61599 S61599C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 61599.C1. -/

theorem S61599D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B61599 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S61599C1 ρ hρ

/-- 证书叶 61599.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S61599C2P : TMParams :=
  ⟨[], [], []⟩

theorem S61599C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B61599 S61599C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 61599.C2. -/

theorem S61599D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B61599 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S61599C2 ρ hρ

/-- 导数叶 61599（+∂x3f，then 支，全盒）. -/

def DP61599 : TMParams :=
  ⟨[⟨6049985399447991872396909068945597808960918, 6049985399447991872396909068945597808960918, 715624495767585154293989424582468021635978573470, (-80), (-80)⟩, ⟨6049985399447991872396909068945597808960918, 6049985399447991872396909068945597808960918, 715624495767585154293989424582468021635978573470, (-80), (-80)⟩, ⟨6049985399447991872396909068945597808960918, 6049985399447991872396909068945597808960918, 715624495767585154293989424582468021635978573470, (-80), (-80)⟩, ⟨6049985399447991872396909068945597808960918, 6049985399447991872396909068945597808960918, 715624495767585154293989424582468021635978573470, (-80), (-80)⟩, ⟨6049985399447991872396909068945597808960918, 6049985399447991872396909068945597808960918, 715624495767585154293989424582468021635978573470, (-80), (-80)⟩, ⟨6049985399447991872396909068945597808960918, 6049985399447991872396909068945597808960918, 715624495767585154293989424582468021635978573470, (-80), (-80)⟩, ⟨6049985399447991872396909068945597808960918, 6049985399447991872396909068945597808960918, 715624495767585154293989424582468021635978573470, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der61599 :
    checkPosTMHull (derivIExpr E549 2) B61599 DP61599
    = true := by
  decide

/-- 面叶 61599（lo 面）. -/

def FB61599 : Fin 6 → DInterval := faceBoxLo B61599 2

def PF61599 : TMParams :=
  ⟨[⟨27518580213277155515846641192412271718200, 245920448928564528780657222348946264816871, 0, (-80), (-80)⟩, ⟨5998232042103770159677579125998730597221012, 5998232042103770159677579125998730597221012, 721738984332466644461853554286475995161496468271, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face61599 :
    checkPosTMHull E549 FB61599 PF61599
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 61599，then 支）. -/

def DSafe61599 : DerivSafeOn B61599 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S61599D2) S61599D1) (Or.inr (Or.inr rfl))) S61599D0)))

/-- mono 折叠组合（叶 61599，两叶引用零重算）. -/

theorem Fold61599 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B61599 2 PF61599 DP61599 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B61599 DP61599 = true := Der61599
  have h2 : checkPosTMHull E549 (faceBoxLo B61599 2) PF61599 = true := Face61599
  show (checkPosTMHull (derivIExpr E549 2) B61599 DP61599
      && checkPosTMHull E549 (faceBoxLo B61599 2) PF61599) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 61599）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem61599 (ρ : Fin 6 → ℝ) (hρ : boxMem B61599 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe61599 Fold61599 hρ

#print axioms Sem61599

/-- 叶 61751（then 支，lo 面）原盒. -/

def B61751 : Fin 6 → DInterval :=
  ![⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩]

/-- 证书叶 61751.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S61751C0P : TMParams :=
  ⟨[⟨229969713425997941456091553514318685656949, 251893918294977274048756237554635941530747, 0, (-80), (-80)⟩], [], []⟩

theorem S61751C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B61751 S61751C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 61751.C0. -/

theorem S61751D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B61751 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S61751C0 ρ hρ

/-- 证书叶 61751.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S61751C1P : TMParams :=
  ⟨[⟨229969713425997941456091553514318685656949, 251893918294977274048756237554635941530747, 0, (-80), (-80)⟩], [], []⟩

theorem S61751C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B61751 S61751C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 61751.C1. -/

theorem S61751D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B61751 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S61751C1 ρ hρ

/-- 证书叶 61751.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S61751C2P : TMParams :=
  ⟨[], [], []⟩

theorem S61751C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B61751 S61751C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 61751.C2. -/

theorem S61751D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B61751 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S61751C2 ρ hρ

/-- 导数叶 61751（+∂x3f，then 支，全盒）. -/

def DP61751 : TMParams :=
  ⟨[⟨6166507079612333207062014080876415432783742, 6166507079612333207062014080876415432783742, 744971532886206186669998690590469268780833295554, (-80), (-80)⟩, ⟨6166507079612333207062014080876415432783742, 6166507079612333207062014080876415432783742, 744971532886206186669998690590469268780833295554, (-80), (-80)⟩, ⟨6166507079612333207062014080876415432783742, 6166507079612333207062014080876415432783742, 744971532886206186669998690590469268780833295554, (-80), (-80)⟩, ⟨6166507079612333207062014080876415432783742, 6166507079612333207062014080876415432783742, 744971532886206186669998690590469268780833295554, (-80), (-80)⟩, ⟨6166507079612333207062014080876415432783742, 6166507079612333207062014080876415432783742, 744971532886206186669998690590469268780833295554, (-80), (-80)⟩, ⟨6166507079612333207062014080876415432783742, 6166507079612333207062014080876415432783742, 744971532886206186669998690590469268780833295554, (-80), (-80)⟩, ⟨6166507079612333207062014080876415432783742, 6166507079612333207062014080876415432783742, 744971532886206186669998690590469268780833295554, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der61751 :
    checkPosTMHull (derivIExpr E549 2) B61751 DP61751
    = true := by
  decide

/-- 面叶 61751（lo 面）. -/

def FB61751 : Fin 6 → DInterval := faceBoxLo B61751 2

def PF61751 : TMParams :=
  ⟨[⟨259515248961883395257324443280396818306408, 241459973335894125745060152832765755067909, 0, (-80), (-80)⟩, ⟨6125656373140710730017966621674368169272244, 6125656373140710730017966621674368169272244, 749946975945949760597086249565636533178473874178, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face61751 :
    checkPosTMHull E549 FB61751 PF61751
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 61751，then 支）. -/

def DSafe61751 : DerivSafeOn B61751 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S61751D2) S61751D1) (Or.inr (Or.inr rfl))) S61751D0)))

/-- mono 折叠组合（叶 61751，两叶引用零重算）. -/

theorem Fold61751 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B61751 2 PF61751 DP61751 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B61751 DP61751 = true := Der61751
  have h2 : checkPosTMHull E549 (faceBoxLo B61751 2) PF61751 = true := Face61751
  show (checkPosTMHull (derivIExpr E549 2) B61751 DP61751
      && checkPosTMHull E549 (faceBoxLo B61751 2) PF61751) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 61751）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem61751 (ρ : Fin 6 → ℝ) (hρ : boxMem B61751 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe61751 Fold61751 hρ

#print axioms Sem61751

/-- 叶 61933（then 支，lo 面）原盒. -/

def B61933 : Fin 6 → DInterval :=
  ![⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩]

/-- 证书叶 61933.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S61933C0P : TMParams :=
  ⟨[⟨308424625065936004706464563633031039405243, 78346083363766171661197261671925265276556, 0, (-80), (-80)⟩], [], []⟩

theorem S61933C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B61933 S61933C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 61933.C0. -/

theorem S61933D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B61933 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S61933C0 ρ hρ

/-- 证书叶 61933.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S61933C1P : TMParams :=
  ⟨[⟨308424625065936004706464563633031039405243, 78346083363766171661197261671925265276556, 0, (-80), (-80)⟩], [], []⟩

theorem S61933C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B61933 S61933C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 61933.C1. -/

theorem S61933D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B61933 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S61933C1 ρ hρ

/-- 证书叶 61933.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S61933C2P : TMParams :=
  ⟨[], [], []⟩

theorem S61933C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B61933 S61933C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 61933.C2. -/

theorem S61933D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B61933 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S61933C2 ρ hρ

/-- 导数叶 61933（+∂x3f，then 支，全盒）. -/

def DP61933 : TMParams :=
  ⟨[⟨7793580070001353089631964074179039082241840, 7793580070001353089631964074179039082241840, 947696229359861798974147253255676032805015957690, (-80), (-80)⟩, ⟨7793580070001353089631964074179039082241840, 7793580070001353089631964074179039082241840, 947696229359861798974147253255676032805015957690, (-80), (-80)⟩, ⟨7793580070001353089631964074179039082241840, 7793580070001353089631964074179039082241840, 947696229359861798974147253255676032805015957690, (-80), (-80)⟩, ⟨7793580070001353089631964074179039082241840, 7793580070001353089631964074179039082241840, 947696229359861798974147253255676032805015957690, (-80), (-80)⟩, ⟨7793580070001353089631964074179039082241840, 7793580070001353089631964074179039082241840, 947696229359861798974147253255676032805015957690, (-80), (-80)⟩, ⟨7793580070001353089631964074179039082241840, 7793580070001353089631964074179039082241840, 947696229359861798974147253255676032805015957690, (-80), (-80)⟩, ⟨7793580070001353089631964074179039082241840, 7793580070001353089631964074179039082241840, 947696229359861798974147253255676032805015957690, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der61933 :
    checkPosTMHull (derivIExpr E549 2) B61933 DP61933
    = true := by
  decide

/-- 面叶 61933（lo 面）. -/

def FB61933 : Fin 6 → DInterval := faceBoxLo B61933 2

def PF61933 : TMParams :=
  ⟨[⟨341718343288521718125248013677824203147250, 75329518482007320890998637925133379969144, 0, (-80), (-80)⟩, ⟨7753158167739986837338729562274884769190748, 7753158167739986837338729562274884769190748, 953096380863482544491480545264013128073270633130, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face61933 :
    checkPosTMHull E549 FB61933 PF61933
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 61933，then 支）. -/

def DSafe61933 : DerivSafeOn B61933 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S61933D2) S61933D1) (Or.inr (Or.inr rfl))) S61933D0)))

/-- mono 折叠组合（叶 61933，两叶引用零重算）. -/

theorem Fold61933 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B61933 2 PF61933 DP61933 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B61933 DP61933 = true := Der61933
  have h2 : checkPosTMHull E549 (faceBoxLo B61933 2) PF61933 = true := Face61933
  show (checkPosTMHull (derivIExpr E549 2) B61933 DP61933
      && checkPosTMHull E549 (faceBoxLo B61933 2) PF61933) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 61933）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem61933 (ρ : Fin 6 → ℝ) (hρ : boxMem B61933 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe61933 Fold61933 hρ

#print axioms Sem61933

/-- 叶 62267（then 支，lo 面）原盒. -/

def B62267 : Fin 6 → DInterval :=
  ![⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩]

/-- 证书叶 62267.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S62267C0P : TMParams :=
  ⟨[⟨146528237021565779546568334794870933318482, 591378477890178701550716040370232926247178, 0, (-80), (-80)⟩], [], []⟩

theorem S62267C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B62267 S62267C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 62267.C0. -/

theorem S62267D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B62267 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S62267C0 ρ hρ

/-- 证书叶 62267.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S62267C1P : TMParams :=
  ⟨[⟨146528237021565779546568334794870933318482, 591378477890178701550716040370232926247178, 0, (-80), (-80)⟩], [], []⟩

theorem S62267C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B62267 S62267C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 62267.C1. -/

theorem S62267D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B62267 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S62267C1 ρ hρ

/-- 证书叶 62267.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S62267C2P : TMParams :=
  ⟨[], [], []⟩

theorem S62267C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B62267 S62267C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 62267.C2. -/

theorem S62267D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B62267 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S62267C2 ρ hρ

/-- 导数叶 62267（+∂x3f，then 支，全盒）. -/

def DP62267 : TMParams :=
  ⟨[⟨7362245537027774139855752694728886213202731, 7362245537027774139855752694728886213202731, 894487654470788344189117438668204060034341648791, (-80), (-80)⟩, ⟨7362245537027774139855752694728886213202731, 7362245537027774139855752694728886213202731, 894487654470788344189117438668204060034341648791, (-80), (-80)⟩, ⟨7362245537027774139855752694728886213202731, 7362245537027774139855752694728886213202731, 894487654470788344189117438668204060034341648791, (-80), (-80)⟩, ⟨7362245537027774139855752694728886213202731, 7362245537027774139855752694728886213202731, 894487654470788344189117438668204060034341648791, (-80), (-80)⟩, ⟨7362245537027774139855752694728886213202731, 7362245537027774139855752694728886213202731, 894487654470788344189117438668204060034341648791, (-80), (-80)⟩, ⟨7362245537027774139855752694728886213202731, 7362245537027774139855752694728886213202731, 894487654470788344189117438668204060034341648791, (-80), (-80)⟩, ⟨7362245537027774139855752694728886213202731, 7362245537027774139855752694728886213202731, 894487654470788344189117438668204060034341648791, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der62267 :
    checkPosTMHull (derivIExpr E549 2) B62267 DP62267
    = true := by
  decide

/-- 面叶 62267（lo 面）. -/

def FB62267 : Fin 6 → DInterval := faceBoxLo B62267 2

def PF62267 : TMParams :=
  ⟨[⟨161380201015222620301312122420312274413385, 568375918283773648890929461770607984292261, 0, (-80), (-80)⟩, ⟨7313433911529051664764185906807428705279719, 7313433911529051664764185906807428705279719, 899716452791100919161131609461304926228178285925, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face62267 :
    checkPosTMHull E549 FB62267 PF62267
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 62267，then 支）. -/

def DSafe62267 : DerivSafeOn B62267 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S62267D2) S62267D1) (Or.inr (Or.inr rfl))) S62267D0)))

/-- mono 折叠组合（叶 62267，两叶引用零重算）. -/

theorem Fold62267 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B62267 2 PF62267 DP62267 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B62267 DP62267 = true := Der62267
  have h2 : checkPosTMHull E549 (faceBoxLo B62267 2) PF62267 = true := Face62267
  show (checkPosTMHull (derivIExpr E549 2) B62267 DP62267
      && checkPosTMHull E549 (faceBoxLo B62267 2) PF62267) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 62267）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem62267 (ρ : Fin 6 → ℝ) (hρ : boxMem B62267 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe62267 Fold62267 hρ

#print axioms Sem62267

/-- 叶 62678（then 支，lo 面）原盒. -/

def B62678 : Fin 6 → DInterval :=
  ![⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩]

/-- 证书叶 62678.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S62678C0P : TMParams :=
  ⟨[⟨142743487624140646864205926063929327959125, 296240343467457709273048749546220834796645, 0, (-80), (-80)⟩], [], []⟩

theorem S62678C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B62678 S62678C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 62678.C0. -/

theorem S62678D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B62678 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S62678C0 ρ hρ

/-- 证书叶 62678.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S62678C1P : TMParams :=
  ⟨[⟨142743487624140646864205926063929327959125, 296240343467457709273048749546220834796645, 0, (-80), (-80)⟩], [], []⟩

theorem S62678C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B62678 S62678C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 62678.C1. -/

theorem S62678D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B62678 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S62678C1 ρ hρ

/-- 证书叶 62678.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S62678C2P : TMParams :=
  ⟨[], [], []⟩

theorem S62678C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B62678 S62678C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 62678.C2. -/

theorem S62678D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B62678 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S62678C2 ρ hρ

/-- 导数叶 62678（+∂x3f，then 支，全盒）. -/

def DP62678 : TMParams :=
  ⟨[⟨7333408537678171824860489981329757538284645, 7333408537678171824860489981329757538284645, 890288836823324310912334617317691354721588184785, (-80), (-80)⟩, ⟨7333408537678171824860489981329757538284645, 7333408537678171824860489981329757538284645, 890288836823324310912334617317691354721588184785, (-80), (-80)⟩, ⟨7333408537678171824860489981329757538284645, 7333408537678171824860489981329757538284645, 890288836823324310912334617317691354721588184785, (-80), (-80)⟩, ⟨7333408537678171824860489981329757538284645, 7333408537678171824860489981329757538284645, 890288836823324310912334617317691354721588184785, (-80), (-80)⟩, ⟨7333408537678171824860489981329757538284645, 7333408537678171824860489981329757538284645, 890288836823324310912334617317691354721588184785, (-80), (-80)⟩, ⟨7333408537678171824860489981329757538284645, 7333408537678171824860489981329757538284645, 890288836823324310912334617317691354721588184785, (-80), (-80)⟩, ⟨7333408537678171824860489981329757538284645, 7333408537678171824860489981329757538284645, 890288836823324310912334617317691354721588184785, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der62678 :
    checkPosTMHull (derivIExpr E549 2) B62678 DP62678
    = true := by
  decide

/-- 面叶 62678（lo 面）. -/

def FB62678 : Fin 6 → DInterval := faceBoxLo B62678 2

def PF62678 : TMParams :=
  ⟨[⟨158412180440979362396393971145794436699029, 569496768038562709231054600423245256976202, 0, (-80), (-80)⟩, ⟨7290393359464231342992100758427437963719571, 7290393359464231342992100758427437963719571, 895622448915815908819947243674892563524283105241, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face62678 :
    checkPosTMHull E549 FB62678 PF62678
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 62678，then 支）. -/

def DSafe62678 : DerivSafeOn B62678 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S62678D2) S62678D1) (Or.inr (Or.inr rfl))) S62678D0)))

/-- mono 折叠组合（叶 62678，两叶引用零重算）. -/

theorem Fold62678 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B62678 2 PF62678 DP62678 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B62678 DP62678 = true := Der62678
  have h2 : checkPosTMHull E549 (faceBoxLo B62678 2) PF62678 = true := Face62678
  show (checkPosTMHull (derivIExpr E549 2) B62678 DP62678
      && checkPosTMHull E549 (faceBoxLo B62678 2) PF62678) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 62678）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem62678 (ρ : Fin 6 → ℝ) (hρ : boxMem B62678 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe62678 Fold62678 hρ

#print axioms Sem62678

/-- 叶 62847（then 支，lo 面）原盒. -/

def B62847 : Fin 6 → DInterval :=
  ![⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩]

/-- 证书叶 62847.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S62847C0P : TMParams :=
  ⟨[⟨269097745099457611197364060380122562970997, 71206195791816986228705736449783762159835, 0, (-80), (-80)⟩], [], []⟩

theorem S62847C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B62847 S62847C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 62847.C0. -/

theorem S62847D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B62847 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S62847C0 ρ hρ

/-- 证书叶 62847.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S62847C1P : TMParams :=
  ⟨[⟨269097745099457611197364060380122562970997, 71206195791816986228705736449783762159835, 0, (-80), (-80)⟩], [], []⟩

theorem S62847C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B62847 S62847C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 62847.C1. -/

theorem S62847D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B62847 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S62847C1 ρ hρ

/-- 证书叶 62847.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S62847C2P : TMParams :=
  ⟨[], [], []⟩

theorem S62847C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B62847 S62847C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 62847.C2. -/

theorem S62847D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B62847 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S62847C2 ρ hρ

/-- 导数叶 62847（+∂x3f，then 支，全盒）. -/

def DP62847 : TMParams :=
  ⟨[⟨7023204719143007751263471474482335958092010, 7023204719143007751263471474482335958092010, 851369269015146507584945019775451349123711935751, (-80), (-80)⟩, ⟨7023204719143007751263471474482335958092010, 7023204719143007751263471474482335958092010, 851369269015146507584945019775451349123711935751, (-80), (-80)⟩, ⟨7023204719143007751263471474482335958092010, 7023204719143007751263471474482335958092010, 851369269015146507584945019775451349123711935751, (-80), (-80)⟩, ⟨7023204719143007751263471474482335958092010, 7023204719143007751263471474482335958092010, 851369269015146507584945019775451349123711935751, (-80), (-80)⟩, ⟨7023204719143007751263471474482335958092010, 7023204719143007751263471474482335958092010, 851369269015146507584945019775451349123711935751, (-80), (-80)⟩, ⟨7023204719143007751263471474482335958092010, 7023204719143007751263471474482335958092010, 851369269015146507584945019775451349123711935751, (-80), (-80)⟩, ⟨7023204719143007751263471474482335958092010, 7023204719143007751263471474482335958092010, 851369269015146507584945019775451349123711935751, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der62847 :
    checkPosTMHull (derivIExpr E549 2) B62847 DP62847
    = true := by
  decide

/-- 面叶 62847（lo 面）. -/

def FB62847 : Fin 6 → DInterval := faceBoxLo B62847 2

def PF62847 : TMParams :=
  ⟨[⟨150059089202234938625326358479454994461030, 34170446667677668930394601055024938080627, 0, (-80), (-80)⟩, ⟨6975323917782466898629687441159940566076241, 6975323917782466898629687441159940566076241, 856731401379337576294722104493888366167806429593, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face62847 :
    checkPosTMHull E549 FB62847 PF62847
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 62847，then 支）. -/

def DSafe62847 : DerivSafeOn B62847 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S62847D2) S62847D1) (Or.inr (Or.inr rfl))) S62847D0)))

/-- mono 折叠组合（叶 62847，两叶引用零重算）. -/

theorem Fold62847 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B62847 2 PF62847 DP62847 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B62847 DP62847 = true := Der62847
  have h2 : checkPosTMHull E549 (faceBoxLo B62847 2) PF62847 = true := Face62847
  show (checkPosTMHull (derivIExpr E549 2) B62847 DP62847
      && checkPosTMHull E549 (faceBoxLo B62847 2) PF62847) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 62847）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem62847 (ρ : Fin 6 → ℝ) (hρ : boxMem B62847 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe62847 Fold62847 hρ

#print axioms Sem62847

/-- 叶 63582（then 支，lo 面）原盒. -/

def B63582 : Fin 6 → DInterval :=
  ![⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩]

/-- 证书叶 63582.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S63582C0P : TMParams :=
  ⟨[⟨276718594912084975015513002654999708174676, 285624857419091019948435778498766273471732, 0, (-80), (-80)⟩], [], []⟩

theorem S63582C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B63582 S63582C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 63582.C0. -/

theorem S63582D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B63582 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S63582C0 ρ hρ

/-- 证书叶 63582.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S63582C1P : TMParams :=
  ⟨[⟨276718594912084975015513002654999708174676, 285624857419091019948435778498766273471732, 0, (-80), (-80)⟩], [], []⟩

theorem S63582C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B63582 S63582C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 63582.C1. -/

theorem S63582D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B63582 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S63582C1 ρ hρ

/-- 证书叶 63582.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S63582C2P : TMParams :=
  ⟨[], [], []⟩

theorem S63582C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B63582 S63582C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 63582.C2. -/

theorem S63582D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B63582 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S63582C2 ρ hρ

/-- 导数叶 63582（+∂x3f，then 支，全盒）. -/

def DP63582 : TMParams :=
  ⟨[⟨7076463239928534387936666963998880332743767, 7076463239928534387936666963998880332743767, 858652053486885272101717740659132309787781553848, (-80), (-80)⟩, ⟨7076463239928534387936666963998880332743767, 7076463239928534387936666963998880332743767, 858652053486885272101717740659132309787781553848, (-80), (-80)⟩, ⟨7076463239928534387936666963998880332743767, 7076463239928534387936666963998880332743767, 858652053486885272101717740659132309787781553848, (-80), (-80)⟩, ⟨7076463239928534387936666963998880332743767, 7076463239928534387936666963998880332743767, 858652053486885272101717740659132309787781553848, (-80), (-80)⟩, ⟨7076463239928534387936666963998880332743767, 7076463239928534387936666963998880332743767, 858652053486885272101717740659132309787781553848, (-80), (-80)⟩, ⟨7076463239928534387936666963998880332743767, 7076463239928534387936666963998880332743767, 858652053486885272101717740659132309787781553848, (-80), (-80)⟩, ⟨7076463239928534387936666963998880332743767, 7076463239928534387936666963998880332743767, 858652053486885272101717740659132309787781553848, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der63582 :
    checkPosTMHull (derivIExpr E549 2) B63582 DP63582
    = true := by
  decide

/-- 面叶 63582（lo 面）. -/

def FB63582 : Fin 6 → DInterval := faceBoxLo B63582 2

def PF63582 : TMParams :=
  ⟨[⟨305705904120353820766136258050283210242314, 274672747057954599809107951755297982166597, 0, (-80), (-80)⟩, ⟨7031940644412759520185198219411891951911230, 7031940644412759520185198219411891951911230, 863839446520006315017775417297987655981195972895, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face63582 :
    checkPosTMHull E549 FB63582 PF63582
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 63582，then 支）. -/

def DSafe63582 : DerivSafeOn B63582 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S63582D2) S63582D1) (Or.inr (Or.inr rfl))) S63582D0)))

/-- mono 折叠组合（叶 63582，两叶引用零重算）. -/

theorem Fold63582 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B63582 2 PF63582 DP63582 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B63582 DP63582 = true := Der63582
  have h2 : checkPosTMHull E549 (faceBoxLo B63582 2) PF63582 = true := Face63582
  show (checkPosTMHull (derivIExpr E549 2) B63582 DP63582
      && checkPosTMHull E549 (faceBoxLo B63582 2) PF63582) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 63582）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem63582 (ρ : Fin 6 → ℝ) (hρ : boxMem B63582 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe63582 Fold63582 hρ

#print axioms Sem63582


end Kepler.Interval.C549MonoBatch17
