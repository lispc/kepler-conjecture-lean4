import Kepler.Interval.Cases.C549Mono
import Kepler.Interval.Cases.C549CertSlimDefs


/-! ## 549 facePos 全量评估（emit_mono.py 生成；勿手改）。

C549MonoBatch14 — rung 128（发射钉死） shard 14/53（20 叶；modes ['then']）
每叶：面叶 + 导数叶 + DerivSafeOn 证书叶 ⇒ 嵌套 DSafe ⇒
checkPosFace*_sound ⇒ 全盒语义正性 0 < evalReal ρ。
本模块层级：['cert', 'der', 'face', 'fold']；decide 战术：decide。 -/


set_option maxHeartbeats 0
set_option maxRecDepth 1000000


namespace Kepler.Interval.C549MonoBatch14

open Kepler.Interval


/-- case 549 表达式（本模块自包含副本）. -/

def E549 : IExpr 6 :=
  (.sub (.div (.const ⟨1893, 0⟩) (.const ⟨1000, 0⟩) (-64)) (.add (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.const ⟨2, 0⟩) (-64)) (.ite (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) (.trans .arctanK (.div (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0) (-64)) 128 (-80)) (.ite (.sub (.const ⟨0, 0⟩) (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sub (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.const ⟨2, 0⟩) (-64)) (.trans .arctanK (.div (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0) (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) (-64)) 128 (-80))) (.ite (.sub (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) (.const ⟨0, 0⟩)) (.sub (.neg (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.const ⟨2, 0⟩) (-64))) (.trans .arctanK (.div (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0) (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) (-64)) 128 (-80))) (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))))))))

/-- 叶 50411（then 支，lo 面）原盒. -/

def B50411 : Fin 6 → DInterval :=
  ![⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩]

/-- 证书叶 50411.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S50411C0P : TMParams :=
  ⟨[⟨70045036075972233530368056607402728431079, 571420279584329144562747469796889322443548, 0, (-80), (-80)⟩], [], []⟩

theorem S50411C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B50411 S50411C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 50411.C0. -/

theorem S50411D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B50411 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S50411C0 ρ hρ

/-- 证书叶 50411.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S50411C1P : TMParams :=
  ⟨[⟨70045036075972233530368056607402728431079, 571420279584329144562747469796889322443548, 0, (-80), (-80)⟩], [], []⟩

theorem S50411C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B50411 S50411C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 50411.C1. -/

theorem S50411D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B50411 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S50411C1 ρ hρ

/-- 证书叶 50411.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S50411C2P : TMParams :=
  ⟨[], [], []⟩

theorem S50411C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B50411 S50411C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 50411.C2. -/

theorem S50411D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B50411 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S50411C2 ρ hρ

/-- 导数叶 50411（+∂x3f，then 支，全盒）. -/

def DP50411 : TMParams :=
  ⟨[⟨7095068573672059940161113343728518130813292, 7095068573672059940161113343728518130813292, 861269944446996512723354274195017593001380327659, (-80), (-80)⟩, ⟨7095068573672059940161113343728518130813292, 7095068573672059940161113343728518130813292, 861269944446996512723354274195017593001380327659, (-80), (-80)⟩, ⟨7095068573672059940161113343728518130813292, 7095068573672059940161113343728518130813292, 861269944446996512723354274195017593001380327659, (-80), (-80)⟩, ⟨7095068573672059940161113343728518130813292, 7095068573672059940161113343728518130813292, 861269944446996512723354274195017593001380327659, (-80), (-80)⟩, ⟨7095068573672059940161113343728518130813292, 7095068573672059940161113343728518130813292, 861269944446996512723354274195017593001380327659, (-80), (-80)⟩, ⟨7095068573672059940161113343728518130813292, 7095068573672059940161113343728518130813292, 861269944446996512723354274195017593001380327659, (-80), (-80)⟩, ⟨7095068573672059940161113343728518130813292, 7095068573672059940161113343728518130813292, 861269944446996512723354274195017593001380327659, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der50411 :
    checkPosTMHull (derivIExpr E549 2) B50411 DP50411
    = true := by
  decide

/-- 面叶 50411（lo 面）. -/

def FB50411 : Fin 6 → DInterval := faceBoxLo B50411 2

def PF50411 : TMParams :=
  ⟨[⟨77393147831856075024032027271049817181531, 549763347317626226906186261775164216531352, 0, (-80), (-80)⟩, ⟨7057123612128792449237306933341409928326572, 7057123612128792449237306933341409928326572, 866306602518577379814138298791727847208253910870, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face50411 :
    checkPosTMHull E549 FB50411 PF50411
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 50411，then 支）. -/

def DSafe50411 : DerivSafeOn B50411 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S50411D2) S50411D1) (Or.inr (Or.inr rfl))) S50411D0)))

/-- mono 折叠组合（叶 50411，两叶引用零重算）. -/

theorem Fold50411 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B50411 2 PF50411 DP50411 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B50411 DP50411 = true := Der50411
  have h2 : checkPosTMHull E549 (faceBoxLo B50411 2) PF50411 = true := Face50411
  show (checkPosTMHull (derivIExpr E549 2) B50411 DP50411
      && checkPosTMHull E549 (faceBoxLo B50411 2) PF50411) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 50411）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem50411 (ρ : Fin 6 → ℝ) (hρ : boxMem B50411 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe50411 Fold50411 hρ

#print axioms Sem50411

/-- 叶 50599（then 支，lo 面）原盒. -/

def B50599 : Fin 6 → DInterval :=
  ![⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩]

/-- 证书叶 50599.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S50599C0P : TMParams :=
  ⟨[⟨70888122075408775124737117923044336398644, 573206764673491054136303002796709144317760, 0, (-80), (-80)⟩], [], []⟩

theorem S50599C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B50599 S50599C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 50599.C0. -/

theorem S50599D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B50599 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S50599C0 ρ hρ

/-- 证书叶 50599.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S50599C1P : TMParams :=
  ⟨[⟨70888122075408775124737117923044336398644, 573206764673491054136303002796709144317760, 0, (-80), (-80)⟩], [], []⟩

theorem S50599C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B50599 S50599C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 50599.C1. -/

theorem S50599D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B50599 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S50599C1 ρ hρ

/-- 证书叶 50599.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S50599C2P : TMParams :=
  ⟨[], [], []⟩

theorem S50599C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B50599 S50599C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 50599.C2. -/

theorem S50599D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B50599 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S50599C2 ρ hρ

/-- 导数叶 50599（+∂x3f，then 支，全盒）. -/

def DP50599 : TMParams :=
  ⟨[⟨7130576355585600404710250837288678832430994, 7130576355585600404710250837288678832430994, 865853364745739905647820650180318467849310550668, (-80), (-80)⟩, ⟨7130576355585600404710250837288678832430994, 7130576355585600404710250837288678832430994, 865853364745739905647820650180318467849310550668, (-80), (-80)⟩, ⟨7130576355585600404710250837288678832430994, 7130576355585600404710250837288678832430994, 865853364745739905647820650180318467849310550668, (-80), (-80)⟩, ⟨7130576355585600404710250837288678832430994, 7130576355585600404710250837288678832430994, 865853364745739905647820650180318467849310550668, (-80), (-80)⟩, ⟨7130576355585600404710250837288678832430994, 7130576355585600404710250837288678832430994, 865853364745739905647820650180318467849310550668, (-80), (-80)⟩, ⟨7130576355585600404710250837288678832430994, 7130576355585600404710250837288678832430994, 865853364745739905647820650180318467849310550668, (-80), (-80)⟩, ⟨7130576355585600404710250837288678832430994, 7130576355585600404710250837288678832430994, 865853364745739905647820650180318467849310550668, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der50599 :
    checkPosTMHull (derivIExpr E549 2) B50599 DP50599
    = true := by
  decide

/-- 面叶 50599（lo 面）. -/

def FB50599 : Fin 6 → DInterval := faceBoxLo B50599 2

def PF50599 : TMParams :=
  ⟨[⟨39083719006502814460183870996359782814931, 275836499272300266594952216459196039192336, 0, (-80), (-80)⟩, ⟨7093551185278820622800978276595066474856885, 7093551185278820622800978276595066474856885, 870852757832911254429725346152883251869864775775, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face50599 :
    checkPosTMHull E549 FB50599 PF50599
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 50599，then 支）. -/

def DSafe50599 : DerivSafeOn B50599 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S50599D2) S50599D1) (Or.inr (Or.inr rfl))) S50599D0)))

/-- mono 折叠组合（叶 50599，两叶引用零重算）. -/

theorem Fold50599 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B50599 2 PF50599 DP50599 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B50599 DP50599 = true := Der50599
  have h2 : checkPosTMHull E549 (faceBoxLo B50599 2) PF50599 = true := Face50599
  show (checkPosTMHull (derivIExpr E549 2) B50599 DP50599
      && checkPosTMHull E549 (faceBoxLo B50599 2) PF50599) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 50599）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem50599 (ρ : Fin 6 → ℝ) (hρ : boxMem B50599 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe50599 Fold50599 hρ

#print axioms Sem50599

/-- 叶 50756（then 支，lo 面）原盒. -/

def B50756 : Fin 6 → DInterval :=
  ![⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨10264971839, -32⟩⟩]

/-- 证书叶 50756.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S50756C0P : TMParams :=
  ⟨[⟨127813537321158821785625981776375277894073, 305419081683567969123331497768168918048670, 0, (-80), (-80)⟩], [], []⟩

theorem S50756C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B50756 S50756C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 50756.C0. -/

theorem S50756D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B50756 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S50756C0 ρ hρ

/-- 证书叶 50756.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S50756C1P : TMParams :=
  ⟨[⟨127813537321158821785625981776375277894073, 305419081683567969123331497768168918048670, 0, (-80), (-80)⟩], [], []⟩

theorem S50756C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B50756 S50756C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 50756.C1. -/

theorem S50756D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B50756 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S50756C1 ρ hρ

/-- 证书叶 50756.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S50756C2P : TMParams :=
  ⟨[], [], []⟩

theorem S50756C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B50756 S50756C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 50756.C2. -/

theorem S50756D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B50756 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S50756C2 ρ hρ

/-- 导数叶 50756（+∂x3f，then 支，全盒）. -/

def DP50756 : TMParams :=
  ⟨[⟨7358696687152660698394994254709029371617878, 7358696687152660698394994254709029371617878, 880487106413179020454284937191475015405090312651, (-80), (-80)⟩, ⟨7358696687152660698394994254709029371617878, 7358696687152660698394994254709029371617878, 880487106413179020454284937191475015405090312651, (-80), (-80)⟩, ⟨7358696687152660698394994254709029371617878, 7358696687152660698394994254709029371617878, 880487106413179020454284937191475015405090312651, (-80), (-80)⟩, ⟨7358696687152660698394994254709029371617878, 7358696687152660698394994254709029371617878, 880487106413179020454284937191475015405090312651, (-80), (-80)⟩, ⟨7358696687152660698394994254709029371617878, 7358696687152660698394994254709029371617878, 880487106413179020454284937191475015405090312651, (-80), (-80)⟩, ⟨7358696687152660698394994254709029371617878, 7358696687152660698394994254709029371617878, 880487106413179020454284937191475015405090312651, (-80), (-80)⟩, ⟨7358696687152660698394994254709029371617878, 7358696687152660698394994254709029371617878, 880487106413179020454284937191475015405090312651, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der50756 :
    checkPosTMHull (derivIExpr E549 2) B50756 DP50756
    = true := by
  decide

/-- 面叶 50756（lo 面）. -/

def FB50756 : Fin 6 → DInterval := faceBoxLo B50756 2

def PF50756 : TMParams :=
  ⟨[⟨143830765453589232501772547207399618116850, 146906838906681967204747426476186712860991, 0, (-80), (-80)⟩, ⟨7298181364441581064700757817353518644689378, 7298181364441581064700757817353518644689378, 886865088229794486360803789151425497590479449105, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face50756 :
    checkPosTMHull E549 FB50756 PF50756
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 50756，then 支）. -/

def DSafe50756 : DerivSafeOn B50756 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S50756D2) S50756D1) (Or.inr (Or.inr rfl))) S50756D0)))

/-- mono 折叠组合（叶 50756，两叶引用零重算）. -/

theorem Fold50756 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B50756 2 PF50756 DP50756 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B50756 DP50756 = true := Der50756
  have h2 : checkPosTMHull E549 (faceBoxLo B50756 2) PF50756 = true := Face50756
  show (checkPosTMHull (derivIExpr E549 2) B50756 DP50756
      && checkPosTMHull E549 (faceBoxLo B50756 2) PF50756) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 50756）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem50756 (ρ : Fin 6 → ℝ) (hρ : boxMem B50756 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe50756 Fold50756 hρ

#print axioms Sem50756

/-- 叶 50909（then 支，lo 面）原盒. -/

def B50909 : Fin 6 → DInterval :=
  ![⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩]

/-- 证书叶 50909.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S50909C0P : TMParams :=
  ⟨[⟨288231710649104630985129627597588895129935, 291170479902012066041711153686092357302668, 0, (-80), (-80)⟩], [], []⟩

theorem S50909C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B50909 S50909C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 50909.C0. -/

theorem S50909D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B50909 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S50909C0 ρ hρ

/-- 证书叶 50909.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S50909C1P : TMParams :=
  ⟨[⟨288231710649104630985129627597588895129935, 291170479902012066041711153686092357302668, 0, (-80), (-80)⟩], [], []⟩

theorem S50909C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B50909 S50909C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 50909.C1. -/

theorem S50909D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B50909 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S50909C1 ρ hρ

/-- 证书叶 50909.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S50909C2P : TMParams :=
  ⟨[], [], []⟩

theorem S50909C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B50909 S50909C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 50909.C2. -/

theorem S50909D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B50909 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S50909C2 ρ hρ

/-- 导数叶 50909（+∂x3f，then 支，全盒）. -/

def DP50909 : TMParams :=
  ⟨[⟨7246604688226095106337767622707462794904215, 7246604688226095106337767622707462794904215, 880202238530310121662088469450256686425785006614, (-80), (-80)⟩, ⟨7246604688226095106337767622707462794904215, 7246604688226095106337767622707462794904215, 880202238530310121662088469450256686425785006614, (-80), (-80)⟩, ⟨7246604688226095106337767622707462794904215, 7246604688226095106337767622707462794904215, 880202238530310121662088469450256686425785006614, (-80), (-80)⟩, ⟨7246604688226095106337767622707462794904215, 7246604688226095106337767622707462794904215, 880202238530310121662088469450256686425785006614, (-80), (-80)⟩, ⟨7246604688226095106337767622707462794904215, 7246604688226095106337767622707462794904215, 880202238530310121662088469450256686425785006614, (-80), (-80)⟩, ⟨7246604688226095106337767622707462794904215, 7246604688226095106337767622707462794904215, 880202238530310121662088469450256686425785006614, (-80), (-80)⟩, ⟨7246604688226095106337767622707462794904215, 7246604688226095106337767622707462794904215, 880202238530310121662088469450256686425785006614, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der50909 :
    checkPosTMHull (derivIExpr E549 2) B50909 DP50909
    = true := by
  decide

/-- 面叶 50909（lo 面）. -/

def FB50909 : Fin 6 → DInterval := faceBoxLo B50909 2

def PF50909 : TMParams :=
  ⟨[⟨316546591000147424122129001048970167957679, 279942361578733170919649148712506466197088, 0, (-80), (-80)⟩, ⟨7195540990195465843785798925412166575782794, 7195540990195465843785798925412166575782794, 885390713574966894588448969534781748470329823714, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face50909 :
    checkPosTMHull E549 FB50909 PF50909
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 50909，then 支）. -/

def DSafe50909 : DerivSafeOn B50909 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S50909D2) S50909D1) (Or.inr (Or.inr rfl))) S50909D0)))

/-- mono 折叠组合（叶 50909，两叶引用零重算）. -/

theorem Fold50909 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B50909 2 PF50909 DP50909 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B50909 DP50909 = true := Der50909
  have h2 : checkPosTMHull E549 (faceBoxLo B50909 2) PF50909 = true := Face50909
  show (checkPosTMHull (derivIExpr E549 2) B50909 DP50909
      && checkPosTMHull E549 (faceBoxLo B50909 2) PF50909) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 50909）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem50909 (ρ : Fin 6 → ℝ) (hρ : boxMem B50909 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe50909 Fold50909 hρ

#print axioms Sem50909

/-- 叶 51065（then 支，lo 面）原盒. -/

def B51065 : Fin 6 → DInterval :=
  ![⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩]

/-- 证书叶 51065.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S51065C0P : TMParams :=
  ⟨[⟨66370780316366157838866944372715233572957, 544339578103473916918127988453406227501351, 0, (-80), (-80)⟩], [], []⟩

theorem S51065C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B51065 S51065C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 51065.C0. -/

theorem S51065D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B51065 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S51065C0 ρ hρ

/-- 证书叶 51065.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S51065C1P : TMParams :=
  ⟨[⟨66370780316366157838866944372715233572957, 544339578103473916918127988453406227501351, 0, (-80), (-80)⟩], [], []⟩

theorem S51065C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B51065 S51065C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 51065.C1. -/

theorem S51065D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B51065 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S51065C1 ρ hρ

/-- 证书叶 51065.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S51065C2P : TMParams :=
  ⟨[], [], []⟩

theorem S51065C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B51065 S51065C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 51065.C2. -/

theorem S51065D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B51065 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S51065C2 ρ hρ

/-- 导数叶 51065（+∂x3f，then 支，全盒）. -/

def DP51065 : TMParams :=
  ⟨[⟨6750577491169061975564058885919252077859343, 6750577491169061975564058885919252077859343, 818523756954606786228984045298317434291361216971, (-80), (-80)⟩, ⟨6750577491169061975564058885919252077859343, 6750577491169061975564058885919252077859343, 818523756954606786228984045298317434291361216971, (-80), (-80)⟩, ⟨6750577491169061975564058885919252077859343, 6750577491169061975564058885919252077859343, 818523756954606786228984045298317434291361216971, (-80), (-80)⟩, ⟨6750577491169061975564058885919252077859343, 6750577491169061975564058885919252077859343, 818523756954606786228984045298317434291361216971, (-80), (-80)⟩, ⟨6750577491169061975564058885919252077859343, 6750577491169061975564058885919252077859343, 818523756954606786228984045298317434291361216971, (-80), (-80)⟩, ⟨6750577491169061975564058885919252077859343, 6750577491169061975564058885919252077859343, 818523756954606786228984045298317434291361216971, (-80), (-80)⟩, ⟨6750577491169061975564058885919252077859343, 6750577491169061975564058885919252077859343, 818523756954606786228984045298317434291361216971, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der51065 :
    checkPosTMHull (derivIExpr E549 2) B51065 DP51065
    = true := by
  decide

/-- 面叶 51065（lo 面）. -/

def FB51065 : Fin 6 → DInterval := faceBoxLo B51065 2

def PF51065 : TMParams :=
  ⟨[⟨73195696130613630239373088342314040711834, 523438923142675471361544232489053125149831, 0, (-80), (-80)⟩, ⟨6707231212436383998508464381830939751393571, 6707231212436383998508464381830939751393571, 823495180122907335716286427323964473326130855315, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face51065 :
    checkPosTMHull E549 FB51065 PF51065
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 51065，then 支）. -/

def DSafe51065 : DerivSafeOn B51065 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S51065D2) S51065D1) (Or.inr (Or.inr rfl))) S51065D0)))

/-- mono 折叠组合（叶 51065，两叶引用零重算）. -/

theorem Fold51065 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B51065 2 PF51065 DP51065 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B51065 DP51065 = true := Der51065
  have h2 : checkPosTMHull E549 (faceBoxLo B51065 2) PF51065 = true := Face51065
  show (checkPosTMHull (derivIExpr E549 2) B51065 DP51065
      && checkPosTMHull E549 (faceBoxLo B51065 2) PF51065) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 51065）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem51065 (ρ : Fin 6 → ℝ) (hρ : boxMem B51065 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe51065 Fold51065 hρ

#print axioms Sem51065

/-- 叶 51217（then 支，lo 面）原盒. -/

def B51217 : Fin 6 → DInterval :=
  ![⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨10264971839, -32⟩⟩]

/-- 证书叶 51217.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S51217C0P : TMParams :=
  ⟨[⟨123490763670578222842632173616870959364266, 303290296674480218415107079490235908704511, 0, (-80), (-80)⟩], [], []⟩

theorem S51217C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B51217 S51217C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 51217.C0. -/

theorem S51217D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B51217 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S51217C0 ρ hρ

/-- 证书叶 51217.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S51217C1P : TMParams :=
  ⟨[⟨123490763670578222842632173616870959364266, 303290296674480218415107079490235908704511, 0, (-80), (-80)⟩], [], []⟩

theorem S51217C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B51217 S51217C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 51217.C1. -/

theorem S51217D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B51217 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S51217C1 ρ hρ

/-- 证书叶 51217.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S51217C2P : TMParams :=
  ⟨[], [], []⟩

theorem S51217C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B51217 S51217C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 51217.C2. -/

theorem S51217D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B51217 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S51217C2 ρ hρ

/-- 导数叶 51217（+∂x3f，then 支，全盒）. -/

def DP51217 : TMParams :=
  ⟨[⟨7274414086727319692475407652617003342942673, 7274414086727319692475407652617003342942673, 870144517182746665778828586465594131265975100558, (-80), (-80)⟩, ⟨7274414086727319692475407652617003342942673, 7274414086727319692475407652617003342942673, 870144517182746665778828586465594131265975100558, (-80), (-80)⟩, ⟨7274414086727319692475407652617003342942673, 7274414086727319692475407652617003342942673, 870144517182746665778828586465594131265975100558, (-80), (-80)⟩, ⟨7274414086727319692475407652617003342942673, 7274414086727319692475407652617003342942673, 870144517182746665778828586465594131265975100558, (-80), (-80)⟩, ⟨7274414086727319692475407652617003342942673, 7274414086727319692475407652617003342942673, 870144517182746665778828586465594131265975100558, (-80), (-80)⟩, ⟨7274414086727319692475407652617003342942673, 7274414086727319692475407652617003342942673, 870144517182746665778828586465594131265975100558, (-80), (-80)⟩, ⟨7274414086727319692475407652617003342942673, 7274414086727319692475407652617003342942673, 870144517182746665778828586465594131265975100558, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der51217 :
    checkPosTMHull (derivIExpr E549 2) B51217 DP51217
    = true := by
  decide

/-- 面叶 51217（lo 面）. -/

def FB51217 : Fin 6 → DInterval := faceBoxLo B51217 2

def PF51217 : TMParams :=
  ⟨[⟨140804912589895888808711602772629444081861, 145917013659041547486452866302031543172663, 0, (-80), (-80)⟩, ⟨7226778047133118419234839214009210340066895, 7226778047133118419234839214009210340066895, 876478774257552368096118203874250949526985199249, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face51217 :
    checkPosTMHull E549 FB51217 PF51217
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 51217，then 支）. -/

def DSafe51217 : DerivSafeOn B51217 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S51217D2) S51217D1) (Or.inr (Or.inr rfl))) S51217D0)))

/-- mono 折叠组合（叶 51217，两叶引用零重算）. -/

theorem Fold51217 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B51217 2 PF51217 DP51217 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B51217 DP51217 = true := Der51217
  have h2 : checkPosTMHull E549 (faceBoxLo B51217 2) PF51217 = true := Face51217
  show (checkPosTMHull (derivIExpr E549 2) B51217 DP51217
      && checkPosTMHull E549 (faceBoxLo B51217 2) PF51217) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 51217）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem51217 (ρ : Fin 6 → ℝ) (hρ : boxMem B51217 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe51217 Fold51217 hρ

#print axioms Sem51217

/-- 叶 51369（then 支，lo 面）原盒. -/

def B51369 : Fin 6 → DInterval :=
  ![⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩]

/-- 证书叶 51369.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S51369C0P : TMParams :=
  ⟨[⟨64539892821894720982781185313179286707414, 545345053770460750358868172540949328395369, 0, (-80), (-80)⟩], [], []⟩

theorem S51369C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B51369 S51369C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 51369.C0. -/

theorem S51369D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B51369 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S51369C0 ρ hρ

/-- 证书叶 51369.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S51369C1P : TMParams :=
  ⟨[⟨64539892821894720982781185313179286707414, 545345053770460750358868172540949328395369, 0, (-80), (-80)⟩], [], []⟩

theorem S51369C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B51369 S51369C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 51369.C1. -/

theorem S51369D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B51369 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S51369C1 ρ hρ

/-- 证书叶 51369.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S51369C2P : TMParams :=
  ⟨[], [], []⟩

theorem S51369C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B51369 S51369C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 51369.C2. -/

theorem S51369D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B51369 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S51369C2 ρ hρ

/-- 导数叶 51369（+∂x3f，then 支，全盒）. -/

def DP51369 : TMParams :=
  ⟨[⟨6722315818080321994781391052482949160184052, 6722315818080321994781391052482949160184052, 814434713995469181635997851121154995536125004257, (-80), (-80)⟩, ⟨6722315818080321994781391052482949160184052, 6722315818080321994781391052482949160184052, 814434713995469181635997851121154995536125004257, (-80), (-80)⟩, ⟨6722315818080321994781391052482949160184052, 6722315818080321994781391052482949160184052, 814434713995469181635997851121154995536125004257, (-80), (-80)⟩, ⟨6722315818080321994781391052482949160184052, 6722315818080321994781391052482949160184052, 814434713995469181635997851121154995536125004257, (-80), (-80)⟩, ⟨6722315818080321994781391052482949160184052, 6722315818080321994781391052482949160184052, 814434713995469181635997851121154995536125004257, (-80), (-80)⟩, ⟨6722315818080321994781391052482949160184052, 6722315818080321994781391052482949160184052, 814434713995469181635997851121154995536125004257, (-80), (-80)⟩, ⟨6722315818080321994781391052482949160184052, 6722315818080321994781391052482949160184052, 814434713995469181635997851121154995536125004257, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der51369 :
    checkPosTMHull (derivIExpr E549 2) B51369 DP51369
    = true := by
  decide

/-- 面叶 51369（lo 面）. -/

def FB51369 : Fin 6 → DInterval := faceBoxLo B51369 2

def PF51369 : TMParams :=
  ⟨[⟨72001948105774575744490323937952674829718, 523685502865516364786390893661374686030321, 0, (-80), (-80)⟩, ⟨6681293179144398315932445975287919059177972, 6681293179144398315932445975287919059177972, 819488140272209719008801956284319684848959845473, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face51369 :
    checkPosTMHull E549 FB51369 PF51369
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 51369，then 支）. -/

def DSafe51369 : DerivSafeOn B51369 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S51369D2) S51369D1) (Or.inr (Or.inr rfl))) S51369D0)))

/-- mono 折叠组合（叶 51369，两叶引用零重算）. -/

theorem Fold51369 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B51369 2 PF51369 DP51369 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B51369 DP51369 = true := Der51369
  have h2 : checkPosTMHull E549 (faceBoxLo B51369 2) PF51369 = true := Face51369
  show (checkPosTMHull (derivIExpr E549 2) B51369 DP51369
      && checkPosTMHull E549 (faceBoxLo B51369 2) PF51369) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 51369）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem51369 (ρ : Fin 6 → ℝ) (hρ : boxMem B51369 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe51369 Fold51369 hρ

#print axioms Sem51369

/-- 叶 51534（then 支，lo 面）原盒. -/

def B51534 : Fin 6 → DInterval :=
  ![⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩]

/-- 证书叶 51534.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S51534C0P : TMParams :=
  ⟨[⟨67117580974267796375561608162748646684816, 560400917213206210016996506857950760034133, 0, (-80), (-80)⟩], [], []⟩

theorem S51534C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B51534 S51534C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 51534.C0. -/

theorem S51534D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B51534 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S51534C0 ρ hρ

/-- 证书叶 51534.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S51534C1P : TMParams :=
  ⟨[⟨67117580974267796375561608162748646684816, 560400917213206210016996506857950760034133, 0, (-80), (-80)⟩], [], []⟩

theorem S51534C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B51534 S51534C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 51534.C1. -/

theorem S51534D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B51534 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S51534C1 ρ hρ

/-- 证书叶 51534.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S51534C2P : TMParams :=
  ⟨[], [], []⟩

theorem S51534C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B51534 S51534C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 51534.C2. -/

theorem S51534D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B51534 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S51534C2 ρ hρ

/-- 导数叶 51534（+∂x3f，then 支，全盒）. -/

def DP51534 : TMParams :=
  ⟨[⟨6924826951959558581289312151953399737630909, 6924826951959558581289312151953399737630909, 839662125445992441322983280015855621033770876444, (-80), (-80)⟩, ⟨6924826951959558581289312151953399737630909, 6924826951959558581289312151953399737630909, 839662125445992441322983280015855621033770876444, (-80), (-80)⟩, ⟨6924826951959558581289312151953399737630909, 6924826951959558581289312151953399737630909, 839662125445992441322983280015855621033770876444, (-80), (-80)⟩, ⟨6924826951959558581289312151953399737630909, 6924826951959558581289312151953399737630909, 839662125445992441322983280015855621033770876444, (-80), (-80)⟩, ⟨6924826951959558581289312151953399737630909, 6924826951959558581289312151953399737630909, 839662125445992441322983280015855621033770876444, (-80), (-80)⟩, ⟨6924826951959558581289312151953399737630909, 6924826951959558581289312151953399737630909, 839662125445992441322983280015855621033770876444, (-80), (-80)⟩, ⟨6924826951959558581289312151953399737630909, 6924826951959558581289312151953399737630909, 839662125445992441322983280015855621033770876444, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der51534 :
    checkPosTMHull (derivIExpr E549 2) B51534 DP51534
    = true := by
  decide

/-- 面叶 51534（lo 面）. -/

def FB51534 : Fin 6 → DInterval := faceBoxLo B51534 2

def PF51534 : TMParams :=
  ⟨[⟨74669607710817444029946358254050616428193, 269708980356317614121460544329731459829754, 0, (-80), (-80)⟩, ⟨6895129256092571284129876246770550974476026, 6895129256092571284129876246770550974476026, 844676254281378109439699824602925195492815718363, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face51534 :
    checkPosTMHull E549 FB51534 PF51534
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 51534，then 支）. -/

def DSafe51534 : DerivSafeOn B51534 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S51534D2) S51534D1) (Or.inr (Or.inr rfl))) S51534D0)))

/-- mono 折叠组合（叶 51534，两叶引用零重算）. -/

theorem Fold51534 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B51534 2 PF51534 DP51534 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B51534 DP51534 = true := Der51534
  have h2 : checkPosTMHull E549 (faceBoxLo B51534 2) PF51534 = true := Face51534
  show (checkPosTMHull (derivIExpr E549 2) B51534 DP51534
      && checkPosTMHull E549 (faceBoxLo B51534 2) PF51534) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 51534）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem51534 (ρ : Fin 6 → ℝ) (hρ : boxMem B51534 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe51534 Fold51534 hρ

#print axioms Sem51534

/-- 叶 51688（then 支，lo 面）原盒. -/

def B51688 : Fin 6 → DInterval :=
  ![⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩]

/-- 证书叶 51688.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S51688C0P : TMParams :=
  ⟨[⟨282782914175570030475417766884828950634122, 289724813383448061597395500724407210985891, 0, (-80), (-80)⟩], [], []⟩

theorem S51688C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B51688 S51688C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 51688.C0. -/

theorem S51688D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B51688 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S51688C0 ρ hρ

/-- 证书叶 51688.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S51688C1P : TMParams :=
  ⟨[⟨282782914175570030475417766884828950634122, 289724813383448061597395500724407210985891, 0, (-80), (-80)⟩], [], []⟩

theorem S51688C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B51688 S51688C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 51688.C1. -/

theorem S51688D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B51688 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S51688C1 ρ hρ

/-- 证书叶 51688.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S51688C2P : TMParams :=
  ⟨[], [], []⟩

theorem S51688C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B51688 S51688C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 51688.C2. -/

theorem S51688D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B51688 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S51688C2 ρ hρ

/-- 导数叶 51688（+∂x3f，then 支，全盒）. -/

def DP51688 : TMParams :=
  ⟨[⟨7189306161927188697899681347825183718055788, 7189306161927188697899681347825183718055788, 872783509340147500108830191240755952068948413963, (-80), (-80)⟩, ⟨7189306161927188697899681347825183718055788, 7189306161927188697899681347825183718055788, 872783509340147500108830191240755952068948413963, (-80), (-80)⟩, ⟨7189306161927188697899681347825183718055788, 7189306161927188697899681347825183718055788, 872783509340147500108830191240755952068948413963, (-80), (-80)⟩, ⟨7189306161927188697899681347825183718055788, 7189306161927188697899681347825183718055788, 872783509340147500108830191240755952068948413963, (-80), (-80)⟩, ⟨7189306161927188697899681347825183718055788, 7189306161927188697899681347825183718055788, 872783509340147500108830191240755952068948413963, (-80), (-80)⟩, ⟨7189306161927188697899681347825183718055788, 7189306161927188697899681347825183718055788, 872783509340147500108830191240755952068948413963, (-80), (-80)⟩, ⟨7189306161927188697899681347825183718055788, 7189306161927188697899681347825183718055788, 872783509340147500108830191240755952068948413963, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der51688 :
    checkPosTMHull (derivIExpr E549 2) B51688 DP51688
    = true := by
  decide

/-- 面叶 51688（lo 面）. -/

def FB51688 : Fin 6 → DInterval := faceBoxLo B51688 2

def PF51688 : TMParams :=
  ⟨[⟨311611466775558966825697654931284823659805, 139071731036378858329436719174890430808742, 0, (-80), (-80)⟩, ⟨7131372423448848593964414735197115538593967, 7131372423448848593964414735197115538593967, 878031217572915757362801518589020615337357499110, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face51688 :
    checkPosTMHull E549 FB51688 PF51688
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 51688，then 支）. -/

def DSafe51688 : DerivSafeOn B51688 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S51688D2) S51688D1) (Or.inr (Or.inr rfl))) S51688D0)))

/-- mono 折叠组合（叶 51688，两叶引用零重算）. -/

theorem Fold51688 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B51688 2 PF51688 DP51688 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B51688 DP51688 = true := Der51688
  have h2 : checkPosTMHull E549 (faceBoxLo B51688 2) PF51688 = true := Face51688
  show (checkPosTMHull (derivIExpr E549 2) B51688 DP51688
      && checkPosTMHull E549 (faceBoxLo B51688 2) PF51688) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 51688）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem51688 (ρ : Fin 6 → ℝ) (hρ : boxMem B51688 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe51688 Fold51688 hρ

#print axioms Sem51688

/-- 叶 51840（then 支，lo 面）原盒. -/

def B51840 : Fin 6 → DInterval :=
  ![⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩]

/-- 证书叶 51840.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S51840C0P : TMParams :=
  ⟨[⟨284187237212268944335118882885026690951994, 292622259187501769295332468570791643216261, 0, (-80), (-80)⟩], [], []⟩

theorem S51840C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B51840 S51840C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 51840.C0. -/

theorem S51840D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B51840 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S51840C0 ρ hρ

/-- 证书叶 51840.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S51840C1P : TMParams :=
  ⟨[⟨284187237212268944335118882885026690951994, 292622259187501769295332468570791643216261, 0, (-80), (-80)⟩], [], []⟩

theorem S51840C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B51840 S51840C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 51840.C1. -/

theorem S51840D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B51840 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S51840C1 ρ hρ

/-- 证书叶 51840.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S51840C2P : TMParams :=
  ⟨[], [], []⟩

theorem S51840C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B51840 S51840C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 51840.C2. -/

theorem S51840D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B51840 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S51840C2 ρ hρ

/-- 导数叶 51840（+∂x3f，then 支，全盒）. -/

def DP51840 : TMParams :=
  ⟨[⟨7253944576968329216828522461530311488046971, 7253944576968329216828522461530311488046971, 880688205394210846438586953686043602862102840017, (-80), (-80)⟩, ⟨7253944576968329216828522461530311488046971, 7253944576968329216828522461530311488046971, 880688205394210846438586953686043602862102840017, (-80), (-80)⟩, ⟨7253944576968329216828522461530311488046971, 7253944576968329216828522461530311488046971, 880688205394210846438586953686043602862102840017, (-80), (-80)⟩, ⟨7253944576968329216828522461530311488046971, 7253944576968329216828522461530311488046971, 880688205394210846438586953686043602862102840017, (-80), (-80)⟩, ⟨7253944576968329216828522461530311488046971, 7253944576968329216828522461530311488046971, 880688205394210846438586953686043602862102840017, (-80), (-80)⟩, ⟨7253944576968329216828522461530311488046971, 7253944576968329216828522461530311488046971, 880688205394210846438586953686043602862102840017, (-80), (-80)⟩, ⟨7253944576968329216828522461530311488046971, 7253944576968329216828522461530311488046971, 880688205394210846438586953686043602862102840017, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der51840 :
    checkPosTMHull (derivIExpr E549 2) B51840 DP51840
    = true := by
  decide

/-- 面叶 51840（lo 面）. -/

def FB51840 : Fin 6 → DInterval := faceBoxLo B51840 2

def PF51840 : TMParams :=
  ⟨[⟨314226110216024202789484535109596578497114, 281271536615893765994697945587547228274924, 0, (-80), (-80)⟩, ⟨7207590902607137132470343861255526104113415, 7207590902607137132470343861255526104113415, 885934279515958191107286353441138693598755862882, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face51840 :
    checkPosTMHull E549 FB51840 PF51840
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 51840，then 支）. -/

def DSafe51840 : DerivSafeOn B51840 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S51840D2) S51840D1) (Or.inr (Or.inr rfl))) S51840D0)))

/-- mono 折叠组合（叶 51840，两叶引用零重算）. -/

theorem Fold51840 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B51840 2 PF51840 DP51840 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B51840 DP51840 = true := Der51840
  have h2 : checkPosTMHull E549 (faceBoxLo B51840 2) PF51840 = true := Face51840
  show (checkPosTMHull (derivIExpr E549 2) B51840 DP51840
      && checkPosTMHull E549 (faceBoxLo B51840 2) PF51840) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 51840）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem51840 (ρ : Fin 6 → ℝ) (hρ : boxMem B51840 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe51840 Fold51840 hρ

#print axioms Sem51840

/-- 叶 51992（then 支，lo 面）原盒. -/

def B51992 : Fin 6 → DInterval :=
  ![⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩]

/-- 证书叶 51992.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S51992C0P : TMParams :=
  ⟨[⟨67303293103655746901814101934357735448660, 555896837478278101616705165955770946086643, 0, (-80), (-80)⟩], [], []⟩

theorem S51992C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B51992 S51992C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 51992.C0. -/

theorem S51992D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B51992 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S51992C0 ρ hρ

/-- 证书叶 51992.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S51992C1P : TMParams :=
  ⟨[⟨67303293103655746901814101934357735448660, 555896837478278101616705165955770946086643, 0, (-80), (-80)⟩], [], []⟩

theorem S51992C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B51992 S51992C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 51992.C1. -/

theorem S51992D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B51992 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S51992C1 ρ hρ

/-- 证书叶 51992.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S51992C2P : TMParams :=
  ⟨[], [], []⟩

theorem S51992C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B51992 S51992C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 51992.C2. -/

theorem S51992D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B51992 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S51992C2 ρ hρ

/-- 导数叶 51992（+∂x3f，then 支，全盒）. -/

def DP51992 : TMParams :=
  ⟨[⟨6884300491658112155612347168797562243375972, 6884300491658112155612347168797562243375972, 834916366593238428336171998970727192359976190915, (-80), (-80)⟩, ⟨6884300491658112155612347168797562243375972, 6884300491658112155612347168797562243375972, 834916366593238428336171998970727192359976190915, (-80), (-80)⟩, ⟨6884300491658112155612347168797562243375972, 6884300491658112155612347168797562243375972, 834916366593238428336171998970727192359976190915, (-80), (-80)⟩, ⟨6884300491658112155612347168797562243375972, 6884300491658112155612347168797562243375972, 834916366593238428336171998970727192359976190915, (-80), (-80)⟩, ⟨6884300491658112155612347168797562243375972, 6884300491658112155612347168797562243375972, 834916366593238428336171998970727192359976190915, (-80), (-80)⟩, ⟨6884300491658112155612347168797562243375972, 6884300491658112155612347168797562243375972, 834916366593238428336171998970727192359976190915, (-80), (-80)⟩, ⟨6884300491658112155612347168797562243375972, 6884300491658112155612347168797562243375972, 834916366593238428336171998970727192359976190915, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der51992 :
    checkPosTMHull (derivIExpr E549 2) B51992 DP51992
    = true := by
  decide

/-- 面叶 51992（lo 面）. -/

def FB51992 : Fin 6 → DInterval := faceBoxLo B51992 2

def PF51992 : TMParams :=
  ⟨[⟨74280806786322140154236725804866595598452, 534565939039604449822649953755880154609264, 0, (-80), (-80)⟩, ⟨6839392430653516502542784486357710347129316, 6839392430653516502542784486357710347129316, 839990229938041792346650529160179261961517702552, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face51992 :
    checkPosTMHull E549 FB51992 PF51992
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 51992，then 支）. -/

def DSafe51992 : DerivSafeOn B51992 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S51992D2) S51992D1) (Or.inr (Or.inr rfl))) S51992D0)))

/-- mono 折叠组合（叶 51992，两叶引用零重算）. -/

theorem Fold51992 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B51992 2 PF51992 DP51992 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B51992 DP51992 = true := Der51992
  have h2 : checkPosTMHull E549 (faceBoxLo B51992 2) PF51992 = true := Face51992
  show (checkPosTMHull (derivIExpr E549 2) B51992 DP51992
      && checkPosTMHull E549 (faceBoxLo B51992 2) PF51992) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 51992）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem51992 (ρ : Fin 6 → ℝ) (hρ : boxMem B51992 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe51992 Fold51992 hρ

#print axioms Sem51992

/-- 叶 52144（then 支，lo 面）原盒. -/

def B52144 : Fin 6 → DInterval :=
  ![⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩]

/-- 证书叶 52144.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S52144C0P : TMParams :=
  ⟨[⟨148575329372044230133610431614554932296710, 608968344750702716815505571817634538100179, 0, (-80), (-80)⟩], [], []⟩

theorem S52144C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B52144 S52144C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 52144.C0. -/

theorem S52144D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B52144 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S52144C0 ρ hρ

/-- 证书叶 52144.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S52144C1P : TMParams :=
  ⟨[⟨148575329372044230133610431614554932296710, 608968344750702716815505571817634538100179, 0, (-80), (-80)⟩], [], []⟩

theorem S52144C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B52144 S52144C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 52144.C1. -/

theorem S52144D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B52144 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S52144C1 ρ hρ

/-- 证书叶 52144.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S52144C2P : TMParams :=
  ⟨[], [], []⟩

theorem S52144C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B52144 S52144C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 52144.C2. -/

theorem S52144D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B52144 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S52144C2 ρ hρ

/-- 导数叶 52144（+∂x3f，then 支，全盒）. -/

def DP52144 : TMParams :=
  ⟨[⟨7557345138618087322473508299579524819584882, 7557345138618087322473508299579524819584882, 918302203626662501980330322875298803627981553166, (-80), (-80)⟩, ⟨7557345138618087322473508299579524819584882, 7557345138618087322473508299579524819584882, 918302203626662501980330322875298803627981553166, (-80), (-80)⟩, ⟨7557345138618087322473508299579524819584882, 7557345138618087322473508299579524819584882, 918302203626662501980330322875298803627981553166, (-80), (-80)⟩, ⟨7557345138618087322473508299579524819584882, 7557345138618087322473508299579524819584882, 918302203626662501980330322875298803627981553166, (-80), (-80)⟩, ⟨7557345138618087322473508299579524819584882, 7557345138618087322473508299579524819584882, 918302203626662501980330322875298803627981553166, (-80), (-80)⟩, ⟨7557345138618087322473508299579524819584882, 7557345138618087322473508299579524819584882, 918302203626662501980330322875298803627981553166, (-80), (-80)⟩, ⟨7557345138618087322473508299579524819584882, 7557345138618087322473508299579524819584882, 918302203626662501980330322875298803627981553166, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der52144 :
    checkPosTMHull (derivIExpr E549 2) B52144 DP52144
    = true := by
  decide

/-- 面叶 52144（lo 面）. -/

def FB52144 : Fin 6 → DInterval := faceBoxLo B52144 2

def PF52144 : TMParams :=
  ⟨[⟨164486768680823674812064541681340748745518, 292210064645074039172506130410594293173576, 0, (-80), (-80)⟩, ⟨7501665289297349383911065771771671055523008, 7501665289297349383911065771771671055523008, 923647829463802108337708389709799990769130279464, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face52144 :
    checkPosTMHull E549 FB52144 PF52144
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 52144，then 支）. -/

def DSafe52144 : DerivSafeOn B52144 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S52144D2) S52144D1) (Or.inr (Or.inr rfl))) S52144D0)))

/-- mono 折叠组合（叶 52144，两叶引用零重算）. -/

theorem Fold52144 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B52144 2 PF52144 DP52144 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B52144 DP52144 = true := Der52144
  have h2 : checkPosTMHull E549 (faceBoxLo B52144 2) PF52144 = true := Face52144
  show (checkPosTMHull (derivIExpr E549 2) B52144 DP52144
      && checkPosTMHull E549 (faceBoxLo B52144 2) PF52144) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 52144）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem52144 (ρ : Fin 6 → ℝ) (hρ : boxMem B52144 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe52144 Fold52144 hρ

#print axioms Sem52144

/-- 叶 52296（then 支，lo 面）原盒. -/

def B52296 : Fin 6 → DInterval :=
  ![⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩]

/-- 证书叶 52296.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S52296C0P : TMParams :=
  ⟨[⟨289188478088437767438434305206153847826827, 75769143667795515429085385070872248369556, 0, (-80), (-80)⟩], [], []⟩

theorem S52296C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B52296 S52296C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 52296.C0. -/

theorem S52296D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B52296 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S52296C0 ρ hρ

/-- 证书叶 52296.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S52296C1P : TMParams :=
  ⟨[⟨289188478088437767438434305206153847826827, 75769143667795515429085385070872248369556, 0, (-80), (-80)⟩], [], []⟩

theorem S52296C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B52296 S52296C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 52296.C1. -/

theorem S52296D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B52296 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S52296C1 ρ hρ

/-- 证书叶 52296.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S52296C2P : TMParams :=
  ⟨[], [], []⟩

theorem S52296C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B52296 S52296C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 52296.C2. -/

theorem S52296D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B52296 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S52296C2 ρ hρ

/-- 导数叶 52296（+∂x3f，then 支，全盒）. -/

def DP52296 : TMParams :=
  ⟨[⟨7489033119188928952817130428015007728990613, 7489033119188928952817130428015007728990613, 909229019364985890580553833356598258805370206911, (-80), (-80)⟩, ⟨7489033119188928952817130428015007728990613, 7489033119188928952817130428015007728990613, 909229019364985890580553833356598258805370206911, (-80), (-80)⟩, ⟨7489033119188928952817130428015007728990613, 7489033119188928952817130428015007728990613, 909229019364985890580553833356598258805370206911, (-80), (-80)⟩, ⟨7489033119188928952817130428015007728990613, 7489033119188928952817130428015007728990613, 909229019364985890580553833356598258805370206911, (-80), (-80)⟩, ⟨7489033119188928952817130428015007728990613, 7489033119188928952817130428015007728990613, 909229019364985890580553833356598258805370206911, (-80), (-80)⟩, ⟨7489033119188928952817130428015007728990613, 7489033119188928952817130428015007728990613, 909229019364985890580553833356598258805370206911, (-80), (-80)⟩, ⟨7489033119188928952817130428015007728990613, 7489033119188928952817130428015007728990613, 909229019364985890580553833356598258805370206911, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der52296 :
    checkPosTMHull (derivIExpr E549 2) B52296 DP52296
    = true := by
  decide

/-- 面叶 52296（lo 面）. -/

def FB52296 : Fin 6 → DInterval := faceBoxLo B52296 2

def PF52296 : TMParams :=
  ⟨[⟨322415731137549982802114159300069727623877, 36329894060443130724557515610227041896238, 0, (-80), (-80)⟩, ⟨7433963479262810493029614013161665658821669, 7433963479262810493029614013161665658821669, 914671011416420617692197829134653166538656101453, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face52296 :
    checkPosTMHull E549 FB52296 PF52296
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 52296，then 支）. -/

def DSafe52296 : DerivSafeOn B52296 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S52296D2) S52296D1) (Or.inr (Or.inr rfl))) S52296D0)))

/-- mono 折叠组合（叶 52296，两叶引用零重算）. -/

theorem Fold52296 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B52296 2 PF52296 DP52296 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B52296 DP52296 = true := Der52296
  have h2 : checkPosTMHull E549 (faceBoxLo B52296 2) PF52296 = true := Face52296
  show (checkPosTMHull (derivIExpr E549 2) B52296 DP52296
      && checkPosTMHull E549 (faceBoxLo B52296 2) PF52296) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 52296）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem52296 (ρ : Fin 6 → ℝ) (hρ : boxMem B52296 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe52296 Fold52296 hρ

#print axioms Sem52296

/-- 叶 52448（then 支，lo 面）原盒. -/

def B52448 : Fin 6 → DInterval :=
  ![⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩]

/-- 证书叶 52448.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S52448C0P : TMParams :=
  ⟨[⟨135415291054283680393479278712343115908105, 569625964795682284625456756907473991890851, 0, (-80), (-80)⟩], [], []⟩

theorem S52448C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B52448 S52448C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 52448.C0. -/

theorem S52448D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B52448 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S52448C0 ρ hρ

/-- 证书叶 52448.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S52448C1P : TMParams :=
  ⟨[⟨135415291054283680393479278712343115908105, 569625964795682284625456756907473991890851, 0, (-80), (-80)⟩], [], []⟩

theorem S52448C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B52448 S52448C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 52448.C1. -/

theorem S52448D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B52448 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S52448C1 ρ hρ

/-- 证书叶 52448.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S52448C2P : TMParams :=
  ⟨[], [], []⟩

theorem S52448C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B52448 S52448C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 52448.C2. -/

theorem S52448D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B52448 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S52448C2 ρ hρ

/-- 导数叶 52448（+∂x3f，then 支，全盒）. -/

def DP52448 : TMParams :=
  ⟨[⟨7030801752862457454408938858202115177321992, 7030801752862457454408938858202115177321992, 852510056072357635387676858758951963820724797872, (-80), (-80)⟩, ⟨7030801752862457454408938858202115177321992, 7030801752862457454408938858202115177321992, 852510056072357635387676858758951963820724797872, (-80), (-80)⟩, ⟨7030801752862457454408938858202115177321992, 7030801752862457454408938858202115177321992, 852510056072357635387676858758951963820724797872, (-80), (-80)⟩, ⟨7030801752862457454408938858202115177321992, 7030801752862457454408938858202115177321992, 852510056072357635387676858758951963820724797872, (-80), (-80)⟩, ⟨7030801752862457454408938858202115177321992, 7030801752862457454408938858202115177321992, 852510056072357635387676858758951963820724797872, (-80), (-80)⟩, ⟨7030801752862457454408938858202115177321992, 7030801752862457454408938858202115177321992, 852510056072357635387676858758951963820724797872, (-80), (-80)⟩, ⟨7030801752862457454408938858202115177321992, 7030801752862457454408938858202115177321992, 852510056072357635387676858758951963820724797872, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der52448 :
    checkPosTMHull (derivIExpr E549 2) B52448 DP52448
    = true := by
  decide

/-- 面叶 52448（lo 面）. -/

def FB52448 : Fin 6 → DInterval := faceBoxLo B52448 2

def PF52448 : TMParams :=
  ⟨[⟨75578900775858294181760211468801210386498, 273165403560653432972416945560468328211216, 0, (-80), (-80)⟩, ⟨6981532080322279455200429249791651855602628, 6981532080322279455200429249791651855602628, 857722191898123813120245702718449520378517540889, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face52448 :
    checkPosTMHull E549 FB52448 PF52448
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 52448，then 支）. -/

def DSafe52448 : DerivSafeOn B52448 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S52448D2) S52448D1) (Or.inr (Or.inr rfl))) S52448D0)))

/-- mono 折叠组合（叶 52448，两叶引用零重算）. -/

theorem Fold52448 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B52448 2 PF52448 DP52448 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B52448 DP52448 = true := Der52448
  have h2 : checkPosTMHull E549 (faceBoxLo B52448 2) PF52448 = true := Face52448
  show (checkPosTMHull (derivIExpr E549 2) B52448 DP52448
      && checkPosTMHull E549 (faceBoxLo B52448 2) PF52448) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 52448）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem52448 (ρ : Fin 6 → ℝ) (hρ : boxMem B52448 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe52448 Fold52448 hρ

#print axioms Sem52448

/-- 叶 52600（then 支，lo 面）原盒. -/

def B52600 : Fin 6 → DInterval :=
  ![⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩]

/-- 证书叶 52600.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S52600C0P : TMParams :=
  ⟨[⟨303382183866858050274445301587384599008767, 77351194921587670901094417434395334511199, 0, (-80), (-80)⟩], [], []⟩

theorem S52600C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B52600 S52600C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 52600.C0. -/

theorem S52600D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B52600 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S52600C0 ρ hρ

/-- 证书叶 52600.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S52600C1P : TMParams :=
  ⟨[⟨303382183866858050274445301587384599008767, 77351194921587670901094417434395334511199, 0, (-80), (-80)⟩], [], []⟩

theorem S52600C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B52600 S52600C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 52600.C1. -/

theorem S52600D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B52600 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S52600C1 ρ hρ

/-- 证书叶 52600.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S52600C2P : TMParams :=
  ⟨[], [], []⟩

theorem S52600C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B52600 S52600C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 52600.C2. -/

theorem S52600D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B52600 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S52600C2 ρ hρ

/-- 导数叶 52600（+∂x3f，then 支，全盒）. -/

def DP52600 : TMParams :=
  ⟨[⟨7688265232600646503355664004360523117958898, 7688265232600646503355664004360523117958898, 934545436516420374937817047221301248667220842736, (-80), (-80)⟩, ⟨7688265232600646503355664004360523117958898, 7688265232600646503355664004360523117958898, 934545436516420374937817047221301248667220842736, (-80), (-80)⟩, ⟨7688265232600646503355664004360523117958898, 7688265232600646503355664004360523117958898, 934545436516420374937817047221301248667220842736, (-80), (-80)⟩, ⟨7688265232600646503355664004360523117958898, 7688265232600646503355664004360523117958898, 934545436516420374937817047221301248667220842736, (-80), (-80)⟩, ⟨7688265232600646503355664004360523117958898, 7688265232600646503355664004360523117958898, 934545436516420374937817047221301248667220842736, (-80), (-80)⟩, ⟨7688265232600646503355664004360523117958898, 7688265232600646503355664004360523117958898, 934545436516420374937817047221301248667220842736, (-80), (-80)⟩, ⟨7688265232600646503355664004360523117958898, 7688265232600646503355664004360523117958898, 934545436516420374937817047221301248667220842736, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der52600 :
    checkPosTMHull (derivIExpr E549 2) B52600 DP52600
    = true := by
  decide

/-- 面叶 52600（lo 面）. -/

def FB52600 : Fin 6 → DInterval := faceBoxLo B52600 2

def PF52600 : TMParams :=
  ⟨[⟨334939634341362417764845680661788133125235, 74237104873681299976202338973952471376141, 0, (-80), (-80)⟩, ⟨7628448224420564996559725187171639336583593, 7628448224420564996559725187171639336583593, 940016852373721348686985023925985607709942397501, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face52600 :
    checkPosTMHull E549 FB52600 PF52600
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 52600，then 支）. -/

def DSafe52600 : DerivSafeOn B52600 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S52600D2) S52600D1) (Or.inr (Or.inr rfl))) S52600D0)))

/-- mono 折叠组合（叶 52600，两叶引用零重算）. -/

theorem Fold52600 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B52600 2 PF52600 DP52600 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B52600 DP52600 = true := Der52600
  have h2 : checkPosTMHull E549 (faceBoxLo B52600 2) PF52600 = true := Face52600
  show (checkPosTMHull (derivIExpr E549 2) B52600 DP52600
      && checkPosTMHull E549 (faceBoxLo B52600 2) PF52600) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 52600）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem52600 (ρ : Fin 6 → ℝ) (hρ : boxMem B52600 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe52600 Fold52600 hρ

#print axioms Sem52600

/-- 叶 52752（then 支，lo 面）原盒. -/

def B52752 : Fin 6 → DInterval :=
  ![⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩]

/-- 证书叶 52752.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S52752C0P : TMParams :=
  ⟨[⟨140107587886027159002848231249856226601706, 574483891979987349933796527210731099522208, 0, (-80), (-80)⟩], [], []⟩

theorem S52752C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B52752 S52752C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 52752.C0. -/

theorem S52752D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B52752 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S52752C0 ρ hρ

/-- 证书叶 52752.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S52752C1P : TMParams :=
  ⟨[⟨140107587886027159002848231249856226601706, 574483891979987349933796527210731099522208, 0, (-80), (-80)⟩], [], []⟩

theorem S52752C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B52752 S52752C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 52752.C1. -/

theorem S52752D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B52752 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S52752C1 ρ hρ

/-- 证书叶 52752.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S52752C2P : TMParams :=
  ⟨[], [], []⟩

theorem S52752C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B52752 S52752C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 52752.C2. -/

theorem S52752D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B52752 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S52752C2 ρ hρ

/-- 导数叶 52752（+∂x3f，then 支，全盒）. -/

def DP52752 : TMParams :=
  ⟨[⟨7127706361455685106766603975446522555831238, 7127706361455685106766603975446522555831238, 865069542532227817533916683309935262959245236132, (-80), (-80)⟩, ⟨7127706361455685106766603975446522555831238, 7127706361455685106766603975446522555831238, 865069542532227817533916683309935262959245236132, (-80), (-80)⟩, ⟨7127706361455685106766603975446522555831238, 7127706361455685106766603975446522555831238, 865069542532227817533916683309935262959245236132, (-80), (-80)⟩, ⟨7127706361455685106766603975446522555831238, 7127706361455685106766603975446522555831238, 865069542532227817533916683309935262959245236132, (-80), (-80)⟩, ⟨7127706361455685106766603975446522555831238, 7127706361455685106766603975446522555831238, 865069542532227817533916683309935262959245236132, (-80), (-80)⟩, ⟨7127706361455685106766603975446522555831238, 7127706361455685106766603975446522555831238, 865069542532227817533916683309935262959245236132, (-80), (-80)⟩, ⟨7127706361455685106766603975446522555831238, 7127706361455685106766603975446522555831238, 865069542532227817533916683309935262959245236132, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der52752 :
    checkPosTMHull (derivIExpr E549 2) B52752 DP52752
    = true := by
  decide

/-- 面叶 52752（lo 面）. -/

def FB52752 : Fin 6 → DInterval := faceBoxLo B52752 2

def PF52752 : TMParams :=
  ⟨[⟨155003965532738895953684785544349741185672, 551527844078460041738720498940188879157124, 0, (-80), (-80)⟩, ⟨7076821929287194977929026849334067121578212, 7076821929287194977929026849334067121578212, 870264873236161928883591965092262359180843676411, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face52752 :
    checkPosTMHull E549 FB52752 PF52752
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 52752，then 支）. -/

def DSafe52752 : DerivSafeOn B52752 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S52752D2) S52752D1) (Or.inr (Or.inr rfl))) S52752D0)))

/-- mono 折叠组合（叶 52752，两叶引用零重算）. -/

theorem Fold52752 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B52752 2 PF52752 DP52752 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B52752 DP52752 = true := Der52752
  have h2 : checkPosTMHull E549 (faceBoxLo B52752 2) PF52752 = true := Face52752
  show (checkPosTMHull (derivIExpr E549 2) B52752 DP52752
      && checkPosTMHull E549 (faceBoxLo B52752 2) PF52752) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 52752）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem52752 (ρ : Fin 6 → ℝ) (hρ : boxMem B52752 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe52752 Fold52752 hρ

#print axioms Sem52752

/-- 叶 52904（then 支，lo 面）原盒. -/

def B52904 : Fin 6 → DInterval :=
  ![⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨9148280341, -32⟩, ⟨4853313045, -31⟩⟩]

/-- 证书叶 52904.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S52904C0P : TMParams :=
  ⟨[⟨125508402616595510098560774774501906786106, 39277540655998190817332729218999340924279, 0, (-80), (-80)⟩], [], []⟩

theorem S52904C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B52904 S52904C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 52904.C0. -/

theorem S52904D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B52904 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S52904C0 ρ hρ

/-- 证书叶 52904.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S52904C1P : TMParams :=
  ⟨[⟨125508402616595510098560774774501906786106, 39277540655998190817332729218999340924279, 0, (-80), (-80)⟩], [], []⟩

theorem S52904C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B52904 S52904C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 52904.C1. -/

theorem S52904D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B52904 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S52904C1 ρ hρ

/-- 证书叶 52904.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S52904C2P : TMParams :=
  ⟨[], [], []⟩

theorem S52904C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B52904 S52904C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 52904.C2. -/

theorem S52904D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B52904 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S52904C2 ρ hρ

/-- 导数叶 52904（+∂x3f，then 支，全盒）. -/

def DP52904 : TMParams :=
  ⟨[⟨7517228220892464015765909426177641704935225, 7517228220892464015765909426177641704935225, 897018177948983727896093504412011590328512179117, (-80), (-80)⟩, ⟨7517228220892464015765909426177641704935225, 7517228220892464015765909426177641704935225, 897018177948983727896093504412011590328512179117, (-80), (-80)⟩, ⟨7517228220892464015765909426177641704935225, 7517228220892464015765909426177641704935225, 897018177948983727896093504412011590328512179117, (-80), (-80)⟩, ⟨7517228220892464015765909426177641704935225, 7517228220892464015765909426177641704935225, 897018177948983727896093504412011590328512179117, (-80), (-80)⟩, ⟨7517228220892464015765909426177641704935225, 7517228220892464015765909426177641704935225, 897018177948983727896093504412011590328512179117, (-80), (-80)⟩, ⟨7517228220892464015765909426177641704935225, 7517228220892464015765909426177641704935225, 897018177948983727896093504412011590328512179117, (-80), (-80)⟩, ⟨7517228220892464015765909426177641704935225, 7517228220892464015765909426177641704935225, 897018177948983727896093504412011590328512179117, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der52904 :
    checkPosTMHull (derivIExpr E549 2) B52904 DP52904
    = true := by
  decide

/-- 面叶 52904（lo 面）. -/

def FB52904 : Fin 6 → DInterval := faceBoxLo B52904 2

def PF52904 : TMParams :=
  ⟨[⟨144551425660844128320993653382888527192969, 37760865344735288003135398087483417556008, 0, (-80), (-80)⟩, ⟨7469644184531489476919093605398712433112110, 7469644184531489476919093605398712433112110, 903663058066115010725792250056597401481943577264, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face52904 :
    checkPosTMHull E549 FB52904 PF52904
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 52904，then 支）. -/

def DSafe52904 : DerivSafeOn B52904 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S52904D2) S52904D1) (Or.inr (Or.inr rfl))) S52904D0)))

/-- mono 折叠组合（叶 52904，两叶引用零重算）. -/

theorem Fold52904 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B52904 2 PF52904 DP52904 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B52904 DP52904 = true := Der52904
  have h2 : checkPosTMHull E549 (faceBoxLo B52904 2) PF52904 = true := Face52904
  show (checkPosTMHull (derivIExpr E549 2) B52904 DP52904
      && checkPosTMHull E549 (faceBoxLo B52904 2) PF52904) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 52904）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem52904 (ρ : Fin 6 → ℝ) (hρ : boxMem B52904 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe52904 Fold52904 hρ

#print axioms Sem52904

/-- 叶 53056（then 支，lo 面）原盒. -/

def B53056 : Fin 6 → DInterval :=
  ![⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩]

/-- 证书叶 53056.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S53056C0P : TMParams :=
  ⟨[⟨272182189283864656513339079788968987718097, 73367478166403472253995544985673367726240, 0, (-80), (-80)⟩], [], []⟩

theorem S53056C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B53056 S53056C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 53056.C0. -/

theorem S53056D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B53056 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S53056C0 ρ hρ

/-- 证书叶 53056.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S53056C1P : TMParams :=
  ⟨[⟨272182189283864656513339079788968987718097, 73367478166403472253995544985673367726240, 0, (-80), (-80)⟩], [], []⟩

theorem S53056C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B53056 S53056C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 53056.C1. -/

theorem S53056D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B53056 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S53056C1 ρ hρ

/-- 证书叶 53056.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S53056C2P : TMParams :=
  ⟨[], [], []⟩

theorem S53056C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B53056 S53056C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 53056.C2. -/

theorem S53056D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B53056 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S53056C2 ρ hρ

/-- 导数叶 53056（+∂x3f，then 支，全盒）. -/

def DP53056 : TMParams :=
  ⟨[⟨7211091182943778606498389142431887104699945, 7211091182943778606498389142431887104699945, 874167421132322034465955449570408468959110093012, (-80), (-80)⟩, ⟨7211091182943778606498389142431887104699945, 7211091182943778606498389142431887104699945, 874167421132322034465955449570408468959110093012, (-80), (-80)⟩, ⟨7211091182943778606498389142431887104699945, 7211091182943778606498389142431887104699945, 874167421132322034465955449570408468959110093012, (-80), (-80)⟩, ⟨7211091182943778606498389142431887104699945, 7211091182943778606498389142431887104699945, 874167421132322034465955449570408468959110093012, (-80), (-80)⟩, ⟨7211091182943778606498389142431887104699945, 7211091182943778606498389142431887104699945, 874167421132322034465955449570408468959110093012, (-80), (-80)⟩, ⟨7211091182943778606498389142431887104699945, 7211091182943778606498389142431887104699945, 874167421132322034465955449570408468959110093012, (-80), (-80)⟩, ⟨7211091182943778606498389142431887104699945, 7211091182943778606498389142431887104699945, 874167421132322034465955449570408468959110093012, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der53056 :
    checkPosTMHull (derivIExpr E549 2) B53056 DP53056
    = true := by
  decide

/-- 面叶 53056（lo 面）. -/

def FB53056 : Fin 6 → DInterval := faceBoxLo B53056 2

def PF53056 : TMParams :=
  ⟨[⟨306040116476943435404897307908910569998124, 35160690871491464845764258795181832574729, 0, (-80), (-80)⟩, ⟨7160554408579019919284234457434178207500537, 7160554408579019919284234457434178207500537, 879636483698073596988395050373584792262010642270, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face53056 :
    checkPosTMHull E549 FB53056 PF53056
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 53056，then 支）. -/

def DSafe53056 : DerivSafeOn B53056 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S53056D2) S53056D1) (Or.inr (Or.inr rfl))) S53056D0)))

/-- mono 折叠组合（叶 53056，两叶引用零重算）. -/

theorem Fold53056 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B53056 2 PF53056 DP53056 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B53056 DP53056 = true := Der53056
  have h2 : checkPosTMHull E549 (faceBoxLo B53056 2) PF53056 = true := Face53056
  show (checkPosTMHull (derivIExpr E549 2) B53056 DP53056
      && checkPosTMHull E549 (faceBoxLo B53056 2) PF53056) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 53056）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem53056 (ρ : Fin 6 → ℝ) (hρ : boxMem B53056 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe53056 Fold53056 hρ

#print axioms Sem53056

/-- 叶 53208（then 支，lo 面）原盒. -/

def B53208 : Fin 6 → DInterval :=
  ![⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩]

/-- 证书叶 53208.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S53208C0P : TMParams :=
  ⟨[⟨63762364113819900344430128533195022263056, 551518757161917903333974934049253464898220, 0, (-80), (-80)⟩], [], []⟩

theorem S53208C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B53208 S53208C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 53208.C0. -/

theorem S53208D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B53208 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S53208C0 ρ hρ

/-- 证书叶 53208.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S53208C1P : TMParams :=
  ⟨[⟨63762364113819900344430128533195022263056, 551518757161917903333974934049253464898220, 0, (-80), (-80)⟩], [], []⟩

theorem S53208C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B53208 S53208C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 53208.C1. -/

theorem S53208D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B53208 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S53208C1 ρ hρ

/-- 证书叶 53208.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S53208C2P : TMParams :=
  ⟨[], [], []⟩

theorem S53208C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B53208 S53208C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 53208.C2. -/

theorem S53208D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B53208 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S53208C2 ρ hρ

/-- 导数叶 53208（+∂x3f，then 支，全盒）. -/

def DP53208 : TMParams :=
  ⟨[⟨6770219183120152286894822416075990616631328, 6770219183120152286894822416075990616631328, 819713147492357253643589543150593596080960918621, (-80), (-80)⟩, ⟨6770219183120152286894822416075990616631328, 6770219183120152286894822416075990616631328, 819713147492357253643589543150593596080960918621, (-80), (-80)⟩, ⟨6770219183120152286894822416075990616631328, 6770219183120152286894822416075990616631328, 819713147492357253643589543150593596080960918621, (-80), (-80)⟩, ⟨6770219183120152286894822416075990616631328, 6770219183120152286894822416075990616631328, 819713147492357253643589543150593596080960918621, (-80), (-80)⟩, ⟨6770219183120152286894822416075990616631328, 6770219183120152286894822416075990616631328, 819713147492357253643589543150593596080960918621, (-80), (-80)⟩, ⟨6770219183120152286894822416075990616631328, 6770219183120152286894822416075990616631328, 819713147492357253643589543150593596080960918621, (-80), (-80)⟩, ⟨6770219183120152286894822416075990616631328, 6770219183120152286894822416075990616631328, 819713147492357253643589543150593596080960918621, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der53208 :
    checkPosTMHull (derivIExpr E549 2) B53208 DP53208
    = true := by
  decide

/-- 面叶 53208（lo 面）. -/

def FB53208 : Fin 6 → DInterval := faceBoxLo B53208 2

def PF53208 : TMParams :=
  ⟨[⟨143929914312060446449338163314749855193036, 529133249124928951581936004511063823918611, 0, (-80), (-80)⟩, ⟨6733895696787994893512959349000019360688666, 6733895696787994893512959349000019360688666, 824874665471418443414942411799648595029448087664, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face53208 :
    checkPosTMHull E549 FB53208 PF53208
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 53208，then 支）. -/

def DSafe53208 : DerivSafeOn B53208 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S53208D2) S53208D1) (Or.inr (Or.inr rfl))) S53208D0)))

/-- mono 折叠组合（叶 53208，两叶引用零重算）. -/

theorem Fold53208 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B53208 2 PF53208 DP53208 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B53208 DP53208 = true := Der53208
  have h2 : checkPosTMHull E549 (faceBoxLo B53208 2) PF53208 = true := Face53208
  show (checkPosTMHull (derivIExpr E549 2) B53208 DP53208
      && checkPosTMHull E549 (faceBoxLo B53208 2) PF53208) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 53208）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem53208 (ρ : Fin 6 → ℝ) (hρ : boxMem B53208 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe53208 Fold53208 hρ

#print axioms Sem53208

/-- 叶 53360（then 支，lo 面）原盒. -/

def B53360 : Fin 6 → DInterval :=
  ![⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩]

/-- 证书叶 53360.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S53360C0P : TMParams :=
  ⟨[⟨277766233091928231825200100718364562320641, 73057720997908123544994192580528200954610, 0, (-80), (-80)⟩], [], []⟩

theorem S53360C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B53360 S53360C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 53360.C0. -/

theorem S53360D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B53360 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S53360C0 ρ hρ

/-- 证书叶 53360.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S53360C1P : TMParams :=
  ⟨[⟨277766233091928231825200100718364562320641, 73057720997908123544994192580528200954610, 0, (-80), (-80)⟩], [], []⟩

theorem S53360C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B53360 S53360C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 53360.C1. -/

theorem S53360D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B53360 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S53360C1 ρ hρ

/-- 证书叶 53360.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S53360C2P : TMParams :=
  ⟨[], [], []⟩

theorem S53360C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B53360 S53360C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 53360.C2. -/

theorem S53360D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B53360 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S53360C2 ρ hρ

/-- 导数叶 53360（+∂x3f，then 支，全盒）. -/

def DP53360 : TMParams :=
  ⟨[⟨7214796501242866417723703872163068156088170, 7214796501242866417723703872163068156088170, 875175974483719301105088963266307071672138613169, (-80), (-80)⟩, ⟨7214796501242866417723703872163068156088170, 7214796501242866417723703872163068156088170, 875175974483719301105088963266307071672138613169, (-80), (-80)⟩, ⟨7214796501242866417723703872163068156088170, 7214796501242866417723703872163068156088170, 875175974483719301105088963266307071672138613169, (-80), (-80)⟩, ⟨7214796501242866417723703872163068156088170, 7214796501242866417723703872163068156088170, 875175974483719301105088963266307071672138613169, (-80), (-80)⟩, ⟨7214796501242866417723703872163068156088170, 7214796501242866417723703872163068156088170, 875175974483719301105088963266307071672138613169, (-80), (-80)⟩, ⟨7214796501242866417723703872163068156088170, 7214796501242866417723703872163068156088170, 875175974483719301105088963266307071672138613169, (-80), (-80)⟩, ⟨7214796501242866417723703872163068156088170, 7214796501242866417723703872163068156088170, 875175974483719301105088963266307071672138613169, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der53360 :
    checkPosTMHull (derivIExpr E549 2) B53360 DP53360
    = true := by
  decide

/-- 面叶 53360（lo 面）. -/

def FB53360 : Fin 6 → DInterval := faceBoxLo B53360 2

def PF53360 : TMParams :=
  ⟨[⟨308972657775889943794031888115187167535614, 35025187122365545381107839262013169404891, 0, (-80), (-80)⟩, ⟨7156586893836982513865604269615064092625840, 7156586893836982513865604269615064092625840, 880607869509328033225150459691678790182971664769, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face53360 :
    checkPosTMHull E549 FB53360 PF53360
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 53360，then 支）. -/

def DSafe53360 : DerivSafeOn B53360 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S53360D2) S53360D1) (Or.inr (Or.inr rfl))) S53360D0)))

/-- mono 折叠组合（叶 53360，两叶引用零重算）. -/

theorem Fold53360 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B53360 2 PF53360 DP53360 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B53360 DP53360 = true := Der53360
  have h2 : checkPosTMHull E549 (faceBoxLo B53360 2) PF53360 = true := Face53360
  show (checkPosTMHull (derivIExpr E549 2) B53360 DP53360
      && checkPosTMHull E549 (faceBoxLo B53360 2) PF53360) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 53360）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem53360 (ρ : Fin 6 → ℝ) (hρ : boxMem B53360 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe53360 Fold53360 hρ

#print axioms Sem53360


end Kepler.Interval.C549MonoBatch14
