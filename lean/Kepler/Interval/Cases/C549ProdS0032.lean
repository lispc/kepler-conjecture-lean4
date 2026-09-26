import Kepler.Interval.Cases.C549Mono
import Kepler.Interval.Cases.C549CertSlimDefs


/-! ## 549 facePos 全量评估（emit_mono.py 生成；勿手改）。

C549ProdS0032 — rung 128（发射钉死） shard 1/1（17 叶；modes ['then']）
每叶：面叶 + 导数叶 + DerivSafeOn 证书叶 ⇒ 嵌套 DSafe ⇒
checkPosFace*_sound ⇒ 全盒语义正性 0 < evalReal ρ。
本模块层级：['cert', 'der', 'face', 'fold']；decide 战术：decide。 -/


set_option maxHeartbeats 0
set_option maxRecDepth 1000000


namespace Kepler.Interval.C549ProdS0032

open Kepler.Interval


/-- case 549 表达式（本模块自包含副本）. -/

def E549 : IExpr 6 :=
  (.sub (.div (.const ⟨1893, 0⟩) (.const ⟨1000, 0⟩) (-64)) (.add (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.const ⟨2, 0⟩) (-64)) (.ite (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) (.trans .arctanK (.div (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0) (-64)) 128 (-80)) (.ite (.sub (.const ⟨0, 0⟩) (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sub (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.const ⟨2, 0⟩) (-64)) (.trans .arctanK (.div (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0) (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) (-64)) 128 (-80))) (.ite (.sub (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) (.const ⟨0, 0⟩)) (.sub (.neg (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.const ⟨2, 0⟩) (-64))) (.trans .arctanK (.div (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0) (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) (-64)) 128 (-80))) (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))))))))

/-- 叶 127806（then 支，lo 面）原盒. -/

def B127806 : Fin 6 → DInterval :=
  ![⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩]

/-- 证书叶 127806.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S127806C0P : TMParams :=
  ⟨[⟨275018174676225112182562585089307680588031, 139236347999358757949082624001546421640670, 0, (-80), (-80)⟩], [], []⟩

theorem S127806C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B127806 S127806C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 127806.C0. -/

theorem S127806D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B127806 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S127806C0 ρ hρ

/-- 证书叶 127806.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S127806C1P : TMParams :=
  ⟨[⟨275018174676225112182562585089307680588031, 139236347999358757949082624001546421640670, 0, (-80), (-80)⟩], [], []⟩

theorem S127806C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B127806 S127806C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 127806.C1. -/

theorem S127806D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B127806 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S127806C1 ρ hρ

/-- 证书叶 127806.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S127806C2P : TMParams :=
  ⟨[], [], []⟩

theorem S127806C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B127806 S127806C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 127806.C2. -/

theorem S127806D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B127806 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S127806C2 ρ hρ

/-- 导数叶 127806（+∂x3f，then 支，全盒）. -/

def DP127806 : TMParams :=
  ⟨[⟨6924202128684859542047629657781605828041141, 6924202128684859542047629657781605828041141, 840313303571301554359916334601725375815438808940, (-80), (-80)⟩, ⟨6924202128684859542047629657781605828041141, 6924202128684859542047629657781605828041141, 840313303571301554359916334601725375815438808940, (-80), (-80)⟩, ⟨6924202128684859542047629657781605828041141, 6924202128684859542047629657781605828041141, 840313303571301554359916334601725375815438808940, (-80), (-80)⟩, ⟨6924202128684859542047629657781605828041141, 6924202128684859542047629657781605828041141, 840313303571301554359916334601725375815438808940, (-80), (-80)⟩, ⟨6924202128684859542047629657781605828041141, 6924202128684859542047629657781605828041141, 840313303571301554359916334601725375815438808940, (-80), (-80)⟩, ⟨6924202128684859542047629657781605828041141, 6924202128684859542047629657781605828041141, 840313303571301554359916334601725375815438808940, (-80), (-80)⟩, ⟨6924202128684859542047629657781605828041141, 6924202128684859542047629657781605828041141, 840313303571301554359916334601725375815438808940, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der127806 :
    checkPosTMHull (derivIExpr E549 2) B127806 DP127806
    = true := by
  decide

/-- 面叶 127806（lo 面）. -/

def FB127806 : Fin 6 → DInterval := faceBoxLo B127806 2

def PF127806 : TMParams :=
  ⟨[⟨301100399573021570475793619459168011191553, 133772160869425650159248203248782043204170, 0, (-80), (-80)⟩, ⟨6865740352139564262001356796065540442956361, 6865740352139564262001356796065540442956361, 845351072620373296616337296802431538978070807943, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face127806 :
    checkPosTMHull E549 FB127806 PF127806
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 127806，then 支）. -/

def DSafe127806 : DerivSafeOn B127806 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S127806D2) S127806D1) (Or.inr (Or.inr rfl))) S127806D0)))

/-- mono 折叠组合（叶 127806，两叶引用零重算）. -/

theorem Fold127806 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B127806 2 PF127806 DP127806 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B127806 DP127806 = true := Der127806
  have h2 : checkPosTMHull E549 (faceBoxLo B127806 2) PF127806 = true := Face127806
  show (checkPosTMHull (derivIExpr E549 2) B127806 DP127806
      && checkPosTMHull E549 (faceBoxLo B127806 2) PF127806) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 127806）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem127806 (ρ : Fin 6 → ℝ) (hρ : boxMem B127806 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe127806 Fold127806 hρ

#print axioms Sem127806

/-- 叶 127997（then 支，lo 面）原盒. -/

def B127997 : Fin 6 → DInterval :=
  ![⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩]

/-- 证书叶 127997.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S127997C0P : TMParams :=
  ⟨[⟨123083520566199733304075770871681262675616, 253633297035690425483506119222281203755597, 0, (-80), (-80)⟩], [], []⟩

theorem S127997C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B127997 S127997C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 127997.C0. -/

theorem S127997D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B127997 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S127997C0 ρ hρ

/-- 证书叶 127997.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S127997C1P : TMParams :=
  ⟨[⟨123083520566199733304075770871681262675616, 253633297035690425483506119222281203755597, 0, (-80), (-80)⟩], [], []⟩

theorem S127997C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B127997 S127997C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 127997.C1. -/

theorem S127997D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B127997 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S127997C1 ρ hρ

/-- 证书叶 127997.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S127997C2P : TMParams :=
  ⟨[], [], []⟩

theorem S127997C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B127997 S127997C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 127997.C2. -/

theorem S127997D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B127997 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S127997C2 ρ hρ

/-- 导数叶 127997（+∂x3f，then 支，全盒）. -/

def DP127997 : TMParams :=
  ⟨[⟨6281124887702610004669755789735796009461040, 6281124887702610004669755789735796009461040, 760474987559106518741944557789649528467933565095, (-80), (-80)⟩, ⟨6281124887702610004669755789735796009461040, 6281124887702610004669755789735796009461040, 760474987559106518741944557789649528467933565095, (-80), (-80)⟩, ⟨6281124887702610004669755789735796009461040, 6281124887702610004669755789735796009461040, 760474987559106518741944557789649528467933565095, (-80), (-80)⟩, ⟨6281124887702610004669755789735796009461040, 6281124887702610004669755789735796009461040, 760474987559106518741944557789649528467933565095, (-80), (-80)⟩, ⟨6281124887702610004669755789735796009461040, 6281124887702610004669755789735796009461040, 760474987559106518741944557789649528467933565095, (-80), (-80)⟩, ⟨6281124887702610004669755789735796009461040, 6281124887702610004669755789735796009461040, 760474987559106518741944557789649528467933565095, (-80), (-80)⟩, ⟨6281124887702610004669755789735796009461040, 6281124887702610004669755789735796009461040, 760474987559106518741944557789649528467933565095, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der127997 :
    checkPosTMHull (derivIExpr E549 2) B127997 DP127997
    = true := by
  decide

/-- 面叶 127997（lo 面）. -/

def FB127997 : Fin 6 → DInterval := faceBoxLo B127997 2

def PF127997 : TMParams :=
  ⟨[⟨67629564452312311415318070617545610282789, 243517184699359177774330145749685427174185, 0, (-80), (-80)⟩, ⟨6226316737666988665716857984362168031877504, 6226316737666988665716857984362168031877504, 765260864641239510965802711797052810814109840244, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face127997 :
    checkPosTMHull E549 FB127997 PF127997
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 127997，then 支）. -/

def DSafe127997 : DerivSafeOn B127997 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S127997D2) S127997D1) (Or.inr (Or.inr rfl))) S127997D0)))

/-- mono 折叠组合（叶 127997，两叶引用零重算）. -/

theorem Fold127997 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B127997 2 PF127997 DP127997 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B127997 DP127997 = true := Der127997
  have h2 : checkPosTMHull E549 (faceBoxLo B127997 2) PF127997 = true := Face127997
  show (checkPosTMHull (derivIExpr E549 2) B127997 DP127997
      && checkPosTMHull E549 (faceBoxLo B127997 2) PF127997) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 127997）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem127997 (ρ : Fin 6 → ℝ) (hρ : boxMem B127997 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe127997 Fold127997 hρ

#print axioms Sem127997

/-- 叶 128162（then 支，lo 面）原盒. -/

def B128162 : Fin 6 → DInterval :=
  ![⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩]

/-- 证书叶 128162.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S128162C0P : TMParams :=
  ⟨[⟨251864700160464768989527171304535213165891, 131488693502710012958018970931863965155969, 0, (-80), (-80)⟩], [], []⟩

theorem S128162C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B128162 S128162C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 128162.C0. -/

theorem S128162D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B128162 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S128162C0 ρ hρ

/-- 证书叶 128162.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S128162C1P : TMParams :=
  ⟨[⟨251864700160464768989527171304535213165891, 131488693502710012958018970931863965155969, 0, (-80), (-80)⟩], [], []⟩

theorem S128162C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B128162 S128162C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 128162.C1. -/

theorem S128162D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B128162 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S128162C1 ρ hρ

/-- 证书叶 128162.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S128162C2P : TMParams :=
  ⟨[], [], []⟩

theorem S128162C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B128162 S128162C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 128162.C2. -/

theorem S128162D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B128162 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S128162C2 ρ hρ

/-- 导数叶 128162（+∂x3f，then 支，全盒）. -/

def DP128162 : TMParams :=
  ⟨[⟨6496749448240288712018308385992927676510884, 6496749448240288712018308385992927676510884, 786828735058512445944100000217830367191532702923, (-80), (-80)⟩, ⟨6496749448240288712018308385992927676510884, 6496749448240288712018308385992927676510884, 786828735058512445944100000217830367191532702923, (-80), (-80)⟩, ⟨6496749448240288712018308385992927676510884, 6496749448240288712018308385992927676510884, 786828735058512445944100000217830367191532702923, (-80), (-80)⟩, ⟨6496749448240288712018308385992927676510884, 6496749448240288712018308385992927676510884, 786828735058512445944100000217830367191532702923, (-80), (-80)⟩, ⟨6496749448240288712018308385992927676510884, 6496749448240288712018308385992927676510884, 786828735058512445944100000217830367191532702923, (-80), (-80)⟩, ⟨6496749448240288712018308385992927676510884, 6496749448240288712018308385992927676510884, 786828735058512445944100000217830367191532702923, (-80), (-80)⟩, ⟨6496749448240288712018308385992927676510884, 6496749448240288712018308385992927676510884, 786828735058512445944100000217830367191532702923, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der128162 :
    checkPosTMHull (derivIExpr E549 2) B128162 DP128162
    = true := by
  decide

/-- 面叶 128162（lo 面）. -/

def FB128162 : Fin 6 → DInterval := faceBoxLo B128162 2

def PF128162 : TMParams :=
  ⟨[⟨276132043087721050981658515483544886723834, 63080711344925611852661852360178695356245, 0, (-80), (-80)⟩, ⟨6428803569741930093722582372590957434445673, 6428803569741930093722582372590957434445673, 791863470664614872146645236388309436035897036232, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face128162 :
    checkPosTMHull E549 FB128162 PF128162
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 128162，then 支）. -/

def DSafe128162 : DerivSafeOn B128162 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S128162D2) S128162D1) (Or.inr (Or.inr rfl))) S128162D0)))

/-- mono 折叠组合（叶 128162，两叶引用零重算）. -/

theorem Fold128162 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B128162 2 PF128162 DP128162 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B128162 DP128162 = true := Der128162
  have h2 : checkPosTMHull E549 (faceBoxLo B128162 2) PF128162 = true := Face128162
  show (checkPosTMHull (derivIExpr E549 2) B128162 DP128162
      && checkPosTMHull E549 (faceBoxLo B128162 2) PF128162) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 128162）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem128162 (ρ : Fin 6 → ℝ) (hρ : boxMem B128162 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe128162 Fold128162 hρ

#print axioms Sem128162

/-- 叶 128333（then 支，lo 面）原盒. -/

def B128333 : Fin 6 → DInterval :=
  ![⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩]

/-- 证书叶 128333.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S128333C0P : TMParams :=
  ⟨[⟨247334870383263665005390647244421825770330, 130918655724542677808919817337473670084646, 0, (-80), (-80)⟩], [], []⟩

theorem S128333C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B128333 S128333C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 128333.C0. -/

theorem S128333D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B128333 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S128333C0 ρ hρ

/-- 证书叶 128333.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S128333C1P : TMParams :=
  ⟨[⟨247334870383263665005390647244421825770330, 130918655724542677808919817337473670084646, 0, (-80), (-80)⟩], [], []⟩

theorem S128333C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B128333 S128333C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 128333.C1. -/

theorem S128333D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B128333 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S128333C1 ρ hρ

/-- 证书叶 128333.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S128333C2P : TMParams :=
  ⟨[], [], []⟩

theorem S128333C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B128333 S128333C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 128333.C2. -/

theorem S128333D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B128333 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S128333C2 ρ hρ

/-- 导数叶 128333（+∂x3f，then 支，全盒）. -/

def DP128333 : TMParams :=
  ⟨[⟨6450452880445934438067946962811754439780641, 6450452880445934438067946962811754439780641, 780774943151379984401589109811706042977041492595, (-80), (-80)⟩, ⟨6450452880445934438067946962811754439780641, 6450452880445934438067946962811754439780641, 780774943151379984401589109811706042977041492595, (-80), (-80)⟩, ⟨6450452880445934438067946962811754439780641, 6450452880445934438067946962811754439780641, 780774943151379984401589109811706042977041492595, (-80), (-80)⟩, ⟨6450452880445934438067946962811754439780641, 6450452880445934438067946962811754439780641, 780774943151379984401589109811706042977041492595, (-80), (-80)⟩, ⟨6450452880445934438067946962811754439780641, 6450452880445934438067946962811754439780641, 780774943151379984401589109811706042977041492595, (-80), (-80)⟩, ⟨6450452880445934438067946962811754439780641, 6450452880445934438067946962811754439780641, 780774943151379984401589109811706042977041492595, (-80), (-80)⟩, ⟨6450452880445934438067946962811754439780641, 6450452880445934438067946962811754439780641, 780774943151379984401589109811706042977041492595, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der128333 :
    checkPosTMHull (derivIExpr E549 2) B128333 DP128333
    = true := by
  decide

/-- 面叶 128333（lo 面）. -/

def FB128333 : Fin 6 → DInterval := faceBoxLo B128333 2

def PF128333 : TMParams :=
  ⟨[⟨272818106774321778745758404545473480411921, 125473846990878198475027301234367875793241, 0, (-80), (-80)⟩, ⟨6382454203409982496450010510598359207267547, 6382454203409982496450010510598359207267547, 785840849461379305392123740811529563119843365295, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face128333 :
    checkPosTMHull E549 FB128333 PF128333
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 128333，then 支）. -/

def DSafe128333 : DerivSafeOn B128333 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S128333D2) S128333D1) (Or.inr (Or.inr rfl))) S128333D0)))

/-- mono 折叠组合（叶 128333，两叶引用零重算）. -/

theorem Fold128333 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B128333 2 PF128333 DP128333 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B128333 DP128333 = true := Der128333
  have h2 : checkPosTMHull E549 (faceBoxLo B128333 2) PF128333 = true := Face128333
  show (checkPosTMHull (derivIExpr E549 2) B128333 DP128333
      && checkPosTMHull E549 (faceBoxLo B128333 2) PF128333) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 128333）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem128333 (ρ : Fin 6 → ℝ) (hρ : boxMem B128333 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe128333 Fold128333 hρ

#print axioms Sem128333

/-- 叶 128501（then 支，lo 面）原盒. -/

def B128501 : Fin 6 → DInterval :=
  ![⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩]

/-- 证书叶 128501.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S128501C0P : TMParams :=
  ⟨[⟨119832881156971953117846291696647112294252, 499400524442717834782793122611987033980218, 0, (-80), (-80)⟩], [], []⟩

theorem S128501C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B128501 S128501C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 128501.C0. -/

theorem S128501D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B128501 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S128501C0 ρ hρ

/-- 证书叶 128501.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S128501C1P : TMParams :=
  ⟨[⟨119832881156971953117846291696647112294252, 499400524442717834782793122611987033980218, 0, (-80), (-80)⟩], [], []⟩

theorem S128501C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B128501 S128501C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 128501.C1. -/

theorem S128501D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B128501 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S128501C1 ρ hρ

/-- 证书叶 128501.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S128501C2P : TMParams :=
  ⟨[], [], []⟩

theorem S128501C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B128501 S128501C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 128501.C2. -/

theorem S128501D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B128501 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S128501C2 ρ hρ

/-- 导数叶 128501（+∂x3f，then 支，全盒）. -/

def DP128501 : TMParams :=
  ⟨[⟨6169430833374571434691323888091402948470515, 6169430833374571434691323888091402948470515, 746462232071702698345100656595644109924354387131, (-80), (-80)⟩, ⟨6169430833374571434691323888091402948470515, 6169430833374571434691323888091402948470515, 746462232071702698345100656595644109924354387131, (-80), (-80)⟩, ⟨6169430833374571434691323888091402948470515, 6169430833374571434691323888091402948470515, 746462232071702698345100656595644109924354387131, (-80), (-80)⟩, ⟨6169430833374571434691323888091402948470515, 6169430833374571434691323888091402948470515, 746462232071702698345100656595644109924354387131, (-80), (-80)⟩, ⟨6169430833374571434691323888091402948470515, 6169430833374571434691323888091402948470515, 746462232071702698345100656595644109924354387131, (-80), (-80)⟩, ⟨6169430833374571434691323888091402948470515, 6169430833374571434691323888091402948470515, 746462232071702698345100656595644109924354387131, (-80), (-80)⟩, ⟨6169430833374571434691323888091402948470515, 6169430833374571434691323888091402948470515, 746462232071702698345100656595644109924354387131, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der128501 :
    checkPosTMHull (derivIExpr E549 2) B128501 DP128501
    = true := by
  decide

/-- 面叶 128501（lo 面）. -/

def FB128501 : Fin 6 → DInterval := faceBoxLo B128501 2

def PF128501 : TMParams :=
  ⟨[⟨131745207810994677649316185993264436024263, 479213949551889932709725172435499580377264, 0, (-80), (-80)⟩, ⟨6110521565865968077036172249121365454109498, 6110521565865968077036172249121365454109498, 751269024635319223217228251805066831460822816194, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face128501 :
    checkPosTMHull E549 FB128501 PF128501
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 128501，then 支）. -/

def DSafe128501 : DerivSafeOn B128501 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S128501D2) S128501D1) (Or.inr (Or.inr rfl))) S128501D0)))

/-- mono 折叠组合（叶 128501，两叶引用零重算）. -/

theorem Fold128501 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B128501 2 PF128501 DP128501 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B128501 DP128501 = true := Der128501
  have h2 : checkPosTMHull E549 (faceBoxLo B128501 2) PF128501 = true := Face128501
  show (checkPosTMHull (derivIExpr E549 2) B128501 DP128501
      && checkPosTMHull E549 (faceBoxLo B128501 2) PF128501) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 128501）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem128501 (ρ : Fin 6 → ℝ) (hρ : boxMem B128501 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe128501 Fold128501 hρ

#print axioms Sem128501

/-- 叶 128678（then 支，lo 面）原盒. -/

def B128678 : Fin 6 → DInterval :=
  ![⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩]

/-- 证书叶 128678.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S128678C0P : TMParams :=
  ⟨[⟨247734050797969050153222928387105124008097, 255070319973203322815211668425900811083635, 0, (-80), (-80)⟩], [], []⟩

theorem S128678C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B128678 S128678C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 128678.C0. -/

theorem S128678D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B128678 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S128678C0 ρ hρ

/-- 证书叶 128678.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S128678C1P : TMParams :=
  ⟨[⟨247734050797969050153222928387105124008097, 255070319973203322815211668425900811083635, 0, (-80), (-80)⟩], [], []⟩

theorem S128678C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B128678 S128678C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 128678.C1. -/

theorem S128678D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B128678 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S128678C1 ρ hρ

/-- 证书叶 128678.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S128678C2P : TMParams :=
  ⟨[], [], []⟩

theorem S128678C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B128678 S128678C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 128678.C2. -/

theorem S128678D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B128678 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S128678C2 ρ hρ

/-- 导数叶 128678（+∂x3f，then 支，全盒）. -/

def DP128678 : TMParams :=
  ⟨[⟨6316566294904218188022055422108275547167374, 6316566294904218188022055422108275547167374, 764896334836970231608904803553524275147424500167, (-80), (-80)⟩, ⟨6316566294904218188022055422108275547167374, 6316566294904218188022055422108275547167374, 764896334836970231608904803553524275147424500167, (-80), (-80)⟩, ⟨6316566294904218188022055422108275547167374, 6316566294904218188022055422108275547167374, 764896334836970231608904803553524275147424500167, (-80), (-80)⟩, ⟨6316566294904218188022055422108275547167374, 6316566294904218188022055422108275547167374, 764896334836970231608904803553524275147424500167, (-80), (-80)⟩, ⟨6316566294904218188022055422108275547167374, 6316566294904218188022055422108275547167374, 764896334836970231608904803553524275147424500167, (-80), (-80)⟩, ⟨6316566294904218188022055422108275547167374, 6316566294904218188022055422108275547167374, 764896334836970231608904803553524275147424500167, (-80), (-80)⟩, ⟨6316566294904218188022055422108275547167374, 6316566294904218188022055422108275547167374, 764896334836970231608904803553524275147424500167, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der128678 :
    checkPosTMHull (derivIExpr E549 2) B128678 DP128678
    = true := by
  decide

/-- 面叶 128678（lo 面）. -/

def FB128678 : Fin 6 → DInterval := faceBoxLo B128678 2

def PF128678 : TMParams :=
  ⟨[⟨272600096848734746589684526532944295900529, 245022133291184902630528703827551697587436, 0, (-80), (-80)⟩, ⟨6266522110841465210011098581027905032018098, 6266522110841465210011098581027905032018098, 769630355395814191454612056150615053070312030859, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face128678 :
    checkPosTMHull E549 FB128678 PF128678
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 128678，then 支）. -/

def DSafe128678 : DerivSafeOn B128678 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S128678D2) S128678D1) (Or.inr (Or.inr rfl))) S128678D0)))

/-- mono 折叠组合（叶 128678，两叶引用零重算）. -/

theorem Fold128678 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B128678 2 PF128678 DP128678 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B128678 DP128678 = true := Der128678
  have h2 : checkPosTMHull E549 (faceBoxLo B128678 2) PF128678 = true := Face128678
  show (checkPosTMHull (derivIExpr E549 2) B128678 DP128678
      && checkPosTMHull E549 (faceBoxLo B128678 2) PF128678) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 128678）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem128678 (ρ : Fin 6 → ℝ) (hρ : boxMem B128678 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe128678 Fold128678 hρ

#print axioms Sem128678

/-- 叶 128946（then 支，lo 面）原盒. -/

def B128946 : Fin 6 → DInterval :=
  ![⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩]

/-- 证书叶 128946.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S128946C0P : TMParams :=
  ⟨[⟨246775037431622789822284776063296704137070, 129648438934436427263705998862934079250183, 0, (-80), (-80)⟩], [], []⟩

theorem S128946C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B128946 S128946C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 128946.C0. -/

theorem S128946D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B128946 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S128946C0 ρ hρ

/-- 证书叶 128946.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S128946C1P : TMParams :=
  ⟨[⟨246775037431622789822284776063296704137070, 129648438934436427263705998862934079250183, 0, (-80), (-80)⟩], [], []⟩

theorem S128946C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B128946 S128946C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 128946.C1. -/

theorem S128946D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B128946 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S128946C1 ρ hρ

/-- 证书叶 128946.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S128946C2P : TMParams :=
  ⟨[], [], []⟩

theorem S128946C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B128946 S128946C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 128946.C2. -/

theorem S128946D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B128946 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S128946C2 ρ hρ

/-- 导数叶 128946（+∂x3f，then 支，全盒）. -/

def DP128946 : TMParams :=
  ⟨[⟨6395137184523351505664403590813434924803562, 6395137184523351505664403590813434924803562, 774186702994406216136362269078810654778201127936, (-80), (-80)⟩, ⟨6395137184523351505664403590813434924803562, 6395137184523351505664403590813434924803562, 774186702994406216136362269078810654778201127936, (-80), (-80)⟩, ⟨6395137184523351505664403590813434924803562, 6395137184523351505664403590813434924803562, 774186702994406216136362269078810654778201127936, (-80), (-80)⟩, ⟨6395137184523351505664403590813434924803562, 6395137184523351505664403590813434924803562, 774186702994406216136362269078810654778201127936, (-80), (-80)⟩, ⟨6395137184523351505664403590813434924803562, 6395137184523351505664403590813434924803562, 774186702994406216136362269078810654778201127936, (-80), (-80)⟩, ⟨6395137184523351505664403590813434924803562, 6395137184523351505664403590813434924803562, 774186702994406216136362269078810654778201127936, (-80), (-80)⟩, ⟨6395137184523351505664403590813434924803562, 6395137184523351505664403590813434924803562, 774186702994406216136362269078810654778201127936, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der128946 :
    checkPosTMHull (derivIExpr E549 2) B128946 DP128946
    = true := by
  decide

/-- 面叶 128946（lo 面）. -/

def FB128946 : Fin 6 → DInterval := faceBoxLo B128946 2

def PF128946 : TMParams :=
  ⟨[⟨271086439997950687208661933421294744828922, 248797822320407789976287071948343282393769, 0, (-80), (-80)⟩, ⟨6330157829748984695387021832162329871525795, 6330157829748984695387021832162329871525795, 779128400393462531283578009344431724026252948276, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face128946 :
    checkPosTMHull E549 FB128946 PF128946
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 128946，then 支）. -/

def DSafe128946 : DerivSafeOn B128946 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S128946D2) S128946D1) (Or.inr (Or.inr rfl))) S128946D0)))

/-- mono 折叠组合（叶 128946，两叶引用零重算）. -/

theorem Fold128946 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B128946 2 PF128946 DP128946 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B128946 DP128946 = true := Der128946
  have h2 : checkPosTMHull E549 (faceBoxLo B128946 2) PF128946 = true := Face128946
  show (checkPosTMHull (derivIExpr E549 2) B128946 DP128946
      && checkPosTMHull E549 (faceBoxLo B128946 2) PF128946) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 128946）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem128946 (ρ : Fin 6 → ℝ) (hρ : boxMem B128946 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe128946 Fold128946 hρ

#print axioms Sem128946

/-- 叶 129125（then 支，lo 面）原盒. -/

def B129125 : Fin 6 → DInterval :=
  ![⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩]

/-- 证书叶 129125.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S129125C0P : TMParams :=
  ⟨[⟨26683330412605296788913937126890, 488880197628402459224025013711958570677713, 0, (-80), (-80)⟩], [], []⟩

theorem S129125C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B129125 S129125C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 129125.C0. -/

theorem S129125D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B129125 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S129125C0 ρ hρ

/-- 证书叶 129125.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S129125C1P : TMParams :=
  ⟨[⟨26683330412605296788913937126890, 488880197628402459224025013711958570677713, 0, (-80), (-80)⟩], [], []⟩

theorem S129125C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B129125 S129125C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 129125.C1. -/

theorem S129125D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B129125 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S129125C1 ρ hρ

/-- 证书叶 129125.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S129125C2P : TMParams :=
  ⟨[], [], []⟩

theorem S129125C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B129125 S129125C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 129125.C2. -/

theorem S129125D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B129125 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S129125C2 ρ hρ

/-- 导数叶 129125（+∂x3f，then 支，全盒）. -/

def DP129125 : TMParams :=
  ⟨[⟨6008933067447192034410403637770706721331121, 6008933067447192034410403637770706721331121, 726280753741229558712399611707818611952690869102, (-80), (-80)⟩, ⟨6008933067447192034410403637770706721331121, 6008933067447192034410403637770706721331121, 726280753741229558712399611707818611952690869102, (-80), (-80)⟩, ⟨6008933067447192034410403637770706721331121, 6008933067447192034410403637770706721331121, 726280753741229558712399611707818611952690869102, (-80), (-80)⟩, ⟨6008933067447192034410403637770706721331121, 6008933067447192034410403637770706721331121, 726280753741229558712399611707818611952690869102, (-80), (-80)⟩, ⟨6008933067447192034410403637770706721331121, 6008933067447192034410403637770706721331121, 726280753741229558712399611707818611952690869102, (-80), (-80)⟩, ⟨6008933067447192034410403637770706721331121, 6008933067447192034410403637770706721331121, 726280753741229558712399611707818611952690869102, (-80), (-80)⟩, ⟨6008933067447192034410403637770706721331121, 6008933067447192034410403637770706721331121, 726280753741229558712399611707818611952690869102, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der129125 :
    checkPosTMHull (derivIExpr E549 2) B129125 DP129125
    = true := by
  decide

/-- 面叶 129125（lo 面）. -/

def FB129125 : Fin 6 → DInterval := faceBoxLo B129125 2

def PF129125 : TMParams :=
  ⟨[⟨29464006982574666253173394252532, 469001039812083892147793476212260841671171, 0, (-80), (-80)⟩, ⟨5951002590587911867577674119370846970998948, 5951002590587911867577674119370846970998948, 731040008621450594384262263615303276494799733011, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face129125 :
    checkPosTMHull E549 FB129125 PF129125
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 129125，then 支）. -/

def DSafe129125 : DerivSafeOn B129125 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S129125D2) S129125D1) (Or.inr (Or.inr rfl))) S129125D0)))

/-- mono 折叠组合（叶 129125，两叶引用零重算）. -/

theorem Fold129125 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B129125 2 PF129125 DP129125 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B129125 DP129125 = true := Der129125
  have h2 : checkPosTMHull E549 (faceBoxLo B129125 2) PF129125 = true := Face129125
  show (checkPosTMHull (derivIExpr E549 2) B129125 DP129125
      && checkPosTMHull E549 (faceBoxLo B129125 2) PF129125) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 129125）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem129125 (ρ : Fin 6 → ℝ) (hρ : boxMem B129125 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe129125 Fold129125 hρ

#print axioms Sem129125

/-- 叶 129568（then 支，lo 面）原盒. -/

def B129568 : Fin 6 → DInterval :=
  ![⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩]

/-- 证书叶 129568.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S129568C0P : TMParams :=
  ⟨[⟨247264895441529491745584024706082965238232, 254952729853803594089881445923950596799471, 0, (-80), (-80)⟩], [], []⟩

theorem S129568C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B129568 S129568C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 129568.C0. -/

theorem S129568D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B129568 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S129568C0 ρ hρ

/-- 证书叶 129568.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S129568C1P : TMParams :=
  ⟨[⟨247264895441529491745584024706082965238232, 254952729853803594089881445923950596799471, 0, (-80), (-80)⟩], [], []⟩

theorem S129568C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B129568 S129568C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 129568.C1. -/

theorem S129568D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B129568 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S129568C1 ρ hρ

/-- 证书叶 129568.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S129568C2P : TMParams :=
  ⟨[], [], []⟩

theorem S129568C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B129568 S129568C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 129568.C2. -/

theorem S129568D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B129568 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S129568C2 ρ hρ

/-- 导数叶 129568（+∂x3f，then 支，全盒）. -/

def DP129568 : TMParams :=
  ⟨[⟨6311846355347770694887678288084051582209477, 6311846355347770694887678288084051582209477, 764276607248156743914355247611213528415861778578, (-80), (-80)⟩, ⟨6311846355347770694887678288084051582209477, 6311846355347770694887678288084051582209477, 764276607248156743914355247611213528415861778578, (-80), (-80)⟩, ⟨6311846355347770694887678288084051582209477, 6311846355347770694887678288084051582209477, 764276607248156743914355247611213528415861778578, (-80), (-80)⟩, ⟨6311846355347770694887678288084051582209477, 6311846355347770694887678288084051582209477, 764276607248156743914355247611213528415861778578, (-80), (-80)⟩, ⟨6311846355347770694887678288084051582209477, 6311846355347770694887678288084051582209477, 764276607248156743914355247611213528415861778578, (-80), (-80)⟩, ⟨6311846355347770694887678288084051582209477, 6311846355347770694887678288084051582209477, 764276607248156743914355247611213528415861778578, (-80), (-80)⟩, ⟨6311846355347770694887678288084051582209477, 6311846355347770694887678288084051582209477, 764276607248156743914355247611213528415861778578, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der129568 :
    checkPosTMHull (derivIExpr E549 2) B129568 DP129568
    = true := by
  decide

/-- 面叶 129568（lo 面）. -/

def FB129568 : Fin 6 → DInterval := faceBoxLo B129568 2

def PF129568 : TMParams :=
  ⟨[⟨272010573546185035553477479368054660934495, 244914373179578229027859796095288971028907, 0, (-80), (-80)⟩, ⟨6261134754124871145181798614619458995426420, 6261134754124871145181798614619458995426420, 769016981198457580798320489716753982791452103274, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face129568 :
    checkPosTMHull E549 FB129568 PF129568
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 129568，then 支）. -/

def DSafe129568 : DerivSafeOn B129568 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S129568D2) S129568D1) (Or.inr (Or.inr rfl))) S129568D0)))

/-- mono 折叠组合（叶 129568，两叶引用零重算）. -/

theorem Fold129568 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B129568 2 PF129568 DP129568 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B129568 DP129568 = true := Der129568
  have h2 : checkPosTMHull E549 (faceBoxLo B129568 2) PF129568 = true := Face129568
  show (checkPosTMHull (derivIExpr E549 2) B129568 DP129568
      && checkPosTMHull E549 (faceBoxLo B129568 2) PF129568) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 129568）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem129568 (ρ : Fin 6 → ℝ) (hρ : boxMem B129568 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe129568 Fold129568 hρ

#print axioms Sem129568

/-- 叶 129783（then 支，lo 面）原盒. -/

def B129783 : Fin 6 → DInterval :=
  ![⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩]

/-- 证书叶 129783.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S129783C0P : TMParams :=
  ⟨[⟨242050044149422618246483609465419453062101, 251386714733816883333162305460061485412650, 0, (-80), (-80)⟩], [], []⟩

theorem S129783C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B129783 S129783C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 129783.C0. -/

theorem S129783D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B129783 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S129783C0 ρ hρ

/-- 证书叶 129783.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S129783C1P : TMParams :=
  ⟨[⟨242050044149422618246483609465419453062101, 251386714733816883333162305460061485412650, 0, (-80), (-80)⟩], [], []⟩

theorem S129783C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B129783 S129783C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 129783.C1. -/

theorem S129783D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B129783 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S129783C1 ρ hρ

/-- 证书叶 129783.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S129783C2P : TMParams :=
  ⟨[], [], []⟩

theorem S129783C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B129783 S129783C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 129783.C2. -/

theorem S129783D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B129783 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S129783C2 ρ hρ

/-- 导数叶 129783（+∂x3f，then 支，全盒）. -/

def DP129783 : TMParams :=
  ⟨[⟨6214018259600548964278581825286718356154806, 6214018259600548964278581825286718356154806, 752048841814889705080955068893500904529395482570, (-80), (-80)⟩, ⟨6214018259600548964278581825286718356154806, 6214018259600548964278581825286718356154806, 752048841814889705080955068893500904529395482570, (-80), (-80)⟩, ⟨6214018259600548964278581825286718356154806, 6214018259600548964278581825286718356154806, 752048841814889705080955068893500904529395482570, (-80), (-80)⟩, ⟨6214018259600548964278581825286718356154806, 6214018259600548964278581825286718356154806, 752048841814889705080955068893500904529395482570, (-80), (-80)⟩, ⟨6214018259600548964278581825286718356154806, 6214018259600548964278581825286718356154806, 752048841814889705080955068893500904529395482570, (-80), (-80)⟩, ⟨6214018259600548964278581825286718356154806, 6214018259600548964278581825286718356154806, 752048841814889705080955068893500904529395482570, (-80), (-80)⟩, ⟨6214018259600548964278581825286718356154806, 6214018259600548964278581825286718356154806, 752048841814889705080955068893500904529395482570, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der129783 :
    checkPosTMHull (derivIExpr E549 2) B129783 DP129783
    = true := by
  decide

/-- 面叶 129783（lo 面）. -/

def FB129783 : Fin 6 → DInterval := faceBoxLo B129783 2

def PF129783 : TMParams :=
  ⟨[⟨266748977777910708510522050411218184381036, 241622528290232865604152929376034002781925, 0, (-80), (-80)⟩, ⟨6167945453156862408382093652928167070074369, 6167945453156862408382093652928167070074369, 756759135705668927483637681127061496767051867428, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face129783 :
    checkPosTMHull E549 FB129783 PF129783
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 129783，then 支）. -/

def DSafe129783 : DerivSafeOn B129783 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S129783D2) S129783D1) (Or.inr (Or.inr rfl))) S129783D0)))

/-- mono 折叠组合（叶 129783，两叶引用零重算）. -/

theorem Fold129783 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B129783 2 PF129783 DP129783 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B129783 DP129783 = true := Der129783
  have h2 : checkPosTMHull E549 (faceBoxLo B129783 2) PF129783 = true := Face129783
  show (checkPosTMHull (derivIExpr E549 2) B129783 DP129783
      && checkPosTMHull E549 (faceBoxLo B129783 2) PF129783) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 129783）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem129783 (ρ : Fin 6 → ℝ) (hρ : boxMem B129783 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe129783 Fold129783 hρ

#print axioms Sem129783

/-- 叶 129964（then 支，lo 面）原盒. -/

def B129964 : Fin 6 → DInterval :=
  ![⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩]

/-- 证书叶 129964.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S129964C0P : TMParams :=
  ⟨[⟨24676483000361769646653128709050, 463187774417048969409008973608264024089316, 0, (-80), (-80)⟩], [], []⟩

theorem S129964C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B129964 S129964C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 129964.C0. -/

theorem S129964D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B129964 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S129964C0 ρ hρ

/-- 证书叶 129964.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S129964C1P : TMParams :=
  ⟨[⟨24676483000361769646653128709050, 463187774417048969409008973608264024089316, 0, (-80), (-80)⟩], [], []⟩

theorem S129964C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B129964 S129964C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 129964.C1. -/

theorem S129964D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B129964 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S129964C1 ρ hρ

/-- 证书叶 129964.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S129964C2P : TMParams :=
  ⟨[], [], []⟩

theorem S129964C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B129964 S129964C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 129964.C2. -/

theorem S129964D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B129964 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S129964C2 ρ hρ

/-- 导数叶 129964（+∂x3f，then 支，全盒）. -/

def DP129964 : TMParams :=
  ⟨[⟨5665911180308781548951430452278602466568901, 5665911180308781548951430452278602466568901, 683518502028161743417739514755370886098336575570, (-80), (-80)⟩, ⟨5665911180308781548951430452278602466568901, 5665911180308781548951430452278602466568901, 683518502028161743417739514755370886098336575570, (-80), (-80)⟩, ⟨5665911180308781548951430452278602466568901, 5665911180308781548951430452278602466568901, 683518502028161743417739514755370886098336575570, (-80), (-80)⟩, ⟨5665911180308781548951430452278602466568901, 5665911180308781548951430452278602466568901, 683518502028161743417739514755370886098336575570, (-80), (-80)⟩, ⟨5665911180308781548951430452278602466568901, 5665911180308781548951430452278602466568901, 683518502028161743417739514755370886098336575570, (-80), (-80)⟩, ⟨5665911180308781548951430452278602466568901, 5665911180308781548951430452278602466568901, 683518502028161743417739514755370886098336575570, (-80), (-80)⟩, ⟨5665911180308781548951430452278602466568901, 5665911180308781548951430452278602466568901, 683518502028161743417739514755370886098336575570, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der129964 :
    checkPosTMHull (derivIExpr E549 2) B129964 DP129964
    = true := by
  decide

/-- 面叶 129964（lo 面）. -/

def FB129964 : Fin 6 → DInterval := faceBoxLo B129964 2

def PF129964 : TMParams :=
  ⟨[⟨27326101245059754671531003562863, 443942752676950690891360314113291464313240, 0, (-80), (-80)⟩, ⟨5604952472181244554258881525963800025859857, 5604952472181244554258881525963800025859857, 688231543253997174364857139289501060683866698376, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face129964 :
    checkPosTMHull E549 FB129964 PF129964
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 129964，then 支）. -/

def DSafe129964 : DerivSafeOn B129964 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S129964D2) S129964D1) (Or.inr (Or.inr rfl))) S129964D0)))

/-- mono 折叠组合（叶 129964，两叶引用零重算）. -/

theorem Fold129964 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B129964 2 PF129964 DP129964 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B129964 DP129964 = true := Der129964
  have h2 : checkPosTMHull E549 (faceBoxLo B129964 2) PF129964 = true := Face129964
  show (checkPosTMHull (derivIExpr E549 2) B129964 DP129964
      && checkPosTMHull E549 (faceBoxLo B129964 2) PF129964) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 129964）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem129964 (ρ : Fin 6 → ℝ) (hρ : boxMem B129964 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe129964 Fold129964 hρ

#print axioms Sem129964

/-- 叶 130129（then 支，lo 面）原盒. -/

def B130129 : Fin 6 → DInterval :=
  ![⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩]

/-- 证书叶 130129.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S130129C0P : TMParams :=
  ⟨[⟨224237692074710914678222551968059884682992, 238031191168487864330492715176983506727302, 0, (-80), (-80)⟩], [], []⟩

theorem S130129C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B130129 S130129C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 130129.C0. -/

theorem S130129D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B130129 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S130129C0 ρ hρ

/-- 证书叶 130129.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S130129C1P : TMParams :=
  ⟨[⟨224237692074710914678222551968059884682992, 238031191168487864330492715176983506727302, 0, (-80), (-80)⟩], [], []⟩

theorem S130129C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B130129 S130129C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 130129.C1. -/

theorem S130129D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B130129 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S130129C1 ρ hρ

/-- 证书叶 130129.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S130129C2P : TMParams :=
  ⟨[], [], []⟩

theorem S130129C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B130129 S130129C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 130129.C2. -/

theorem S130129D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B130129 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S130129C2 ρ hρ

/-- 导数叶 130129（+∂x3f，then 支，全盒）. -/

def DP130129 : TMParams :=
  ⟨[⟨5857411374496590001415044455149728184673744, 5857411374496590001415044455149728184673744, 707637091380200133357132357508997098422651595887, (-80), (-80)⟩, ⟨5857411374496590001415044455149728184673744, 5857411374496590001415044455149728184673744, 707637091380200133357132357508997098422651595887, (-80), (-80)⟩, ⟨5857411374496590001415044455149728184673744, 5857411374496590001415044455149728184673744, 707637091380200133357132357508997098422651595887, (-80), (-80)⟩, ⟨5857411374496590001415044455149728184673744, 5857411374496590001415044455149728184673744, 707637091380200133357132357508997098422651595887, (-80), (-80)⟩, ⟨5857411374496590001415044455149728184673744, 5857411374496590001415044455149728184673744, 707637091380200133357132357508997098422651595887, (-80), (-80)⟩, ⟨5857411374496590001415044455149728184673744, 5857411374496590001415044455149728184673744, 707637091380200133357132357508997098422651595887, (-80), (-80)⟩, ⟨5857411374496590001415044455149728184673744, 5857411374496590001415044455149728184673744, 707637091380200133357132357508997098422651595887, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der130129 :
    checkPosTMHull (derivIExpr E549 2) B130129 DP130129
    = true := by
  decide

/-- 面叶 130129（lo 面）. -/

def FB130129 : Fin 6 → DInterval := faceBoxLo B130129 2

def PF130129 : TMParams :=
  ⟨[⟨247788661489493538799812155032105689370751, 228226270212108304331051903325086739555106, 0, (-80), (-80)⟩, ⟨5800177874824292763497875842215892368242587, 5800177874824292763497875842215892368242587, 712322829594000651039581183553344649288904396770, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face130129 :
    checkPosTMHull E549 FB130129 PF130129
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 130129，then 支）. -/

def DSafe130129 : DerivSafeOn B130129 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S130129D2) S130129D1) (Or.inr (Or.inr rfl))) S130129D0)))

/-- mono 折叠组合（叶 130129，两叶引用零重算）. -/

theorem Fold130129 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B130129 2 PF130129 DP130129 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B130129 DP130129 = true := Der130129
  have h2 : checkPosTMHull E549 (faceBoxLo B130129 2) PF130129 = true := Face130129
  show (checkPosTMHull (derivIExpr E549 2) B130129 DP130129
      && checkPosTMHull E549 (faceBoxLo B130129 2) PF130129) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 130129）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem130129 (ρ : Fin 6 → ℝ) (hρ : boxMem B130129 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe130129 Fold130129 hρ

#print axioms Sem130129

/-- 叶 130349（then 支，lo 面）原盒. -/

def B130349 : Fin 6 → DInterval :=
  ![⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩]

/-- 证书叶 130349.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S130349C0P : TMParams :=
  ⟨[⟨25217855144032692825969669483382, 465484869068176279219718539382187712030425, 0, (-80), (-80)⟩], [], []⟩

theorem S130349C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B130349 S130349C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 130349.C0. -/

theorem S130349D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B130349 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S130349C0 ρ hρ

/-- 证书叶 130349.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S130349C1P : TMParams :=
  ⟨[⟨25217855144032692825969669483382, 465484869068176279219718539382187712030425, 0, (-80), (-80)⟩], [], []⟩

theorem S130349C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B130349 S130349C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 130349.C1. -/

theorem S130349D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B130349 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S130349C1 ρ hρ

/-- 证书叶 130349.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S130349C2P : TMParams :=
  ⟨[], [], []⟩

theorem S130349C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B130349 S130349C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 130349.C2. -/

theorem S130349D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B130349 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S130349C2 ρ hρ

/-- 导数叶 130349（+∂x3f，then 支，全盒）. -/

def DP130349 : TMParams :=
  ⟨[⟨5712267801484610600989250677136955541142288, 5712267801484610600989250677136955541142288, 689539201514120487454546788203782429704539135171, (-80), (-80)⟩, ⟨5712267801484610600989250677136955541142288, 5712267801484610600989250677136955541142288, 689539201514120487454546788203782429704539135171, (-80), (-80)⟩, ⟨5712267801484610600989250677136955541142288, 5712267801484610600989250677136955541142288, 689539201514120487454546788203782429704539135171, (-80), (-80)⟩, ⟨5712267801484610600989250677136955541142288, 5712267801484610600989250677136955541142288, 689539201514120487454546788203782429704539135171, (-80), (-80)⟩, ⟨5712267801484610600989250677136955541142288, 5712267801484610600989250677136955541142288, 689539201514120487454546788203782429704539135171, (-80), (-80)⟩, ⟨5712267801484610600989250677136955541142288, 5712267801484610600989250677136955541142288, 689539201514120487454546788203782429704539135171, (-80), (-80)⟩, ⟨5712267801484610600989250677136955541142288, 5712267801484610600989250677136955541142288, 689539201514120487454546788203782429704539135171, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der130349 :
    checkPosTMHull (derivIExpr E549 2) B130349 DP130349
    = true := by
  decide

/-- 面叶 130349（lo 面）. -/

def FB130349 : Fin 6 → DInterval := faceBoxLo B130349 2

def PF130349 : TMParams :=
  ⟨[⟨27888981075189705932717611133142, 446769445572888545350657050251761284946693, 0, (-80), (-80)⟩, ⟨5660111692700681912727121388085059481023705, 5660111692700681912727121388085059481023705, 694171597570451487089097344174612294748019896974, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face130349 :
    checkPosTMHull E549 FB130349 PF130349
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 130349，then 支）. -/

def DSafe130349 : DerivSafeOn B130349 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S130349D2) S130349D1) (Or.inr (Or.inr rfl))) S130349D0)))

/-- mono 折叠组合（叶 130349，两叶引用零重算）. -/

theorem Fold130349 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B130349 2 PF130349 DP130349 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B130349 DP130349 = true := Der130349
  have h2 : checkPosTMHull E549 (faceBoxLo B130349 2) PF130349 = true := Face130349
  show (checkPosTMHull (derivIExpr E549 2) B130349 DP130349
      && checkPosTMHull E549 (faceBoxLo B130349 2) PF130349) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 130349）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem130349 (ρ : Fin 6 → ℝ) (hρ : boxMem B130349 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe130349 Fold130349 hρ

#print axioms Sem130349

/-- 叶 130522（then 支，lo 面）原盒. -/

def B130522 : Fin 6 → DInterval :=
  ![⟨⟨37151467113, -34⟩, ⟨18854906431, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩]

/-- 证书叶 130522.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S130522C0P : TMParams :=
  ⟨[⟨517086127265107670902613509464581521349547, 1011022118819623741851030528918343900026436, 0, (-80), (-80)⟩], [], []⟩

theorem S130522C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B130522 S130522C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 130522.C0. -/

theorem S130522D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B130522 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S130522C0 ρ hρ

/-- 证书叶 130522.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S130522C1P : TMParams :=
  ⟨[⟨517086127265107670902613509464581521349547, 1011022118819623741851030528918343900026436, 0, (-80), (-80)⟩], [], []⟩

theorem S130522C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B130522 S130522C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 130522.C1. -/

theorem S130522D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B130522 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S130522C1 ρ hρ

/-- 证书叶 130522.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S130522C2P : TMParams :=
  ⟨[], [], []⟩

theorem S130522C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B130522 S130522C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 130522.C2. -/

theorem S130522D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B130522 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S130522C2 ρ hρ

/-- 导数叶 130522（+∂x3f，then 支，全盒）. -/

def DP130522 : TMParams :=
  ⟨[⟨50883114290241496442243219867465504046559106, 50883114290241496442243219867465504046559106, 12531312430875129370303505388483687774017439924112, (-80), (-80)⟩, ⟨50883114290241496442243219867465504046559106, 50883114290241496442243219867465504046559106, 12531312430875129370303505388483687774017439924112, (-80), (-80)⟩, ⟨50883114290241496442243219867465504046559106, 50883114290241496442243219867465504046559106, 12531312430875129370303505388483687774017439924112, (-80), (-80)⟩, ⟨50883114290241496442243219867465504046559106, 50883114290241496442243219867465504046559106, 12531312430875129370303505388483687774017439924112, (-80), (-80)⟩, ⟨50883114290241496442243219867465504046559106, 50883114290241496442243219867465504046559106, 12531312430875129370303505388483687774017439924112, (-80), (-80)⟩, ⟨50883114290241496442243219867465504046559106, 50883114290241496442243219867465504046559106, 12531312430875129370303505388483687774017439924112, (-80), (-80)⟩, ⟨50883114290241496442243219867465504046559106, 50883114290241496442243219867465504046559106, 12531312430875129370303505388483687774017439924112, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der130522 :
    checkPosTMHull (derivIExpr E549 2) B130522 DP130522
    = true := by
  decide

/-- 面叶 130522（lo 面）. -/

def FB130522 : Fin 6 → DInterval := faceBoxLo B130522 2

def PF130522 : TMParams :=
  ⟨[⟨567396795421187029859260338496579407239671, 967022406614327667546066534409352770793084, 0, (-80), (-80)⟩, ⟨50356702155238005095718924315857010420738487, 50356702155238005095718924315857010420738487, 12598825783504793575817400696216925387407209806974, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face130522 :
    checkPosTMHull E549 FB130522 PF130522
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 130522，then 支）. -/

def DSafe130522 : DerivSafeOn B130522 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S130522D2) S130522D1) (Or.inr (Or.inr rfl))) S130522D0)))

/-- mono 折叠组合（叶 130522，两叶引用零重算）. -/

theorem Fold130522 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B130522 2 PF130522 DP130522 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B130522 DP130522 = true := Der130522
  have h2 : checkPosTMHull E549 (faceBoxLo B130522 2) PF130522 = true := Face130522
  show (checkPosTMHull (derivIExpr E549 2) B130522 DP130522
      && checkPosTMHull E549 (faceBoxLo B130522 2) PF130522) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 130522）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem130522 (ρ : Fin 6 → ℝ) (hρ : boxMem B130522 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe130522 Fold130522 hρ

#print axioms Sem130522

/-- 叶 130687（then 支，lo 面）原盒. -/

def B130687 : Fin 6 → DInterval :=
  ![⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩]

/-- 证书叶 130687.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S130687C0P : TMParams :=
  ⟨[⟨242635377319871223568559772981008483035184, 130329532390333382365747616152972823346826, 0, (-80), (-80)⟩], [], []⟩

theorem S130687C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B130687 S130687C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 130687.C0. -/

theorem S130687D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B130687 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S130687C0 ρ hρ

/-- 证书叶 130687.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S130687C1P : TMParams :=
  ⟨[⟨242635377319871223568559772981008483035184, 130329532390333382365747616152972823346826, 0, (-80), (-80)⟩], [], []⟩

theorem S130687C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B130687 S130687C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 130687.C1. -/

theorem S130687D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B130687 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S130687C1 ρ hρ

/-- 证书叶 130687.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S130687C2P : TMParams :=
  ⟨[], [], []⟩

theorem S130687C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B130687 S130687C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 130687.C2. -/

theorem S130687D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B130687 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S130687C2 ρ hρ

/-- 导数叶 130687（+∂x3f，then 支，全盒）. -/

def DP130687 : TMParams :=
  ⟨[⟨6402977610044886543161449634868894655855970, 6402977610044886543161449634868894655855970, 774690423707846202017631054522740674337307272519, (-80), (-80)⟩, ⟨6402977610044886543161449634868894655855970, 6402977610044886543161449634868894655855970, 774690423707846202017631054522740674337307272519, (-80), (-80)⟩, ⟨6402977610044886543161449634868894655855970, 6402977610044886543161449634868894655855970, 774690423707846202017631054522740674337307272519, (-80), (-80)⟩, ⟨6402977610044886543161449634868894655855970, 6402977610044886543161449634868894655855970, 774690423707846202017631054522740674337307272519, (-80), (-80)⟩, ⟨6402977610044886543161449634868894655855970, 6402977610044886543161449634868894655855970, 774690423707846202017631054522740674337307272519, (-80), (-80)⟩, ⟨6402977610044886543161449634868894655855970, 6402977610044886543161449634868894655855970, 774690423707846202017631054522740674337307272519, (-80), (-80)⟩, ⟨6402977610044886543161449634868894655855970, 6402977610044886543161449634868894655855970, 774690423707846202017631054522740674337307272519, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der130687 :
    checkPosTMHull (derivIExpr E549 2) B130687 DP130687
    = true := by
  decide

/-- 面叶 130687（lo 面）. -/

def FB130687 : Fin 6 → DInterval := faceBoxLo B130687 2

def PF130687 : TMParams :=
  ⟨[⟨270588333015209906418014349579682426583147, 124823360445237624625572515569492368963107, 0, (-80), (-80)⟩, ⟨6343154919121269525978014774328157162569707, 6343154919121269525978014774328157162569707, 779659055129689035368071284584196374311590850218, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face130687 :
    checkPosTMHull E549 FB130687 PF130687
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 130687，then 支）. -/

def DSafe130687 : DerivSafeOn B130687 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S130687D2) S130687D1) (Or.inr (Or.inr rfl))) S130687D0)))

/-- mono 折叠组合（叶 130687，两叶引用零重算）. -/

theorem Fold130687 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B130687 2 PF130687 DP130687 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B130687 DP130687 = true := Der130687
  have h2 : checkPosTMHull E549 (faceBoxLo B130687 2) PF130687 = true := Face130687
  show (checkPosTMHull (derivIExpr E549 2) B130687 DP130687
      && checkPosTMHull E549 (faceBoxLo B130687 2) PF130687) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 130687）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem130687 (ρ : Fin 6 → ℝ) (hρ : boxMem B130687 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe130687 Fold130687 hρ

#print axioms Sem130687

/-- 叶 130900（then 支，lo 面）原盒. -/

def B130900 : Fin 6 → DInterval :=
  ![⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩]

/-- 证书叶 130900.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S130900C0P : TMParams :=
  ⟨[⟨120910915747132608648375118019041849566971, 505029254666350794956676193829664331595170, 0, (-80), (-80)⟩], [], []⟩

theorem S130900C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B130900 S130900C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 130900.C0. -/

theorem S130900D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B130900 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S130900C0 ρ hρ

/-- 证书叶 130900.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S130900C1P : TMParams :=
  ⟨[⟨120910915747132608648375118019041849566971, 505029254666350794956676193829664331595170, 0, (-80), (-80)⟩], [], []⟩

theorem S130900C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B130900 S130900C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 130900.C1. -/

theorem S130900D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B130900 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S130900C1 ρ hρ

/-- 证书叶 130900.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S130900C2P : TMParams :=
  ⟨[], [], []⟩

theorem S130900C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B130900 S130900C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 130900.C2. -/

theorem S130900D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B130900 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S130900C2 ρ hρ

/-- 导数叶 130900（+∂x3f，then 支，全盒）. -/

def DP130900 : TMParams :=
  ⟨[⟨6236135851295494799193212130025399640950732, 6236135851295494799193212130025399640950732, 754623929048260756214996032638373012883479391831, (-80), (-80)⟩, ⟨6236135851295494799193212130025399640950732, 6236135851295494799193212130025399640950732, 754623929048260756214996032638373012883479391831, (-80), (-80)⟩, ⟨6236135851295494799193212130025399640950732, 6236135851295494799193212130025399640950732, 754623929048260756214996032638373012883479391831, (-80), (-80)⟩, ⟨6236135851295494799193212130025399640950732, 6236135851295494799193212130025399640950732, 754623929048260756214996032638373012883479391831, (-80), (-80)⟩, ⟨6236135851295494799193212130025399640950732, 6236135851295494799193212130025399640950732, 754623929048260756214996032638373012883479391831, (-80), (-80)⟩, ⟨6236135851295494799193212130025399640950732, 6236135851295494799193212130025399640950732, 754623929048260756214996032638373012883479391831, (-80), (-80)⟩, ⟨6236135851295494799193212130025399640950732, 6236135851295494799193212130025399640950732, 754623929048260756214996032638373012883479391831, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der130900 :
    checkPosTMHull (derivIExpr E549 2) B130900 DP130900
    = true := by
  decide

/-- 面叶 130900（lo 面）. -/

def FB130900 : Fin 6 → DInterval := faceBoxLo B130900 2

def PF130900 : TMParams :=
  ⟨[⟨133656383065068446228615699913232384748059, 484391931573738955852361626642049981512736, 0, (-80), (-80)⟩, ⟨6181602846889042466405632347787471443846969, 6181602846889042466405632347787471443846969, 759426095415091727263622586004047120586265674957, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face130900 :
    checkPosTMHull E549 FB130900 PF130900
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 130900，then 支）. -/

def DSafe130900 : DerivSafeOn B130900 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S130900D2) S130900D1) (Or.inr (Or.inr rfl))) S130900D0)))

/-- mono 折叠组合（叶 130900，两叶引用零重算）. -/

theorem Fold130900 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B130900 2 PF130900 DP130900 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B130900 DP130900 = true := Der130900
  have h2 : checkPosTMHull E549 (faceBoxLo B130900 2) PF130900 = true := Face130900
  show (checkPosTMHull (derivIExpr E549 2) B130900 DP130900
      && checkPosTMHull E549 (faceBoxLo B130900 2) PF130900) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 130900）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem130900 (ρ : Fin 6 → ℝ) (hρ : boxMem B130900 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe130900 Fold130900 hρ

#print axioms Sem130900

/-- 叶 131234（then 支，lo 面）原盒. -/

def B131234 : Fin 6 → DInterval :=
  ![⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩]

/-- 证书叶 131234.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S131234C0P : TMParams :=
  ⟨[⟨113986780268699407047205204865077182244485, 493467873855365309712305883897422615829766, 0, (-80), (-80)⟩], [], []⟩

theorem S131234C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B131234 S131234C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 131234.C0. -/

theorem S131234D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B131234 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S131234C0 ρ hρ

/-- 证书叶 131234.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S131234C1P : TMParams :=
  ⟨[⟨113986780268699407047205204865077182244485, 493467873855365309712305883897422615829766, 0, (-80), (-80)⟩], [], []⟩

theorem S131234C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B131234 S131234C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 131234.C1. -/

theorem S131234D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B131234 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S131234C1 ρ hρ

/-- 证书叶 131234.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S131234C2P : TMParams :=
  ⟨[], [], []⟩

theorem S131234C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B131234 S131234C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 131234.C2. -/

theorem S131234D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B131234 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S131234C2 ρ hρ

/-- 导数叶 131234（+∂x3f，then 支，全盒）. -/

def DP131234 : TMParams :=
  ⟨[⟨6050305250322597125462318329017807862503076, 6050305250322597125462318329017807862503076, 731040674688025721492929911326606255693938603421, (-80), (-80)⟩, ⟨6050305250322597125462318329017807862503076, 6050305250322597125462318329017807862503076, 731040674688025721492929911326606255693938603421, (-80), (-80)⟩, ⟨6050305250322597125462318329017807862503076, 6050305250322597125462318329017807862503076, 731040674688025721492929911326606255693938603421, (-80), (-80)⟩, ⟨6050305250322597125462318329017807862503076, 6050305250322597125462318329017807862503076, 731040674688025721492929911326606255693938603421, (-80), (-80)⟩, ⟨6050305250322597125462318329017807862503076, 6050305250322597125462318329017807862503076, 731040674688025721492929911326606255693938603421, (-80), (-80)⟩, ⟨6050305250322597125462318329017807862503076, 6050305250322597125462318329017807862503076, 731040674688025721492929911326606255693938603421, (-80), (-80)⟩, ⟨6050305250322597125462318329017807862503076, 6050305250322597125462318329017807862503076, 731040674688025721492929911326606255693938603421, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der131234 :
    checkPosTMHull (derivIExpr E549 2) B131234 DP131234
    = true := by
  decide

/-- 面叶 131234（lo 面）. -/

def FB131234 : Fin 6 → DInterval := faceBoxLo B131234 2

def PF131234 : TMParams :=
  ⟨[⟨63139846164110296529296991693474375213156, 472564686581086668632995426032610218751109, 0, (-80), (-80)⟩, ⟨5982772271475593217775644860743194318150097, 5982772271475593217775644860743194318150097, 735947658717915900457625644493731945058806712534, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face131234 :
    checkPosTMHull E549 FB131234 PF131234
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 131234，then 支）. -/

def DSafe131234 : DerivSafeOn B131234 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S131234D2) S131234D1) (Or.inr (Or.inr rfl))) S131234D0)))

/-- mono 折叠组合（叶 131234，两叶引用零重算）. -/

theorem Fold131234 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B131234 2 PF131234 DP131234 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B131234 DP131234 = true := Der131234
  have h2 : checkPosTMHull E549 (faceBoxLo B131234 2) PF131234 = true := Face131234
  show (checkPosTMHull (derivIExpr E549 2) B131234 DP131234
      && checkPosTMHull E549 (faceBoxLo B131234 2) PF131234) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 131234）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem131234 (ρ : Fin 6 → ℝ) (hρ : boxMem B131234 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe131234 Fold131234 hρ

#print axioms Sem131234


end Kepler.Interval.C549ProdS0032
