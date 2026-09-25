import Kepler.Interval.Cases.C549Mono
import Kepler.Interval.Cases.C549CertSlimDefs


/-! ## 549 facePos 全量评估（emit_mono.py 生成；勿手改）。

C549MonoBatch34 — rung 128（发射钉死） shard 34/53（20 叶；modes ['then']）
每叶：面叶 + 导数叶 + DerivSafeOn 证书叶 ⇒ 嵌套 DSafe ⇒
checkPosFace*_sound ⇒ 全盒语义正性 0 < evalReal ρ。
本模块层级：['cert', 'der', 'face', 'fold']；decide 战术：decide。 -/


set_option maxHeartbeats 0
set_option maxRecDepth 1000000


namespace Kepler.Interval.C549MonoBatch34

open Kepler.Interval


/-- case 549 表达式（本模块自包含副本）. -/

def E549 : IExpr 6 :=
  (.sub (.div (.const ⟨1893, 0⟩) (.const ⟨1000, 0⟩) (-64)) (.add (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.const ⟨2, 0⟩) (-64)) (.ite (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) (.trans .arctanK (.div (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0) (-64)) 128 (-80)) (.ite (.sub (.const ⟨0, 0⟩) (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sub (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.const ⟨2, 0⟩) (-64)) (.trans .arctanK (.div (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0) (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) (-64)) 128 (-80))) (.ite (.sub (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) (.const ⟨0, 0⟩)) (.sub (.neg (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.const ⟨2, 0⟩) (-64))) (.trans .arctanK (.div (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0) (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) (-64)) 128 (-80))) (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))))))))

/-- 叶 126902（then 支，lo 面）原盒. -/

def B126902 : Fin 6 → DInterval :=
  ![⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩]

/-- 证书叶 126902.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S126902C0P : TMParams :=
  ⟨[⟨123741444335893853639957389628869028002584, 512429485586741485376007217970413875511617, 0, (-80), (-80)⟩], [], []⟩

theorem S126902C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B126902 S126902C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 126902.C0. -/

theorem S126902D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B126902 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S126902C0 ρ hρ

/-- 证书叶 126902.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S126902C1P : TMParams :=
  ⟨[⟨123741444335893853639957389628869028002584, 512429485586741485376007217970413875511617, 0, (-80), (-80)⟩], [], []⟩

theorem S126902C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B126902 S126902C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 126902.C1. -/

theorem S126902D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B126902 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S126902C1 ρ hρ

/-- 证书叶 126902.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S126902C2P : TMParams :=
  ⟨[], [], []⟩

theorem S126902C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B126902 S126902C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 126902.C2. -/

theorem S126902D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B126902 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S126902C2 ρ hρ

/-- 导数叶 126902（+∂x3f，then 支，全盒）. -/

def DP126902 : TMParams :=
  ⟨[⟨6338951485701105515937102455803201496565424, 6338951485701105515937102455803201496565424, 767523148757773208000865675263410294411437536197, (-80), (-80)⟩, ⟨6338951485701105515937102455803201496565424, 6338951485701105515937102455803201496565424, 767523148757773208000865675263410294411437536197, (-80), (-80)⟩, ⟨6338951485701105515937102455803201496565424, 6338951485701105515937102455803201496565424, 767523148757773208000865675263410294411437536197, (-80), (-80)⟩, ⟨6338951485701105515937102455803201496565424, 6338951485701105515937102455803201496565424, 767523148757773208000865675263410294411437536197, (-80), (-80)⟩, ⟨6338951485701105515937102455803201496565424, 6338951485701105515937102455803201496565424, 767523148757773208000865675263410294411437536197, (-80), (-80)⟩, ⟨6338951485701105515937102455803201496565424, 6338951485701105515937102455803201496565424, 767523148757773208000865675263410294411437536197, (-80), (-80)⟩, ⟨6338951485701105515937102455803201496565424, 6338951485701105515937102455803201496565424, 767523148757773208000865675263410294411437536197, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der126902 :
    checkPosTMHull (derivIExpr E549 2) B126902 DP126902
    = true := by
  decide

/-- 面叶 126902（lo 面）. -/

def FB126902 : Fin 6 → DInterval := faceBoxLo B126902 2

def PF126902 : TMParams :=
  ⟨[⟨136183979231409481091886224931626145042457, 491650871257364633257372911702329251408614, 0, (-80), (-80)⟩, ⟨6280718847362390812666416908538257970939024, 6280718847362390812666416908538257970939024, 772354908136212371314903015562824483636809818836, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face126902 :
    checkPosTMHull E549 FB126902 PF126902
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 126902，then 支）. -/

def DSafe126902 : DerivSafeOn B126902 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S126902D2) S126902D1) (Or.inr (Or.inr rfl))) S126902D0)))

/-- mono 折叠组合（叶 126902，两叶引用零重算）. -/

theorem Fold126902 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B126902 2 PF126902 DP126902 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B126902 DP126902 = true := Der126902
  have h2 : checkPosTMHull E549 (faceBoxLo B126902 2) PF126902 = true := Face126902
  show (checkPosTMHull (derivIExpr E549 2) B126902 DP126902
      && checkPosTMHull E549 (faceBoxLo B126902 2) PF126902) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 126902）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem126902 (ρ : Fin 6 → ℝ) (hρ : boxMem B126902 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe126902 Fold126902 hρ

#print axioms Sem126902

/-- 叶 127135（then 支，lo 面）原盒. -/

def B127135 : Fin 6 → DInterval :=
  ![⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩]

/-- 证书叶 127135.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S127135C0P : TMParams :=
  ⟨[⟨122773266120568307378490225734146545197198, 520581882992601563296955516694446986437657, 0, (-80), (-80)⟩], [], []⟩

theorem S127135C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B127135 S127135C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 127135.C0. -/

theorem S127135D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B127135 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S127135C0 ρ hρ

/-- 证书叶 127135.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S127135C1P : TMParams :=
  ⟨[⟨122773266120568307378490225734146545197198, 520581882992601563296955516694446986437657, 0, (-80), (-80)⟩], [], []⟩

theorem S127135C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B127135 S127135C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 127135.C1. -/

theorem S127135D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B127135 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S127135C1 ρ hρ

/-- 证书叶 127135.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S127135C2P : TMParams :=
  ⟨[], [], []⟩

theorem S127135C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B127135 S127135C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 127135.C2. -/

theorem S127135D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B127135 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S127135C2 ρ hρ

/-- 导数叶 127135（+∂x3f，then 支，全盒）. -/

def DP127135 : TMParams :=
  ⟨[⟨6409618177244019817679654518190361539949812, 6409618177244019817679654518190361539949812, 775773372196356101790947885669741798577280760249, (-80), (-80)⟩, ⟨6409618177244019817679654518190361539949812, 6409618177244019817679654518190361539949812, 775773372196356101790947885669741798577280760249, (-80), (-80)⟩, ⟨6409618177244019817679654518190361539949812, 6409618177244019817679654518190361539949812, 775773372196356101790947885669741798577280760249, (-80), (-80)⟩, ⟨6409618177244019817679654518190361539949812, 6409618177244019817679654518190361539949812, 775773372196356101790947885669741798577280760249, (-80), (-80)⟩, ⟨6409618177244019817679654518190361539949812, 6409618177244019817679654518190361539949812, 775773372196356101790947885669741798577280760249, (-80), (-80)⟩, ⟨6409618177244019817679654518190361539949812, 6409618177244019817679654518190361539949812, 775773372196356101790947885669741798577280760249, (-80), (-80)⟩, ⟨6409618177244019817679654518190361539949812, 6409618177244019817679654518190361539949812, 775773372196356101790947885669741798577280760249, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der127135 :
    checkPosTMHull (derivIExpr E549 2) B127135 DP127135
    = true := by
  decide

/-- 面叶 127135（lo 面）. -/

def FB127135 : Fin 6 → DInterval := faceBoxLo B127135 2

def PF127135 : TMParams :=
  ⟨[⟨134936464095364086010836547066545038537350, 499141464806415108693565173989973262265061, 0, (-80), (-80)⟩, ⟨6338690125570531872449422650548097744401400, 6338690125570531872449422650548097744401400, 780810719583171196284292982182390012323095931967, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face127135 :
    checkPosTMHull E549 FB127135 PF127135
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 127135，then 支）. -/

def DSafe127135 : DerivSafeOn B127135 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S127135D2) S127135D1) (Or.inr (Or.inr rfl))) S127135D0)))

/-- mono 折叠组合（叶 127135，两叶引用零重算）. -/

theorem Fold127135 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B127135 2 PF127135 DP127135 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B127135 DP127135 = true := Der127135
  have h2 : checkPosTMHull E549 (faceBoxLo B127135 2) PF127135 = true := Face127135
  show (checkPosTMHull (derivIExpr E549 2) B127135 DP127135
      && checkPosTMHull E549 (faceBoxLo B127135 2) PF127135) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 127135）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem127135 (ρ : Fin 6 → ℝ) (hρ : boxMem B127135 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe127135 Fold127135 hρ

#print axioms Sem127135

/-- 叶 127287（then 支，lo 面）原盒. -/

def B127287 : Fin 6 → DInterval :=
  ![⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩]

/-- 证书叶 127287.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S127287C0P : TMParams :=
  ⟨[⟨264918646088799977197528709649275436405522, 136714350820693935291235565696135031599967, 0, (-80), (-80)⟩], [], []⟩

theorem S127287C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B127287 S127287C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 127287.C0. -/

theorem S127287D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B127287 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S127287C0 ρ hρ

/-- 证书叶 127287.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S127287C1P : TMParams :=
  ⟨[⟨264918646088799977197528709649275436405522, 136714350820693935291235565696135031599967, 0, (-80), (-80)⟩], [], []⟩

theorem S127287C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B127287 S127287C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 127287.C1. -/

theorem S127287D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B127287 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S127287C1 ρ hρ

/-- 证书叶 127287.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S127287C2P : TMParams :=
  ⟨[], [], []⟩

theorem S127287C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B127287 S127287C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 127287.C2. -/

theorem S127287D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B127287 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S127287C2 ρ hρ

/-- 导数叶 127287（+∂x3f，then 支，全盒）. -/

def DP127287 : TMParams :=
  ⟨[⟨6771397165098340226149955085660488909430434, 6771397165098340226149955085660488909430434, 821015379605641107541099052398314084476734601574, (-80), (-80)⟩, ⟨6771397165098340226149955085660488909430434, 6771397165098340226149955085660488909430434, 821015379605641107541099052398314084476734601574, (-80), (-80)⟩, ⟨6771397165098340226149955085660488909430434, 6771397165098340226149955085660488909430434, 821015379605641107541099052398314084476734601574, (-80), (-80)⟩, ⟨6771397165098340226149955085660488909430434, 6771397165098340226149955085660488909430434, 821015379605641107541099052398314084476734601574, (-80), (-80)⟩, ⟨6771397165098340226149955085660488909430434, 6771397165098340226149955085660488909430434, 821015379605641107541099052398314084476734601574, (-80), (-80)⟩, ⟨6771397165098340226149955085660488909430434, 6771397165098340226149955085660488909430434, 821015379605641107541099052398314084476734601574, (-80), (-80)⟩, ⟨6771397165098340226149955085660488909430434, 6771397165098340226149955085660488909430434, 821015379605641107541099052398314084476734601574, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der127287 :
    checkPosTMHull (derivIExpr E549 2) B127287 DP127287
    = true := by
  decide

/-- 面叶 127287（lo 面）. -/

def FB127287 : Fin 6 → DInterval := faceBoxLo B127287 2

def PF127287 : TMParams :=
  ⟨[⟨290309094257600934278644456975966599824297, 131161106188543845631754148949223695567226, 0, (-80), (-80)⟩, ⟨6702047281651874309689494566648513458775968, 6702047281651874309689494566648513458775968, 826107190905615865860592088695847910893976178220, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face127287 :
    checkPosTMHull E549 FB127287 PF127287
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 127287，then 支）. -/

def DSafe127287 : DerivSafeOn B127287 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S127287D2) S127287D1) (Or.inr (Or.inr rfl))) S127287D0)))

/-- mono 折叠组合（叶 127287，两叶引用零重算）. -/

theorem Fold127287 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B127287 2 PF127287 DP127287 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B127287 DP127287 = true := Der127287
  have h2 : checkPosTMHull E549 (faceBoxLo B127287 2) PF127287 = true := Face127287
  show (checkPosTMHull (derivIExpr E549 2) B127287 DP127287
      && checkPosTMHull E549 (faceBoxLo B127287 2) PF127287) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 127287）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem127287 (ρ : Fin 6 → ℝ) (hρ : boxMem B127287 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe127287 Fold127287 hρ

#print axioms Sem127287

/-- 叶 127645（then 支，lo 面）原盒. -/

def B127645 : Fin 6 → DInterval :=
  ![⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩]

/-- 证书叶 127645.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S127645C0P : TMParams :=
  ⟨[⟨129035848822710518760038824694586378140283, 531668364572321648099933294258957192293137, 0, (-80), (-80)⟩], [], []⟩

theorem S127645C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B127645 S127645C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 127645.C0. -/

theorem S127645D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B127645 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S127645C0 ρ hρ

/-- 证书叶 127645.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S127645C1P : TMParams :=
  ⟨[⟨129035848822710518760038824694586378140283, 531668364572321648099933294258957192293137, 0, (-80), (-80)⟩], [], []⟩

theorem S127645C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B127645 S127645C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 127645.C1. -/

theorem S127645D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B127645 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S127645C1 ρ hρ

/-- 证书叶 127645.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S127645C2P : TMParams :=
  ⟨[], [], []⟩

theorem S127645C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B127645 S127645C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 127645.C2. -/

theorem S127645D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B127645 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S127645C2 ρ hρ

/-- 导数叶 127645（+∂x3f，then 支，全盒）. -/

def DP127645 : TMParams :=
  ⟨[⟨6584320537847080032829942263227601153163663, 6584320537847080032829942263227601153163663, 797926035599027874206915280233993823656395590221, (-80), (-80)⟩, ⟨6584320537847080032829942263227601153163663, 6584320537847080032829942263227601153163663, 797926035599027874206915280233993823656395590221, (-80), (-80)⟩, ⟨6584320537847080032829942263227601153163663, 6584320537847080032829942263227601153163663, 797926035599027874206915280233993823656395590221, (-80), (-80)⟩, ⟨6584320537847080032829942263227601153163663, 6584320537847080032829942263227601153163663, 797926035599027874206915280233993823656395590221, (-80), (-80)⟩, ⟨6584320537847080032829942263227601153163663, 6584320537847080032829942263227601153163663, 797926035599027874206915280233993823656395590221, (-80), (-80)⟩, ⟨6584320537847080032829942263227601153163663, 6584320537847080032829942263227601153163663, 797926035599027874206915280233993823656395590221, (-80), (-80)⟩, ⟨6584320537847080032829942263227601153163663, 6584320537847080032829942263227601153163663, 797926035599027874206915280233993823656395590221, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der127645 :
    checkPosTMHull (derivIExpr E549 2) B127645 DP127645
    = true := by
  decide

/-- 面叶 127645（lo 面）. -/

def FB127645 : Fin 6 → DInterval := faceBoxLo B127645 2

def PF127645 : TMParams :=
  ⟨[⟨141918510105501375963603020503512298346359, 510154644513720780574784553253533273643185, 0, (-80), (-80)⟩, ⟨6524538881911943992945346730824475115160460, 6524538881911943992945346730824475115160460, 802848246455555779863597718572902119455053030680, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face127645 :
    checkPosTMHull E549 FB127645 PF127645
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 127645，then 支）. -/

def DSafe127645 : DerivSafeOn B127645 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S127645D2) S127645D1) (Or.inr (Or.inr rfl))) S127645D0)))

/-- mono 折叠组合（叶 127645，两叶引用零重算）. -/

theorem Fold127645 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B127645 2 PF127645 DP127645 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B127645 DP127645 = true := Der127645
  have h2 : checkPosTMHull E549 (faceBoxLo B127645 2) PF127645 = true := Face127645
  show (checkPosTMHull (derivIExpr E549 2) B127645 DP127645
      && checkPosTMHull E549 (faceBoxLo B127645 2) PF127645) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 127645）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem127645 (ρ : Fin 6 → ℝ) (hρ : boxMem B127645 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe127645 Fold127645 hρ

#print axioms Sem127645

/-- 叶 127800（then 支，lo 面）原盒. -/

def B127800 : Fin 6 → DInterval :=
  ![⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩]

/-- 证书叶 127800.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S127800C0P : TMParams :=
  ⟨[⟨271604242676878378409776787344797076788301, 69392884078321275292591843056513336722931, 0, (-80), (-80)⟩], [], []⟩

theorem S127800C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B127800 S127800C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 127800.C0. -/

theorem S127800D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B127800 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S127800C0 ρ hρ

/-- 证书叶 127800.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S127800C1P : TMParams :=
  ⟨[⟨271604242676878378409776787344797076788301, 69392884078321275292591843056513336722931, 0, (-80), (-80)⟩], [], []⟩

theorem S127800C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B127800 S127800C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 127800.C1. -/

theorem S127800D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B127800 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S127800C1 ρ hρ

/-- 证书叶 127800.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S127800C2P : TMParams :=
  ⟨[], [], []⟩

theorem S127800C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B127800 S127800C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 127800.C2. -/

theorem S127800D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B127800 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S127800C2 ρ hρ

/-- 导数叶 127800（+∂x3f，then 支，全盒）. -/

def DP127800 : TMParams :=
  ⟨[⟨6888314129103377430985862042426173173239137, 6888314129103377430985862042426173173239137, 835661860644721727134031521525413384965616081630, (-80), (-80)⟩, ⟨6888314129103377430985862042426173173239137, 6888314129103377430985862042426173173239137, 835661860644721727134031521525413384965616081630, (-80), (-80)⟩, ⟨6888314129103377430985862042426173173239137, 6888314129103377430985862042426173173239137, 835661860644721727134031521525413384965616081630, (-80), (-80)⟩, ⟨6888314129103377430985862042426173173239137, 6888314129103377430985862042426173173239137, 835661860644721727134031521525413384965616081630, (-80), (-80)⟩, ⟨6888314129103377430985862042426173173239137, 6888314129103377430985862042426173173239137, 835661860644721727134031521525413384965616081630, (-80), (-80)⟩, ⟨6888314129103377430985862042426173173239137, 6888314129103377430985862042426173173239137, 835661860644721727134031521525413384965616081630, (-80), (-80)⟩, ⟨6888314129103377430985862042426173173239137, 6888314129103377430985862042426173173239137, 835661860644721727134031521525413384965616081630, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der127800 :
    checkPosTMHull (derivIExpr E549 2) B127800 DP127800
    = true := by
  decide

/-- 面叶 127800（lo 面）. -/

def FB127800 : Fin 6 → DInterval := faceBoxLo B127800 2

def PF127800 : TMParams :=
  ⟨[⟨297287893676437859825705882990456357872051, 66623676148296864060150244737486114636154, 0, (-80), (-80)⟩, ⟨6823142101747973843510397617618289134006384, 6823142101747973843510397617618289134006384, 840764191665452319279508392908117956510322726184, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face127800 :
    checkPosTMHull E549 FB127800 PF127800
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 127800，then 支）. -/

def DSafe127800 : DerivSafeOn B127800 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S127800D2) S127800D1) (Or.inr (Or.inr rfl))) S127800D0)))

/-- mono 折叠组合（叶 127800，两叶引用零重算）. -/

theorem Fold127800 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B127800 2 PF127800 DP127800 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B127800 DP127800 = true := Der127800
  have h2 : checkPosTMHull E549 (faceBoxLo B127800 2) PF127800 = true := Face127800
  show (checkPosTMHull (derivIExpr E549 2) B127800 DP127800
      && checkPosTMHull E549 (faceBoxLo B127800 2) PF127800) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 127800）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem127800 (ρ : Fin 6 → ℝ) (hρ : boxMem B127800 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe127800 Fold127800 hρ

#print axioms Sem127800

/-- 叶 127980（then 支，lo 面）原盒. -/

def B127980 : Fin 6 → DInterval :=
  ![⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩]

/-- 证书叶 127980.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S127980C0P : TMParams :=
  ⟨[⟨254594770793816811050848827383250055451708, 130699128304774243251423616524033749448797, 0, (-80), (-80)⟩], [], []⟩

theorem S127980C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B127980 S127980C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 127980.C0. -/

theorem S127980D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B127980 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S127980C0 ρ hρ

/-- 证书叶 127980.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S127980C1P : TMParams :=
  ⟨[⟨254594770793816811050848827383250055451708, 130699128304774243251423616524033749448797, 0, (-80), (-80)⟩], [], []⟩

theorem S127980C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B127980 S127980C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 127980.C1. -/

theorem S127980D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B127980 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S127980C1 ρ hρ

/-- 证书叶 127980.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S127980C2P : TMParams :=
  ⟨[], [], []⟩

theorem S127980C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B127980 S127980C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 127980.C2. -/

theorem S127980D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B127980 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S127980C2 ρ hρ

/-- 导数叶 127980（+∂x3f，then 支，全盒）. -/

def DP127980 : TMParams :=
  ⟨[⟨6479701194294113310576797833271413489410432, 6479701194294113310576797833271413489410432, 785046147252473420923218182682466940321095004679, (-80), (-80)⟩, ⟨6479701194294113310576797833271413489410432, 6479701194294113310576797833271413489410432, 785046147252473420923218182682466940321095004679, (-80), (-80)⟩, ⟨6479701194294113310576797833271413489410432, 6479701194294113310576797833271413489410432, 785046147252473420923218182682466940321095004679, (-80), (-80)⟩, ⟨6479701194294113310576797833271413489410432, 6479701194294113310576797833271413489410432, 785046147252473420923218182682466940321095004679, (-80), (-80)⟩, ⟨6479701194294113310576797833271413489410432, 6479701194294113310576797833271413489410432, 785046147252473420923218182682466940321095004679, (-80), (-80)⟩, ⟨6479701194294113310576797833271413489410432, 6479701194294113310576797833271413489410432, 785046147252473420923218182682466940321095004679, (-80), (-80)⟩, ⟨6479701194294113310576797833271413489410432, 6479701194294113310576797833271413489410432, 785046147252473420923218182682466940321095004679, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der127980 :
    checkPosTMHull (derivIExpr E549 2) B127980 DP127980
    = true := by
  decide

/-- 面叶 127980（lo 面）. -/

def FB127980 : Fin 6 → DInterval := faceBoxLo B127980 2

def PF127980 : TMParams :=
  ⟨[⟨279614968632210757651610351232334013591878, 62721926860275377089095456600527864983989, 0, (-80), (-80)⟩, ⟨6420947351474984969206041671984215410768723, 6420947351474984969206041671984215410768723, 789946925518649744784444834811056681804983678977, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face127980 :
    checkPosTMHull E549 FB127980 PF127980
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 127980，then 支）. -/

def DSafe127980 : DerivSafeOn B127980 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S127980D2) S127980D1) (Or.inr (Or.inr rfl))) S127980D0)))

/-- mono 折叠组合（叶 127980，两叶引用零重算）. -/

theorem Fold127980 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B127980 2 PF127980 DP127980 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B127980 DP127980 = true := Der127980
  have h2 : checkPosTMHull E549 (faceBoxLo B127980 2) PF127980 = true := Face127980
  show (checkPosTMHull (derivIExpr E549 2) B127980 DP127980
      && checkPosTMHull E549 (faceBoxLo B127980 2) PF127980) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 127980）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem127980 (ρ : Fin 6 → ℝ) (hρ : boxMem B127980 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe127980 Fold127980 hρ

#print axioms Sem127980

/-- 叶 128132（then 支，lo 面）原盒. -/

def B128132 : Fin 6 → DInterval :=
  ![⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩]

/-- 证书叶 128132.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S128132C0P : TMParams :=
  ⟨[⟨121545141178733052693098811539789542734254, 257359933597184820693488220197284538277151, 0, (-80), (-80)⟩], [], []⟩

theorem S128132C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B128132 S128132C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 128132.C0. -/

theorem S128132D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B128132 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S128132C0 ρ hρ

/-- 证书叶 128132.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S128132C1P : TMParams :=
  ⟨[⟨121545141178733052693098811539789542734254, 257359933597184820693488220197284538277151, 0, (-80), (-80)⟩], [], []⟩

theorem S128132C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B128132 S128132C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 128132.C1. -/

theorem S128132D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B128132 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S128132C1 ρ hρ

/-- 证书叶 128132.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S128132C2P : TMParams :=
  ⟨[], [], []⟩

theorem S128132C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B128132 S128132C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 128132.C2. -/

theorem S128132D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B128132 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S128132C2 ρ hρ

/-- 导数叶 128132（+∂x3f，then 支，全盒）. -/

def DP128132 : TMParams :=
  ⟨[⟨6338811511142573559786410728056408959039501, 6338811511142573559786410728056408959039501, 767056077103734769585921904762747923379464390271, (-80), (-80)⟩, ⟨6338811511142573559786410728056408959039501, 6338811511142573559786410728056408959039501, 767056077103734769585921904762747923379464390271, (-80), (-80)⟩, ⟨6338811511142573559786410728056408959039501, 6338811511142573559786410728056408959039501, 767056077103734769585921904762747923379464390271, (-80), (-80)⟩, ⟨6338811511142573559786410728056408959039501, 6338811511142573559786410728056408959039501, 767056077103734769585921904762747923379464390271, (-80), (-80)⟩, ⟨6338811511142573559786410728056408959039501, 6338811511142573559786410728056408959039501, 767056077103734769585921904762747923379464390271, (-80), (-80)⟩, ⟨6338811511142573559786410728056408959039501, 6338811511142573559786410728056408959039501, 767056077103734769585921904762747923379464390271, (-80), (-80)⟩, ⟨6338811511142573559786410728056408959039501, 6338811511142573559786410728056408959039501, 767056077103734769585921904762747923379464390271, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der128132 :
    checkPosTMHull (derivIExpr E549 2) B128132 DP128132
    = true := by
  decide

/-- 面叶 128132（lo 面）. -/

def FB128132 : Fin 6 → DInterval := faceBoxLo B128132 2

def PF128132 : TMParams :=
  ⟨[⟨133987896892731150110971836242832959443055, 493367052976925863428373468711971698225132, 0, (-80), (-80)⟩, ⟨6271682070199247466775896864698666943476320, 6271682070199247466775896864698666943476320, 772018811136681315341094611473445144271836137461, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face128132 :
    checkPosTMHull E549 FB128132 PF128132
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 128132，then 支）. -/

def DSafe128132 : DerivSafeOn B128132 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S128132D2) S128132D1) (Or.inr (Or.inr rfl))) S128132D0)))

/-- mono 折叠组合（叶 128132，两叶引用零重算）. -/

theorem Fold128132 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B128132 2 PF128132 DP128132 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B128132 DP128132 = true := Der128132
  have h2 : checkPosTMHull E549 (faceBoxLo B128132 2) PF128132 = true := Face128132
  show (checkPosTMHull (derivIExpr E549 2) B128132 DP128132
      && checkPosTMHull E549 (faceBoxLo B128132 2) PF128132) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 128132）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem128132 (ρ : Fin 6 → ℝ) (hρ : boxMem B128132 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe128132 Fold128132 hρ

#print axioms Sem128132

/-- 叶 128286（then 支，lo 面）原盒. -/

def B128286 : Fin 6 → DInterval :=
  ![⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩]

/-- 证书叶 128286.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S128286C0P : TMParams :=
  ⟨[⟨258779544102105762542857547889723519744754, 133561908991779604541115141403728117997101, 0, (-80), (-80)⟩], [], []⟩

theorem S128286C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B128286 S128286C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 128286.C0. -/

theorem S128286D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B128286 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S128286C0 ρ hρ

/-- 证书叶 128286.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S128286C1P : TMParams :=
  ⟨[⟨258779544102105762542857547889723519744754, 133561908991779604541115141403728117997101, 0, (-80), (-80)⟩], [], []⟩

theorem S128286C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B128286 S128286C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 128286.C1. -/

theorem S128286D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B128286 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S128286C1 ρ hρ

/-- 证书叶 128286.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S128286C2P : TMParams :=
  ⟨[], [], []⟩

theorem S128286C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B128286 S128286C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 128286.C2. -/

theorem S128286D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B128286 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S128286C2 ρ hρ

/-- 导数叶 128286（+∂x3f，then 支，全盒）. -/

def DP128286 : TMParams :=
  ⟨[⟨6614783597706837363042969658525322022891617, 6614783597706837363042969658525322022891617, 801634154855082203049930255299249804598214157076, (-80), (-80)⟩, ⟨6614783597706837363042969658525322022891617, 6614783597706837363042969658525322022891617, 801634154855082203049930255299249804598214157076, (-80), (-80)⟩, ⟨6614783597706837363042969658525322022891617, 6614783597706837363042969658525322022891617, 801634154855082203049930255299249804598214157076, (-80), (-80)⟩, ⟨6614783597706837363042969658525322022891617, 6614783597706837363042969658525322022891617, 801634154855082203049930255299249804598214157076, (-80), (-80)⟩, ⟨6614783597706837363042969658525322022891617, 6614783597706837363042969658525322022891617, 801634154855082203049930255299249804598214157076, (-80), (-80)⟩, ⟨6614783597706837363042969658525322022891617, 6614783597706837363042969658525322022891617, 801634154855082203049930255299249804598214157076, (-80), (-80)⟩, ⟨6614783597706837363042969658525322022891617, 6614783597706837363042969658525322022891617, 801634154855082203049930255299249804598214157076, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der128286 :
    checkPosTMHull (derivIExpr E549 2) B128286 DP128286
    = true := by
  decide

/-- 面叶 128286（lo 面）. -/

def FB128286 : Fin 6 → DInterval := faceBoxLo B128286 2

def PF128286 : TMParams :=
  ⟨[⟨283489485261854616468530367063908810805646, 128209920395872037210585586776459597844251, 0, (-80), (-80)⟩, ⟨6550053363684667754716214063751159953242260, 6550053363684667754716214063751159953242260, 806662672403912500380896297962484457778144176426, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face128286 :
    checkPosTMHull E549 FB128286 PF128286
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 128286，then 支）. -/

def DSafe128286 : DerivSafeOn B128286 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S128286D2) S128286D1) (Or.inr (Or.inr rfl))) S128286D0)))

/-- mono 折叠组合（叶 128286，两叶引用零重算）. -/

theorem Fold128286 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B128286 2 PF128286 DP128286 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B128286 DP128286 = true := Der128286
  have h2 : checkPosTMHull E549 (faceBoxLo B128286 2) PF128286 = true := Face128286
  show (checkPosTMHull (derivIExpr E549 2) B128286 DP128286
      && checkPosTMHull E549 (faceBoxLo B128286 2) PF128286) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 128286）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem128286 (ρ : Fin 6 → ℝ) (hρ : boxMem B128286 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe128286 Fold128286 hρ

#print axioms Sem128286

/-- 叶 128445（then 支，lo 面）原盒. -/

def B128445 : Fin 6 → DInterval :=
  ![⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩]

/-- 证书叶 128445.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S128445C0P : TMParams :=
  ⟨[⟨118455186428265013946604827200772140359126, 502440843440149979747907832801672765414111, 0, (-80), (-80)⟩], [], []⟩

theorem S128445C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B128445 S128445C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 128445.C0. -/

theorem S128445D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B128445 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S128445C0 ρ hρ

/-- 证书叶 128445.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S128445C1P : TMParams :=
  ⟨[⟨118455186428265013946604827200772140359126, 502440843440149979747907832801672765414111, 0, (-80), (-80)⟩], [], []⟩

theorem S128445C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B128445 S128445C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 128445.C1. -/

theorem S128445D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B128445 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S128445C1 ρ hρ

/-- 证书叶 128445.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S128445C2P : TMParams :=
  ⟨[], [], []⟩

theorem S128445C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B128445 S128445C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 128445.C2. -/

theorem S128445D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B128445 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S128445C2 ρ hρ

/-- 导数叶 128445（+∂x3f，then 支，全盒）. -/

def DP128445 : TMParams :=
  ⟨[⟨6185350035900076719677668315242193855894373, 6185350035900076719677668315242193855894373, 748089668455790551515183027130404110064101323141, (-80), (-80)⟩, ⟨6185350035900076719677668315242193855894373, 6185350035900076719677668315242193855894373, 748089668455790551515183027130404110064101323141, (-80), (-80)⟩, ⟨6185350035900076719677668315242193855894373, 6185350035900076719677668315242193855894373, 748089668455790551515183027130404110064101323141, (-80), (-80)⟩, ⟨6185350035900076719677668315242193855894373, 6185350035900076719677668315242193855894373, 748089668455790551515183027130404110064101323141, (-80), (-80)⟩, ⟨6185350035900076719677668315242193855894373, 6185350035900076719677668315242193855894373, 748089668455790551515183027130404110064101323141, (-80), (-80)⟩, ⟨6185350035900076719677668315242193855894373, 6185350035900076719677668315242193855894373, 748089668455790551515183027130404110064101323141, (-80), (-80)⟩, ⟨6185350035900076719677668315242193855894373, 6185350035900076719677668315242193855894373, 748089668455790551515183027130404110064101323141, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der128445 :
    checkPosTMHull (derivIExpr E549 2) B128445 DP128445
    = true := by
  decide

/-- 面叶 128445（lo 面）. -/

def FB128445 : Fin 6 → DInterval := faceBoxLo B128445 2

def PF128445 : TMParams :=
  ⟨[⟨130243902931301372209617351964126523776596, 241065895903981162107504839584490352726632, 0, (-80), (-80)⟩, ⟨6122012441937431034035023067937135315469873, 6122012441937431034035023067937135315469873, 753013500466006691182086470294670819121594711235, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face128445 :
    checkPosTMHull E549 FB128445 PF128445
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 128445，then 支）. -/

def DSafe128445 : DerivSafeOn B128445 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S128445D2) S128445D1) (Or.inr (Or.inr rfl))) S128445D0)))

/-- mono 折叠组合（叶 128445，两叶引用零重算）. -/

theorem Fold128445 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B128445 2 PF128445 DP128445 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B128445 DP128445 = true := Der128445
  have h2 : checkPosTMHull E549 (faceBoxLo B128445 2) PF128445 = true := Face128445
  show (checkPosTMHull (derivIExpr E549 2) B128445 DP128445
      && checkPosTMHull E549 (faceBoxLo B128445 2) PF128445) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 128445）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem128445 (ρ : Fin 6 → ℝ) (hρ : boxMem B128445 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe128445 Fold128445 hρ

#print axioms Sem128445

/-- 叶 128607（then 支，lo 面）原盒. -/

def B128607 : Fin 6 → DInterval :=
  ![⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩]

/-- 证书叶 128607.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S128607C0P : TMParams :=
  ⟨[⟨248205880954318816446842411125054609409688, 259684422444453395355799452976890941422109, 0, (-80), (-80)⟩], [], []⟩

theorem S128607C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B128607 S128607C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 128607.C0. -/

theorem S128607D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B128607 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S128607C0 ρ hρ

/-- 证书叶 128607.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S128607C1P : TMParams :=
  ⟨[⟨248205880954318816446842411125054609409688, 259684422444453395355799452976890941422109, 0, (-80), (-80)⟩], [], []⟩

theorem S128607C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B128607 S128607C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 128607.C1. -/

theorem S128607D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B128607 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S128607C1 ρ hρ

/-- 证书叶 128607.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S128607C2P : TMParams :=
  ⟨[], [], []⟩

theorem S128607C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B128607 S128607C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 128607.C2. -/

theorem S128607D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B128607 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S128607C2 ρ hρ

/-- 导数叶 128607（+∂x3f，then 支，全盒）. -/

def DP128607 : TMParams :=
  ⟨[⟨6410028381510413227048242891206065890867154, 6410028381510413227048242891206065890867154, 776084334875858523390752426112262154026420851247, (-80), (-80)⟩, ⟨6410028381510413227048242891206065890867154, 6410028381510413227048242891206065890867154, 776084334875858523390752426112262154026420851247, (-80), (-80)⟩, ⟨6410028381510413227048242891206065890867154, 6410028381510413227048242891206065890867154, 776084334875858523390752426112262154026420851247, (-80), (-80)⟩, ⟨6410028381510413227048242891206065890867154, 6410028381510413227048242891206065890867154, 776084334875858523390752426112262154026420851247, (-80), (-80)⟩, ⟨6410028381510413227048242891206065890867154, 6410028381510413227048242891206065890867154, 776084334875858523390752426112262154026420851247, (-80), (-80)⟩, ⟨6410028381510413227048242891206065890867154, 6410028381510413227048242891206065890867154, 776084334875858523390752426112262154026420851247, (-80), (-80)⟩, ⟨6410028381510413227048242891206065890867154, 6410028381510413227048242891206065890867154, 776084334875858523390752426112262154026420851247, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der128607 :
    checkPosTMHull (derivIExpr E549 2) B128607 DP128607
    = true := by
  decide

/-- 面叶 128607（lo 面）. -/

def FB128607 : Fin 6 → DInterval := faceBoxLo B128607 2

def PF128607 : TMParams :=
  ⟨[⟨273918455075794596871096569726408658283727, 249028814109365823753032623863690076553854, 0, (-80), (-80)⟩, ⟨6349881261884508126926540882368452251216544, 6349881261884508126926540882368452251216544, 780961996261684393955023591116711731866336458187, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face128607 :
    checkPosTMHull E549 FB128607 PF128607
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 128607，then 支）. -/

def DSafe128607 : DerivSafeOn B128607 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S128607D2) S128607D1) (Or.inr (Or.inr rfl))) S128607D0)))

/-- mono 折叠组合（叶 128607，两叶引用零重算）. -/

theorem Fold128607 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B128607 2 PF128607 DP128607 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B128607 DP128607 = true := Der128607
  have h2 : checkPosTMHull E549 (faceBoxLo B128607 2) PF128607 = true := Face128607
  show (checkPosTMHull (derivIExpr E549 2) B128607 DP128607
      && checkPosTMHull E549 (faceBoxLo B128607 2) PF128607) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 128607）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem128607 (ρ : Fin 6 → ℝ) (hρ : boxMem B128607 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe128607 Fold128607 hρ

#print axioms Sem128607

/-- 叶 128761（then 支，lo 面）原盒. -/

def B128761 : Fin 6 → DInterval :=
  ![⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩]

/-- 证书叶 128761.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S128761C0P : TMParams :=
  ⟨[⟨26552439042279510985798042945414, 242027362818391739580713517982341487292036, 0, (-80), (-80)⟩], [], []⟩

theorem S128761C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B128761 S128761C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 128761.C0. -/

theorem S128761D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B128761 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S128761C0 ρ hρ

/-- 证书叶 128761.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S128761C1P : TMParams :=
  ⟨[⟨26552439042279510985798042945414, 242027362818391739580713517982341487292036, 0, (-80), (-80)⟩], [], []⟩

theorem S128761C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B128761 S128761C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 128761.C1. -/

theorem S128761D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B128761 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S128761C1 ρ hρ

/-- 证书叶 128761.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S128761C2P : TMParams :=
  ⟨[], [], []⟩

theorem S128761C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B128761 S128761C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 128761.C2. -/

theorem S128761D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B128761 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S128761C2 ρ hρ

/-- 导数叶 128761（+∂x3f，then 支，全盒）. -/

def DP128761 : TMParams :=
  ⟨[⟨5955212688070161043502202139947098297768871, 5955212688070161043502202139947098297768871, 719724982831846720787734787818582610271261635242, (-80), (-80)⟩, ⟨5955212688070161043502202139947098297768871, 5955212688070161043502202139947098297768871, 719724982831846720787734787818582610271261635242, (-80), (-80)⟩, ⟨5955212688070161043502202139947098297768871, 5955212688070161043502202139947098297768871, 719724982831846720787734787818582610271261635242, (-80), (-80)⟩, ⟨5955212688070161043502202139947098297768871, 5955212688070161043502202139947098297768871, 719724982831846720787734787818582610271261635242, (-80), (-80)⟩, ⟨5955212688070161043502202139947098297768871, 5955212688070161043502202139947098297768871, 719724982831846720787734787818582610271261635242, (-80), (-80)⟩, ⟨5955212688070161043502202139947098297768871, 5955212688070161043502202139947098297768871, 719724982831846720787734787818582610271261635242, (-80), (-80)⟩, ⟨5955212688070161043502202139947098297768871, 5955212688070161043502202139947098297768871, 719724982831846720787734787818582610271261635242, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der128761 :
    checkPosTMHull (derivIExpr E549 2) B128761 DP128761
    = true := by
  decide

/-- 面叶 128761（lo 面）. -/

def FB128761 : Fin 6 → DInterval := faceBoxLo B128761 2

def PF128761 : TMParams :=
  ⟨[⟨14695859902352982782537856009369, 232104404623991117846630293433984306752374, 0, (-80), (-80)⟩, ⟨5900712835379167731767460484583359898426407, 5900712835379167731767460484583359898426407, 724406202540407912931050365521795340754577548423, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face128761 :
    checkPosTMHull E549 FB128761 PF128761
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 128761，then 支）. -/

def DSafe128761 : DerivSafeOn B128761 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S128761D2) S128761D1) (Or.inr (Or.inr rfl))) S128761D0)))

/-- mono 折叠组合（叶 128761，两叶引用零重算）. -/

theorem Fold128761 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B128761 2 PF128761 DP128761 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B128761 DP128761 = true := Der128761
  have h2 : checkPosTMHull E549 (faceBoxLo B128761 2) PF128761 = true := Face128761
  show (checkPosTMHull (derivIExpr E549 2) B128761 DP128761
      && checkPosTMHull E549 (faceBoxLo B128761 2) PF128761) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 128761）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem128761 (ρ : Fin 6 → ℝ) (hρ : boxMem B128761 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe128761 Fold128761 hρ

#print axioms Sem128761

/-- 叶 129023（then 支，lo 面）原盒. -/

def B129023 : Fin 6 → DInterval :=
  ![⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩]

/-- 证书叶 129023.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S129023C0P : TMParams :=
  ⟨[⟨234089732834861484309532269516265768396213, 251582863270813174308845084776020312755216, 0, (-80), (-80)⟩], [], []⟩

theorem S129023C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B129023 S129023C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 129023.C0. -/

theorem S129023D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B129023 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S129023C0 ρ hρ

/-- 证书叶 129023.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S129023C1P : TMParams :=
  ⟨[⟨234089732834861484309532269516265768396213, 251582863270813174308845084776020312755216, 0, (-80), (-80)⟩], [], []⟩

theorem S129023C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B129023 S129023C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 129023.C1. -/

theorem S129023D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B129023 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S129023C1 ρ hρ

/-- 证书叶 129023.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S129023C2P : TMParams :=
  ⟨[], [], []⟩

theorem S129023C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B129023 S129023C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 129023.C2. -/

theorem S129023D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B129023 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S129023C2 ρ hρ

/-- 导数叶 129023（+∂x3f，then 支，全盒）. -/

def DP129023 : TMParams :=
  ⟨[⟨6176710260422837693059970065771103854806057, 6176710260422837693059970065771103854806057, 746741860768057749077433114334997652836823056623, (-80), (-80)⟩, ⟨6176710260422837693059970065771103854806057, 6176710260422837693059970065771103854806057, 746741860768057749077433114334997652836823056623, (-80), (-80)⟩, ⟨6176710260422837693059970065771103854806057, 6176710260422837693059970065771103854806057, 746741860768057749077433114334997652836823056623, (-80), (-80)⟩, ⟨6176710260422837693059970065771103854806057, 6176710260422837693059970065771103854806057, 746741860768057749077433114334997652836823056623, (-80), (-80)⟩, ⟨6176710260422837693059970065771103854806057, 6176710260422837693059970065771103854806057, 746741860768057749077433114334997652836823056623, (-80), (-80)⟩, ⟨6176710260422837693059970065771103854806057, 6176710260422837693059970065771103854806057, 746741860768057749077433114334997652836823056623, (-80), (-80)⟩, ⟨6176710260422837693059970065771103854806057, 6176710260422837693059970065771103854806057, 746741860768057749077433114334997652836823056623, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der129023 :
    checkPosTMHull (derivIExpr E549 2) B129023 DP129023
    = true := by
  decide

/-- 面叶 129023（lo 面）. -/

def FB129023 : Fin 6 → DInterval := faceBoxLo B129023 2

def PF129023 : TMParams :=
  ⟨[⟨258758933300471324704817423687685651231896, 241055368479844162205800683120875171069532, 0, (-80), (-80)⟩, ⟨6109805125536870018860937943760577387388865, 6109805125536870018860937943760577387388865, 751681632670292500435423861007482362904358285197, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face129023 :
    checkPosTMHull E549 FB129023 PF129023
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 129023，then 支）. -/

def DSafe129023 : DerivSafeOn B129023 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S129023D2) S129023D1) (Or.inr (Or.inr rfl))) S129023D0)))

/-- mono 折叠组合（叶 129023，两叶引用零重算）. -/

theorem Fold129023 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B129023 2 PF129023 DP129023 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B129023 DP129023 = true := Der129023
  have h2 : checkPosTMHull E549 (faceBoxLo B129023 2) PF129023 = true := Face129023
  show (checkPosTMHull (derivIExpr E549 2) B129023 DP129023
      && checkPosTMHull E549 (faceBoxLo B129023 2) PF129023) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 129023）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem129023 (ρ : Fin 6 → ℝ) (hρ : boxMem B129023 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe129023 Fold129023 hρ

#print axioms Sem129023

/-- 叶 129447（then 支，lo 面）原盒. -/

def B129447 : Fin 6 → DInterval :=
  ![⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩]

/-- 证书叶 129447.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S129447C0P : TMParams :=
  ⟨[⟨243616496476454852766516698454606640385575, 254007442414747882169824831122904128978455, 0, (-80), (-80)⟩], [], []⟩

theorem S129447C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B129447 S129447C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 129447.C0. -/

theorem S129447D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B129447 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S129447C0 ρ hρ

/-- 证书叶 129447.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S129447C1P : TMParams :=
  ⟨[⟨243616496476454852766516698454606640385575, 254007442414747882169824831122904128978455, 0, (-80), (-80)⟩], [], []⟩

theorem S129447C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B129447 S129447C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 129447.C1. -/

theorem S129447D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B129447 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S129447C1 ρ hρ

/-- 证书叶 129447.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S129447C2P : TMParams :=
  ⟨[], [], []⟩

theorem S129447C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B129447 S129447C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 129447.C2. -/

theorem S129447D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B129447 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S129447C2 ρ hρ

/-- 导数叶 129447（+∂x3f，then 支，全盒）. -/

def DP129447 : TMParams :=
  ⟨[⟨6274084839151999750112271225161491627910389, 6274084839151999750112271225161491627910389, 759384624853740275244056616956739453846127424643, (-80), (-80)⟩, ⟨6274084839151999750112271225161491627910389, 6274084839151999750112271225161491627910389, 759384624853740275244056616956739453846127424643, (-80), (-80)⟩, ⟨6274084839151999750112271225161491627910389, 6274084839151999750112271225161491627910389, 759384624853740275244056616956739453846127424643, (-80), (-80)⟩, ⟨6274084839151999750112271225161491627910389, 6274084839151999750112271225161491627910389, 759384624853740275244056616956739453846127424643, (-80), (-80)⟩, ⟨6274084839151999750112271225161491627910389, 6274084839151999750112271225161491627910389, 759384624853740275244056616956739453846127424643, (-80), (-80)⟩, ⟨6274084839151999750112271225161491627910389, 6274084839151999750112271225161491627910389, 759384624853740275244056616956739453846127424643, (-80), (-80)⟩, ⟨6274084839151999750112271225161491627910389, 6274084839151999750112271225161491627910389, 759384624853740275244056616956739453846127424643, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der129447 :
    checkPosTMHull (derivIExpr E549 2) B129447 DP129447
    = true := by
  decide

/-- 面叶 129447（lo 面）. -/

def FB129447 : Fin 6 → DInterval := faceBoxLo B129447 2

def PF129447 : TMParams :=
  ⟨[⟨133934042468328086763772902713762846051864, 243945318802879244749808525417225318561311, 0, (-80), (-80)⟩, ⟨6218802393159835908442873068129369588584338, 6218802393159835908442873068129369588584338, 764194999671821238687237887641829578363726927098, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face129447 :
    checkPosTMHull E549 FB129447 PF129447
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 129447，then 支）. -/

def DSafe129447 : DerivSafeOn B129447 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S129447D2) S129447D1) (Or.inr (Or.inr rfl))) S129447D0)))

/-- mono 折叠组合（叶 129447，两叶引用零重算）. -/

theorem Fold129447 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B129447 2 PF129447 DP129447 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B129447 DP129447 = true := Der129447
  have h2 : checkPosTMHull E549 (faceBoxLo B129447 2) PF129447 = true := Face129447
  show (checkPosTMHull (derivIExpr E549 2) B129447 DP129447
      && checkPosTMHull E549 (faceBoxLo B129447 2) PF129447) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 129447）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem129447 (ρ : Fin 6 → ℝ) (hρ : boxMem B129447 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe129447 Fold129447 hρ

#print axioms Sem129447

/-- 叶 129599（then 支，lo 面）原盒. -/

def B129599 : Fin 6 → DInterval :=
  ![⟨⟨2, 0⟩, ⟨34918084117, -34⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩]

/-- 证书叶 129599.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S129599C0P : TMParams :=
  ⟨[⟨55496420127836658058191021411572, 1848013201353878243592345323092794420801473, 0, (-80), (-80)⟩], [], []⟩

theorem S129599C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B129599 S129599C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 129599.C0. -/

theorem S129599D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B129599 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S129599C0 ρ hρ

/-- 证书叶 129599.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S129599C1P : TMParams :=
  ⟨[⟨55496420127836658058191021411572, 1848013201353878243592345323092794420801473, 0, (-80), (-80)⟩], [], []⟩

theorem S129599C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B129599 S129599C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 129599.C1. -/

theorem S129599D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B129599 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S129599C1 ρ hρ

/-- 证书叶 129599.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S129599C2P : TMParams :=
  ⟨[], [], []⟩

theorem S129599C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B129599 S129599C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 129599.C2. -/

theorem S129599D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B129599 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S129599C2 ρ hρ

/-- 导数叶 129599（+∂x3f，then 支，全盒）. -/

def DP129599 : TMParams :=
  ⟨[⟨46577342190173334586673628371144406444287143, 46577342190173334586673628371144406444287143, 11470966576818340335843011375550109962662834666384, (-80), (-80)⟩, ⟨46577342190173334586673628371144406444287143, 46577342190173334586673628371144406444287143, 11470966576818340335843011375550109962662834666384, (-80), (-80)⟩, ⟨46577342190173334586673628371144406444287143, 46577342190173334586673628371144406444287143, 11470966576818340335843011375550109962662834666384, (-80), (-80)⟩, ⟨46577342190173334586673628371144406444287143, 46577342190173334586673628371144406444287143, 11470966576818340335843011375550109962662834666384, (-80), (-80)⟩, ⟨46577342190173334586673628371144406444287143, 46577342190173334586673628371144406444287143, 11470966576818340335843011375550109962662834666384, (-80), (-80)⟩, ⟨46577342190173334586673628371144406444287143, 46577342190173334586673628371144406444287143, 11470966576818340335843011375550109962662834666384, (-80), (-80)⟩, ⟨46577342190173334586673628371144406444287143, 46577342190173334586673628371144406444287143, 11470966576818340335843011375550109962662834666384, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der129599 :
    checkPosTMHull (derivIExpr E549 2) B129599 DP129599
    = true := by
  decide

/-- 面叶 129599（lo 面）. -/

def FB129599 : Fin 6 → DInterval := faceBoxLo B129599 2

def PF129599 : TMParams :=
  ⟨[⟨30363390549972844309164468792314, 1772679550949231973038568044305688397514103, 0, (-80), (-80)⟩, ⟨46195353827942616432676211065133328875579985, 46195353827942616432676211065133328875579985, 11532946026628696849405131802407132780185278600258, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face129599 :
    checkPosTMHull E549 FB129599 PF129599
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 129599，then 支）. -/

def DSafe129599 : DerivSafeOn B129599 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S129599D2) S129599D1) (Or.inr (Or.inr rfl))) S129599D0)))

/-- mono 折叠组合（叶 129599，两叶引用零重算）. -/

theorem Fold129599 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B129599 2 PF129599 DP129599 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B129599 DP129599 = true := Der129599
  have h2 : checkPosTMHull E549 (faceBoxLo B129599 2) PF129599 = true := Face129599
  show (checkPosTMHull (derivIExpr E549 2) B129599 DP129599
      && checkPosTMHull E549 (faceBoxLo B129599 2) PF129599) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 129599）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem129599 (ρ : Fin 6 → ℝ) (hρ : boxMem B129599 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe129599 Fold129599 hρ

#print axioms Sem129599

/-- 叶 129805（then 支，lo 面）原盒. -/

def B129805 : Fin 6 → DInterval :=
  ![⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩]

/-- 证书叶 129805.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S129805C0P : TMParams :=
  ⟨[⟨25981717415885393264338129608620, 473095443667234164773505890710124184094399, 0, (-80), (-80)⟩], [], []⟩

theorem S129805C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B129805 S129805C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 129805.C0. -/

theorem S129805D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B129805 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S129805C0 ρ hρ

/-- 证书叶 129805.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S129805C1P : TMParams :=
  ⟨[⟨25981717415885393264338129608620, 473095443667234164773505890710124184094399, 0, (-80), (-80)⟩], [], []⟩

theorem S129805C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B129805 S129805C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 129805.C1. -/

theorem S129805D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B129805 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S129805C1 ρ hρ

/-- 证书叶 129805.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S129805C2P : TMParams :=
  ⟨[], [], []⟩

theorem S129805C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B129805 S129805C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 129805.C2. -/

theorem S129805D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B129805 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S129805C2 ρ hρ

/-- 导数叶 129805（+∂x3f，then 支，全盒）. -/

def DP129805 : TMParams :=
  ⟨[⟨5821283492470211907805379648697104102491063, 5821283492470211907805379648697104102491063, 703220635003066179386816450332545914514249546193, (-80), (-80)⟩, ⟨5821283492470211907805379648697104102491063, 5821283492470211907805379648697104102491063, 703220635003066179386816450332545914514249546193, (-80), (-80)⟩, ⟨5821283492470211907805379648697104102491063, 5821283492470211907805379648697104102491063, 703220635003066179386816450332545914514249546193, (-80), (-80)⟩, ⟨5821283492470211907805379648697104102491063, 5821283492470211907805379648697104102491063, 703220635003066179386816450332545914514249546193, (-80), (-80)⟩, ⟨5821283492470211907805379648697104102491063, 5821283492470211907805379648697104102491063, 703220635003066179386816450332545914514249546193, (-80), (-80)⟩, ⟨5821283492470211907805379648697104102491063, 5821283492470211907805379648697104102491063, 703220635003066179386816450332545914514249546193, (-80), (-80)⟩, ⟨5821283492470211907805379648697104102491063, 5821283492470211907805379648697104102491063, 703220635003066179386816450332545914514249546193, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der129805 :
    checkPosTMHull (derivIExpr E549 2) B129805 DP129805
    = true := by
  decide

/-- 面叶 129805（lo 面）. -/

def FB129805 : Fin 6 → DInterval := faceBoxLo B129805 2

def PF129805 : TMParams :=
  ⟨[⟨28720234772038700007315244179682, 227027505321041092602410974106930838069469, 0, (-80), (-80)⟩, ⟨5770602490736292487314584212522024653588019, 5770602490736292487314584212522024653588019, 707837715538027069210346711147783744242425857853, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face129805 :
    checkPosTMHull E549 FB129805 PF129805
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 129805，then 支）. -/

def DSafe129805 : DerivSafeOn B129805 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S129805D2) S129805D1) (Or.inr (Or.inr rfl))) S129805D0)))

/-- mono 折叠组合（叶 129805，两叶引用零重算）. -/

theorem Fold129805 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B129805 2 PF129805 DP129805 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B129805 DP129805 = true := Der129805
  have h2 : checkPosTMHull E549 (faceBoxLo B129805 2) PF129805 = true := Face129805
  show (checkPosTMHull (derivIExpr E549 2) B129805 DP129805
      && checkPosTMHull E549 (faceBoxLo B129805 2) PF129805) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 129805）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem129805 (ρ : Fin 6 → ℝ) (hρ : boxMem B129805 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe129805 Fold129805 hρ

#print axioms Sem129805

/-- 叶 129969（then 支，lo 面）原盒. -/

def B129969 : Fin 6 → DInterval :=
  ![⟨⟨36034775615, -34⟩, ⟨9148280341, -32⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩]

/-- 证书叶 129969.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S129969C0P : TMParams :=
  ⟨[⟨1013737336870133400220528318921148716959500, 492138958757557206123594249695166137209880, 0, (-80), (-80)⟩], [], []⟩

theorem S129969C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B129969 S129969C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 129969.C0. -/

theorem S129969D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B129969 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S129969C0 ρ hρ

/-- 证书叶 129969.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S129969C1P : TMParams :=
  ⟨[⟨1013737336870133400220528318921148716959500, 492138958757557206123594249695166137209880, 0, (-80), (-80)⟩], [], []⟩

theorem S129969C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B129969 S129969C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 129969.C1. -/

theorem S129969D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B129969 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S129969C1 ρ hρ

/-- 证书叶 129969.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S129969C2P : TMParams :=
  ⟨[], [], []⟩

theorem S129969C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B129969 S129969C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 129969.C2. -/

theorem S129969D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B129969 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S129969C2 ρ hρ

/-- 导数叶 129969（+∂x3f，then 支，全盒）. -/

def DP129969 : TMParams :=
  ⟨[⟨49606801887490535570225608006248980750312342, 49606801887490535570225608006248980750312342, 12220881092644470702708639244717374373888812715761, (-80), (-80)⟩, ⟨49606801887490535570225608006248980750312342, 49606801887490535570225608006248980750312342, 12220881092644470702708639244717374373888812715761, (-80), (-80)⟩, ⟨49606801887490535570225608006248980750312342, 49606801887490535570225608006248980750312342, 12220881092644470702708639244717374373888812715761, (-80), (-80)⟩, ⟨49606801887490535570225608006248980750312342, 49606801887490535570225608006248980750312342, 12220881092644470702708639244717374373888812715761, (-80), (-80)⟩, ⟨49606801887490535570225608006248980750312342, 49606801887490535570225608006248980750312342, 12220881092644470702708639244717374373888812715761, (-80), (-80)⟩, ⟨49606801887490535570225608006248980750312342, 49606801887490535570225608006248980750312342, 12220881092644470702708639244717374373888812715761, (-80), (-80)⟩, ⟨49606801887490535570225608006248980750312342, 49606801887490535570225608006248980750312342, 12220881092644470702708639244717374373888812715761, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der129969 :
    checkPosTMHull (derivIExpr E549 2) B129969 DP129969
    = true := by
  decide

/-- 面叶 129969（lo 面）. -/

def FB129969 : Fin 6 → DInterval := faceBoxLo B129969 2

def PF129969 : TMParams :=
  ⟨[⟨1106366122702062518523408591759673564220937, 471182544797155861054286456951497159119669, 0, (-80), (-80)⟩, ⟨49082884957707908965662651553755432607625397, 49082884957707908965662651553755432607625397, 12286894598837107917859933431817489526738753647245, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face129969 :
    checkPosTMHull E549 FB129969 PF129969
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 129969，then 支）. -/

def DSafe129969 : DerivSafeOn B129969 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S129969D2) S129969D1) (Or.inr (Or.inr rfl))) S129969D0)))

/-- mono 折叠组合（叶 129969，两叶引用零重算）. -/

theorem Fold129969 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B129969 2 PF129969 DP129969 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B129969 DP129969 = true := Der129969
  have h2 : checkPosTMHull E549 (faceBoxLo B129969 2) PF129969 = true := Face129969
  show (checkPosTMHull (derivIExpr E549 2) B129969 DP129969
      && checkPosTMHull E549 (faceBoxLo B129969 2) PF129969) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 129969）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem129969 (ρ : Fin 6 → ℝ) (hρ : boxMem B129969 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe129969 Fold129969 hρ

#print axioms Sem129969

/-- 叶 130121（then 支，lo 面）原盒. -/

def B130121 : Fin 6 → DInterval :=
  ![⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩]

/-- 证书叶 130121.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S130121C0P : TMParams :=
  ⟨[⟨219936201760452744206128042194635999605662, 236937040121714629141136565551137593854451, 0, (-80), (-80)⟩], [], []⟩

theorem S130121C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B130121 S130121C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 130121.C0. -/

theorem S130121D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B130121 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S130121C0 ρ hρ

/-- 证书叶 130121.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S130121C1P : TMParams :=
  ⟨[⟨219936201760452744206128042194635999605662, 236937040121714629141136565551137593854451, 0, (-80), (-80)⟩], [], []⟩

theorem S130121C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B130121 S130121C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 130121.C1. -/

theorem S130121D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B130121 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S130121C1 ρ hρ

/-- 证书叶 130121.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S130121C2P : TMParams :=
  ⟨[], [], []⟩

theorem S130121C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B130121 S130121C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 130121.C2. -/

theorem S130121D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B130121 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S130121C2 ρ hρ

/-- 导数叶 130121（+∂x3f，then 支，全盒）. -/

def DP130121 : TMParams :=
  ⟨[⟨5813659345271238779603064955202556364588984, 5813659345271238779603064955202556364588984, 701986794953355337742970874352142358058270727778, (-80), (-80)⟩, ⟨5813659345271238779603064955202556364588984, 5813659345271238779603064955202556364588984, 701986794953355337742970874352142358058270727778, (-80), (-80)⟩, ⟨5813659345271238779603064955202556364588984, 5813659345271238779603064955202556364588984, 701986794953355337742970874352142358058270727778, (-80), (-80)⟩, ⟨5813659345271238779603064955202556364588984, 5813659345271238779603064955202556364588984, 701986794953355337742970874352142358058270727778, (-80), (-80)⟩, ⟨5813659345271238779603064955202556364588984, 5813659345271238779603064955202556364588984, 701986794953355337742970874352142358058270727778, (-80), (-80)⟩, ⟨5813659345271238779603064955202556364588984, 5813659345271238779603064955202556364588984, 701986794953355337742970874352142358058270727778, (-80), (-80)⟩, ⟨5813659345271238779603064955202556364588984, 5813659345271238779603064955202556364588984, 701986794953355337742970874352142358058270727778, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der130121 :
    checkPosTMHull (derivIExpr E549 2) B130121 DP130121
    = true := by
  decide

/-- 面叶 130121（lo 面）. -/

def FB130121 : Fin 6 → DInterval := faceBoxLo B130121 2

def PF130121 : TMParams :=
  ⟨[⟨243359461845176204753116976389461826829475, 113512907473473668849759468561370592260505, 0, (-80), (-80)⟩, ⟨5751556420701091687421031649798128480473475, 5751556420701091687421031649798128480473475, 706726310832067817494940335835747990576675228936, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face130121 :
    checkPosTMHull E549 FB130121 PF130121
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 130121，then 支）. -/

def DSafe130121 : DerivSafeOn B130121 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S130121D2) S130121D1) (Or.inr (Or.inr rfl))) S130121D0)))

/-- mono 折叠组合（叶 130121，两叶引用零重算）. -/

theorem Fold130121 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B130121 2 PF130121 DP130121 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B130121 DP130121 = true := Der130121
  have h2 : checkPosTMHull E549 (faceBoxLo B130121 2) PF130121 = true := Face130121
  show (checkPosTMHull (derivIExpr E549 2) B130121 DP130121
      && checkPosTMHull E549 (faceBoxLo B130121 2) PF130121) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 130121）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem130121 (ρ : Fin 6 → ℝ) (hρ : boxMem B130121 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe130121 Fold130121 hρ

#print axioms Sem130121

/-- 叶 130321（then 支，lo 面）原盒. -/

def B130321 : Fin 6 → DInterval :=
  ![⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩]

/-- 证书叶 130321.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S130321C0P : TMParams :=
  ⟨[⟨112394183156513816982194657622547543572556, 238196616506491112563443815328499346315675, 0, (-80), (-80)⟩], [], []⟩

theorem S130321C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B130321 S130321C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 130321.C0. -/

theorem S130321D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B130321 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S130321C0 ρ hρ

/-- 证书叶 130321.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S130321C1P : TMParams :=
  ⟨[⟨112394183156513816982194657622547543572556, 238196616506491112563443815328499346315675, 0, (-80), (-80)⟩], [], []⟩

theorem S130321C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B130321 S130321C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 130321.C1. -/

theorem S130321D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B130321 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S130321C1 ρ hρ

/-- 证书叶 130321.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S130321C2P : TMParams :=
  ⟨[], [], []⟩

theorem S130321C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B130321 S130321C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 130321.C2. -/

theorem S130321D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B130321 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S130321C2 ρ hρ

/-- 导数叶 130321（+∂x3f，then 支，全盒）. -/

def DP130321 : TMParams :=
  ⟨[⟨5863475914118885035988293270258638115400424, 5863475914118885035988293270258638115400424, 708407430939140729420424073474334764316328841972, (-80), (-80)⟩, ⟨5863475914118885035988293270258638115400424, 5863475914118885035988293270258638115400424, 708407430939140729420424073474334764316328841972, (-80), (-80)⟩, ⟨5863475914118885035988293270258638115400424, 5863475914118885035988293270258638115400424, 708407430939140729420424073474334764316328841972, (-80), (-80)⟩, ⟨5863475914118885035988293270258638115400424, 5863475914118885035988293270258638115400424, 708407430939140729420424073474334764316328841972, (-80), (-80)⟩, ⟨5863475914118885035988293270258638115400424, 5863475914118885035988293270258638115400424, 708407430939140729420424073474334764316328841972, (-80), (-80)⟩, ⟨5863475914118885035988293270258638115400424, 5863475914118885035988293270258638115400424, 708407430939140729420424073474334764316328841972, (-80), (-80)⟩, ⟨5863475914118885035988293270258638115400424, 5863475914118885035988293270258638115400424, 708407430939140729420424073474334764316328841972, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der130321 :
    checkPosTMHull (derivIExpr E549 2) B130321 DP130321
    = true := by
  decide

/-- 面叶 130321（lo 面）. -/

def FB130321 : Fin 6 → DInterval := faceBoxLo B130321 2

def PF130321 : TMParams :=
  ⟨[⟨247970695247783685804517452498029408751358, 228596214840286847257207759740497156670197, 0, (-80), (-80)⟩, ⟨5809158339041038495296155157246625712800296, 5809158339041038495296155157246625712800296, 713102381315180140159162716271829378971713124150, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face130321 :
    checkPosTMHull E549 FB130321 PF130321
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 130321，then 支）. -/

def DSafe130321 : DerivSafeOn B130321 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S130321D2) S130321D1) (Or.inr (Or.inr rfl))) S130321D0)))

/-- mono 折叠组合（叶 130321，两叶引用零重算）. -/

theorem Fold130321 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B130321 2 PF130321 DP130321 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B130321 DP130321 = true := Der130321
  have h2 : checkPosTMHull E549 (faceBoxLo B130321 2) PF130321 = true := Face130321
  show (checkPosTMHull (derivIExpr E549 2) B130321 DP130321
      && checkPosTMHull E549 (faceBoxLo B130321 2) PF130321) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 130321）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem130321 (ρ : Fin 6 → ℝ) (hρ : boxMem B130321 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe130321 Fold130321 hρ

#print axioms Sem130321

/-- 叶 130488（then 支，lo 面）原盒. -/

def B130488 : Fin 6 → DInterval :=
  ![⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩]

/-- 证书叶 130488.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S130488C0P : TMParams :=
  ⟨[⟨128886668976155472926102810324406899251229, 540806070363064071821222471564124615452776, 0, (-80), (-80)⟩], [], []⟩

theorem S130488C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B130488 S130488C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 130488.C0. -/

theorem S130488D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B130488 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S130488C0 ρ hρ

/-- 证书叶 130488.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S130488C1P : TMParams :=
  ⟨[⟨128886668976155472926102810324406899251229, 540806070363064071821222471564124615452776, 0, (-80), (-80)⟩], [], []⟩

theorem S130488C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B130488 S130488C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 130488.C1. -/

theorem S130488D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B130488 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S130488C1 ρ hρ

/-- 证书叶 130488.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S130488C2P : TMParams :=
  ⟨[], [], []⟩

theorem S130488C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B130488 S130488C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 130488.C2. -/

theorem S130488D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B130488 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S130488C2 ρ hρ

/-- 导数叶 130488（+∂x3f，then 支，全盒）. -/

def DP130488 : TMParams :=
  ⟨[⟨6672937281929407861188620485141084171977739, 6672937281929407861188620485141084171977739, 808483951817945848549277151801554943202201239935, (-80), (-80)⟩, ⟨6672937281929407861188620485141084171977739, 6672937281929407861188620485141084171977739, 808483951817945848549277151801554943202201239935, (-80), (-80)⟩, ⟨6672937281929407861188620485141084171977739, 6672937281929407861188620485141084171977739, 808483951817945848549277151801554943202201239935, (-80), (-80)⟩, ⟨6672937281929407861188620485141084171977739, 6672937281929407861188620485141084171977739, 808483951817945848549277151801554943202201239935, (-80), (-80)⟩, ⟨6672937281929407861188620485141084171977739, 6672937281929407861188620485141084171977739, 808483951817945848549277151801554943202201239935, (-80), (-80)⟩, ⟨6672937281929407861188620485141084171977739, 6672937281929407861188620485141084171977739, 808483951817945848549277151801554943202201239935, (-80), (-80)⟩, ⟨6672937281929407861188620485141084171977739, 6672937281929407861188620485141084171977739, 808483951817945848549277151801554943202201239935, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der130488 :
    checkPosTMHull (derivIExpr E549 2) B130488 DP130488
    = true := by
  decide

/-- 面叶 130488（lo 面）. -/

def FB130488 : Fin 6 → DInterval := faceBoxLo B130488 2

def PF130488 : TMParams :=
  ⟨[⟨142400300559544154372801069113229752991191, 518374593696910870296422645797428173816005, 0, (-80), (-80)⟩, ⟨6608164583922186595888408085503349818276514, 6608164583922186595888408085503349818276514, 813522046799459430634534582338737910695119916934, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face130488 :
    checkPosTMHull E549 FB130488 PF130488
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 130488，then 支）. -/

def DSafe130488 : DerivSafeOn B130488 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S130488D2) S130488D1) (Or.inr (Or.inr rfl))) S130488D0)))

/-- mono 折叠组合（叶 130488，两叶引用零重算）. -/

theorem Fold130488 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B130488 2 PF130488 DP130488 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B130488 DP130488 = true := Der130488
  have h2 : checkPosTMHull E549 (faceBoxLo B130488 2) PF130488 = true := Face130488
  show (checkPosTMHull (derivIExpr E549 2) B130488 DP130488
      && checkPosTMHull E549 (faceBoxLo B130488 2) PF130488) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 130488）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem130488 (ρ : Fin 6 → ℝ) (hρ : boxMem B130488 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe130488 Fold130488 hρ

#print axioms Sem130488

/-- 叶 130640（then 支，lo 面）原盒. -/

def B130640 : Fin 6 → DInterval :=
  ![⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩]

/-- 证书叶 130640.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S130640C0P : TMParams :=
  ⟨[⟨126217858739922087482248383369555076643122, 524084333569662050954840282055009116254920, 0, (-80), (-80)⟩], [], []⟩

theorem S130640C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B130640 S130640C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 130640.C0. -/

theorem S130640D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B130640 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S130640C0 ρ hρ

/-- 证书叶 130640.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S130640C1P : TMParams :=
  ⟨[⟨126217858739922087482248383369555076643122, 524084333569662050954840282055009116254920, 0, (-80), (-80)⟩], [], []⟩

theorem S130640C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B130640 S130640C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 130640.C1. -/

theorem S130640D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B130640 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S130640C1 ρ hρ

/-- 证书叶 130640.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S130640C2P : TMParams :=
  ⟨[], [], []⟩

theorem S130640C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B130640 S130640C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 130640.C2. -/

theorem S130640D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B130640 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S130640C2 ρ hρ

/-- 导数叶 130640（+∂x3f，then 支，全盒）. -/

def DP130640 : TMParams :=
  ⟨[⟨6479969922427194666770203023069799026042458, 6479969922427194666770203023069799026042458, 784890144326381252201619305155594600143888488279, (-80), (-80)⟩, ⟨6479969922427194666770203023069799026042458, 6479969922427194666770203023069799026042458, 784890144326381252201619305155594600143888488279, (-80), (-80)⟩, ⟨6479969922427194666770203023069799026042458, 6479969922427194666770203023069799026042458, 784890144326381252201619305155594600143888488279, (-80), (-80)⟩, ⟨6479969922427194666770203023069799026042458, 6479969922427194666770203023069799026042458, 784890144326381252201619305155594600143888488279, (-80), (-80)⟩, ⟨6479969922427194666770203023069799026042458, 6479969922427194666770203023069799026042458, 784890144326381252201619305155594600143888488279, (-80), (-80)⟩, ⟨6479969922427194666770203023069799026042458, 6479969922427194666770203023069799026042458, 784890144326381252201619305155594600143888488279, (-80), (-80)⟩, ⟨6479969922427194666770203023069799026042458, 6479969922427194666770203023069799026042458, 784890144326381252201619305155594600143888488279, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der130640 :
    checkPosTMHull (derivIExpr E549 2) B130640 DP130640
    = true := by
  decide

/-- 面叶 130640（lo 面）. -/

def FB130640 : Fin 6 → DInterval := faceBoxLo B130640 2

def PF130640 : TMParams :=
  ⟨[⟨139354761251833310912244232186713314098498, 502688968027737551153114469368463871630381, 0, (-80), (-80)⟩, ⟨6422838572963873116460311996670448077975956, 6422838572963873116460311996670448077975956, 789761447654536207307237250586385852267938196708, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face130640 :
    checkPosTMHull E549 FB130640 PF130640
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 130640，then 支）. -/

def DSafe130640 : DerivSafeOn B130640 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S130640D2) S130640D1) (Or.inr (Or.inr rfl))) S130640D0)))

/-- mono 折叠组合（叶 130640，两叶引用零重算）. -/

theorem Fold130640 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B130640 2 PF130640 DP130640 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B130640 DP130640 = true := Der130640
  have h2 : checkPosTMHull E549 (faceBoxLo B130640 2) PF130640 = true := Face130640
  show (checkPosTMHull (derivIExpr E549 2) B130640 DP130640
      && checkPosTMHull E549 (faceBoxLo B130640 2) PF130640) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 130640）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem130640 (ρ : Fin 6 → ℝ) (hρ : boxMem B130640 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe130640 Fold130640 hρ

#print axioms Sem130640


end Kepler.Interval.C549MonoBatch34
