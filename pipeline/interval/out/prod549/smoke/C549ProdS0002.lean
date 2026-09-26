import Kepler.Interval.Cases.C549Mono
import Kepler.Interval.Cases.C549CertSlimDefs


/-! ## 549 facePos 全量评估（emit_mono.py 生成；勿手改）。

C549ProdS0002 — rung 128（发射钉死） shard 1/1（18 叶；modes ['then']）
每叶：面叶 + 导数叶 + DerivSafeOn 证书叶 ⇒ 嵌套 DSafe ⇒
checkPosFace*_sound ⇒ 全盒语义正性 0 < evalReal ρ。
本模块层级：['cert', 'der', 'face', 'fold']；decide 战术：decide。 -/


set_option maxHeartbeats 0
set_option maxRecDepth 1000000


namespace Kepler.Interval.C549ProdS0002

open Kepler.Interval


/-- case 549 表达式（本模块自包含副本）. -/

def E549 : IExpr 6 :=
  (.sub (.div (.const ⟨1893, 0⟩) (.const ⟨1000, 0⟩) (-64)) (.add (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.const ⟨2, 0⟩) (-64)) (.ite (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) (.trans .arctanK (.div (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0) (-64)) 128 (-80)) (.ite (.sub (.const ⟨0, 0⟩) (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sub (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.const ⟨2, 0⟩) (-64)) (.trans .arctanK (.div (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0) (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) (-64)) 128 (-80))) (.ite (.sub (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) (.const ⟨0, 0⟩)) (.sub (.neg (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.const ⟨2, 0⟩) (-64))) (.trans .arctanK (.div (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0) (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) (-64)) 128 (-80))) (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))))))))

/-- 叶 100277（then 支，lo 面）原盒. -/

def B100277 : Fin 6 → DInterval :=
  ![⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩]

/-- 证书叶 100277.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S100277C0P : TMParams :=
  ⟨[⟨56183638006834322993141906987206784167728, 497188669606131052382892645337057377772423, 0, (-80), (-80)⟩], [], []⟩

theorem S100277C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B100277 S100277C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 100277.C0. -/

theorem S100277D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B100277 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S100277C0 ρ hρ

/-- 证书叶 100277.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S100277C1P : TMParams :=
  ⟨[⟨56183638006834322993141906987206784167728, 497188669606131052382892645337057377772423, 0, (-80), (-80)⟩], [], []⟩

theorem S100277C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B100277 S100277C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 100277.C1. -/

theorem S100277D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B100277 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S100277C1 ρ hρ

/-- 证书叶 100277.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S100277C2P : TMParams :=
  ⟨[], [], []⟩

theorem S100277C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B100277 S100277C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 100277.C2. -/

theorem S100277D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B100277 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S100277C2 ρ hρ

/-- 导数叶 100277（+∂x3f，then 支，全盒）. -/

def DP100277 : TMParams :=
  ⟨[⟨6075416821252880662554701109781229557353526, 6075416821252880662554701109781229557353526, 733456680381713272535859521075798917611225267231, (-80), (-80)⟩, ⟨6075416821252880662554701109781229557353526, 6075416821252880662554701109781229557353526, 733456680381713272535859521075798917611225267231, (-80), (-80)⟩, ⟨6075416821252880662554701109781229557353526, 6075416821252880662554701109781229557353526, 733456680381713272535859521075798917611225267231, (-80), (-80)⟩, ⟨6075416821252880662554701109781229557353526, 6075416821252880662554701109781229557353526, 733456680381713272535859521075798917611225267231, (-80), (-80)⟩, ⟨6075416821252880662554701109781229557353526, 6075416821252880662554701109781229557353526, 733456680381713272535859521075798917611225267231, (-80), (-80)⟩, ⟨6075416821252880662554701109781229557353526, 6075416821252880662554701109781229557353526, 733456680381713272535859521075798917611225267231, (-80), (-80)⟩, ⟨6075416821252880662554701109781229557353526, 6075416821252880662554701109781229557353526, 733456680381713272535859521075798917611225267231, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der100277 :
    checkPosTMHull (derivIExpr E549 2) B100277 DP100277
    = true := by
  decide

/-- 面叶 100277（lo 面）. -/

def FB100277 : Fin 6 → DInterval := faceBoxLo B100277 2

def PF100277 : TMParams :=
  ⟨[⟨63172832721110056434075084754392627580677, 475886207577179608929031368400994575101778, 0, (-80), (-80)⟩, ⟨6019203811834492756191365601319525011438887, 6019203811834492756191365601319525011438887, 738544498155357822158468103215734118516891795411, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face100277 :
    checkPosTMHull E549 FB100277 PF100277
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 100277，then 支）. -/

def DSafe100277 : DerivSafeOn B100277 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S100277D2) S100277D1) (Or.inr (Or.inr rfl))) S100277D0)))

/-- mono 折叠组合（叶 100277，两叶引用零重算）. -/

theorem Fold100277 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B100277 2 PF100277 DP100277 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B100277 DP100277 = true := Der100277
  have h2 : checkPosTMHull E549 (faceBoxLo B100277 2) PF100277 = true := Face100277
  show (checkPosTMHull (derivIExpr E549 2) B100277 DP100277
      && checkPosTMHull E549 (faceBoxLo B100277 2) PF100277) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 100277）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem100277 (ρ : Fin 6 → ℝ) (hρ : boxMem B100277 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe100277 Fold100277 hρ

#print axioms Sem100277

/-- 叶 104537（then 支，lo 面）原盒. -/

def B104537 : Fin 6 → DInterval :=
  ![⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩]

/-- 证书叶 104537.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S104537C0P : TMParams :=
  ⟨[⟨52075666106246264979872613194959125393591, 459878343785020423414659373084909344454886, 0, (-80), (-80)⟩], [], []⟩

theorem S104537C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B104537 S104537C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 104537.C0. -/

theorem S104537D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B104537 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S104537C0 ρ hρ

/-- 证书叶 104537.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S104537C1P : TMParams :=
  ⟨[⟨52075666106246264979872613194959125393591, 459878343785020423414659373084909344454886, 0, (-80), (-80)⟩], [], []⟩

theorem S104537C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B104537 S104537C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 104537.C1. -/

theorem S104537D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B104537 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S104537C1 ρ hρ

/-- 证书叶 104537.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S104537C2P : TMParams :=
  ⟨[], [], []⟩

theorem S104537C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B104537 S104537C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 104537.C2. -/

theorem S104537D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B104537 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S104537C2 ρ hρ

/-- 导数叶 104537（+∂x3f，then 支，全盒）. -/

def DP104537 : TMParams :=
  ⟨[⟨5618547401341487670351829963263678257102924, 5618547401341487670351829963263678257102924, 677330451502343891998378201989759716834952018158, (-80), (-80)⟩, ⟨5618547401341487670351829963263678257102924, 5618547401341487670351829963263678257102924, 677330451502343891998378201989759716834952018158, (-80), (-80)⟩, ⟨5618547401341487670351829963263678257102924, 5618547401341487670351829963263678257102924, 677330451502343891998378201989759716834952018158, (-80), (-80)⟩, ⟨5618547401341487670351829963263678257102924, 5618547401341487670351829963263678257102924, 677330451502343891998378201989759716834952018158, (-80), (-80)⟩, ⟨5618547401341487670351829963263678257102924, 5618547401341487670351829963263678257102924, 677330451502343891998378201989759716834952018158, (-80), (-80)⟩, ⟨5618547401341487670351829963263678257102924, 5618547401341487670351829963263678257102924, 677330451502343891998378201989759716834952018158, (-80), (-80)⟩, ⟨5618547401341487670351829963263678257102924, 5618547401341487670351829963263678257102924, 677330451502343891998378201989759716834952018158, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der104537 :
    checkPosTMHull (derivIExpr E549 2) B104537 DP104537
    = true := by
  decide

/-- 面叶 104537（lo 面）. -/

def FB104537 : Fin 6 → DInterval := faceBoxLo B104537 2

def PF104537 : TMParams :=
  ⟨[⟨58325221485731170675547768693724881445143, 440621949421897632275181473017847014590447, 0, (-80), (-80)⟩, ⟨5568296167003712419875972025308818504018762, 5568296167003712419875972025308818504018762, 682156602162422361615023939629448397099226159931, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face104537 :
    checkPosTMHull E549 FB104537 PF104537
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 104537，then 支）. -/

def DSafe104537 : DerivSafeOn B104537 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S104537D2) S104537D1) (Or.inr (Or.inr rfl))) S104537D0)))

/-- mono 折叠组合（叶 104537，两叶引用零重算）. -/

theorem Fold104537 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B104537 2 PF104537 DP104537 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B104537 DP104537 = true := Der104537
  have h2 : checkPosTMHull E549 (faceBoxLo B104537 2) PF104537 = true := Face104537
  show (checkPosTMHull (derivIExpr E549 2) B104537 DP104537
      && checkPosTMHull E549 (faceBoxLo B104537 2) PF104537) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 104537）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem104537 (ρ : Fin 6 → ℝ) (hρ : boxMem B104537 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe104537 Fold104537 hρ

#print axioms Sem104537

/-- 叶 109770（then 支，lo 面）原盒. -/

def B109770 : Fin 6 → DInterval :=
  ![⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩]

/-- 证书叶 109770.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S109770C0P : TMParams :=
  ⟨[⟨117467359324668899014353218450993499830124, 246266485306400317498076916618309612038524, 0, (-80), (-80)⟩], [], []⟩

theorem S109770C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B109770 S109770C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 109770.C0. -/

theorem S109770D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B109770 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S109770C0 ρ hρ

/-- 证书叶 109770.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S109770C1P : TMParams :=
  ⟨[⟨117467359324668899014353218450993499830124, 246266485306400317498076916618309612038524, 0, (-80), (-80)⟩], [], []⟩

theorem S109770C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B109770 S109770C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 109770.C1. -/

theorem S109770D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B109770 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S109770C1 ρ hρ

/-- 证书叶 109770.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S109770C2P : TMParams :=
  ⟨[], [], []⟩

theorem S109770C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B109770 S109770C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 109770.C2. -/

theorem S109770D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B109770 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S109770C2 ρ hρ

/-- 导数叶 109770（+∂x3f，then 支，全盒）. -/

def DP109770 : TMParams :=
  ⟨[⟨6076855079389122370901513060257851716519591, 6076855079389122370901513060257851716519591, 734907860142244340756006842876565151248624813722, (-80), (-80)⟩, ⟨6076855079389122370901513060257851716519591, 6076855079389122370901513060257851716519591, 734907860142244340756006842876565151248624813722, (-80), (-80)⟩, ⟨6076855079389122370901513060257851716519591, 6076855079389122370901513060257851716519591, 734907860142244340756006842876565151248624813722, (-80), (-80)⟩, ⟨6076855079389122370901513060257851716519591, 6076855079389122370901513060257851716519591, 734907860142244340756006842876565151248624813722, (-80), (-80)⟩, ⟨6076855079389122370901513060257851716519591, 6076855079389122370901513060257851716519591, 734907860142244340756006842876565151248624813722, (-80), (-80)⟩, ⟨6076855079389122370901513060257851716519591, 6076855079389122370901513060257851716519591, 734907860142244340756006842876565151248624813722, (-80), (-80)⟩, ⟨6076855079389122370901513060257851716519591, 6076855079389122370901513060257851716519591, 734907860142244340756006842876565151248624813722, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der109770 :
    checkPosTMHull (derivIExpr E549 2) B109770 DP109770
    = true := by
  decide

/-- 面叶 109770（lo 面）. -/

def FB109770 : Fin 6 → DInterval := faceBoxLo B109770 2

def PF109770 : TMParams :=
  ⟨[⟨65236374941915360622874725708582653323374, 236201020118916813250051198382860319522782, 0, (-80), (-80)⟩, ⟨6029348364250339538261000888815164942663117, 6029348364250339538261000888815164942663117, 739572413938225826013010056362102102920891245731, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face109770 :
    checkPosTMHull E549 FB109770 PF109770
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 109770，then 支）. -/

def DSafe109770 : DerivSafeOn B109770 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S109770D2) S109770D1) (Or.inr (Or.inr rfl))) S109770D0)))

/-- mono 折叠组合（叶 109770，两叶引用零重算）. -/

theorem Fold109770 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B109770 2 PF109770 DP109770 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B109770 DP109770 = true := Der109770
  have h2 : checkPosTMHull E549 (faceBoxLo B109770 2) PF109770 = true := Face109770
  show (checkPosTMHull (derivIExpr E549 2) B109770 DP109770
      && checkPosTMHull E549 (faceBoxLo B109770 2) PF109770) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 109770）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem109770 (ρ : Fin 6 → ℝ) (hρ : boxMem B109770 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe109770 Fold109770 hρ

#print axioms Sem109770

/-- 叶 114678（then 支，lo 面）原盒. -/

def B114678 : Fin 6 → DInterval :=
  ![⟨⟨34918084117, -34⟩, ⟨17738214933, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩]

/-- 证书叶 114678.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S114678C0P : TMParams :=
  ⟨[⟨900639255154994862271910195130254968738408, 442365461722861519169126489334292906553751, 0, (-80), (-80)⟩], [], []⟩

theorem S114678C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B114678 S114678C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 114678.C0. -/

theorem S114678D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B114678 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S114678C0 ρ hρ

/-- 证书叶 114678.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S114678C1P : TMParams :=
  ⟨[⟨900639255154994862271910195130254968738408, 442365461722861519169126489334292906553751, 0, (-80), (-80)⟩], [], []⟩

theorem S114678C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B114678 S114678C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 114678.C1. -/

theorem S114678D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B114678 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S114678C1 ρ hρ

/-- 证书叶 114678.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S114678C2P : TMParams :=
  ⟨[], [], []⟩

theorem S114678C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B114678 S114678C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 114678.C2. -/

theorem S114678D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B114678 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S114678C2 ρ hρ

/-- 导数叶 114678（+∂x3f，then 支，全盒）. -/

def DP114678 : TMParams :=
  ⟨[⟨44463489938188673081486281888160527573423453, 44463489938188673081486281888160527573423453, 10930694175804168067742808305477331907786818919145, (-80), (-80)⟩, ⟨44463489938188673081486281888160527573423453, 44463489938188673081486281888160527573423453, 10930694175804168067742808305477331907786818919145, (-80), (-80)⟩, ⟨44463489938188673081486281888160527573423453, 44463489938188673081486281888160527573423453, 10930694175804168067742808305477331907786818919145, (-80), (-80)⟩, ⟨44463489938188673081486281888160527573423453, 44463489938188673081486281888160527573423453, 10930694175804168067742808305477331907786818919145, (-80), (-80)⟩, ⟨44463489938188673081486281888160527573423453, 44463489938188673081486281888160527573423453, 10930694175804168067742808305477331907786818919145, (-80), (-80)⟩, ⟨44463489938188673081486281888160527573423453, 44463489938188673081486281888160527573423453, 10930694175804168067742808305477331907786818919145, (-80), (-80)⟩, ⟨44463489938188673081486281888160527573423453, 44463489938188673081486281888160527573423453, 10930694175804168067742808305477331907786818919145, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der114678 :
    checkPosTMHull (derivIExpr E549 2) B114678 DP114678
    = true := by
  decide

/-- 面叶 114678（lo 面）. -/

def FB114678 : Fin 6 → DInterval := faceBoxLo B114678 2

def PF114678 : TMParams :=
  ⟨[⟨997479068471828535367798649396601450512824, 424212192406848359720431269468970363620800, 0, (-80), (-80)⟩, ⟨44200154195167633968047784848763400436551354, 44200154195167633968047784848763400436551354, 10990837384541964344331522420595941440732088805825, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face114678 :
    checkPosTMHull E549 FB114678 PF114678
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 114678，then 支）. -/

def DSafe114678 : DerivSafeOn B114678 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S114678D2) S114678D1) (Or.inr (Or.inr rfl))) S114678D0)))

/-- mono 折叠组合（叶 114678，两叶引用零重算）. -/

theorem Fold114678 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B114678 2 PF114678 DP114678 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B114678 DP114678 = true := Der114678
  have h2 : checkPosTMHull E549 (faceBoxLo B114678 2) PF114678 = true := Face114678
  show (checkPosTMHull (derivIExpr E549 2) B114678 DP114678
      && checkPosTMHull E549 (faceBoxLo B114678 2) PF114678) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 114678）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem114678 (ρ : Fin 6 → ℝ) (hρ : boxMem B114678 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe114678 Fold114678 hρ

#print axioms Sem114678

/-- 叶 119068（then 支，lo 面）原盒. -/

def B119068 : Fin 6 → DInterval :=
  ![⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩]

/-- 证书叶 119068.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S119068C0P : TMParams :=
  ⟨[⟨24352933523797155388164830590141, 457545818779076679052139582429652135260154, 0, (-80), (-80)⟩], [], []⟩

theorem S119068C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B119068 S119068C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 119068.C0. -/

theorem S119068D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B119068 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S119068C0 ρ hρ

/-- 证书叶 119068.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S119068C1P : TMParams :=
  ⟨[⟨24352933523797155388164830590141, 457545818779076679052139582429652135260154, 0, (-80), (-80)⟩], [], []⟩

theorem S119068C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B119068 S119068C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 119068.C1. -/

theorem S119068D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B119068 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S119068C1 ρ hρ

/-- 证书叶 119068.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S119068C2P : TMParams :=
  ⟨[], [], []⟩

theorem S119068C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B119068 S119068C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 119068.C2. -/

theorem S119068D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B119068 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S119068C2 ρ hρ

/-- 导数叶 119068（+∂x3f，then 支，全盒）. -/

def DP119068 : TMParams :=
  ⟨[⟨5595632443134002303591285358575360243516580, 5595632443134002303591285358575360243516580, 674835579336072404493871627494908175890842735113, (-80), (-80)⟩, ⟨5595632443134002303591285358575360243516580, 5595632443134002303591285358575360243516580, 674835579336072404493871627494908175890842735113, (-80), (-80)⟩, ⟨5595632443134002303591285358575360243516580, 5595632443134002303591285358575360243516580, 674835579336072404493871627494908175890842735113, (-80), (-80)⟩, ⟨5595632443134002303591285358575360243516580, 5595632443134002303591285358575360243516580, 674835579336072404493871627494908175890842735113, (-80), (-80)⟩, ⟨5595632443134002303591285358575360243516580, 5595632443134002303591285358575360243516580, 674835579336072404493871627494908175890842735113, (-80), (-80)⟩, ⟨5595632443134002303591285358575360243516580, 5595632443134002303591285358575360243516580, 674835579336072404493871627494908175890842735113, (-80), (-80)⟩, ⟨5595632443134002303591285358575360243516580, 5595632443134002303591285358575360243516580, 674835579336072404493871627494908175890842735113, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der119068 :
    checkPosTMHull (derivIExpr E549 2) B119068 DP119068
    = true := by
  decide

/-- 面叶 119068（lo 面）. -/

def FB119068 : Fin 6 → DInterval := faceBoxLo B119068 2

def PF119068 : TMParams :=
  ⟨[⟨27592684226103591820649756465251, 439653944433782659839988228719205002496980, 0, (-80), (-80)⟩, ⟨5576441686092397699960825405107857568172568, 5576441686092397699960825405107857568172568, 679151685666692330016099835987680785483260855051, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face119068 :
    checkPosTMHull E549 FB119068 PF119068
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 119068，then 支）. -/

def DSafe119068 : DerivSafeOn B119068 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S119068D2) S119068D1) (Or.inr (Or.inr rfl))) S119068D0)))

/-- mono 折叠组合（叶 119068，两叶引用零重算）. -/

theorem Fold119068 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B119068 2 PF119068 DP119068 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B119068 DP119068 = true := Der119068
  have h2 : checkPosTMHull E549 (faceBoxLo B119068 2) PF119068 = true := Face119068
  show (checkPosTMHull (derivIExpr E549 2) B119068 DP119068
      && checkPosTMHull E549 (faceBoxLo B119068 2) PF119068) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 119068）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem119068 (ρ : Fin 6 → ℝ) (hρ : boxMem B119068 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe119068 Fold119068 hρ

#print axioms Sem119068

/-- 叶 138060（then 支，lo 面）原盒. -/

def B138060 : Fin 6 → DInterval :=
  ![⟨⟨34918084117, -34⟩, ⟨17738214933, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩]

/-- 证书叶 138060.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S138060C0P : TMParams :=
  ⟨[⟨933226811715114642141900266209239066461620, 916374214101908436119337987875697626168929, 0, (-80), (-80)⟩], [], []⟩

theorem S138060C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B138060 S138060C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 138060.C0. -/

theorem S138060D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B138060 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S138060C0 ρ hρ

/-- 证书叶 138060.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S138060C1P : TMParams :=
  ⟨[⟨933226811715114642141900266209239066461620, 916374214101908436119337987875697626168929, 0, (-80), (-80)⟩], [], []⟩

theorem S138060C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B138060 S138060C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 138060.C1. -/

theorem S138060D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B138060 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S138060C1 ρ hρ

/-- 证书叶 138060.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S138060C2P : TMParams :=
  ⟨[], [], []⟩

theorem S138060C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B138060 S138060C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 138060.C2. -/

theorem S138060D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B138060 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S138060C2 ρ hρ

/-- 导数叶 138060（+∂x3f，then 支，全盒）. -/

def DP138060 : TMParams :=
  ⟨[⟨46062429286300476683532440853591441976798134, 46062429286300476683532440853591441976798134, 11330556334200793334088957425187567462320337431143, (-80), (-80)⟩, ⟨46062429286300476683532440853591441976798134, 46062429286300476683532440853591441976798134, 11330556334200793334088957425187567462320337431143, (-80), (-80)⟩, ⟨46062429286300476683532440853591441976798134, 46062429286300476683532440853591441976798134, 11330556334200793334088957425187567462320337431143, (-80), (-80)⟩, ⟨46062429286300476683532440853591441976798134, 46062429286300476683532440853591441976798134, 11330556334200793334088957425187567462320337431143, (-80), (-80)⟩, ⟨46062429286300476683532440853591441976798134, 46062429286300476683532440853591441976798134, 11330556334200793334088957425187567462320337431143, (-80), (-80)⟩, ⟨46062429286300476683532440853591441976798134, 46062429286300476683532440853591441976798134, 11330556334200793334088957425187567462320337431143, (-80), (-80)⟩, ⟨46062429286300476683532440853591441976798134, 46062429286300476683532440853591441976798134, 11330556334200793334088957425187567462320337431143, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der138060 :
    checkPosTMHull (derivIExpr E549 2) B138060 DP138060
    = true := by
  decide

/-- 面叶 138060（lo 面）. -/

def FB138060 : Fin 6 → DInterval := faceBoxLo B138060 2

def PF138060 : TMParams :=
  ⟨[⟨1024192122240093891778163839371397785530432, 878380227262839406518958580017955363860933, 0, (-80), (-80)⟩, ⟨45665881995339578035139752857895776707467698, 45665881995339578035139752857895776707467698, 11393304049633638797604765094519281967317212584614, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face138060 :
    checkPosTMHull E549 FB138060 PF138060
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 138060，then 支）. -/

def DSafe138060 : DerivSafeOn B138060 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S138060D2) S138060D1) (Or.inr (Or.inr rfl))) S138060D0)))

/-- mono 折叠组合（叶 138060，两叶引用零重算）. -/

theorem Fold138060 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B138060 2 PF138060 DP138060 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B138060 DP138060 = true := Der138060
  have h2 : checkPosTMHull E549 (faceBoxLo B138060 2) PF138060 = true := Face138060
  show (checkPosTMHull (derivIExpr E549 2) B138060 DP138060
      && checkPosTMHull E549 (faceBoxLo B138060 2) PF138060) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 138060）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem138060 (ρ : Fin 6 → ℝ) (hρ : boxMem B138060 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe138060 Fold138060 hρ

#print axioms Sem138060

/-- 叶 142271（then 支，lo 面）原盒. -/

def B142271 : Fin 6 → DInterval :=
  ![⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩]

/-- 证书叶 142271.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S142271C0P : TMParams :=
  ⟨[⟨207993357635218931009747036342106343890971, 229557088082616190424317777525124228953460, 0, (-80), (-80)⟩], [], []⟩

theorem S142271C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B142271 S142271C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 142271.C0. -/

theorem S142271D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B142271 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S142271C0 ρ hρ

/-- 证书叶 142271.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S142271C1P : TMParams :=
  ⟨[⟨207993357635218931009747036342106343890971, 229557088082616190424317777525124228953460, 0, (-80), (-80)⟩], [], []⟩

theorem S142271C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B142271 S142271C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 142271.C1. -/

theorem S142271D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B142271 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S142271C1 ρ hρ

/-- 证书叶 142271.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S142271C2P : TMParams :=
  ⟨[], [], []⟩

theorem S142271C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B142271 S142271C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 142271.C2. -/

theorem S142271D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B142271 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S142271C2 ρ hρ

/-- 导数叶 142271（+∂x3f，then 支，全盒）. -/

def DP142271 : TMParams :=
  ⟨[⟨5606620312009530315517960148686802116542875, 5606620312009530315517960148686802116542875, 676069945666713222791233018872958652627748073030, (-80), (-80)⟩, ⟨5606620312009530315517960148686802116542875, 5606620312009530315517960148686802116542875, 676069945666713222791233018872958652627748073030, (-80), (-80)⟩, ⟨5606620312009530315517960148686802116542875, 5606620312009530315517960148686802116542875, 676069945666713222791233018872958652627748073030, (-80), (-80)⟩, ⟨5606620312009530315517960148686802116542875, 5606620312009530315517960148686802116542875, 676069945666713222791233018872958652627748073030, (-80), (-80)⟩, ⟨5606620312009530315517960148686802116542875, 5606620312009530315517960148686802116542875, 676069945666713222791233018872958652627748073030, (-80), (-80)⟩, ⟨5606620312009530315517960148686802116542875, 5606620312009530315517960148686802116542875, 676069945666713222791233018872958652627748073030, (-80), (-80)⟩, ⟨5606620312009530315517960148686802116542875, 5606620312009530315517960148686802116542875, 676069945666713222791233018872958652627748073030, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der142271 :
    checkPosTMHull (derivIExpr E549 2) B142271 DP142271
    = true := by
  decide

/-- 面叶 142271（lo 面）. -/

def FB142271 : Fin 6 → DInterval := faceBoxLo B142271 2

def PF142271 : TMParams :=
  ⟨[⟨233068449550959305299753629422594326747738, 219819627696075234367635938513221106555987, 0, (-80), (-80)⟩, ⟨5554099758715560029017338742423066184671566, 5554099758715560029017338742423066184671566, 680739502803173387697604242419059951864654733778, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face142271 :
    checkPosTMHull E549 FB142271 PF142271
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 142271，then 支）. -/

def DSafe142271 : DerivSafeOn B142271 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S142271D2) S142271D1) (Or.inr (Or.inr rfl))) S142271D0)))

/-- mono 折叠组合（叶 142271，两叶引用零重算）. -/

theorem Fold142271 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B142271 2 PF142271 DP142271 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B142271 DP142271 = true := Der142271
  have h2 : checkPosTMHull E549 (faceBoxLo B142271 2) PF142271 = true := Face142271
  show (checkPosTMHull (derivIExpr E549 2) B142271 DP142271
      && checkPosTMHull E549 (faceBoxLo B142271 2) PF142271) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 142271）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem142271 (ρ : Fin 6 → ℝ) (hρ : boxMem B142271 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe142271 Fold142271 hρ

#print axioms Sem142271

/-- 叶 152420（then 支，lo 面）原盒. -/

def B152420 : Fin 6 → DInterval :=
  ![⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩]

/-- 证书叶 152420.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S152420C0P : TMParams :=
  ⟨[⟨11567532921101834807737169032224, 427602286078823414442974031110607984221204, 0, (-80), (-80)⟩], [], []⟩

theorem S152420C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B152420 S152420C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 152420.C0. -/

theorem S152420D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B152420 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S152420C0 ρ hρ

/-- 证书叶 152420.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S152420C1P : TMParams :=
  ⟨[⟨11567532921101834807737169032224, 427602286078823414442974031110607984221204, 0, (-80), (-80)⟩], [], []⟩

theorem S152420C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B152420 S152420C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 152420.C1. -/

theorem S152420D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B152420 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S152420C1 ρ hρ

/-- 证书叶 152420.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S152420C2P : TMParams :=
  ⟨[], [], []⟩

theorem S152420C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B152420 S152420C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 152420.C2. -/

theorem S152420D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B152420 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S152420C2 ρ hρ

/-- 导数叶 152420（+∂x3f，then 支，全盒）. -/

def DP152420 : TMParams :=
  ⟨[⟨5244642543852940023670678814542834678761457, 5244642543852940023670678814542834678761457, 631910517716747395296335053340953266753722906388, (-80), (-80)⟩, ⟨5244642543852940023670678814542834678761457, 5244642543852940023670678814542834678761457, 631910517716747395296335053340953266753722906388, (-80), (-80)⟩, ⟨5244642543852940023670678814542834678761457, 5244642543852940023670678814542834678761457, 631910517716747395296335053340953266753722906388, (-80), (-80)⟩, ⟨5244642543852940023670678814542834678761457, 5244642543852940023670678814542834678761457, 631910517716747395296335053340953266753722906388, (-80), (-80)⟩, ⟨5244642543852940023670678814542834678761457, 5244642543852940023670678814542834678761457, 631910517716747395296335053340953266753722906388, (-80), (-80)⟩, ⟨5244642543852940023670678814542834678761457, 5244642543852940023670678814542834678761457, 631910517716747395296335053340953266753722906388, (-80), (-80)⟩, ⟨5244642543852940023670678814542834678761457, 5244642543852940023670678814542834678761457, 631910517716747395296335053340953266753722906388, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der152420 :
    checkPosTMHull (derivIExpr E549 2) B152420 DP152420
    = true := by
  decide

/-- 面叶 152420（lo 面）. -/

def FB152420 : Fin 6 → DInterval := faceBoxLo B152420 2

def PF152420 : TMParams :=
  ⟨[⟨12883882031147749656786525378231, 410095815151551727620299756628974212937463, 0, (-80), (-80)⟩, ⟨5201976834191311091269306716230327439852975, 5201976834191311091269306716230327439852975, 636255100924255599450911219269598043137199007119, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face152420 :
    checkPosTMHull E549 FB152420 PF152420
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 152420，then 支）. -/

def DSafe152420 : DerivSafeOn B152420 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S152420D2) S152420D1) (Or.inr (Or.inr rfl))) S152420D0)))

/-- mono 折叠组合（叶 152420，两叶引用零重算）. -/

theorem Fold152420 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B152420 2 PF152420 DP152420 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B152420 DP152420 = true := Der152420
  have h2 : checkPosTMHull E549 (faceBoxLo B152420 2) PF152420 = true := Face152420
  show (checkPosTMHull (derivIExpr E549 2) B152420 DP152420
      && checkPosTMHull E549 (faceBoxLo B152420 2) PF152420) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 152420）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem152420 (ρ : Fin 6 → ℝ) (hρ : boxMem B152420 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe152420 Fold152420 hρ

#print axioms Sem152420

/-- 叶 157588（then 支，lo 面）原盒. -/

def B157588 : Fin 6 → DInterval :=
  ![⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩]

/-- 证书叶 157588.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S157588C0P : TMParams :=
  ⟨[⟨254748884132870415497028963251984055153447, 133001274853355942542090671581501213667735, 0, (-80), (-80)⟩], [], []⟩

theorem S157588C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B157588 S157588C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 157588.C0. -/

theorem S157588D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B157588 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S157588C0 ρ hρ

/-- 证书叶 157588.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S157588C1P : TMParams :=
  ⟨[⟨254748884132870415497028963251984055153447, 133001274853355942542090671581501213667735, 0, (-80), (-80)⟩], [], []⟩

theorem S157588C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B157588 S157588C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 157588.C1. -/

theorem S157588D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B157588 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S157588C1 ρ hρ

/-- 证书叶 157588.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S157588C2P : TMParams :=
  ⟨[], [], []⟩

theorem S157588C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B157588 S157588C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 157588.C2. -/

theorem S157588D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B157588 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S157588C2 ρ hρ

/-- 导数叶 157588（+∂x3f，then 支，全盒）. -/

def DP157588 : TMParams :=
  ⟨[⟨6571666841664410911384587931464209307625921, 6571666841664410911384587931464209307625921, 796093440446555836210211286420415511135836614069, (-80), (-80)⟩, ⟨6571666841664410911384587931464209307625921, 6571666841664410911384587931464209307625921, 796093440446555836210211286420415511135836614069, (-80), (-80)⟩, ⟨6571666841664410911384587931464209307625921, 6571666841664410911384587931464209307625921, 796093440446555836210211286420415511135836614069, (-80), (-80)⟩, ⟨6571666841664410911384587931464209307625921, 6571666841664410911384587931464209307625921, 796093440446555836210211286420415511135836614069, (-80), (-80)⟩, ⟨6571666841664410911384587931464209307625921, 6571666841664410911384587931464209307625921, 796093440446555836210211286420415511135836614069, (-80), (-80)⟩, ⟨6571666841664410911384587931464209307625921, 6571666841664410911384587931464209307625921, 796093440446555836210211286420415511135836614069, (-80), (-80)⟩, ⟨6571666841664410911384587931464209307625921, 6571666841664410911384587931464209307625921, 796093440446555836210211286420415511135836614069, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der157588 :
    checkPosTMHull (derivIExpr E549 2) B157588 DP157588
    = true := by
  decide

/-- 面叶 157588（lo 面）. -/

def FB157588 : Fin 6 → DInterval := faceBoxLo B157588 2

def PF157588 : TMParams :=
  ⟨[⟨284054342448652579889995687115338541715815, 127694652137650691414312351574116546609514, 0, (-80), (-80)⟩, ⟨6532596536970938687540816102680622292202919, 6532596536970938687540816102680622292202919, 800906740739707536126725705212720095208331152654, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face157588 :
    checkPosTMHull E549 FB157588 PF157588
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 157588，then 支）. -/

def DSafe157588 : DerivSafeOn B157588 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S157588D2) S157588D1) (Or.inr (Or.inr rfl))) S157588D0)))

/-- mono 折叠组合（叶 157588，两叶引用零重算）. -/

theorem Fold157588 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B157588 2 PF157588 DP157588 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B157588 DP157588 = true := Der157588
  have h2 : checkPosTMHull E549 (faceBoxLo B157588 2) PF157588 = true := Face157588
  show (checkPosTMHull (derivIExpr E549 2) B157588 DP157588
      && checkPosTMHull E549 (faceBoxLo B157588 2) PF157588) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 157588）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem157588 (ρ : Fin 6 → ℝ) (hρ : boxMem B157588 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe157588 Fold157588 hρ

#print axioms Sem157588

/-- 叶 161851（then 支，lo 面）原盒. -/

def B161851 : Fin 6 → DInterval :=
  ![⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩]

/-- 证书叶 161851.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S161851C0P : TMParams :=
  ⟨[⟨245252234062833528765322399162262486731184, 133028595574249131859839001062278337575307, 0, (-80), (-80)⟩], [], []⟩

theorem S161851C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B161851 S161851C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 161851.C0. -/

theorem S161851D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B161851 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S161851C0 ρ hρ

/-- 证书叶 161851.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S161851C1P : TMParams :=
  ⟨[⟨245252234062833528765322399162262486731184, 133028595574249131859839001062278337575307, 0, (-80), (-80)⟩], [], []⟩

theorem S161851C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B161851 S161851C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 161851.C1. -/

theorem S161851D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B161851 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S161851C1 ρ hρ

/-- 证书叶 161851.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S161851C2P : TMParams :=
  ⟨[], [], []⟩

theorem S161851C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B161851 S161851C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 161851.C2. -/

theorem S161851D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B161851 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S161851C2 ρ hρ

/-- 导数叶 161851（+∂x3f，then 支，全盒）. -/

def DP161851 : TMParams :=
  ⟨[⟨6523639157438558728686054087614773258099930, 6523639157438558728686054087614773258099930, 789395553556953157644197525382037641244873654817, (-80), (-80)⟩, ⟨6523639157438558728686054087614773258099930, 6523639157438558728686054087614773258099930, 789395553556953157644197525382037641244873654817, (-80), (-80)⟩, ⟨6523639157438558728686054087614773258099930, 6523639157438558728686054087614773258099930, 789395553556953157644197525382037641244873654817, (-80), (-80)⟩, ⟨6523639157438558728686054087614773258099930, 6523639157438558728686054087614773258099930, 789395553556953157644197525382037641244873654817, (-80), (-80)⟩, ⟨6523639157438558728686054087614773258099930, 6523639157438558728686054087614773258099930, 789395553556953157644197525382037641244873654817, (-80), (-80)⟩, ⟨6523639157438558728686054087614773258099930, 6523639157438558728686054087614773258099930, 789395553556953157644197525382037641244873654817, (-80), (-80)⟩, ⟨6523639157438558728686054087614773258099930, 6523639157438558728686054087614773258099930, 789395553556953157644197525382037641244873654817, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der161851 :
    checkPosTMHull (derivIExpr E549 2) B161851 DP161851
    = true := by
  decide

/-- 面叶 161851（lo 面）. -/

def FB161851 : Fin 6 → DInterval := faceBoxLo B161851 2

def PF161851 : TMParams :=
  ⟨[⟨275855526866651310240213129197240642171259, 127914832567595369475527064685303441650831, 0, (-80), (-80)⟩, ⟨6495942292731327913300891651719267708595679, 6495942292731327913300891651719267708595679, 794356427518695793736924734645827286045632441836, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face161851 :
    checkPosTMHull E549 FB161851 PF161851
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 161851，then 支）. -/

def DSafe161851 : DerivSafeOn B161851 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S161851D2) S161851D1) (Or.inr (Or.inr rfl))) S161851D0)))

/-- mono 折叠组合（叶 161851，两叶引用零重算）. -/

theorem Fold161851 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B161851 2 PF161851 DP161851 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B161851 DP161851 = true := Der161851
  have h2 : checkPosTMHull E549 (faceBoxLo B161851 2) PF161851 = true := Face161851
  show (checkPosTMHull (derivIExpr E549 2) B161851 DP161851
      && checkPosTMHull E549 (faceBoxLo B161851 2) PF161851) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 161851）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem161851 (ρ : Fin 6 → ℝ) (hρ : boxMem B161851 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe161851 Fold161851 hρ

#print axioms Sem161851

/-- 叶 166654（then 支，lo 面）原盒. -/

def B166654 : Fin 6 → DInterval :=
  ![⟨⟨34918084117, -34⟩, ⟨17738214933, -33⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩]

/-- 证书叶 166654.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S166654C0P : TMParams :=
  ⟨[⟨815892625648016168653903310319507018183073, 839390824472149305275399340798558086881497, 0, (-80), (-80)⟩], [], []⟩

theorem S166654C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B166654 S166654C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 166654.C0. -/

theorem S166654D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B166654 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S166654C0 ρ hρ

/-- 证书叶 166654.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S166654C1P : TMParams :=
  ⟨[⟨815892625648016168653903310319507018183073, 839390824472149305275399340798558086881497, 0, (-80), (-80)⟩], [], []⟩

theorem S166654C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B166654 S166654C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 166654.C1. -/

theorem S166654D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B166654 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S166654C1 ρ hρ

/-- 证书叶 166654.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S166654C2P : TMParams :=
  ⟨[], [], []⟩

theorem S166654C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B166654 S166654C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 166654.C2. -/

theorem S166654D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B166654 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S166654C2 ρ hρ

/-- 导数叶 166654（+∂x3f，then 支，全盒）. -/

def DP166654 : TMParams :=
  ⟨[⟨41772244826457247820041921437899716658032746, 41772244826457247820041921437899716658032746, 10247220490640439536919644956941722691494583851760, (-80), (-80)⟩, ⟨41772244826457247820041921437899716658032746, 41772244826457247820041921437899716658032746, 10247220490640439536919644956941722691494583851760, (-80), (-80)⟩, ⟨41772244826457247820041921437899716658032746, 41772244826457247820041921437899716658032746, 10247220490640439536919644956941722691494583851760, (-80), (-80)⟩, ⟨41772244826457247820041921437899716658032746, 41772244826457247820041921437899716658032746, 10247220490640439536919644956941722691494583851760, (-80), (-80)⟩, ⟨41772244826457247820041921437899716658032746, 41772244826457247820041921437899716658032746, 10247220490640439536919644956941722691494583851760, (-80), (-80)⟩, ⟨41772244826457247820041921437899716658032746, 41772244826457247820041921437899716658032746, 10247220490640439536919644956941722691494583851760, (-80), (-80)⟩, ⟨41772244826457247820041921437899716658032746, 41772244826457247820041921437899716658032746, 10247220490640439536919644956941722691494583851760, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der166654 :
    checkPosTMHull (derivIExpr E549 2) B166654 DP166654
    = true := by
  decide

/-- 面叶 166654（lo 面）. -/

def FB166654 : Fin 6 → DInterval := faceBoxLo B166654 2

def PF166654 : TMParams :=
  ⟨[⟨916972703402802686969904392497476439527589, 805781063619766829075475580799289610367732, 0, (-80), (-80)⟩, ⟨41625182689719473564674025212010481888076235, 41625182689719473564674025212010481888076235, 10306372998376201097709540475844842295116134964551, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face166654 :
    checkPosTMHull E549 FB166654 PF166654
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 166654，then 支）. -/

def DSafe166654 : DerivSafeOn B166654 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S166654D2) S166654D1) (Or.inr (Or.inr rfl))) S166654D0)))

/-- mono 折叠组合（叶 166654，两叶引用零重算）. -/

theorem Fold166654 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B166654 2 PF166654 DP166654 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B166654 DP166654 = true := Der166654
  have h2 : checkPosTMHull E549 (faceBoxLo B166654 2) PF166654 = true := Face166654
  show (checkPosTMHull (derivIExpr E549 2) B166654 DP166654
      && checkPosTMHull E549 (faceBoxLo B166654 2) PF166654) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 166654）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem166654 (ρ : Fin 6 → ℝ) (hρ : boxMem B166654 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe166654 Fold166654 hρ

#print axioms Sem166654

/-- 叶 170797（then 支，lo 面）原盒. -/

def B170797 : Fin 6 → DInterval :=
  ![⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩]

/-- 证书叶 170797.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S170797C0P : TMParams :=
  ⟨[⟨191997335851354518673191903038569068004566, 213071875260640715533657182880519997964581, 0, (-80), (-80)⟩], [], []⟩

theorem S170797C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B170797 S170797C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 170797.C0. -/

theorem S170797D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B170797 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S170797C0 ρ hρ

/-- 证书叶 170797.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S170797C1P : TMParams :=
  ⟨[⟨191997335851354518673191903038569068004566, 213071875260640715533657182880519997964581, 0, (-80), (-80)⟩], [], []⟩

theorem S170797C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B170797 S170797C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 170797.C1. -/

theorem S170797D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B170797 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S170797C1 ρ hρ

/-- 证书叶 170797.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S170797C2P : TMParams :=
  ⟨[], [], []⟩

theorem S170797C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B170797 S170797C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 170797.C2. -/

theorem S170797D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B170797 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S170797C2 ρ hρ

/-- 导数叶 170797（+∂x3f，then 支，全盒）. -/

def DP170797 : TMParams :=
  ⟨[⟨5197455979762022091108060700596974524528038, 5197455979762022091108060700596974524528038, 625582900688215632811677704259857685132060673616, (-80), (-80)⟩, ⟨5197455979762022091108060700596974524528038, 5197455979762022091108060700596974524528038, 625582900688215632811677704259857685132060673616, (-80), (-80)⟩, ⟨5197455979762022091108060700596974524528038, 5197455979762022091108060700596974524528038, 625582900688215632811677704259857685132060673616, (-80), (-80)⟩, ⟨5197455979762022091108060700596974524528038, 5197455979762022091108060700596974524528038, 625582900688215632811677704259857685132060673616, (-80), (-80)⟩, ⟨5197455979762022091108060700596974524528038, 5197455979762022091108060700596974524528038, 625582900688215632811677704259857685132060673616, (-80), (-80)⟩, ⟨5197455979762022091108060700596974524528038, 5197455979762022091108060700596974524528038, 625582900688215632811677704259857685132060673616, (-80), (-80)⟩, ⟨5197455979762022091108060700596974524528038, 5197455979762022091108060700596974524528038, 625582900688215632811677704259857685132060673616, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der170797 :
    checkPosTMHull (derivIExpr E549 2) B170797 DP170797
    = true := by
  decide

/-- 面叶 170797（lo 面）. -/

def FB170797 : Fin 6 → DInterval := faceBoxLo B170797 2

def PF170797 : TMParams :=
  ⟨[⟨217758812210329280108402839156801775700947, 204303907620466556750551367247208552036136, 0, (-80), (-80)⟩, ⟨5167796454761097360572329061404691430422894, 5167796454761097360572329061404691430422894, 629895831313814185385374981816054701863501545294, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face170797 :
    checkPosTMHull E549 FB170797 PF170797
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 170797，then 支）. -/

def DSafe170797 : DerivSafeOn B170797 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S170797D2) S170797D1) (Or.inr (Or.inr rfl))) S170797D0)))

/-- mono 折叠组合（叶 170797，两叶引用零重算）. -/

theorem Fold170797 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B170797 2 PF170797 DP170797 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B170797 DP170797 = true := Der170797
  have h2 : checkPosTMHull E549 (faceBoxLo B170797 2) PF170797 = true := Face170797
  show (checkPosTMHull (derivIExpr E549 2) B170797 DP170797
      && checkPosTMHull E549 (faceBoxLo B170797 2) PF170797) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 170797）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem170797 (ρ : Fin 6 → ℝ) (hρ : boxMem B170797 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe170797 Fold170797 hρ

#print axioms Sem170797

/-- 叶 181671（then 支，lo 面）原盒. -/

def B181671 : Fin 6 → DInterval :=
  ![⟨⟨9148280341, -32⟩, ⟨37151467113, -34⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩]

/-- 证书叶 181671.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S181671C0P : TMParams :=
  ⟨[⟨122172086715053697129568395371625192263056, 1894553173842638734517347433350893114891340, 0, (-80), (-80)⟩], [], []⟩

theorem S181671C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B181671 S181671C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 181671.C0. -/

theorem S181671D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B181671 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S181671C0 ρ hρ

/-- 证书叶 181671.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S181671C1P : TMParams :=
  ⟨[⟨122172086715053697129568395371625192263056, 1894553173842638734517347433350893114891340, 0, (-80), (-80)⟩], [], []⟩

theorem S181671C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B181671 S181671C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 181671.C1. -/

theorem S181671D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B181671 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S181671C1 ρ hρ

/-- 证书叶 181671.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S181671C2P : TMParams :=
  ⟨[], [], []⟩

theorem S181671C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B181671 S181671C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 181671.C2. -/

theorem S181671D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B181671 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S181671C2 ρ hρ

/-- 导数叶 181671（+∂x3f，then 支，全盒）. -/

def DP181671 : TMParams :=
  ⟨[⟨47758191486870222916495245869896786031750506, 47758191486870222916495245869896786031750506, 11750157272884116512850775904658295991967511025038, (-80), (-80)⟩, ⟨47758191486870222916495245869896786031750506, 47758191486870222916495245869896786031750506, 11750157272884116512850775904658295991967511025038, (-80), (-80)⟩, ⟨47758191486870222916495245869896786031750506, 47758191486870222916495245869896786031750506, 11750157272884116512850775904658295991967511025038, (-80), (-80)⟩, ⟨47758191486870222916495245869896786031750506, 47758191486870222916495245869896786031750506, 11750157272884116512850775904658295991967511025038, (-80), (-80)⟩, ⟨47758191486870222916495245869896786031750506, 47758191486870222916495245869896786031750506, 11750157272884116512850775904658295991967511025038, (-80), (-80)⟩, ⟨47758191486870222916495245869896786031750506, 47758191486870222916495245869896786031750506, 11750157272884116512850775904658295991967511025038, (-80), (-80)⟩, ⟨47758191486870222916495245869896786031750506, 47758191486870222916495245869896786031750506, 11750157272884116512850775904658295991967511025038, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der181671 :
    checkPosTMHull (derivIExpr E549 2) B181671 DP181671
    = true := by
  decide

/-- 面叶 181671（lo 面）. -/

def FB181671 : Fin 6 → DInterval := faceBoxLo B181671 2

def PF181671 : TMParams :=
  ⟨[⟨133428348816687282591253719270762181489398, 1817429321108231614109347491661813348319142, 0, (-80), (-80)⟩, ⟨47344821921091822689477792907630331642145051, 47344821921091822689477792907630331642145051, 11814463741917203344435294968156962020814533232043, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face181671 :
    checkPosTMHull E549 FB181671 PF181671
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 181671，then 支）. -/

def DSafe181671 : DerivSafeOn B181671 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S181671D2) S181671D1) (Or.inr (Or.inr rfl))) S181671D0)))

/-- mono 折叠组合（叶 181671，两叶引用零重算）. -/

theorem Fold181671 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B181671 2 PF181671 DP181671 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B181671 DP181671 = true := Der181671
  have h2 : checkPosTMHull E549 (faceBoxLo B181671 2) PF181671 = true := Face181671
  show (checkPosTMHull (derivIExpr E549 2) B181671 DP181671
      && checkPosTMHull E549 (faceBoxLo B181671 2) PF181671) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 181671）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem181671 (ρ : Fin 6 → ℝ) (hρ : boxMem B181671 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe181671 Fold181671 hρ

#print axioms Sem181671

/-- 叶 185854（then 支，lo 面）原盒. -/

def B185854 : Fin 6 → DInterval :=
  ![⟨⟨37151467113, -34⟩, ⟨18854906431, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩]

/-- 证书叶 185854.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S185854C0P : TMParams :=
  ⟨[⟨472542027676553842097872460139556200772513, 928220812709513086213870893789368325274740, 0, (-80), (-80)⟩], [], []⟩

theorem S185854C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B185854 S185854C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 185854.C0. -/

theorem S185854D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B185854 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S185854C0 ρ hρ

/-- 证书叶 185854.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S185854C1P : TMParams :=
  ⟨[⟨472542027676553842097872460139556200772513, 928220812709513086213870893789368325274740, 0, (-80), (-80)⟩], [], []⟩

theorem S185854C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B185854 S185854C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 185854.C1. -/

theorem S185854D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B185854 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S185854C1 ρ hρ

/-- 证书叶 185854.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S185854C2P : TMParams :=
  ⟨[], [], []⟩

theorem S185854C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B185854 S185854C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 185854.C2. -/

theorem S185854D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B185854 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S185854C2 ρ hρ

/-- 导数叶 185854（+∂x3f，then 支，全盒）. -/

def DP185854 : TMParams :=
  ⟨[⟨46660526221214233488047747875979953934632772, 46660526221214233488047747875979953934632772, 11464862198247325112439049554591101740872025460580, (-80), (-80)⟩, ⟨46660526221214233488047747875979953934632772, 46660526221214233488047747875979953934632772, 11464862198247325112439049554591101740872025460580, (-80), (-80)⟩, ⟨46660526221214233488047747875979953934632772, 46660526221214233488047747875979953934632772, 11464862198247325112439049554591101740872025460580, (-80), (-80)⟩, ⟨46660526221214233488047747875979953934632772, 46660526221214233488047747875979953934632772, 11464862198247325112439049554591101740872025460580, (-80), (-80)⟩, ⟨46660526221214233488047747875979953934632772, 46660526221214233488047747875979953934632772, 11464862198247325112439049554591101740872025460580, (-80), (-80)⟩, ⟨46660526221214233488047747875979953934632772, 46660526221214233488047747875979953934632772, 11464862198247325112439049554591101740872025460580, (-80), (-80)⟩, ⟨46660526221214233488047747875979953934632772, 46660526221214233488047747875979953934632772, 11464862198247325112439049554591101740872025460580, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der185854 :
    checkPosTMHull (derivIExpr E549 2) B185854 DP185854
    = true := by
  decide

/-- 面叶 185854（lo 面）. -/

def FB185854 : Fin 6 → DInterval := faceBoxLo B185854 2

def PF185854 : TMParams :=
  ⟨[⟨517482390196476168959343883518806569423694, 888036738878104885867843095735802306888455, 0, (-80), (-80)⟩, ⟨46158769180212736261481102416355569206433637, 46158769180212736261481102416355569206433637, 11529598416539256443765287753567761782359151352532, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face185854 :
    checkPosTMHull E549 FB185854 PF185854
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 185854，then 支）. -/

def DSafe185854 : DerivSafeOn B185854 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S185854D2) S185854D1) (Or.inr (Or.inr rfl))) S185854D0)))

/-- mono 折叠组合（叶 185854，两叶引用零重算）. -/

theorem Fold185854 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B185854 2 PF185854 DP185854 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B185854 DP185854 = true := Der185854
  have h2 : checkPosTMHull E549 (faceBoxLo B185854 2) PF185854 = true := Face185854
  show (checkPosTMHull (derivIExpr E549 2) B185854 DP185854
      && checkPosTMHull E549 (faceBoxLo B185854 2) PF185854) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 185854）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem185854 (ρ : Fin 6 → ℝ) (hρ : boxMem B185854 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe185854 Fold185854 hρ

#print axioms Sem185854

/-- 叶 189997（then 支，lo 面）原盒. -/

def B189997 : Fin 6 → DInterval :=
  ![⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩, ⟨⟨19971597929, -33⟩, ⟨10264971839, -32⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩]

/-- 证书叶 189997.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S189997C0P : TMParams :=
  ⟨[⟨233058717561165339903610686618819851059424, 62231014927981751450375848106653489482268, 0, (-80), (-80)⟩], [], []⟩

theorem S189997C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B189997 S189997C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 189997.C0. -/

theorem S189997D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B189997 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S189997C0 ρ hρ

/-- 证书叶 189997.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S189997C1P : TMParams :=
  ⟨[⟨233058717561165339903610686618819851059424, 62231014927981751450375848106653489482268, 0, (-80), (-80)⟩], [], []⟩

theorem S189997C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B189997 S189997C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 189997.C1. -/

theorem S189997D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B189997 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S189997C1 ρ hρ

/-- 证书叶 189997.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S189997C2P : TMParams :=
  ⟨[], [], []⟩

theorem S189997C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B189997 S189997C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 189997.C2. -/

theorem S189997D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B189997 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S189997C2 ρ hρ

/-- 导数叶 189997（+∂x3f，then 支，全盒）. -/

def DP189997 : TMParams :=
  ⟨[⟨6121067664391270867075366988893099825735007, 6121067664391270867075366988893099825735007, 739980791784877880017661539717472794434584681003, (-80), (-80)⟩, ⟨6121067664391270867075366988893099825735007, 6121067664391270867075366988893099825735007, 739980791784877880017661539717472794434584681003, (-80), (-80)⟩, ⟨6121067664391270867075366988893099825735007, 6121067664391270867075366988893099825735007, 739980791784877880017661539717472794434584681003, (-80), (-80)⟩, ⟨6121067664391270867075366988893099825735007, 6121067664391270867075366988893099825735007, 739980791784877880017661539717472794434584681003, (-80), (-80)⟩, ⟨6121067664391270867075366988893099825735007, 6121067664391270867075366988893099825735007, 739980791784877880017661539717472794434584681003, (-80), (-80)⟩, ⟨6121067664391270867075366988893099825735007, 6121067664391270867075366988893099825735007, 739980791784877880017661539717472794434584681003, (-80), (-80)⟩, ⟨6121067664391270867075366988893099825735007, 6121067664391270867075366988893099825735007, 739980791784877880017661539717472794434584681003, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der189997 :
    checkPosTMHull (derivIExpr E549 2) B189997 DP189997
    = true := by
  decide

/-- 面叶 189997（lo 面）. -/

def FB189997 : Fin 6 → DInterval := faceBoxLo B189997 2

def PF189997 : TMParams :=
  ⟨[⟨257760033122661641606679951414593026354670, 119515232348803089867053470112261382438258, 0, (-80), (-80)⟩, ⟨6068718144703067394946384586499432174340751, 6068718144703067394946384586499432174340751, 744892439481665323444481276317520947091802858698, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face189997 :
    checkPosTMHull E549 FB189997 PF189997
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 189997，then 支）. -/

def DSafe189997 : DerivSafeOn B189997 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S189997D2) S189997D1) (Or.inr (Or.inr rfl))) S189997D0)))

/-- mono 折叠组合（叶 189997，两叶引用零重算）. -/

theorem Fold189997 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B189997 2 PF189997 DP189997 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B189997 DP189997 = true := Der189997
  have h2 : checkPosTMHull E549 (faceBoxLo B189997 2) PF189997 = true := Face189997
  show (checkPosTMHull (derivIExpr E549 2) B189997 DP189997
      && checkPosTMHull E549 (faceBoxLo B189997 2) PF189997) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 189997）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem189997 (ρ : Fin 6 → ℝ) (hρ : boxMem B189997 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe189997 Fold189997 hρ

#print axioms Sem189997

/-- 叶 194140（then 支，lo 面）原盒. -/

def B194140 : Fin 6 → DInterval :=
  ![⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩]

/-- 证书叶 194140.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S194140C0P : TMParams :=
  ⟨[⟨203040356233097603575749769423474509681409, 111846985918741808923685062818909131797793, 0, (-80), (-80)⟩], [], []⟩

theorem S194140C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B194140 S194140C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 194140.C0. -/

theorem S194140D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B194140 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S194140C0 ρ hρ

/-- 证书叶 194140.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S194140C1P : TMParams :=
  ⟨[⟨203040356233097603575749769423474509681409, 111846985918741808923685062818909131797793, 0, (-80), (-80)⟩], [], []⟩

theorem S194140C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B194140 S194140C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 194140.C1. -/

theorem S194140D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B194140 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S194140C1 ρ hρ

/-- 证书叶 194140.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S194140C2P : TMParams :=
  ⟨[], [], []⟩

theorem S194140C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B194140 S194140C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 194140.C2. -/

theorem S194140D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B194140 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S194140C2 ρ hρ

/-- 导数叶 194140（+∂x3f，then 支，全盒）. -/

def DP194140 : TMParams :=
  ⟨[⟨5466517076553534602787223582439240243461966, 5466517076553534602787223582439240243461966, 658699789102329845826360815322683450295410367743, (-80), (-80)⟩, ⟨5466517076553534602787223582439240243461966, 5466517076553534602787223582439240243461966, 658699789102329845826360815322683450295410367743, (-80), (-80)⟩, ⟨5466517076553534602787223582439240243461966, 5466517076553534602787223582439240243461966, 658699789102329845826360815322683450295410367743, (-80), (-80)⟩, ⟨5466517076553534602787223582439240243461966, 5466517076553534602787223582439240243461966, 658699789102329845826360815322683450295410367743, (-80), (-80)⟩, ⟨5466517076553534602787223582439240243461966, 5466517076553534602787223582439240243461966, 658699789102329845826360815322683450295410367743, (-80), (-80)⟩, ⟨5466517076553534602787223582439240243461966, 5466517076553534602787223582439240243461966, 658699789102329845826360815322683450295410367743, (-80), (-80)⟩, ⟨5466517076553534602787223582439240243461966, 5466517076553534602787223582439240243461966, 658699789102329845826360815322683450295410367743, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der194140 :
    checkPosTMHull (derivIExpr E549 2) B194140 DP194140
    = true := by
  decide

/-- 面叶 194140（lo 面）. -/

def FB194140 : Fin 6 → DInterval := faceBoxLo B194140 2

def PF194140 : TMParams :=
  ⟨[⟨113408472463108548699806868784925916678098, 107061591250730497985166424365074641760434, 0, (-80), (-80)⟩, ⟨5410012648248259892676266123845542551531849, 5410012648248259892676266123845542551531849, 663395225214168592996640324077340692655389242070, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face194140 :
    checkPosTMHull E549 FB194140 PF194140
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 194140，then 支）. -/

def DSafe194140 : DerivSafeOn B194140 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S194140D2) S194140D1) (Or.inr (Or.inr rfl))) S194140D0)))

/-- mono 折叠组合（叶 194140，两叶引用零重算）. -/

theorem Fold194140 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B194140 2 PF194140 DP194140 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B194140 DP194140 = true := Der194140
  have h2 : checkPosTMHull E549 (faceBoxLo B194140 2) PF194140 = true := Face194140
  show (checkPosTMHull (derivIExpr E549 2) B194140 DP194140
      && checkPosTMHull E549 (faceBoxLo B194140 2) PF194140) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 194140）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem194140 (ρ : Fin 6 → ℝ) (hρ : boxMem B194140 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe194140 Fold194140 hρ

#print axioms Sem194140

/-- 叶 200092（then 支，lo 面）原盒. -/

def B200092 : Fin 6 → DInterval :=
  ![⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩]

/-- 证书叶 200092.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S200092C0P : TMParams :=
  ⟨[⟨101936216234553573550397791990309046609963, 442120219102526060580659714646987114884347, 0, (-80), (-80)⟩], [], []⟩

theorem S200092C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B200092 S200092C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 200092.C0. -/

theorem S200092D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B200092 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S200092C0 ρ hρ

/-- 证书叶 200092.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S200092C1P : TMParams :=
  ⟨[⟨101936216234553573550397791990309046609963, 442120219102526060580659714646987114884347, 0, (-80), (-80)⟩], [], []⟩

theorem S200092C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B200092 S200092C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 200092.C1. -/

theorem S200092D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B200092 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S200092C1 ρ hρ

/-- 证书叶 200092.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S200092C2P : TMParams :=
  ⟨[], [], []⟩

theorem S200092C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B200092 S200092C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 200092.C2. -/

theorem S200092D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B200092 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S200092C2 ρ hρ

/-- 导数叶 200092（+∂x3f，then 支，全盒）. -/

def DP200092 : TMParams :=
  ⟨[⟨5417262232122956675740331217385551972110888, 5417262232122956675740331217385551972110888, 652967999202377428409314461678340034956451821894, (-80), (-80)⟩, ⟨5417262232122956675740331217385551972110888, 5417262232122956675740331217385551972110888, 652967999202377428409314461678340034956451821894, (-80), (-80)⟩, ⟨5417262232122956675740331217385551972110888, 5417262232122956675740331217385551972110888, 652967999202377428409314461678340034956451821894, (-80), (-80)⟩, ⟨5417262232122956675740331217385551972110888, 5417262232122956675740331217385551972110888, 652967999202377428409314461678340034956451821894, (-80), (-80)⟩, ⟨5417262232122956675740331217385551972110888, 5417262232122956675740331217385551972110888, 652967999202377428409314461678340034956451821894, (-80), (-80)⟩, ⟨5417262232122956675740331217385551972110888, 5417262232122956675740331217385551972110888, 652967999202377428409314461678340034956451821894, (-80), (-80)⟩, ⟨5417262232122956675740331217385551972110888, 5417262232122956675740331217385551972110888, 652967999202377428409314461678340034956451821894, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der200092 :
    checkPosTMHull (derivIExpr E549 2) B200092 DP200092
    = true := by
  decide

/-- 面叶 200092（lo 面）. -/

def FB200092 : Fin 6 → DInterval := faceBoxLo B200092 2

def PF200092 : TMParams :=
  ⟨[⟨113295173469496951505897453358735201433995, 423531795327792692638126594261201421381986, 0, (-80), (-80)⟩, ⟨5362686188997471328286041043041478926333497, 5362686188997471328286041043041478926333497, 657548570914030859675549540945691990824075680730, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face200092 :
    checkPosTMHull E549 FB200092 PF200092
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 200092，then 支）. -/

def DSafe200092 : DerivSafeOn B200092 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S200092D2) S200092D1) (Or.inr (Or.inr rfl))) S200092D0)))

/-- mono 折叠组合（叶 200092，两叶引用零重算）. -/

theorem Fold200092 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B200092 2 PF200092 DP200092 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B200092 DP200092 = true := Der200092
  have h2 : checkPosTMHull E549 (faceBoxLo B200092 2) PF200092 = true := Face200092
  show (checkPosTMHull (derivIExpr E549 2) B200092 DP200092
      && checkPosTMHull E549 (faceBoxLo B200092 2) PF200092) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 200092）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem200092 (ρ : Fin 6 → ℝ) (hρ : boxMem B200092 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe200092 Fold200092 hρ

#print axioms Sem200092

/-- 叶 207591（then 支，lo 面）原盒. -/

def B207591 : Fin 6 → DInterval :=
  ![⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨9148280341, -32⟩, ⟨18854906431, -33⟩⟩, ⟨⟨17738214933, -33⟩, ⟨9148280341, -32⟩⟩]

/-- 证书叶 207591.C0（iteNeg，neg 形，裸区间 checkPosI）. -/

def S207591C0P : TMParams :=
  ⟨[⟨210154194884881137915040070609232554497518, 112729208605964578689023294782564328766972, 0, (-80), (-80)⟩], [], []⟩

theorem S207591C0 :
    checkPosI
    ((.neg (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)))) B207591 S207591C0P = true := by
  decide

/-- 逐节点前提（safeIteNegI）叶 207591.C0. -/

theorem S207591D0 (ρ : Fin 6 → ℝ) (hρ : boxMem B207591 ρ) :
    IExpr.evalReal ((.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0))) ρ < 0 :=
  safeIteNegI S207591C0 ρ hρ

/-- 证书叶 207591.C1（divNe，pos 形，裸区间 checkPosI）. -/

def S207591C1P : TMParams :=
  ⟨[⟨210154194884881137915040070609232554497518, 112729208605964578689023294782564328766972, 0, (-80), (-80)⟩], [], []⟩

theorem S207591C1 :
    checkPosI
    ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) B207591 S207591C1P = true := by
  decide

/-- 逐节点前提（safeDivPosI）叶 207591.C1. -/

theorem S207591D1 (ρ : Fin 6 → ℝ) (hρ : boxMem B207591 ρ) :
    IExpr.evalReal ((.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) ρ ≠ 0 :=
  safeDivPosI S207591C1 ρ hρ

/-- 证书叶 207591.C2（sqrtPos，pos 形，裸区间 checkPosI）. -/

def S207591C2P : TMParams :=
  ⟨[], [], []⟩

theorem S207591C2 :
    checkPosI
    ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) B207591 S207591C2P = true := by
  decide

/-- 逐节点前提（safeSqrtPosI）叶 207591.C2. -/

theorem S207591D2 (ρ : Fin 6 → ℝ) (hρ : boxMem B207591 ρ) :
    0 < IExpr.evalReal ((.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) ρ :=
  safeSqrtPosI S207591C2 ρ hρ

/-- 导数叶 207591（+∂x3f，then 支，全盒）. -/

def DP207591 : TMParams :=
  ⟨[⟨5537671914887430371587479651293142951332522, 5537671914887430371587479651293142951332522, 667929970192579060919561742589750412459525664233, (-80), (-80)⟩, ⟨5537671914887430371587479651293142951332522, 5537671914887430371587479651293142951332522, 667929970192579060919561742589750412459525664233, (-80), (-80)⟩, ⟨5537671914887430371587479651293142951332522, 5537671914887430371587479651293142951332522, 667929970192579060919561742589750412459525664233, (-80), (-80)⟩, ⟨5537671914887430371587479651293142951332522, 5537671914887430371587479651293142951332522, 667929970192579060919561742589750412459525664233, (-80), (-80)⟩, ⟨5537671914887430371587479651293142951332522, 5537671914887430371587479651293142951332522, 667929970192579060919561742589750412459525664233, (-80), (-80)⟩, ⟨5537671914887430371587479651293142951332522, 5537671914887430371587479651293142951332522, 667929970192579060919561742589750412459525664233, (-80), (-80)⟩, ⟨5537671914887430371587479651293142951332522, 5537671914887430371587479651293142951332522, 667929970192579060919561742589750412459525664233, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Der207591 :
    checkPosTMHull (derivIExpr E549 2) B207591 DP207591
    = true := by
  decide

/-- 面叶 207591（lo 面）. -/

def FB207591 : Fin 6 → DInterval := faceBoxLo B207591 2

def PF207591 : TMParams :=
  ⟨[⟨117209273717027724478353159936172223936905, 108071873960996601891172816742138882412906, 0, (-80), (-80)⟩, ⟨5492600673820663248429590777667436536990570, 5492600673820663248429590777667436536990570, 672499926422875467595342682003002742424636874282, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

theorem Face207591 :
    checkPosTMHull E549 FB207591 PF207591
    = true := by
  decide

/-- DerivSafeOn 证书发射（叶 207591，then 支）. -/

def DSafe207591 : DerivSafeOn B207591 E549 :=
  (DerivSafeOnM.sub (DerivSafeOnM.div (DerivSafeOnM.const ⟨1893, 0⟩) (DerivSafeOnM.const ⟨1000, 0⟩) (fun ρ _ => safeConstNe 1000 0 (by norm_num) ρ)) (DerivSafeOnM.add (DerivSafeOnM.div (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.trans (DerivSafeOnM.const ⟨1, 0⟩) (Or.inr (Or.inr rfl)))) (DerivSafeOnM.const ⟨2, 0⟩) (fun ρ _ => safeConstNe 2 0 (by norm_num) ρ)) (DerivSafeOnM.iteNeg (DerivSafeOnM.trans (DerivSafeOnM.div (DerivSafeOnM.neg (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))))) (DerivSafeOnM.sqrt (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.const ⟨4, 0⟩) (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.neg (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0))) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2)) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))) (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.add (DerivSafeOnM.sub (DerivSafeOnM.add (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 2) (DerivSafeOnM.var 2))) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 0) (DerivSafeOnM.var 0)) (DerivSafeOnM.mul (DerivSafeOnM.var 1) (DerivSafeOnM.var 1))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5)))) (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.mul (DerivSafeOnM.var 3) (DerivSafeOnM.var 3)) (DerivSafeOnM.mul (DerivSafeOnM.var 4) (DerivSafeOnM.var 4))) (DerivSafeOnM.mul (DerivSafeOnM.var 5) (DerivSafeOnM.var 5))))) S207591D2) S207591D1) (Or.inr (Or.inr rfl))) S207591D0)))

/-- mono 折叠组合（叶 207591，两叶引用零重算）. -/

theorem Fold207591 :
    checkPosFaceLo E549 (derivIExpr E549 2)
    B207591 2 PF207591 DP207591 = true := by
  have h1 : checkPosTMHull (derivIExpr E549 2) B207591 DP207591 = true := Der207591
  have h2 : checkPosTMHull E549 (faceBoxLo B207591 2) PF207591 = true := Face207591
  show (checkPosTMHull (derivIExpr E549 2) B207591 DP207591
      && checkPosTMHull E549 (faceBoxLo B207591 2) PF207591) = true
  rw [h1, h2, Bool.and_true]

/-- 全链 fold（叶 207591）：面叶+导数叶+证书 ⇒ 语义正性. -/

theorem Sem207591 (ρ : Fin 6 → ℝ) (hρ : boxMem B207591 ρ) :
    0 < E549.evalReal ρ :=
  checkPosFaceLo_sound DSafe207591 Fold207591 hρ

#print axioms Sem207591


end Kepler.Interval.C549ProdS0002
