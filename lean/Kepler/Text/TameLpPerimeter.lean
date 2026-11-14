/-
Kepler/Text/TameLpPerimeter.lean — 方案 F（下游重绑定）：父件与 MQMSMAB 的
copy-rename 层（**纯新增**；TameLp 原声明一行未改）。

## 内容

* `fully_surrounded_perimeter_bound'`：陈述与 `TameLp.fully_surrounded_perimeter_bound`
  逐字节同；body = `pW43_parent_perimeterBound_of_fullySurrounded_v5`
  （= `pW42_perimeter_hia_v5` 的无 w 侧槽链 + `p21_hL_of_fullySurrounded`）。
* `MQMSMAB'`：陈述与 `TameLp.MQMSMAB` 逐字节同；body = TameLp 原 body 逐字，
  唯一替换 = 父件换成上面这一件（不再引用 TameLp 的 sorry 占位）。

## 接线（编排者闸做岛协议）

`Kepler/Assembly.lean` 两行：`import Kepler.Text.TameLpPerimeter`
+ `TameLp.MQMSMAB V hc hfan hmain hkcblrqc` → `TameLp.MQMSMAB' ...`。
本文件不改 TameLp；TameLp 原父件的 sorry 变孤儿（pq 记账，不删不改）。
-/
import Kepler.Text.TameLp
import Kepler.Text.LocalFanPerimeterFinalV5

namespace Kepler.Text.TameLp

open Kepler.Geom Kepler.Text.Fan Set Classical

/-- **父件 copy**（陈述与 TameLp 原声明逐字节同；body 走 v5 链，零槽）。 -/
theorem fully_surrounded_perimeter_bound' (V : Set V3) (E : Set (Set V3))
    (hfan : FAN 0 V E) (hsurr : FullySurrounded V E) :
    PerimeterBound V E hfan :=
  pW43_parent_perimeterBound_of_fullySurrounded_v5 V E hfan hsurr

/-- **`MQMSMAB` copy**（陈述逐字节同；body 逐字，唯一替换 = 父件）。 -/
theorem MQMSMAB' (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V))
    (hmain : lp_main_estimate) (hineq : KcblrqcIneqDef) :
    TamePlanarHypermap (hypermapOfFanTl V (ESTD V) hfan) := by
  have hlpfan : LpFan V (ESTD V) := contravening_lp_fan V hc
  have h9a := CRTTXAT (fun V' hfan' hc' => JGTDEBU4 V' hc' hfan') V hc hfan
    (fully_surrounded_perimeter_bound' V (ESTD V) hlpfan.1 hlpfan.2.1)
  exact ⟨⟨JGTDEBU2 V hc hfan, JGTDEBU1 V hc hfan⟩,
    ⟨JGTDEBU3 V hc hfan, JGTDEBU4 V hc hfan⟩, JGTDEBU5 V hc hfan, JGTDEBU6 V hc hfan,
    JGTDEBU7 V hc hfan, JGTDEBU8 V hc hfan, h9a, JGTDEBU10 V hc hfan,
    JGTDEBU11 V hc hfan, SZIPOAS hineq V hc hfan, BDJYFFB1 V hc hmain hineq hfan,
    MQMSMAB_tame13a V hc hlpfan hmain hineq h9a⟩

end Kepler.Text.TameLp

/-! ## 探针（父件'/MQMSMAB' axioms + Assembly 调用点类型检查） -/

#print axioms Kepler.Text.TameLp.fully_surrounded_perimeter_bound'
#print axioms Kepler.Text.TameLp.MQMSMAB'

/-- Assembly:2457 调用点类型检查（与 `TameLp.MQMSMAB` 同型，仅改名）。 -/
example (V : Set Kepler.Geom.V3) (hc : Kepler.Text.TameLp.Contravening V)
    (hmain : Kepler.Text.lp_main_estimate)
    (hfan : Kepler.Text.Fan.FAN 0 V (Kepler.Text.TameLp.ESTD V))
    (hkcblrqc : Kepler.Text.TameLp.KcblrqcIneqDef) :
    Kepler.Text.TameLp.TamePlanarHypermap
      (Kepler.Text.TameLp.hypermapOfFanTl V (Kepler.Text.TameLp.ESTD V) hfan) :=
  Kepler.Text.TameLp.MQMSMAB' V hc hfan hmain hkcblrqc
