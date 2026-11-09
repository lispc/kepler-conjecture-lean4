/-
  Kepler.Text.TameSpine.JcajyduBetwnBase — jcajydu-c2（C2=J0 波）批 1：
  `betwn_corek_z_x.hl` / `betwn_core0_z_y.hl`（两章收官定理，reduction_K5 直接消费件）
  依赖闭包的**通用叶层**。全部为 α 泛型 list/betwn 事实，零 `transform_assumption`
  消费（该塔 = J2 领土，是两收官定理的硬阻塞，见 DELIVERY 闭包表）。

  本批镜像对象（HOL 逐条锚）：
  - OHCGKFU.hl:98 `uniq_betwn`；AQ8.hl:97 `MEM_POWER_NEXT_EL`；
    AQ8.hl:108 `uniq_imp_inj`；AQ23.hl:221 `LAST_FLATTEN_2`；
    AQ4.hl:383 `next_el_last_hd`；AQ4.hl:398 `prev_el_last_hd`；
    AQ23.hl:186 `next_last_betwn`。
  - 私有辅件：`Seq2.index_take`/`index_drop_le` 的 Nodup 形（tame_list 私有
    idxOfTake/idxOfDrop 的公开孪生：续批 next_el_betwn_same 消费）、
    next_el 的 idxOf 模长平移（Seq2 系；沿 TameLp.nextEl_eq_getD 重证）。

  载体折算（沿 TameList3/71 约定）：`betwn` ↦ `Kepler.Graphs.between`、
  `uniq` ↦ `List.Nodup`、`indexl` ↦ `List.idxOf`、`sizel` ↦ `List.length`、
  `next_el` ↦ `Kepler.Assembly.nextEl`、`prev_el` ↦ `Kepler.Assembly.prevEl`、
  `POWER n` ↦ `Function.iterate n`、`HD` ↦ `List.head!`（配 `[Inhabited α]`
  载体伪参）、`LAST` ↦ `List.getLast`（配非空证明）。

  红线：零 sorry、零 axiom、零 native_decide、零既有文件触碰、主仓 tracked 零改动。
-/
import Kepler.Text.TameLp
import Kepler.Text.TameSpine.TameList3
import Kepler.Text.TameSpine.TameList9
import Kepler.Text.TameSpine.TameList71

namespace Kepler.Text.TameSpine

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Kepler.Assembly (nextEl prevEl)
open Kepler.Graphs (between)
open Kepler.Text.TameLp (nextEl_eq_getD idxOf_getElem getElem_idxOf getD_eq_getElem_of_lt
  nextEl_mem_of_mem)

/-! ## §0 私有辅件（next_el idxOf 平移 / take-drop idxOf 平移） -/

/-- Nodup 列表的下标唯一性：`s.idxOf s[i] = i`（batteries `getElem_idxOf` 的逆向，
BEq 载体、无 DecidableEq 强化）。 -/
private theorem idxOfGetElemOfNodup [BEq α] [LawfulBEq α] {s : List α}
    (hnd : s.Nodup) {i : ℕ} (h : i < s.length) : s.idxOf s[i] = i := by
  have hmem := List.getElem_mem h
  have hidxlt : s.idxOf s[i] < s.length := List.idxOf_lt_length_iff.mpr hmem
  have h1 := List.getElem_idxOf hidxlt
  exact List.Nodup.getElem_inj_iff hnd |>.mp h1

/-- `Seq2.index_take` 的 Nodup 形（tame_list 私有 idxOfTake 公开孪生）：
Nodup 列表前段的 idxOf 不变。 -/
theorem idxOfTakeNodup [BEq α] [LawfulBEq α] {s : List α} {v : α} {i : ℕ}
    (hnd : s.Nodup) (hv : v ∈ s) (h : s.idxOf v < i) :
    (s.take i).idxOf v = s.idxOf v := by
  have hmem : v ∈ s.take i := (List.mem_take_iff_idxOf_lt hv).mpr h
  have hpl : (s.take i).idxOf v < (s.take i).length := List.idxOf_lt_length_iff.mpr hmem
  have h1 := List.getElem_idxOf hpl
  rw [List.getElem_take] at h1
  exact List.Nodup.getElem_inj_iff hnd |>.mp
    (h1.trans (List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hv)).symm)

/-- `Seq2.index_drop_le` 的 Nodup 形（tame_list 私有 idxOfDrop 公开孪生）：
Nodup 列表后段的 idxOf 平移。 -/
theorem idxOfDropNodup [BEq α] [LawfulBEq α] {s : List α} {v : α} {k : ℕ}
    (hnd : s.Nodup) (hv : v ∈ s) (h : k ≤ s.idxOf v) :
    (s.drop k).idxOf v = s.idxOf v - k := by
  have hd : v ∈ s.drop k := (memDropIndex hnd hv).mpr h
  have hpl : (s.drop k).idxOf v < (s.drop k).length := List.idxOf_lt_length_iff.mpr hd
  have h1 := List.getElem_idxOf hpl
  rw [List.getElem_drop] at h1
  have heq := List.Nodup.getElem_inj_iff hnd |>.mp
    (h1.trans (List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hv)).symm)
  omega

/-- Nodup 下 next_el 的 idxOf 模长平移：
`uniq s /\ MEM x s ==> indexl (next_el s x) s = (indexl x s + 1) mod sizel s`。
（经 TameLp.nextEl_eq_getD/idxOf_getElem，二者带 `[DecidableEq α]` 载体强化，
本批全部 nextEl 消费件同记档；消费链 A = num#num 恒有 DecidableEq。） -/
theorem idxOfNextElMod [BEq α] [LawfulBEq α] [DecidableEq α] {s : List α} {x : α}
    (hnd : s.Nodup) (hx : x ∈ s) :
    s.idxOf (nextEl s x) = (s.idxOf x + 1) % s.length := by
  have hj : (s.idxOf x + 1) % s.length < s.length :=
    Nat.mod_lt _ (List.length_pos_of_mem hx)
  rw [nextEl_eq_getD hx, getD_eq_getElem_of_lt hj x]
  exact idxOf_getElem hnd hj

/-- 完成器（前驱形）：`v` 的 idxOf 是 `z` 的 idxOf 的前驱 ⇒ `next_el r v = z`。 -/
private theorem nextElPredOfIdx [BEq α] [LawfulBEq α] [DecidableEq α] {r : List α}
    {v z : α} (hz : z ∈ r) (hv : v ∈ r) (hv1 : r.idxOf v + 1 = r.idxOf z) :
    nextEl r v = z := by
  have hzlt : r.idxOf z < r.length := List.idxOf_lt_length_iff.mpr hz
  rw [nextEl_eq_getD hv, hv1, Nat.mod_eq_of_lt hzlt, getD_eq_getElem_of_lt hzlt v]
  exact getElem_idxOf hz

/-- 完成器（环形）：`v` 是末元、`z` 是首元 ⇒ `next_el r v = z`。 -/
private theorem nextElWrap [BEq α] [LawfulBEq α] [DecidableEq α] {r : List α}
    {v z : α} (hz : z ∈ r) (hv : v ∈ r) (hvi : r.idxOf v = r.length - 1)
    (hz0 : r.idxOf z = 0) : nextEl r v = z := by
  have hzlt : r.idxOf z < r.length := List.idxOf_lt_length_iff.mpr hz
  have hlenpos : 0 < r.length := List.length_pos_of_mem hz
  have hmod : (r.idxOf v + 1) % r.length = 0 := by
    have he : r.idxOf v + 1 = r.length := by omega
    rw [he, Nat.mod_self]
  have hzget : r.getD (r.idxOf z) v = z := by
    rw [getD_eq_getElem_of_lt hzlt v]
    exact getElem_idxOf hz
  rw [nextEl_eq_getD hv, hmod, ← hz0]
  exact hzget

/-- Nodup 非空表的 LAST 元下标：`indexl (LAST s) s = sizel s - 1`。 -/
private theorem idxOfGetLastOfNodup [BEq α] [LawfulBEq α] [DecidableEq α] {s : List α}
    (hnd : s.Nodup) (hne : s ≠ []) : s.idxOf (s.getLast hne) = s.length - 1 := by
  have hpos : 0 < s.length := List.length_pos_of_ne_nil hne
  rw [List.getLast_eq_getElem hne]
  exact idxOf_getElem hnd (by omega : s.length - 1 < s.length)

/-! ## §1 betwn 通用件（OHCGKFU / AQ8 / AQ23 / AQ4 叶层） -/

/-- **HOL `Ohcgkfu.uniq_betwn`**（OHCGKFU.hl:98）：
`uniq r /\ MEM z r /\ MEM y r /\ ~(z=y) ==> uniq (betwn r z y)`。 -/
theorem uniqBetwn [BEq α] [LawfulBEq α] {r : List α} {z y : α}
    (hnd : r.Nodup) (hz : z ∈ r) (hy : y ∈ r) (hzy : z ≠ y) :
    (between r z y).Nodup := by
  rw [betwnTakeDrop hnd hy]
  by_cases hlt : r.idxOf z < r.idxOf y
  · rw [if_pos hlt]
    exact uniqTake (uniqDrop hnd)
  · rw [if_neg hlt, List.nodup_append]
    refine ⟨uniqDrop hnd, uniqTake hnd, ?_⟩
    intro a ha b hb hab
    have hd : a ∈ r := List.mem_of_mem_drop ha
    have h1 : r.idxOf z + 1 ≤ r.idxOf a := (memDropIndex hnd hd).mp ha
    have h2 : r.idxOf a < r.idxOf y := (memTakeIndex hd).mp (hab ▸ hb)
    omega

/-- **HOL `Aq8.MEM_POWER_NEXT_EL`**（AQ8.hl:97）：
`MEM x r ==> MEM ((next_el r POWER k) x) r`。 -/
theorem memPowerNextEl [BEq α] [LawfulBEq α] [DecidableEq α] {r : List α} {x : α}
    (hx : x ∈ r) : ∀ k : ℕ, (nextEl r)^[k] x ∈ r := by
  intro k
  induction k with
  | zero => exact hx
  | succ k ih => rw [Function.iterate_succ_apply']; exact nextEl_mem_of_mem ih

/-- **HOL `Aq8.uniq_imp_inj`**（AQ8.hl:108）：
`uniq (MAP f y) ==> (!u v. MEM u y /\ MEM v y /\ f u = f v ==> u = v)`。
（Nodup 载体需 `[BEq β]`，HOL 无此伪参，记档。） -/
theorem uniqImpInj {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    {f : α → β} {l : List α} (hnd : (l.map f).Nodup) {u v : α}
    (hu : u ∈ l) (hv : v ∈ l) (hfv : f u = f v) : u = v := by
  have hi : l.idxOf u < l.length := List.idxOf_lt_length_iff.mpr hu
  have hk : l.idxOf v < l.length := List.idxOf_lt_length_iff.mpr hv
  have himl : l.idxOf u < (l.map f).length := by
    rw [List.length_map]; exact hi
  have himv : l.idxOf v < (l.map f).length := by
    rw [List.length_map]; exact hk
  have hui := List.getElem_idxOf hi
  have hvi := List.getElem_idxOf hk
  have hm1 : (l.map f)[l.idxOf u]'himl = f u := by
    simp [List.getElem_map, hui]
  have hm2 : (l.map f)[l.idxOf v]'himv = f v := by
    simp [List.getElem_map, hvi]
  have hik : l.idxOf u = l.idxOf v := by
    have heq : (l.map f)[l.idxOf u]'himl = (l.map f)[l.idxOf v]'himv := by
      rw [hm1, hm2, hfv]
    exact List.Nodup.getElem_inj_iff hnd |>.mp heq
  exact (List.idxOf_inj hu).mp hik

/-- **HOL `Aq23.LAST_FLATTEN_2`**（AQ23.hl:221）：
`~(r=[]) /\ ~(LAST r=[]) ==> LAST (flatten r) = LAST (LAST r)`。
（LHS 的 getLast 非空证明由前提导出，以默认值参携带，记档。） -/
theorem lastFlatten2 {r : List (List α)} (hne : r ≠ [])
    (hlne : r.getLast hne ≠ []) (hflatne : r.flatten ≠ []) :
    r.flatten.getLast hflatne = (r.getLast hne).getLast hlne := by
  have hf : r.flatten = r.dropLast.flatten ++ r.getLast hne := by
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    rw [List.flatten_append, List.flatten_singleton]
  have hget2 : r.flatten.getLast hflatne
      = (r.dropLast.flatten ++ r.getLast hne).getLast (by rw [← hf]; exact hflatne) :=
    List.getLast_congr hflatne (by rw [← hf]; exact hflatne) hf
  rw [hget2, List.getLast_append_of_right_ne_nil _ _ hlne]

/-- **HOL `Aq4.next_el_last_hd`**（AQ4.hl:383）：
`uniq h /\ ~(h=[]) ==> next_el h (LAST h) = HD h`。 -/
theorem nextElLastHd [Inhabited α] [BEq α] [LawfulBEq α] [DecidableEq α] {h : List α}
    (hnd : h.Nodup) (hne : h ≠ []) :
    nextEl h ((h.getLast hne)) = h.head! := by
  have hpos : 0 < h.length := List.length_pos_of_ne_nil hne
  have hmem : h.getLast hne ∈ h := List.getLast_mem hne
  have hidx : h.idxOf (h.getLast hne) = h.length - 1 := by
    rw [List.getLast_eq_getElem hne]
    exact idxOf_getElem hnd (by omega)
  have he : h.length - 1 + 1 = h.length := by omega
  rw [nextEl_eq_getD hmem, hidx, he, Nat.mod_self, getD_eq_getElem_of_lt hpos (h.getLast hne)]
  cases h with
  | nil => exact absurd hne (by simp)
  | cons a t => simp [List.head!_cons]

/-- **HOL `Aq4.prev_el_last_hd`**（AQ4.hl:398）：
`uniq h /\ ~(h=[]) ==> prev_el h (HD h) = LAST h`。 -/
theorem prevElLastHd [Inhabited α] [DecidableEq α] {h : List α}
    (hnd : h.Nodup) (hne : h ≠ []) :
    prevEl h h.head! = h.getLast hne := by
  cases h with
  | nil => exact absurd hne (by simp)
  | cons a t =>
    have hne' : a :: t ≠ [] := by simp
    have h0 : (a :: t).idxOf (a :: t).head! = 0 := by
      rw [List.head!_cons]; simp
    rw [prevEl, if_neg (by
      simp), if_pos h0, List.head!_cons]
    exact lastLastD hne'

/-- **HOL `Aq23.next_last_betwn`**（AQ23.hl:186）：
`MEM y r /\ MEM z r /\ uniq r /\ ~(y=z) /\ ~(betwn r y z=[])
==> next_el r (LAST (betwn r y z)) = z`。 -/
theorem nextLastBetwn [BEq α] [LawfulBEq α] [DecidableEq α] {r : List α} {y z : α}
    (hy : y ∈ r) (hz : z ∈ r) (hnd : r.Nodup) (hyz : y ≠ z)
    (hb : between r y z ≠ []) :
    nextEl r ((between r y z).getLast hb) = z := by
  have hzlt : r.idxOf z < r.length := List.idxOf_lt_length_iff.mpr hz
  have hlenpos : 0 < r.length := List.length_pos_of_mem hz
  have hbmem : (between r y z).getLast hb ∈ between r y z := List.getLast_mem hb
  have hv0 : (between r y z).getLast hb ∈ r := betwnMem hbmem
  by_cases hlt : r.idxOf y < r.idxOf z
  · -- 直段：betwn = take (iz-iy-1) (drop (iy+1) r)，LAST = r[iz-1]
    have hbeq : between r y z = (r.drop (r.idxOf y + 1)).take
        (r.idxOf z - (r.idxOf y + 1)) :=
      betwnTakeDrop hnd hz |>.trans (if_pos hlt)
    have hbtake : (r.drop (r.idxOf y + 1)).take
        (r.idxOf z - (r.idxOf y + 1)) ≠ [] := by rw [← hbeq]; exact hb
    have hbmem2 : (between r y z).getLast hb
        ∈ (r.drop (r.idxOf y + 1)).take (r.idxOf z - (r.idxOf y + 1)) := by
      rw [← hbeq]; exact hbmem
    have hget : (between r y z).getLast hb
        = ((r.drop (r.idxOf y + 1)).take
            (r.idxOf z - (r.idxOf y + 1))).getLast hbtake :=
      List.getLast_congr hb hbtake hbeq
    rw [hget] at hbmem2 ⊢
    set v := ((r.drop (r.idxOf y + 1)).take
        (r.idxOf z - (r.idxOf y + 1))).getLast hbtake with hvdef
    have hbd : ((r.drop (r.idxOf y + 1)).take
        (r.idxOf z - (r.idxOf y + 1))).Nodup := uniqTake (uniqDrop hnd)
    have hvd : v ∈ r.drop (r.idxOf y + 1) := List.mem_of_mem_take hbmem2
    have hv1r : v ∈ r := List.mem_of_mem_drop hvd
    have hle : r.idxOf y + 1 ≤ r.idxOf v :=
      (memDropIndex hnd hv1r).mp hvd
    have hlt2 : (r.drop (r.idxOf y + 1)).idxOf v
        < r.idxOf z - (r.idxOf y + 1) :=
      (memTakeIndex hvd).mp hbmem2
    have hshift : (r.drop (r.idxOf y + 1)).idxOf v
        = r.idxOf v - (r.idxOf y + 1) :=
      idxOfDropNodup hnd hv1r hle
    have htake2 : (r.drop (r.idxOf y + 1)).idxOf v
        = ((r.drop (r.idxOf y + 1)).take
          (r.idxOf z - (r.idxOf y + 1))).idxOf v :=
      (idxOfTakeNodup (uniqDrop hnd) hvd hlt2).symm
    have hidxb := idxOfGetLastOfNodup hbd hbtake
    rw [← hvdef] at hidxb
    have hdl : (r.drop (r.idxOf y + 1)).length = r.length - (r.idxOf y + 1) :=
      List.length_drop
    have hblen : ((r.drop (r.idxOf y + 1)).take
        (r.idxOf z - (r.idxOf y + 1))).length = r.idxOf z - (r.idxOf y + 1) := by
      rw [List.length_take]; exact Nat.min_eq_left (by omega)
    have hc1 : 1 ≤ r.idxOf z - (r.idxOf y + 1) := by
      have hh := List.length_pos_of_ne_nil hbtake
      rw [hblen] at hh; omega
    have h1 : r.idxOf v - (r.idxOf y + 1)
        = ((r.drop (r.idxOf y + 1)).take
          (r.idxOf z - (r.idxOf y + 1))).length - 1 := by
      rw [← hshift, htake2, hidxb]
    have hiz : r.idxOf y + 1 ≤ r.idxOf z := Nat.succ_le_of_lt hlt
    have he : r.idxOf z - (r.idxOf y + 1) + (r.idxOf y + 1) = r.idxOf z :=
      Nat.sub_add_cancel hiz
    have hfin : r.idxOf v + 1 = r.idxOf z := by omega
    rw [nextElPredOfIdx hz hv1r hfin]
  · -- 环段：betwn = drop (iy+1) r ++ take iz r
    have hbeq : between r y z = r.drop (r.idxOf y + 1) ++ r.take (r.idxOf z) :=
      betwnTakeDrop hnd hz |>.trans (if_neg hlt)
    have hbapp : r.drop (r.idxOf y + 1) ++ r.take (r.idxOf z) ≠ [] := by
      rw [← hbeq]; exact hb
    have hbmem2 : (between r y z).getLast hb
        ∈ r.drop (r.idxOf y + 1) ++ r.take (r.idxOf z) := by
      rw [← hbeq]; exact hbmem
    have hget : (between r y z).getLast hb
        = (r.drop (r.idxOf y + 1) ++ r.take (r.idxOf z)).getLast hbapp :=
      List.getLast_congr hb hbapp hbeq
    rw [hget] at hbmem2 ⊢
    set v := (r.drop (r.idxOf y + 1) ++ r.take (r.idxOf z)).getLast hbapp with hvdef
    have hv0app : v ∈ r := by
      have h0 := hv0
      rw [hget] at h0
      exact h0
    rcases List.mem_append.mp hbmem2 with hd | ht
    · -- hd：LAST 落 drop 段 ⇒ take iz r = [] ⇒ iz = 0
      have htake0 : r.take (r.idxOf z) = [] := by
        by_contra hc0
        have htake : r.take (r.idxOf z) ≠ [] := hc0
        have hlast' : (r.drop (r.idxOf y + 1) ++ r.take (r.idxOf z)).getLast hbapp
            = (r.take (r.idxOf z)).getLast htake :=
          List.getLast_append_of_right_ne_nil _ _ htake
        have hd1 : r.idxOf y + 1 ≤ r.idxOf v :=
          (memDropIndex hnd hv0app).mp hd
        have hvt : (r.take (r.idxOf z)).getLast htake ∈ r :=
          List.mem_of_mem_take (List.getLast_mem htake)
        have hti : r.idxOf ((r.take (r.idxOf z)).getLast htake) < r.idxOf z :=
          (memTakeIndex hvt).mp (List.getLast_mem htake)
        rw [hvdef, hlast'] at hd1
        omega
      have htl : (r.take (r.idxOf z)).length = r.idxOf z := by
        rw [List.length_take]; exact Nat.min_eq_left (Nat.le_of_lt hzlt)
      have hzi : r.idxOf z = 0 := by
        have h1 : (r.take (r.idxOf z)).length = 0 := by rw [htake0]; simp
        omega
      have hdropne : r.drop (r.idxOf y + 1) ≠ [] := by
        rw [htake0, List.append_nil] at hbapp; exact hbapp
      have hdl : (r.drop (r.idxOf y + 1)).length = r.length - (r.idxOf y + 1) :=
        List.length_drop
      have hdlpos : 0 < (r.drop (r.idxOf y + 1)).length :=
        List.length_pos_of_ne_nil hdropne
      have hv2 : (r.drop (r.idxOf y + 1)).getLast hdropne ∈ r :=
        List.mem_of_mem_drop (List.getLast_mem hdropne)
      have heq2 : r.drop (r.idxOf y + 1) ++ r.take (r.idxOf z)
          = r.drop (r.idxOf y + 1) := by
        rw [htake0, List.append_nil]
      have hget2 : v = (r.drop (r.idxOf y + 1)).getLast hdropne := by
        rw [hvdef]
        exact List.getLast_congr hbapp hdropne heq2
      have hle : r.idxOf y + 1 ≤ r.idxOf v := (memDropIndex hnd hv0app).mp hd
      have hshift : (r.drop (r.idxOf y + 1)).idxOf v
          = r.idxOf v - (r.idxOf y + 1) := idxOfDropNodup hnd hv0app hle
      have hidxb := idxOfGetLastOfNodup (uniqDrop hnd) hdropne
      rw [← hget2] at hidxb
      have hvi : r.idxOf v = r.length - 1 := by omega
      rw [nextElWrap hz hv0app hvi hzi]
    · -- ht：LAST 落 take 段尾 ⇒ LAST = r[iz-1]
      have htake : r.take (r.idxOf z) ≠ [] := List.ne_nil_of_mem ht
      have htl : (r.take (r.idxOf z)).length = r.idxOf z := by
        rw [List.length_take]; exact Nat.min_eq_left (Nat.le_of_lt hzlt)
      have hv2 : (r.take (r.idxOf z)).getLast htake ∈ r :=
        List.mem_of_mem_take (List.getLast_mem htake)
      have hti : r.idxOf v < r.idxOf z := (memTakeIndex hv0app).mp ht
      have hidxb := idxOfGetLastOfNodup (uniqTake hnd) htake
      have hlast' : v = (r.take (r.idxOf z)).getLast htake :=
        List.getLast_append_of_right_ne_nil _ _ htake
      rw [← hlast'] at hidxb
      have hshift : (r.take (r.idxOf z)).idxOf v = r.idxOf v :=
        idxOfTakeNodup hnd hv0app hti
      have hv1 : r.idxOf v + 1 = r.idxOf z := by omega
      rw [nextElPredOfIdx hz hv0app hv1]

end Kepler.Text.TameSpine
