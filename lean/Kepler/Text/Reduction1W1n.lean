/-
  Kepler.Text.Reduction1W1n — J4 Wave W1 批 7a：Ob1 `enumerationVertexListEnumMem`
  （`reduction1.hl:1163-:1247` 结论①，护栏二具名落点）。
  纪律：零公理、零占位证明、零反射式判定。全程 `Nat`。
-/
import Kepler.Text.Reduction1W1a
import Kepler.Text.Reduction1W1b
import Kepler.Text.Reduction1W1d
import Kepler.Text.Reduction1W1j
import Kepler.Text.TameSpine.TameList4
import Kepler.Text.TameSpine.TameList3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

open Kepler.Text.TameSpine (showDups0 showDups indexf enumOfVertexList memShowDups0
  indexfLtSizel indexfRefl)

/-! ## §0 私件 -/

/-- `!` 形与依赖式 `getElem` 在界内同值。 -/
theorem getElemBangH {α : Type} [Inhabited α] {l : List α} {i : Nat}
    (h : i < l.length) : l[i]! = l[i]'h := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩]
  simp

/-- `l.drop (l.length-1) = [l.getLast!]`。 -/
theorem dropLastIsLast {α : Type} [Inhabited α] {l : List α} (h : l ≠ []) :
    l.drop (l.length - 1) = [l.getLast!] := by
  have hlt : l.length - 1 < l.length := by
    have := List.length_pos_iff.mpr h
    omega
  rw [List.drop_eq_getElem_cons hlt]
  have hnil : l.drop (l.length - 1 + 1) = [] := by
    rw [show l.length - 1 + 1 = l.length from by omega]
    exact List.drop_length
  rw [hnil, List.getLast!_eq_getElem!, getElemBangH hlt]

/-- `showDups0` 与 `l` 等长。 -/
theorem showDups0Length' {l : List (Option Nat)} (w : Nat) :
    (showDups0 w l).length = l.length := by
  induction l generalizing w with
  | nil => rfl
  | cons b bs ih => cases b with
    | none => rw [showDups0, List.length_cons, ih w, List.length_cons]
    | some c => rw [showDups0, List.length_cons, ih c, List.length_cons]

/-- `map` 的 `getElem!`（界内）。 -/
theorem getElemBangMap' {l : List Nat} {g : Nat → Nat} {k : Nat} (hk : k < l.length) :
    (l.map g)[k]! = g l[k]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk,
    List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  simp

/-- `l.head! = some u → (showDups0 u l)[0]! = u`。 -/
theorem showDups0Head {u : Nat} {l : List (Option Nat)} (h : l.head! = some u) :
    (showDups0 u l)[0]! = u := by
  cases l with
  | nil => rw [List.head!_nil] at h; exact absurd h (by simp)
  | cons b bs => cases b with
    | none => rw [showDups0, List.getElem!_cons_zero]
    | some c => rw [showDups0, List.getElem!_cons_zero]
                have hcu : c = u := by simpa using h
                rw [hcu]

/-- `l[l.length-1]! = l.getLast!`。 -/
theorem getElemLastEq {α : Type} [Inhabited α] {l : List α} (h : 0 < l.length) :
    l[l.length - 1]! = l.getLast! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
    List.getLast!_eq_getLast?_getD,
    List.getLast?_eq_some_getLast (List.length_pos_iff.mp h), Option.getD_some,
    List.getLast_eq_getElem (List.length_pos_iff.mp h)]

/-- 严格链。 -/
theorem strictChain {l : List Nat} (h : ∀ i, i + 1 < l.length → l[i]! < l[i + 1]!) :
    ∀ (n r : Nat), r + n + 1 < l.length → l[r]! < l[r + n + 1]! := by
  intro n
  induction n with
  | zero => intro r hr; simpa using h r hr
  | succ n ih =>
    intro r hr
    have h1 : r + n + 1 < l.length := by omega
    have h2 : r + n + 1 + 1 < l.length := by omega
    have := ih r h1
    have h3 := h (r + n + 1) h2
    rw [show r + (n + 1) + 1 = r + n + 1 + 1 from by omega]
    exact lt_trans this h3

/-- 非空表 = 首元单例 ++ 尾表。 -/
theorem consHeadSplit {α : Type} [Inhabited α] {l : List α} (h : l ≠ []) :
    l = [l[0]!] ++ l.drop 1 := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil h
  rfl

/-- `o` 为 some 时等于 `some o.getD 0`。 -/
theorem eqSomeGetD' {o : Option Nat} (h : o.isSome = true) : o = some (o.getD 0) := by
  cases o with
  | none => simp at h
  | some x => rfl

/-- `showDups0` 的第 `l.length-1` 项 = `l` 末项解包（末项 isSome）。 -/
theorem showDups0LastEq {l : List (Option Nat)} (u : Nat) :
    ∀ (k : Nat), k = l.length - 1 → l[k]!.isSome = true →
      (showDups0 u l)[k]! = l[k]!.getD 0 := by
  induction l generalizing u with
  | nil =>
    intro k hk hsome
    simp at hk
    subst hk
    have hd : ([] : List (Option Nat))[0]! = (none : Option Nat) := rfl
    rw [hd] at hsome
    simp at hsome
  | cons a t ih =>
    intro k hk hsome
    cases t with
    | nil =>
      have hk0 : k = 0 := by simp at hk; omega
      subst hk0
      cases a with
      | none => simp at hsome
      | some c => simp [showDups0]
    | cons b t' =>
      cases k with
      | zero => simp at hk
      | succ k' =>
        have hlen2 : (a :: b :: t').length = (b :: t').length + 1 := rfl
        have hk' : k' = (b :: t').length - 1 := by omega
        cases a with
        | none => rw [showDups0, List.getElem!_cons_succ]; exact ih u k' hk' hsome
        | some c => rw [showDups0, List.getElem!_cons_succ]; exact ih c k' hk' hsome

/-! ## §1 Ob1 -/

theorem enumerationVertexListEnumMem {f : List Nat} {v : Nat} {vs : List (Option Nat)}
    {vs' : List Nat}
    (hvs' : vs' = (vs.filter Option.isSome).map Option.get!)
    (h3 : 3 ≤ vs.length) (hhd : vs.head! = some v)
    (hnd : f.Nodup) (hvmem : v ∈ f)
    (hall : ∀ t ∈ (vs.filter Option.isSome).map Option.get!, t ∈ f)
    (hmono : ∀ i, i + 1 < vs'.length → indexf v vs'[i]! f < indexf v vs'[i + 1]! f)
    (hlastSome : (vs.getLast!).isSome = true)
    (hlastIdx : indexf v (vs.getLast!.getD 0) f = f.length - 1)
    (h2f : 2 ≤ f.length) :
    enumOfVertexList f v vs ∈ Kepler.Graphs.enumerator vs.length f.length := by
  -- S1 / S2
  have hee : enumOfVertexList f v vs = (showDups0 v vs).map (fun u => indexf v u f) := by
    rw [enumOfVertexList]; congr 1
    cases vs with
    | nil => rw [List.head!_nil] at hhd; exact absurd hhd (by simp)
    | cons b bs =>
      have hb : b = some v := by simpa using hhd
      rw [showDups, hb]; rfl
  have hdl : (showDups0 v vs).length = vs.length := showDups0Length' v
  have hev : (enumOfVertexList f v vs).length = vs.length := by
    rw [hee, List.length_map, hdl]
  -- S3 逐项形态
  have helem : ∀ k, k < vs.length →
      (enumOfVertexList f v vs)[k]! = indexf v ((showDups0 v vs)[k]!) f := by
    intro k hk; rw [hee, getElemBangMap' (by rw [hdl]; exact hk)]
  -- S4 单调
  have hmonoE : ∀ i, i + 1 < vs.length →
      (enumOfVertexList f v vs)[i]! ≤ (enumOfVertexList f v vs)[i + 1]! := by
    intro i hi
    exact enumOfVertexListMono (vs := vs) (vs' := vs') (f := f) (v := v)
      hhd hnd hvmem hvs' hmono i hi
  -- S5 首元
  have hhead0 : (enumOfVertexList f v vs)[0]! = 0 := by
    rw [helem 0 (by omega), showDups0Head hhd, indexfRefl hvmem]
  -- S6 末元
  have hlastSomeE : vs[vs.length - 1]!.isSome = true := by
    rw [getElemLastEq (l := vs) (by omega)]; exact hlastSome
  have hlast : (enumOfVertexList f v vs)[vs.length - 1]! = f.length - 1 := by
    rw [helem (vs.length - 1) (by omega),
      showDups0LastEq v (vs.length - 1) rfl hlastSomeE,
      getElemLastEq (l := vs) (by omega)]
    exact hlastIdx
  -- S7a: hstrict（A3）
  have hstrict : ∀ i, i ≤ vs.length - 2 → (vs[i]!).isSome = true →
      indexf v (vs[i]!.getD 0) f < f.length - 1 := by
    intro i hi hsome
    have hiLt : i < vs.length := by omega
    have hjLt : vs.length - 1 < vs.length := by omega
    have hsomeP : vs[i].isSome = true := by rw [← getElemBangH hiLt]; exact hsome
    have hlastSomeP : vs[vs.length - 1].isSome = true := by
      rw [← getElemBangH hjLt]; exact hlastSomeE
    obtain ⟨r, s, hrs, hsLt, hri, hsj⟩ :=
      filterEl (f := Option.isSome) (vs := vs) (vs' := vs.filter Option.isSome)
        rfl (by omega) hjLt hsomeP hlastSomeP
    have hrVal : vs'[r]? = some (vs[i]!.getD 0) := by
      rw [hvs', List.getElem?_map, ← hri, List.getElem?_eq_getElem hiLt,
        ← getElemBangH hiLt, eqSomeGetD' hsome]
      rfl
    have hsVal : vs'[s]? = some (vs[vs.length - 1]!.getD 0) := by
      rw [hvs', List.getElem?_map, ← hsj, List.getElem?_eq_getElem hjLt,
        ← getElemBangH hjLt, eqSomeGetD' hlastSomeE]
      rfl
    have hsLen : s < vs'.length := by rw [hvs', List.length_map]; exact hsLt
    have hstep : indexf v vs'[r]! f < indexf v vs'[s]! f := by
      have hmonoG : ∀ i, i + 1 < (vs'.map (fun u => indexf v u f)).length →
          (vs'.map (fun u => indexf v u f))[i]! <
            (vs'.map (fun u => indexf v u f))[i + 1]! := by
        intro i hi
        have hi' : i + 1 < vs'.length := by
          rw [List.length_map] at hi; exact hi
        rw [getElemBangMap' (by omega : i < vs'.length), getElemBangMap' hi']
        exact hmono i hi'
      have hb : r + (s - r - 1) + 1 < (vs'.map (fun u => indexf v u f)).length := by
        rw [List.length_map]; omega
      have hstr := strictChain hmonoG (s - r - 1) r hb
      rw [show r + (s - r - 1) + 1 = s from by omega] at hstr
      rwa [getElemBangMap' (by omega : r < vs'.length), getElemBangMap' hsLen] at hstr
    have hrEq : vs'[r]! = vs[i]!.getD 0 := by
      rw [List.getElem!_eq_getElem?_getD, hrVal]; exact Option.getD_some
    have hsEq : vs'[s]! = vs.getLast!.getD 0 := by
      have h2 : vs'[s]! = vs[vs.length - 1]!.getD 0 := by
        rw [List.getElem!_eq_getElem?_getD, hsVal]; exact Option.getD_some
      rw [h2]
      exact congrArg (fun o : Option Nat => o.getD 0)
        (getElemLastEq (l := vs) (by omega))
    rw [hrEq, hsEq] at hstep
    exact hstep.trans_eq hlastIdx
  -- S7b: is 的四槽
  set is : List Nat := (enumOfVertexList f v vs).drop 1 |>.take (vs.length - 2) with his
  have hisLen : is.length = (vs.length - 3) + 1 := by
    rw [his, List.length_take, List.length_drop, hev]; omega
  have hisNe : is ≠ [] := by
    intro hc
    have h0 : is.length = 0 := by rw [hc]; rfl
    rw [hisLen] at h0
    omega
  have hisElem : ∀ q, q < is.length → is[q]! = (enumOfVertexList f v vs)[q + 1]! := by
    intro q hq
    rw [his]
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_take,
      if_pos (by rw [hisLen] at hq; omega), List.getElem?_drop,
      List.getElem!_eq_getElem?_getD]
    simp only [Nat.add_comm 1 q]
  have hisInc : Kepler.Graphs.increasing is := by
    refine increasingOfAdjacent (fun i hi => ?_)
    rw [hisElem i (by omega), hisElem (i + 1) hi]
    exact hmonoE (i + 1) (by rw [hisLen] at hi; omega)
  have hbndEnum : ∀ i, i ≤ vs.length - 2 →
      (enumOfVertexList f v vs)[i]! ≤ f.length - 2 :=
    enumBound (vs := vs) (f := f) (v := v) (r := f.length - 2) (k := vs.length - 2)
      (by omega) (fun _ => by rw [hhd]; simp)
      (fun i hi hso => by
        have h := hstrict i hi hso
        omega)
  have hisBnd : ∀ x ∈ is, x < (f.length - 2) + 1 := by
    intro x hx
    obtain ⟨q, hq, hxq⟩ := List.mem_iff_getElem.mp hx
    have hq1 : q + 1 ≤ vs.length - 2 := by rw [hisLen] at hq; omega
    have h1 := hbndEnum (q + 1) hq1
    have hxq' : is[q]! = x := by
      rw [getElemBangH hq]
      exact hxq
    rw [← hxq', hisElem q hq]
    omega
  -- S8: 三段分解
  have hdropLast : (enumOfVertexList f v vs).drop (vs.length - 1) =
      [(enumOfVertexList f v vs).getLast!] := by
    rw [← hev]
    exact dropLastIsLast (by
      intro hc
      rw [hc] at hev
      rw [List.length_nil] at hev
      omega)
  have hsplit : enumOfVertexList f v vs = [0] ++ is ++ [f.length - 1] := by
    have hene : (enumOfVertexList f v vs) ≠ [] := by
      intro hc
      rw [hc] at hev
      rw [List.length_nil] at hev
      omega
    have h1 : enumOfVertexList f v vs = [(enumOfVertexList f v vs)[0]!] ++
        (enumOfVertexList f v vs).drop 1 := consHeadSplit hene
    have h2 : (enumOfVertexList f v vs).drop 1 = is ++
        [(enumOfVertexList f v vs)[vs.length - 1]!] := by
      rw [his]
      conv_lhs => rw [← List.take_append_drop (vs.length - 2) ((enumOfVertexList f v vs).drop 1)]
      congr 1
      rw [List.drop_drop, show 1 + (vs.length - 2) = vs.length - 1 from by omega,
        hdropLast, show vs.length = (enumOfVertexList f v vs).length from hev.symm,
        getElemLastEq (l := enumOfVertexList f v vs) (by rw [hev]; omega)]
    rw [h1, h2, hhead0, hlast, List.append_assoc]
  -- S9
  rw [Kepler.Graphs.enumerator]
  exact List.mem_map.mpr ⟨is,
    Kepler.Graphs.enumerator_completeness_help (nmax := f.length - 2) (ks := vs.length - 3)
      hisInc hisNe hisLen hisBnd, hsplit.symm⟩

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.getElemBangH
#print axioms Kepler.Text.Reduction1.dropLastIsLast
#print axioms Kepler.Text.Reduction1.showDups0Length'
#print axioms Kepler.Text.Reduction1.getElemBangMap'
#print axioms Kepler.Text.Reduction1.showDups0Head
#print axioms Kepler.Text.Reduction1.getElemLastEq
#print axioms Kepler.Text.Reduction1.strictChain
#print axioms Kepler.Text.Reduction1.consHeadSplit
#print axioms Kepler.Text.Reduction1.eqSomeGetD'
#print axioms Kepler.Text.Reduction1.showDups0LastEq
#print axioms Kepler.Text.Reduction1.enumerationVertexListEnumMem
