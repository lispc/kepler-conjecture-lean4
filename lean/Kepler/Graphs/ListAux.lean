/-
Port of the Isabelle AFP "Flyspeck-Tame" auxiliary list functions used by the
executable graph enumeration.

Source: `reference/afp-flyspeck-tame/ListAux.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).
Only definitions are ported, not lemmas (except `length_removeKeyList`, which is
needed for the termination proof of `ExcessNotAtRec` in `Generator.lean`).

Naming: Isabelle names are kept, snake_case where they already were.
-/
namespace Kepler.Graphs

/-- `ListAux.thy: splitAtRec`. Splits `as` at the first occurrence of `c`,
accumulating the prefix in `bs`. If `c` does not occur, returns `(bs ++ as, [])`. -/
def splitAtRec [BEq α] (c : α) (bs : List α) : List α → List α × List α
  | [] => (bs, [])
  | a :: as => if a == c then (bs, as) else splitAtRec c (bs ++ [a]) as

/-- `ListAux.thy: splitAt`. NB: this splits at the first occurrence of the
*element* `c`; it is NOT Lean's index-based `List.splitAt`. -/
def splitAt [BEq α] (c : α) (as : List α) : List α × List α :=
  splitAtRec c [] as

/-- `ListAux.thy: between`. The vertices strictly between `ram₁` and `ram₂`
when traversing `vs` cyclically from `ram₁`. -/
def between [BEq α] (vs : List α) (ram₁ ram₂ : α) : List α :=
  let (pre₁, post₁) := splitAt ram₁ vs
  if post₁.contains ram₂ then
    let (pre₂, _) := splitAt ram₂ post₁
    pre₂
  else
    let (pre₂, _) := splitAt ram₂ pre₁
    post₁ ++ pre₂

/-- `ListAux.thy: minimal`. The first element of the list minimizing `m`
(on ties the earlier element wins, as in Isabelle's `foldr`-style definition).
Isabelle leaves `minimal m []` unspecified; we return `default` and only ever
call this on nonempty lists (see `Plane1.minimalFace`/`minimalVertex`). -/
def minimal [Inhabited α] (m : α → Nat) : List α → α
  | [] => default
  | x :: xs =>
    if xs.isEmpty then x
    else
      let mxs := minimal m xs
      if m x ≤ m mxs then x else mxs

/-- `ListAux.thy: min_list`. Isabelle leaves `min_list []` unspecified;
we return `0` and only ever call this on nonempty lists. -/
def min_list : List Nat → Nat
  | [] => 0
  | x :: xs => if xs.isEmpty then x else min x (min_list xs)

/-- `ListAux.thy: replace`. Replaces the FIRST occurrence of `x` by the list `ys`. -/
def replace [BEq α] (x : α) (ys : List α) : List α → List α
  | [] => []
  | z :: zs => if z == x then ys ++ zs else z :: replace x ys zs

/-- `ListAux.thy: mapAt`. Applies `f` to the elements at positions `ns`
(indices out of range are skipped). -/
def mapAt : List Nat → (α → α) → List α → List α
  | [], _, as => as
  | n :: ns, f, as =>
    if h : n < as.length then mapAt ns f (as.set n (f as[n]))
    else mapAt ns f as

/-- `ListAux.thy: removeKey`. -/
def removeKey [BEq α] (a : α) (ps : List (α × β)) : List (α × β) :=
  ps.filter (fun p => a != p.1)

/-- `ListAux.thy: removeKeyList`. -/
def removeKeyList [BEq α] : List α → List (α × β) → List (α × β)
  | [], ps => ps
  | w :: ws, ps => removeKey w (removeKeyList ws ps)

/-- `ListAux.thy: length_removeKey` (`[simp]` there). -/
theorem length_removeKey [BEq α] (a : α) (ps : List (α × β)) :
    (removeKey a ps).length ≤ ps.length :=
  List.length_filter_le _ _

/-- `ListAux.thy: length_removeKeyList`. Needed for the termination proof of
`Generator.ExcessNotAtRec`. -/
theorem length_removeKeyList [BEq α] (ws : List α) (ps : List (α × β)) :
    (removeKeyList ws ps).length ≤ ps.length := by
  induction ws generalizing ps with
  | nil => exact Nat.le_refl _
  | cons w ws ih => exact Nat.le_trans (length_removeKey _ _) (ih _)

end Kepler.Graphs
