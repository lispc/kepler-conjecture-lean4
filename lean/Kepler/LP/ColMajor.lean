/-
  Phase 3: column-major (transposed) certificate representation for sparse
  rational LP dual certificates, v2 — tree-indexed dual vector.

  Motivation (see `Cert.lean` header, "Future work"): the row-major checker's
  dominant cost is the column loop `AᵀY ≥ D·c`, where `colDotI` rescans every
  row's support per column — kernel work ~ `numVars × nnz` reductions
  (measured: 25304 s for the 915-var/3882-row/8056-nnz real-graph pilot).
  Storing the constraint matrix **by columns** removes that rescan; the whole
  dual check drops to **O(nnz)** kernel reductions.

  ## Two representation lessons (both measured on toolchain v4.32.2)

  1. *Linked-list indexing is the real enemy.* With `Y : List Int`, each
     sparse entry `(i, a)` pays a `List.getD` walk of `i` cells to fetch
     `Yᵢ`; summed over the pilot's nnz = 8056 entries spread over 3882 rows
     this is ~15M kernel steps, and a naive column-major `decide` did not
     terminate within 1 h. Fix: indexed access goes through a complete
     binary tree (`ITree.getF`, depth-parameterized descent, O(depth) steps);
     the trusted data stays plain lists — the emitted theorems instantiate
     the tree with `ITree.ofList certY d` **inside** the `decide`, so the
      tree exists only transiently during kernel evaluation. Well-formedness
      of the transient tree is part of the checked conjunction
      (`fullB d yt = true`), so soundness needs no side conditions.
      (Measured 2026-08-27 on the 915-var/3882-row/8056-nnz pilot: the
      all-columns dot-product pass is ~169 s — dominated by ~900-bit integer
      reduction at ~11 ms/op, not by tree descent; `bDotTP`'s `s+1` unary
      succ-chain indexing is quadratic and is avoided by the flat
      `checkDualCMTBaseFlat` below.)
   2. *Long list literals elaborate superlinearly* (elaborator whnf /
      pending-mvar synthesis blows up around a few thousand elements or a few
      dozen nested inner lists), and left-nested `++` chains make every kernel
      traversal quadratic (no memoization across repeated head demands).
      Mitigations live on the generator side (`socert.py --col-major`):
     chunked `def`s (≤ 250 items / ≤ 100 columns per declaration) and
     single-pass consumption only.

  ## Certificate layout

  An LP `max cᵀx s.t. A·x ≤ b, x ≥ 0` over the rationals is presented as an
  `LPCM`: `cs` pairs the objective coefficient `cⱼ` with the sparse column
  `Aⱼ` (list of `(row index, coefficient)` pairs, duplicates summed) for each
  variable, and `b` is the dense right-hand side. Sizes are read off the
  lists (`cs.length` variables, `b.length` rows). All checked data stays over
  `Int` (the kernel cannot reduce `Rat`; see `Cert.lean`). A dual certificate
  `(y, γ)` is integerized as `(Y, D, G)` with `y = Y/D`, `γ = G/D`, exactly
  as in `Cert.lean`; `Y` is presented to the checker together with the tree
  depth `d` (any `d` with `2^d ≥ b.length` works).

  All tree accesses are **guard-clamped** at `n = b.length`
  (`ITree.getPad`: positions `≥ n` read as `0`), so the certificate's
  effective dual vector is `padTake` — the `n`-prefix of the flattening,
  zero-padded to `2^d`. Clamping keeps tree padding inert: garbage beyond the
  real rows can neither break soundness nor help the checked inequalities.

  `checkDualCMT` verifies `D > 0`, coverage (`b.length ≤ 2^d`), that `yt` is
  a full depth-`d` tree, well-formedness (row indices `< b.length`),
  `Y ≥ 0` (tree fold), the bound `bᵀY ≤ G`, and the column inequalities
  `∀ j, D·cⱼ ≤ Σ_{(i,a) ∈ cols[j]} a·Yᵢ` — one linear pass over the support,
  no random indexing anywhere.

  ## Soundness is direct weak duality

  `checkDualCMT_sound` proves `Σⱼ cⱼxⱼ ≤ G/D` for every `x ≥ 0` satisfying
  the constraints expressed in terms of the column data themselves
  (`cmRowEval`), by the usual chain
      D·cᵀx = Σⱼ (D·cⱼ)xⱼ ≤ Σⱼ (AᵀY)ⱼxⱼ = Σᵢ Yᵢ(A·x)ᵢ ≤ Σᵢ Yᵢbᵢ = bᵀY ≤ G,
  bridging tree-computed quantities to rational sums through the semantic
  dual vector (`getF_bridge`, `dotCTP_cast`, `bDotTP_cast`). No row-major
  object appears anywhere; the certificate carries its own matrix
  description, so — unlike the remark in `Cert.lean`'s header — there is no
  cross-representation faithfulness condition to discharge. Sharding is
  unnecessary at this scale; `checkDualCMT` is nevertheless a conjunction of
  two independent decidable facts, so generated modules close them by
  separate kernel `decide`s and reassemble term-mode (`checkDualCMT_split`).
 -/
import Kepler.LP.Cert

namespace Kepler.LP

/-! ## Column-major LP data -/

/-- A sparse matrix column: pairs `(row index i, coefficient A_ij)`.
Duplicates are allowed and summed by the `SparseI.get` semantics. -/
abbrev ColI := SparseI

/-- Column-major LP: `max cᵀx s.t. A·x ≤ b, x ≥ 0`, stored as one
`(objective coefficient, sparse column)` pair per variable plus the dense
right-hand side. Sizes are read off the lists (`cs.length` variables,
`b.length` rows); absent entries mean coefficient `0`. -/
structure LPCM where
  /-- per variable: objective coefficient `cⱼ` and the sparse column `Aⱼ` -/
  cs : List (Int × ColI)
  /-- dense right-hand side, one entry per row -/
  b : List Int
deriving Repr

instance : Inhabited LPCM := ⟨⟨[], []⟩⟩

/-- Objective coefficient of variable `j`. -/
def objCoeff (lp : LPCM) (j : ℕ) : Int := (lp.cs.getD j default).1

/-- Column `j` of the constraint matrix (the zero column when absent). -/
def LPCM.col (lp : LPCM) (j : ℕ) : ColI := (lp.cs.getD j default).2

/-- Entry `A_ij` of the matrix described by the column-major data. -/
def cmEntry (lp : LPCM) (i j : ℕ) : Int := (LPCM.col lp j).get i

/-- Rational evaluation of constraint row `i` at `x`: `(A·x)ᵢ = Σⱼ A_ij·xⱼ`. -/
def cmRowEval (lp : LPCM) (i : ℕ) (x : List Rat) : Rat :=
  ∑ j ∈ Finset.range lp.cs.length, ((cmEntry lp i j : Int) : Rat) * x.getD j 0

/-- Rational objective value `cᵀx`. -/
def cmObj (lp : LPCM) (x : List Rat) : Rat :=
  ∑ j ∈ Finset.range lp.cs.length, ((objCoeff lp j : Int) : Rat) * x.getD j 0

/-! ## Helper lemmas about `List.getD` -/

theorem getD_eq_default_of_le {α : Type*} [Inhabited α] :
    ∀ (l : List α) (j : ℕ), l.length ≤ j → l.getD j default = default
  | [], _, _ => rfl
  | _ :: t, j + 1, h => by
      have h' : t.length ≤ j := Nat.le_of_succ_le_succ h
      simpa using getD_eq_default_of_le t j h'

theorem getD_take {α : Type*} :
    ∀ (l : List α) (d : α) (n i : ℕ), i < n →
      (l.take n).getD i d = l.getD i d := by
  intro l d n i hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi,
    List.getD_eq_getElem?_getD]

/-! ## Complete binary trees of ints (kernel-friendly indexed access) -/

/-- Complete binary tree of `Int` leaves. Indexed access `ITree.getF` is
parameterized by the intended depth and descends by index bits, costing
O(depth) kernel steps instead of `List.getD`'s O(index). Malformed shapes
are harmless: they cannot pass `fullB`, which is part of every checked
conjunction. -/
inductive ITree where
  | leaf : Int → ITree
  | node : ITree → ITree → ITree

/-- Is `t` a full binary tree of depth `d` (i.e. exactly `2^d` leaves)? -/
def ITree.fullB : ℕ → ITree → Bool
  | 0, .leaf _ => true
  | 0, .node _ _ => false
  | _ + 1, .leaf _ => false
  | d + 1, .node l r => ITree.fullB d l && ITree.fullB d r

/-- Indexed access by depth-parameterized descent. -/
def ITree.getF : ℕ → ITree → ℕ → Int
  | 0, .leaf v, _ => v
  | 0, .node _ _, i => Int.ofNat i % 2 -- junk shape; rejected by `fullB 0`
  | _ + 1, .leaf v, _ => v             -- junk shape; rejected by `fullB (_+1)`
  | d + 1, .node l r, i =>
    let m := 2 ^ d
    if i < m then ITree.getF d l i else ITree.getF d r (i - m)

/-- Build the full depth-`d` tree holding `l`'s entries (zero-padded; a
longer `l` is truncated). Used only transiently inside `decide`s. -/
def ITree.ofList : List Int → ℕ → ITree
  | l, 0 => .leaf (l.getD 0 0)
  | l, d + 1 =>
    let m := 2 ^ d
    .node (.ofList (l.take m) d) (.ofList (l.drop m) d)

/-- All leaves nonnegative (the `Y ≥ 0` check). -/
def ITree.allPos : ITree → Bool
  | .leaf v => rleI 0 v
  | .node l r => ITree.allPos l && ITree.allPos r

/-- Flattening — used only on the proof side, never in checked computations. -/
def ITree.toList : ITree → List Int
  | .leaf v => [v]
  | .node l r => ITree.toList l ++ ITree.toList r

@[simp] theorem ITree.toList_leaf (v : Int) :
    (ITree.leaf v : ITree).toList = [v] := rfl

@[simp] theorem ITree.toList_node (l r : ITree) :
    (ITree.node l r : ITree).toList = l.toList ++ r.toList := rfl

theorem ITree.fullB_iff_toList_len :
    ∀ (d : ℕ) (t : ITree), ITree.fullB d t = true → t.toList.length = 2 ^ d := by
  intro d
  induction d with
  | zero =>
    intro t hf
    cases t with
    | leaf v =>
      simp only [ITree.fullB] at hf
      simp
    | node l r => simp [ITree.fullB] at hf
  | succ d ih =>
    intro t hf
    cases t with
    | leaf v => simp [ITree.fullB] at hf
    | node l r =>
      simp only [ITree.fullB, Bool.and_eq_true] at hf
      obtain ⟨hl, hr⟩ := hf
      have ihl := ih l hl
      have ihr := ih r hr
      simp only [ITree.toList_node, ihl, ihr, List.length_append, pow_succ]
      omega

/-- **Bridge lemma**: depth-parameterized tree access agrees with `getD` on
the flattened list. -/
theorem ITree.getF_bridge :
    ∀ (d : ℕ) (t : ITree), ITree.fullB d t = true →
      ∀ i, i < 2 ^ d → (t.toList.getD i 0 : Int) = ITree.getF d t i := by
  intro d
  induction d with
  | zero =>
    intro t hf i hi
    cases t with
    | leaf v =>
      simp only [ITree.fullB] at hf
      simp only [pow_zero, Nat.lt_one_iff] at hi
      subst hi
      rfl
    | node l r => simp [ITree.fullB] at hf
  | succ d ih =>
    intro t hf i hi
    cases t with
    | leaf v => simp [ITree.fullB] at hf
    | node l r =>
      simp only [ITree.fullB, Bool.and_eq_true] at hf
      obtain ⟨hl, hr⟩ := hf
      have hll : l.toList.length = 2 ^ d := ITree.fullB_iff_toList_len d l hl
      have hrl : r.toList.length = 2 ^ d := ITree.fullB_iff_toList_len d r hr
      show ((ITree.toList (ITree.node l r)).getD i 0 : Int) =
        (if i < 2 ^ d then ITree.getF d l i else ITree.getF d r (i - 2 ^ d))
      rw [ITree.toList_node]
      rcases Nat.lt_or_ge i (2 ^ d) with hlt | hge
      · have hi' : i < l.toList.length := by omega
        rw [List.getD_append (α := Int) l.toList r.toList 0 i hi', if_pos hlt]
        exact ih l hl i hlt
      · have hni : l.toList.length ≤ i := by omega
        have hin : i - 2 ^ d < 2 ^ d := by
          have := ITree.fullB_iff_toList_len d r hr
          omega
        have hx := List.getD_append_right (α := Int) l.toList r.toList 0 i hni
        rw [hx, if_neg (by omega), hll]
        exact ih r hr (i - 2 ^ d) hin

/-- Positivity transport: a passing `allPos` makes every entry of the
flattened list nonnegative. -/
theorem ITree.allPos_list :
    ∀ (t : ITree), ITree.allPos t = true → ∀ v ∈ t.toList, 0 ≤ v := by
  intro t
  induction t with
  | leaf v =>
    intro h v' hv'
    simp only [ITree.allPos, rleI] at h
    simp only [ITree.toList_leaf, List.mem_singleton] at hv'
    subst hv'
    exact of_decide_eq_true h
  | node l r ihl ihr =>
    intro h v' hv'
    simp only [ITree.allPos, Bool.and_eq_true] at h
    simp only [ITree.toList_node, List.mem_append] at hv'
    rcases hv' with hmem | hmem
    · exact ihl h.1 v' hmem
    · exact ihr h.2 v' hmem

/-! ## Checked computations against the tree

All accesses are **guard-clamped** at `n = b.length`: positions `≥ n` read
as `0`, so tree padding beyond the real rows is inert — the certificate's
effective dual vector is `padTake`, the `n`-prefix of the flattening
zero-padded to `2^d`. Without clamping, nonzero padding leaves could break
the weak-duality chain on phantom rows. -/

/-- Guarded access: positions `≥ n` read as `0`. -/
def ITree.getPad (d : ℕ) (t : ITree) (n : ℕ) (i : ℕ) : Int :=
  if i < n then ITree.getF d t i else 0

/-- Semantic dual vector: `ITree.getPad` evaluated on the index range
`0…2^d-1`, as a list (proof side only). -/
def padTake (d n : ℕ) (t : ITree) : List Int :=
  (List.range (2 ^ d)).map fun i => ITree.getPad d t n i

theorem padTake_len (d n : ℕ) (t : ITree) :
    (padTake d n t).length = 2 ^ d := by
  simp [padTake, List.length_map, List.length_range]

theorem mapRange_getD {α : Type*} :
    ∀ (m : ℕ) (f : ℕ → α) (d : α) (i : ℕ), i < m →
      (List.map f (List.range m)).getD i d = f i := by
  intro m
  induction m with
  | zero => intro f d i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ m ih =>
    intro f d i hi
    have hlen : (List.map f (List.range m)).length = m := by
      simp [List.length_map, List.length_range]
    rw [List.range_succ, List.map_append]
    rcases Nat.lt_or_ge i m with hlt | hge
    · have hx1 : (List.map f (List.range m) ++ List.map f [m]).getD i d =
        (List.map f (List.range m)).getD i d :=
        List.getD_append _ _ _ i (by rw [hlen]; exact hlt)
      rw [hx1, ih f d i hlt]
    · have him : i = m := by omega
      have hx2 : (List.map f (List.range m) ++ List.map f [m]).getD i d =
          (List.map f [m]).getD (i - (List.map f (List.range m)).length) d :=
        List.getD_append_right _ _ _ i (by rw [him, hlen])
      rw [hx2, him, hlen, Nat.sub_self, List.map_cons, List.map_nil,
        List.getD_cons_zero]

theorem padTake_get (d n : ℕ) (t : ITree) (i : ℕ) (hi : i < 2 ^ d) :
    (padTake d n t).getD i 0 = ITree.getPad d t n i := by
  rw [padTake, mapRange_getD _ _ 0 i hi]

/-- Guarded access agrees with the semantic dual vector everywhere. -/
theorem getPad_eq (d n : ℕ) (t : ITree)
    (hf : ITree.fullB d t = true) (hn : n ≤ 2 ^ d) (i : ℕ) :
    ITree.getPad d t n i = (padTake d n t).getD i 0 := by
  rcases Nat.lt_or_ge i (2 ^ d) with h2 | h2
  · rw [padTake_get d n t i h2]
  · rw [ITree.getPad, if_neg (by omega)]
    exact Eq.symm (getD_eq_default_of_le (α := Int) (padTake d n t) i
      (by rw [padTake_len]; exact h2))

/-- Sparse column times tree-held dual vector: `Σ_{(i,a) ∈ col} a·Yᵢ`
(padding clamped to zero). -/
def dotCTP (d : ℕ) (n : ℕ) (col : ColI) (t : ITree) : Int :=
  col.foldr (fun p acc => p.2 * ITree.getPad d t n p.1 + acc) 0

/-- Dense right-hand side times tree-held dual vector: `Σᵢ bᵢ·Yᵢ`
(single index-threaded pass, padding clamped to zero). -/
def bDotTP (d n : ℕ) (b : List Int) (t : ITree) (s : ℕ) : Int :=
  match b with
  | [] => 0
  | x :: bs => x * ITree.getPad d t n s + bDotTP d n bs t (s + 1)

/-- Everything except the column loop. -/
def checkDualCMTBase (lp : LPCM) (d : ℕ) (yt : ITree) (D : ℕ) (G : Int) : Bool :=
  decide (0 < D) &&
  decide (lp.b.length ≤ 2 ^ d) &&
  decide (ITree.fullB d yt = true) &&
  lp.cs.all (fun p => SparseI.wf p.2 lp.b.length) &&
  ITree.allPos yt &&
  rleI (bDotTP d lp.b.length lp.b yt 0) G

/-- The column inequalities `D·cⱼ ≤ (AᵀY)ⱼ`: one linear pass over the
support — this is the whole point of the transposed layout. -/
def checkDualCMTCols (lp : LPCM) (d : ℕ) (yt : ITree) (D : ℕ) : Bool :=
  lp.cs.all (fun p => rleI ((D : Int) * p.1) (dotCTP d lp.b.length p.2 yt))

/-- Dual certificate checker for the integerized certificate `(Y, D, G)`
representing the rational dual `y = Y/D` and claimed bound `γ = G/D`;
`yt` is the transient tree holding `Y` (`ITree.ofList certY d`). -/
def checkDualCMT (lp : LPCM) (d : ℕ) (yt : ITree) (D : ℕ) (G : Int) : Bool :=
  checkDualCMTBase lp d yt D G && checkDualCMTCols lp d yt D

/-- Term-mode reassembly of the two independent checked facts. -/
theorem checkDualCMT_split {lp : LPCM} {d : ℕ} {yt : ITree} {D : ℕ} {G : Int}
    (hb : checkDualCMTBase lp d yt D G = true)
    (hc : checkDualCMTCols lp d yt D = true) :
    checkDualCMT lp d yt D G = true :=
  Bool.and_eq_true_iff.mpr ⟨hb, hc⟩

/-! ## Bridges from the checked layer to rational semantics -/

/-- Casting the column·tree product yields the sparse dot product against
the semantic dual vector. -/
theorem dotCTP_cast (d n : ℕ) (t : ITree)
    (hf : ITree.fullB d t = true) (hn : n ≤ 2 ^ d) :
    ∀ col : ColI, (∀ p ∈ col, p.1 < n) →
      (dotCTP d n col t : Rat) = SparseI.dotRat col (castL (padTake d n t)) := by
  intro col
  induction col with
  | nil => intro _; rfl
  | cons p col ih =>
    intro hwf
    obtain ⟨k, a⟩ := p
    have hk : k < n := hwf (k, a) List.mem_cons_self
    have hwf' : ∀ q ∈ col, q.1 < n :=
      fun q hq => hwf q (List.mem_cons_of_mem _ hq)
    have hbk : ITree.getPad d t n k = t.toList.getD k 0 := by
      rw [ITree.getPad, if_pos hk]
      exact (ITree.getF_bridge d t hf k (lt_of_lt_of_le hk hn)).symm
    have hto : (castL (padTake d n t)).getD k 0 =
        ((t.toList.getD k 0 : Int) : Rat) := by
      simp only [castL, getD_map' (f := Int.cast) (dα := 0) (dβ := 0)
        Int.cast_zero]
      rw [padTake_get d n t k (lt_of_lt_of_le hk hn), ITree.getPad, if_pos hk,
        ← ITree.getF_bridge d t hf k (lt_of_lt_of_le hk hn)]
    show ((a * ITree.getPad d t n k + dotCTP d n col t : Int) : Rat) = _
    rw [Int.cast_add, Int.cast_mul, ih hwf', hbk]
    simp only [SparseI.dotRat, List.foldr_cons, hto]

/-- Casting the rhs·tree product yields the dense pairwise sum against the
semantic dual vector. -/
theorem bDotTP_cast (d n : ℕ) (t : ITree) (hf : ITree.fullB d t = true)
    (hn : n ≤ 2 ^ d) :
    ∀ (b : List Int) (s : ℕ), s + b.length ≤ n →
      ((bDotTP d n b t s : Int) : Rat) =
        ∑ k ∈ Finset.range b.length,
          (((b.getD k 0 : Int) : Rat)) *
            ((((padTake d n t).getD (s + k) 0 : Int) : Rat)) := by
  intro b
  induction b with
  | nil => intro s _; rfl
  | cons x bs ih =>
    intro s hs
    have hlen : (x :: bs).length = bs.length + 1 := rfl
    have hs' : s + 1 + bs.length ≤ n := by
      have h1 : s + (bs.length + 1) ≤ n := by rw [← hlen]; exact hs
      omega
    show (((x * ITree.getPad d t n s + bDotTP d n bs t (s + 1) : Int)) : Rat) = _
    rw [Int.cast_add, Int.cast_mul, ih (s + 1) hs']
    rw [getPad_eq d n t hf hn s]
    rw [hlen, Finset.sum_range_succ']
    simp only [List.getD_cons_zero, Nat.add_zero]
    -- LHS: ↑x·↑pad(s) + ∑ fn(k);  RHS: ∑ fn'(k+1) + ↑x·↑pad(s)
    have hsum : ∀ k ∈ Finset.range bs.length,
        (((bs.getD k 0 : Int) : Rat)) *
          (((padTake d n t).getD (s + 1 + k) 0 : Int) : Rat) =
        (((x :: bs).getD (k + 1) 0 : Int) : Rat) *
          (((padTake d n t).getD (s + (k + 1)) 0 : Int) : Rat) := by
      intro k hkmem
      have hk1 : (s + 1) + k < n := by
        have h5 := Finset.mem_range.mp hkmem
        omega
      have hb2 : (padTake d n t).getD ((s + 1) + k) 0 =
          ITree.getPad d t n ((s + 1) + k) :=
        padTake_get d n t ((s + 1) + k) (by have := hn; omega)
      have hidx : s + (k + 1) = s + 1 + k := by omega
      rw [List.getD_cons_succ, hidx, hb2]
    rw [Finset.sum_congr rfl hsum, add_comm]

/-! ## Soundness (direct weak duality) -/

/-- **Soundness of the column-major dual checker (weak duality).**
A passing integerized certificate `(Y, D, G)` bounds the objective value of
every rational primal-feasible point by `G/D`. Feasibility is stated purely
in terms of the column data (`cmRowEval`); no row-major object appears. -/
theorem checkDualCMT_sound (lp : LPCM) (d : ℕ) (yt : ITree) (D : ℕ) (G : Int)
    (h : checkDualCMT lp d yt D G = true) (x : List Rat)
    (hxlen : x.length = lp.cs.length)
    (hx0 : ∀ j < lp.cs.length, 0 ≤ x.getD j 0)
    (hxrows : ∀ i < lp.b.length, cmRowEval lp i x ≤ (lp.b.getD i 0 : Rat)) :
    cmObj lp x ≤ (G : Rat) / (D : Rat) := by
  simp only [checkDualCMT, checkDualCMTBase, checkDualCMTCols, Bool.and_eq_true,
    List.all_eq_true, SparseI.wf] at h
  obtain ⟨⟨⟨⟨⟨⟨hD, hcov⟩, hfull⟩, hwf⟩, hpos⟩, hbT⟩, hcols⟩ := h
  have hD' : 0 < D := of_decide_eq_true hD
  have hn : lp.b.length ≤ 2 ^ d := of_decide_eq_true hcov
  have hfull : ITree.fullB d yt = true := of_decide_eq_true hfull
  have hflen : yt.toList.length = 2 ^ d :=
    ITree.fullB_iff_toList_len d yt hfull
  have htlen : (padTake d lp.b.length yt).length = 2 ^ d := padTake_len _ _ _
  have hclen : (castL (padTake d lp.b.length yt)).length = 2 ^ d := by
    simp only [castL, List.length_map, htlen]
  have hgetD : ∀ i : ℕ, (castL (padTake d lp.b.length yt)).getD i 0 =
      (((padTake d lp.b.length yt).getD i 0 : Int) : Rat) := fun i => by
    simp only [castL]
    exact getD_map' (f := Int.cast) (dα := 0) (dβ := 0) Int.cast_zero _ _
  have hY0' : ∀ i < 2 ^ d, 0 ≤ ((padTake d lp.b.length yt).getD i 0 : Rat) := by
    intro i hi
    rw [padTake_get d lp.b.length yt i hi]
    rcases Nat.lt_or_ge i lp.b.length with hlt | hge
    · show (0 : Rat) ≤ ((ITree.getPad d yt lp.b.length i : Int) : Rat)
      have hmem : yt.toList.getD i 0 ∈ yt.toList :=
        getD_mem_of_lt (by rw [hflen]; exact hi)
      rw [ITree.getPad, if_pos hlt,
        ← ITree.getF_bridge d yt hfull i hi]
      exact Int.cast_nonneg (ITree.allPos_list yt hpos _ hmem)
    · show (0 : Rat) ≤ ((ITree.getPad d yt lp.b.length i : Int) : Rat)
      rw [ITree.getPad, if_neg (by omega)]
      norm_num
  -- well-formedness transported through the accessors
  have hpwf : ∀ (j : ℕ) (p : ℕ × Int), p ∈ lp.col j → p.1 < lp.b.length := by
    intro j p hp
    by_cases hj : j < lp.cs.length
    · have hmem : lp.cs.getD j default ∈ lp.cs := getD_mem_of_lt hj
      exact of_decide_eq_true (hwf (lp.cs.getD j default) hmem p hp)
    · exfalso
      have hnil : lp.col j = ([] : ColI) := by
        show (lp.cs.getD j default).2 = []
        rw [getD_eq_default_of_le _ _ (Nat.not_lt.mp hj)]
        rfl
      rw [hnil] at hp
      cases hp
  have hpwf' : ∀ (j : ℕ) (p : ℕ × Int), p ∈ lp.col j →
      p.1 < (castL (padTake d lp.b.length yt)).length := by
    intro j p hp
    have h2 := hpwf j p hp
    rw [hclen]
    exact lt_of_lt_of_le h2 hn
  -- checked facts, per column
  have hcolI : ∀ j < lp.cs.length,
      (D : Int) * objCoeff lp j ≤ dotCTP d lp.b.length (lp.col j) yt := by
    intro j hj
    have hmem : lp.cs.getD j default ∈ lp.cs := getD_mem_of_lt hj
    exact rleI_true (hcols (lp.cs.getD j default) hmem)
  have hx0' : ∀ j < x.length, 0 ≤ x.getD j 0 :=
    fun j hj => hx0 j (by rwa [hxlen] at hj)
  have key : (D : Rat) * cmObj lp x ≤ (G : Rat) := by
    calc (D : Rat) * cmObj lp x
        = ∑ j ∈ Finset.range x.length,
            (((D : Int) * objCoeff lp j : Int) : Rat) * x.getD j 0 := by
          rw [hxlen, cmObj, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          push_cast
          ring
      _ ≤ ∑ j ∈ Finset.range x.length,
            ((dotCTP d lp.b.length (lp.col j) yt : Int) : Rat) * x.getD j 0 := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hjx : j < x.length := Finset.mem_range.mp hj
          have hjn : j < lp.cs.length := by rw [← hxlen]; exact hjx
          exact mul_le_mul_of_nonneg_right (Int.cast_le.mpr (hcolI j hjn))
            (hx0' j hjx)
      _ = ∑ j ∈ Finset.range x.length,
            (SparseI.dotRat (lp.col j) (castL (padTake d lp.b.length yt))) *
              x.getD j 0 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [dotCTP_cast d lp.b.length yt hfull hn (lp.col j) (hpwf j)]
      _ = ∑ j ∈ Finset.range x.length,
            (∑ i ∈ Finset.range (castL (padTake d lp.b.length yt)).length,
              (((lp.col j).get i : Int) : Rat) *
                (castL (padTake d lp.b.length yt)).getD i 0) *
              x.getD j 0 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [SparseI.dotRat_eq_sum (lp.col j)
            (castL (padTake d lp.b.length yt)) (hpwf' j)]
      _ = ∑ j ∈ Finset.range x.length,
            ∑ i ∈ Finset.range (castL (padTake d lp.b.length yt)).length,
              ((((lp.col j).get i : Int) : Rat) *
                (castL (padTake d lp.b.length yt)).getD i 0) *
                x.getD j 0 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          exact Finset.sum_mul _ _ _
      _ = ∑ i ∈ Finset.range (castL (padTake d lp.b.length yt)).length,
            ∑ j ∈ Finset.range x.length,
              ((((lp.col j).get i : Int) : Rat) *
                (castL (padTake d lp.b.length yt)).getD i 0) *
                x.getD j 0 :=
          Finset.sum_comm
      _ = ∑ i ∈ Finset.range (castL (padTake d lp.b.length yt)).length,
            ((castL (padTake d lp.b.length yt)).getD i 0) *
              ∑ j ∈ Finset.range x.length,
                (((lp.col j).get i : Int) : Rat) * x.getD j 0 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = ∑ i ∈ Finset.range (castL (padTake d lp.b.length yt)).length,
            ((castL (padTake d lp.b.length yt)).getD i 0) * cmRowEval lp i x := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hxlen]
          rfl
      _ ≤ ∑ i ∈ Finset.range (castL (padTake d lp.b.length yt)).length,
            (((padTake d lp.b.length yt).getD i 0 : Int) : Rat) *
              (lp.b.getD i 0 : Rat) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hid : i < (castL (padTake d lp.b.length yt)).length :=
            Finset.mem_range.mp hi
          have hid2 : i < 2 ^ d := by rwa [hclen] at hid
          rcases Nat.lt_or_ge i lp.b.length with hlt | hge
          · rw [hgetD i, padTake_get d lp.b.length yt i hid2,
              ITree.getPad, if_pos hlt, ← ITree.getF_bridge d yt hfull i hid2]
            have hmem : yt.toList.getD i 0 ∈ yt.toList :=
              getD_mem_of_lt (by rw [hflen]; exact hid2)
            exact mul_le_mul_of_nonneg_left (hxrows i hlt)
              (Int.cast_nonneg (ITree.allPos_list yt hpos _ hmem))
          · rw [hgetD i, padTake_get d lp.b.length yt i hid2,
              ITree.getPad, if_neg (by omega)]
            norm_num
      _ = ((bDotTP d lp.b.length lp.b yt 0 : Int) : Rat) := by
          have hbcast := bDotTP_cast d lp.b.length yt hfull hn lp.b 0 (by omega)
          rw [hbcast]
          rw [hclen, show (2 ^ d) = lp.b.length + (2 ^ d - lp.b.length) from by omega,
            Finset.sum_range_add]
          have hpad : ∀ i ∈ Finset.range (2 ^ d - lp.b.length),
              (((padTake d lp.b.length yt).getD (lp.b.length + i) 0 : Int) : Rat) *
                ((lp.b.getD (lp.b.length + i) 0 : Int) : Rat) = 0 := by
            intro i himem
            have him : i < 2 ^ d - lp.b.length := Finset.mem_range.mp himem
            have hi2 : lp.b.length + i < 2 ^ d := by omega
            rw [padTake_get d lp.b.length yt (lp.b.length + i) hi2,
              ITree.getPad, if_neg (by omega)]
            norm_num
          rw [Finset.sum_eq_zero hpad, add_zero]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Nat.zero_add]
          exact mul_comm _ _
      _ ≤ (G : Rat) := Int.cast_le.mpr (rleI_true hbT)
  have hDpos : (0 : Rat) < (D : Rat) := Nat.cast_pos.mpr hD'
  rw [le_div_iff₀ hDpos]
  rwa [mul_comm] at key

/-! ## Flat (lockstep) base checker — avoids the tree-index bottleneck

The tree-indexed `bDotTP` costs O(depth) per access, and threading `s+1`
through the recursion builds a unary `Nat.succ` chain that makes each
`getPad` comparison O(s): the whole `bᵀY` pass becomes quadratic in the
number of rows (measured ~146 s on the 3882-row pilot).  The dual vector
is available as a plain list, so `bᵀY` is just the lockstep dense product
`dotLI b certY` (O(n), no indexing).  `checkDualCMTBaseFlat` presents the
base conjuncts against the flat vector; it is a strengthening of the
tree-indexed base on the transient tree `ITree.ofList certY d`, so
soundness reuses `checkDualCMT_sound` verbatim via
`checkDualCMTBaseFlat_implies_tree`.  The column loop still uses the tree
(`dotCTP`), whose sparse entries carry *literal* row indices — no unary-chain
buildup there. -/


theorem getD_drop_zero (l : List Int) (s : ℕ) :
    (l.drop s).getD 0 0 = l.getD s 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rw [List.getElem?_drop]
  rfl

theorem drop_cons_of_lt : ∀ (l : List Int) (s : ℕ), s < l.length →
    l.drop s = l.getD s 0 :: l.drop (s + 1) := by
  intro l
  induction l with
  | nil =>
    intro s hs
    simp at hs
  | cons y ys ih =>
    intro s
    cases s with
    | zero =>
      intro hs
      simp
    | succ s =>
      intro hs
      have hs' : s < ys.length := by simpa using hs
      have hrec := ih s hs'
      have hget : (y :: ys).getD (s + 1) 0 = ys.getD s 0 := by
        rw [List.getD_cons_succ]
      rw [List.drop_succ_cons]
      rw [hget, hrec]
      rfl

theorem getD_take_eq (l : List Int) (n i : ℕ) (hi : i < n) :
    (l.take n).getD i 0 = l.getD i 0 := by
  exact getD_take l 0 n i hi

theorem getD_drop_eq (l : List Int) (m i : ℕ) (hm : m ≤ i) :
    (l.drop m).getD (i - m) 0 = l.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rw [List.getElem?_drop]
  have h : m + (i - m) = i := Nat.add_sub_cancel' hm
  rw [h]

theorem getF_ofList (d : ℕ) (certY : List Int) (i : ℕ) (hi : i < 2 ^ d) :
    ITree.getF d (ITree.ofList certY d) i = certY.getD i 0 := by
  induction d generalizing certY i with
  | zero =>
    simp only [ITree.ofList, ITree.getF, pow_zero] at hi ⊢
    cases i with
    | zero => rfl
    | succ i => simp at hi
  | succ d ih =>
    have him : i < 2 ^ (d + 1) := hi
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by omega
    rcases Nat.lt_or_ge i (2 ^ d) with hlt | hge
    · simp only [ITree.ofList, ITree.getF, if_pos hlt]
      rw [ih (certY.take (2 ^ d)) i hlt]
      exact getD_take_eq certY (2 ^ d) i hlt
    · have hsub : i - 2 ^ d < 2 ^ d := by
        have hi' : i < 2 ^ d + 2 ^ d := by simpa [hpow] using him
        omega
      simp only [ITree.ofList, ITree.getF, if_neg (not_lt_of_ge hge)]
      rw [ih (certY.drop (2 ^ d)) (i - 2 ^ d) hsub]
      exact getD_drop_eq certY (2 ^ d) i hge

theorem getPad_ofList (d n : ℕ) (certY : List Int) (i : ℕ) (hi : i < n)
    (hco : n ≤ 2 ^ d) :
    ITree.getPad d (ITree.ofList certY d) n i = certY.getD i 0 := by
  rw [ITree.getPad, if_pos hi]
  exact getF_ofList d certY i (lt_of_lt_of_le hi hco)

theorem bDotTP_drop_eq (d n : ℕ) (certY : List Int) (b : List Int) (s : ℕ)
    (hs : s + b.length = n) (hco : n ≤ 2 ^ d) (hc : n = certY.length) :
    bDotTP d n b (ITree.ofList certY d) s = dotLI b (certY.drop s) := by
  revert s
  induction b with
  | nil =>
    intro s hs
    simp [bDotTP, dotLI]
  | cons x bs ih =>
    intro s hs
    have hs_lt : s < n := by
      have hsbl : s + (bs.length + 1) = n := by simpa using hs
      omega
    have hs_len : s < certY.length := by rwa [← hc]
    have hds : certY.drop s = certY.getD s 0 :: certY.drop (s + 1) :=
      drop_cons_of_lt certY s hs_len
    have hs' : (s + 1) + bs.length = n := by
      have hsbl : s + (bs.length + 1) = n := by simpa using hs
      omega
    rw [show bDotTP d n (x :: bs) (ITree.ofList certY d) s =
        x * ITree.getPad d (ITree.ofList certY d) n s + bDotTP d n bs (ITree.ofList certY d) (s + 1) by rfl]
    rw [getPad_ofList d n certY s hs_lt hco]
    rw [hds]
    rw [show dotLI (x :: bs) (certY.getD s 0 :: certY.drop (s + 1)) =
        x * certY.getD s 0 + dotLI bs (certY.drop (s + 1)) by rfl]
    have hrec := ih (s + 1) hs'
    rw [hrec]

theorem bDotTP_ofList_eq (d n : ℕ) (certY : List Int) (b : List Int)
    (h : b.length = n) (hco : n ≤ 2 ^ d) (hc : n = certY.length) :
    bDotTP d n b (ITree.ofList certY d) 0 = dotLI b certY := by
  rw [bDotTP_drop_eq d n certY b 0 (by simpa using h) hco hc]
  simp

theorem ofList_fullB (d : ℕ) (l : List Int) :
    ITree.fullB d (ITree.ofList l d) = true := by
  induction d generalizing l with
  | zero => simp [ITree.ofList, ITree.fullB]
  | succ d ih =>
    simp only [ITree.ofList, ITree.fullB, ih, Bool.and_self]

theorem allPos_ofList (d : ℕ) (certY : List Int)
    (h : certY.all (fun v => rleI 0 v) = true) :
    ITree.allPos (ITree.ofList certY d) = true := by
  induction d generalizing certY with
  | zero =>
    simp only [ITree.ofList, ITree.allPos]
    by_cases hlen : certY.length = 0
    · have hd : certY.getD 0 0 = 0 := by
        simpa using (getD_eq_default_of_le (α := Int) certY 0 (by simpa using hlen))
      rw [hd]
      rfl
    · have hlt : 0 < certY.length := Nat.pos_of_ne_zero hlen
      have hmem : certY.getD 0 0 ∈ certY := getD_mem_of_lt hlt
      exact (List.all_eq_true.mp h (certY.getD 0 0) hmem)
  | succ d ih =>
    simp only [ITree.ofList, ITree.allPos, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · apply ih
      rw [List.all_eq_true]
      intro v hv
      exact List.all_eq_true.mp h v (List.mem_of_mem_take hv)
    · apply ih
      rw [List.all_eq_true]
      intro v hv
      exact List.all_eq_true.mp h v (List.mem_of_mem_drop hv)


/-! ## Flat (lockstep) base checker — avoids the tree-index bottleneck

The tree-indexed `bDotTP` costs O(depth) per access, and threading `s+1`
through the recursion builds a unary `Nat.succ` chain that makes each
`getPad` comparison O(s): the whole `bᵀY` pass becomes quadratic in the
number of rows (measured ~146 s on the 3882-row pilot).  The dual vector
is available as a plain list, so `bᵀY` is just the lockstep dense product
`dotLI b certY` (O(n), no indexing).  `checkDualCMTBaseFlat` presents the
base conjuncts against the flat vector; it is a strengthening of the
tree-indexed base on the transient tree `ITree.ofList certY d`, so
soundness reuses `checkDualCMT_sound` verbatim via
`checkDualCMTBaseFlat_implies_tree`.  The column loop still uses the tree
(`dotCTP`), whose sparse entries carry *literal* row indices — no unary-chain
buildup there. -/

/-- Flat base checker: `D > 0`, sizes, coverage, well-formedness,
`certY ≥ 0` (flat), and the lockstep bound `bᵀcertY ≤ G`. -/
def checkDualCMTBaseFlat (lp : LPCM) (d : ℕ) (certY : List Int) (D : ℕ) (G : Int) : Bool :=
  decide (0 < D) &&
  decide (certY.length = lp.b.length) &&
  decide (lp.b.length ≤ 2 ^ d) &&
  lp.cs.all (fun p => SparseI.wf p.2 lp.b.length) &&
  certY.all (fun v => rleI 0 v) &&
  rleI (dotLI lp.b certY) G

/-- Full flat-base checker: `checkDualCMTBaseFlat` + the tree column loop. -/
def checkDualCMTF (lp : LPCM) (d : ℕ) (yt : ITree) (certY : List Int) (D : ℕ) (G : Int) : Bool :=
  checkDualCMTBaseFlat lp d certY D G && checkDualCMTCols lp d yt D

/-- Term-mode reassembly for the flat checker. -/
theorem checkDualCMTF_split {lp : LPCM} {d : ℕ} {yt : ITree} {certY : List Int}
    {D : ℕ} {G : Int}
    (hb : checkDualCMTBaseFlat lp d certY D G = true)
    (hc : checkDualCMTCols lp d yt D = true) :
    checkDualCMTF lp d yt certY D G = true :=
  Bool.and_eq_true_iff.mpr ⟨hb, hc⟩

/-- The flat base implies the tree-indexed base on the `ofList` tree. -/
theorem checkDualCMTBaseFlat_implies_tree (lp : LPCM) (d : ℕ) (certY : List Int)
    (D : ℕ) (G : Int) (h : checkDualCMTBaseFlat lp d certY D G = true) :
    checkDualCMTBase lp d (ITree.ofList certY d) D G = true := by
  simp only [checkDualCMTBaseFlat, Bool.and_eq_true] at h
  rcases h with ⟨h1, hbT⟩
  rcases h1 with ⟨h2, hpos⟩
  rcases h2 with ⟨h3, hwf⟩
  rcases h3 with ⟨h4, hcov⟩
  rcases h4 with ⟨hD, hlen⟩
  simp only [checkDualCMTBase, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨hD, hcov⟩, (ofList_fullB d certY).symm ▸ by decide⟩, hwf⟩,
    allPos_ofList d certY hpos⟩, ?_⟩
  have hlenb : lp.b.length = certY.length := by
    rw [← of_decide_eq_true hlen]
  have hb' : rleI (bDotTP d lp.b.length lp.b (ITree.ofList certY d) 0) G = true := by
    rw [bDotTP_ofList_eq d lp.b.length certY lp.b (by rfl) (of_decide_eq_true hcov) hlenb]
    exact hbT
  exact hb'

/-- **Soundness of the flat-base column-major checker (weak duality).**
A passing integerized certificate `(Y, D, G)` bounds the objective value of
every rational primal-feasible point by `G/D`, with `Y` presented as a flat
list and the column loop using the transient tree `yt = ITree.ofList Y d`.
Reduces to `checkDualCMT_sound` on the same tree. -/
theorem checkDualCMTF_sound (lp : LPCM) (d : ℕ) (certY : List Int)
    (D : ℕ) (G : Int) (h : checkDualCMTF lp d (ITree.ofList certY d) certY D G = true)
    (x : List Rat) (hxlen : x.length = lp.cs.length)
    (hx0 : ∀ j < lp.cs.length, 0 ≤ x.getD j 0)
    (hxrows : ∀ i < lp.b.length, cmRowEval lp i x ≤ (lp.b.getD i 0 : Rat)) :
    cmObj lp x ≤ (G : Rat) / (D : Rat) := by
  have hsplit : checkDualCMTBaseFlat lp d certY D G = true ∧
      checkDualCMTCols lp d (ITree.ofList certY d) D = true := by
    simpa [checkDualCMTF] using (Bool.and_eq_true_iff.mp (by simpa [checkDualCMTF] using h))
  have hb : checkDualCMTBase lp d (ITree.ofList certY d) D G = true :=
    checkDualCMTBaseFlat_implies_tree lp d certY D G hsplit.1
  exact checkDualCMT_sound lp d (ITree.ofList certY d) D G
    (Bool.and_eq_true_iff.mpr ⟨hb, hsplit.2⟩) x hxlen hx0 hxrows

/-! ## Small pilot case (kernel `decide` only)

`exLP` from `Cert.lean` (max x+y s.t. 2x+y ≤ 4, x+2y ≤ 5) transposed by hand:
columns paired with objective coefficients, `b = [4, 5]`, tight integerized
certificate `(Y, D, G) = ([1,1], 3, 9)`, transient tree depth 2. Locks the
column-major API end-to-end, including the two-decide decomposition and the
padding-inertness guarantee. -/

def exCM : LPCM where
  cs := [(1, [(0, 2), (1, 1)]), (1, [(0, 1), (1, 2)])]
  b := [4, 5]

/-- Tree unit test: `ofList` pads with zeros. -/
theorem exTree_get : ITree.getF 2 (ITree.ofList [7, 8] 2) 3 = 0 := by decide

/-- Tree unit test: entries land at their indices. -/
theorem exTree_get2 : ITree.getF 2 (ITree.ofList [7, 8, 0, 0] 2) 1 = 8 := by decide

/-- Tree unit test: flattening round-trips. -/
theorem exTree_flat : (ITree.ofList [7, 8] 2).toList = [7, 8, 0, 0] := by decide

/-- The kernel re-checks the tight integerized dual certificate
(`certY = [1,1]` presented as the transient depth-2 tree). -/
theorem exCM_dual_check : checkDualCMT exCM 2 (ITree.ofList [1, 1] 2) 3 9 = true :=
  by decide

/-- Padding is inert: garbage in the tree beyond the real rows does not
change the verdict. -/
theorem exCM_pad_inert :
    checkDualCMT exCM 3
      (ITree.ofList [1, 1, 97, 98, 99, 100, 101, 102] 3) 3 9 = true := by
  decide

/-- End-to-end: every rational-feasible point of `exCM` has objective ≤ 3. -/
theorem exCM_bound (x : List Rat) (hxlen : x.length = exCM.cs.length)
    (hx0 : ∀ j < exCM.cs.length, 0 ≤ x.getD j 0)
    (hxrows : ∀ i < exCM.b.length, cmRowEval exCM i x ≤ (exCM.b.getD i 0 : Rat)) :
    cmObj exCM x ≤ 3 := by
  have h := checkDualCMT_sound exCM 2 (ITree.ofList [1, 1] 2) 3 9 exCM_dual_check
    x hxlen hx0 hxrows
  rwa [show ((9 : Int) : Rat) / ((3 : ℕ) : Rat) = 3 by norm_num] at h

/-- A claimed bound below the dual value is rejected (`bᵀ(1,1) = 9 > 8`). -/
theorem exCM_bad_bound :
    checkDualCMT exCM 2 (ITree.ofList [1, 1] 2) 3 8 = false := by decide

/-- A dual violating `AᵀY ≥ D·c` is rejected (column 1: `1 < 3`). -/
theorem exCM_bad_dual :
    checkDualCMT exCM 2 (ITree.ofList [1, 0] 2) 3 9 = false := by decide

/-- A dual with a negative component is rejected. -/
theorem exCM_neg_check :
    checkDualCMT exCM 2 (ITree.ofList [1, -1] 2) 3 9 = false := by decide

/-- `D = 0` is rejected. -/
theorem exCM_zero_D :
    checkDualCMT exCM 2 (ITree.ofList [1, 1] 2) 0 9 = false := by decide

/-- A corrupted column (coefficient `1` instead of `2`) is rejected:
column 0 then gives `AᵀY ≥ 3·c` violated (`1 + 1 < 3`). -/
theorem exCM_corrupt :
    checkDualCMT
      { exCM with cs := [(1, [(0, 1), (1, 1)]), (1, [(0, 1), (1, 2)])] }
      2 (ITree.ofList [1, 1] 2) 3 9 = false := by decide

/-- An ill-shaped transient tree is rejected (`fullB` guard). -/
theorem exCM_bad_tree :
    checkDualCMT exCM 2 (ITree.node (ITree.leaf 1) (ITree.leaf 1)) 3 9
      = false := by
  decide

/-- Insufficient depth (coverage `b.length ≤ 2^d` fails) is rejected. -/
theorem exCM_shallow :
    checkDualCMT { exCM with b := [4, 5, 6] } 1 (ITree.ofList [1, 1] 1) 3 9
      = false := by decide

/-! ### The flat-base checker on the same small pilot

`exCM` re-verified through `checkDualCMTF`: the base conjuncts against the
flat `certY` (lockstep `dotLI`), the column loop through the transient tree.
Locks the flat API used by `socert.py --col-major` (the O(n) base pass). -/

theorem exCM_flat_base : checkDualCMTBaseFlat exCM 2 [1, 1] 3 9 = true := by
  decide

theorem exCM_flat_cols : checkDualCMTCols exCM 2 (ITree.ofList [1, 1] 2) 3 = true := by
  decide

theorem exCM_flat_check : checkDualCMTF exCM 2 (ITree.ofList [1, 1] 2) [1, 1] 3 9 = true :=
  checkDualCMTF_split exCM_flat_base exCM_flat_cols

/-- End-to-end via the flat checker: every rational-feasible point of `exCM`
has objective ≤ 3. -/
theorem exCM_flat_bound (x : List Rat) (hxlen : x.length = exCM.cs.length)
    (hx0 : ∀ j < exCM.cs.length, 0 ≤ x.getD j 0)
    (hxrows : ∀ i < exCM.b.length, cmRowEval exCM i x ≤ (exCM.b.getD i 0 : Rat)) :
    cmObj exCM x ≤ 3 := by
  have h := checkDualCMTF_sound exCM 2 [1, 1] 3 9 exCM_flat_check
    x hxlen hx0 hxrows
  rwa [show ((9 : Int) : Rat) / ((3 : ℕ) : Rat) = 3 by norm_num] at h

/-- A flat base with a bad bound (`bᵀY = 9 > 8`) is rejected. -/
theorem exCM_flat_bad_bound : checkDualCMTBaseFlat exCM 2 [1, 1] 3 8 = false := by
  decide

end Kepler.LP
