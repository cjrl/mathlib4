/-
Copyright (c) 2025 Christopher J. R. Lloyd and George H. Seelinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher J. R. Lloyd, George H. Seelinger
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Group
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.Hall.Basic

/-! 
# LatinSquare

Description of Latin Squares

## Main definitions

## Main results

## TODO

* Add theorem that a k-1 × n Latin rectangle can be extended to a k × n Latin rectangle.
* Corollary, any k x n Latin rectangle can be extneded to a Latin square.
* Add that a n x n Latin rectangle is a Latin square. 
  This will lead to a computable definition of Latin square.
* Add Ryser's theorem using partial Latin squares.
* Add Evan's Conjeture. 
* Add isomorphism to quasigroups.
* Add isomorphism to orthogonal arrays of triples.

## References

* [vanLint, Wilson, *A Course in Combinatorics*, Chapter 17][vanlint_wilson2001]

-/

section LatinSquare

universe u

variable {α : Type u} [DecidableEq α] 
variable {m n : Nat} [NeZero n]

abbrev symbols (M : Fin m → Fin n → α) : Finset α := 
  (Finset.image fun (x,y) ↦ M x y) Finset.univ

abbrev exactly_n_symbols (M : Fin m → Fin n → α) :=
  (symbols M).card = n

abbrev once_per_row (M : Fin m → Fin n → α) : Prop :=
  ∀ i : Fin m, ∀ y ∈ symbols M, ∃! j: Fin n, M i j = y

abbrev distinct_col_entries (M : Fin m → Fin n → α) : Prop :=
  ∀ y : Fin n, ∀ x₁ x₂ : Fin m, x₁ ≠ x₂ → M x₁ y ≠ M x₂ y

abbrev distinct_row_entries (M : Fin m → Fin n → α) : Prop :=
  ∀ x : Fin m, ∀ y₁ y₂ : Fin n, y₁ ≠ y₂ → M x y₁ ≠ M x y₂

/-- For m ≤ n, an m × n Latin rectangle is a partial n × n Latin Square where 
    the first m entries are filled. -/
class LatinRectangle (m n : Nat) (α : Type u) [DecidableEq α] where
  /-- An m × n array of symbols. -/
  M : Fin m -> Fin n -> α
  /-- An $m × n$ Latin rectangle contains $n$ distinct entries. -/
  exactly_n_symbols : exactly_n_symbols M
  /-- Each row contains each symbol exactly once. -/
  once_per_row : once_per_row M
  /-- Entries cannot repeat in a given column. -/
  distinct_col_entries : distinct_col_entries M
  m_le_n : m ≤ n := by simp

-- Pretty printing of rectangles
instance {m n : Nat} {α : Type u} [DecidableEq α] [ToString α] :
  Repr (LatinRectangle m n α) where
    reprPrec L _ :=
      let row (i : Fin m) := 
        String.intercalate " " (List.ofFn (fun j => (toString (L.M i j))));
      String.intercalate "\n" (List.ofFn row)

abbrev once_per_column (M : Fin n → Fin n → α) : Prop :=
  ∀ j : Fin n, ∀ x ∈ symbols M, ∃! i : Fin n, M i j = x

omit [NeZero n]
lemma latin_square_row_implies_latin_rectangle_row
  (M : Fin n → Fin n → α)
  (h₁ : exactly_n_symbols M)
  (h₂ : once_per_row M) :
  (∀ (x : Fin n), ∀ (y₁ y₂ : Fin n), y₁ ≠ y₂ → ((M x y₁) ≠ (M x y₂))) := by sorry
  
omit [NeZero n]
lemma latin_square_col_implies_latin_rectangle_col
  (M : Fin n → Fin n → α)
  (h₁ : exactly_n_symbols M)
  (h₂ : once_per_column M) :
  (∀ (y : Fin n), ∀ (x₁ x₂ : Fin n), x₁ ≠ x₂ → ((M x₁ y) ≠ (M x₂ y))) := by sorry

/-- A LatinSquare is an n × n array containing exactly n symbols, 
    each occurring exactly once in each row and exactly once in each column. -/
class LatinSquare (n : Nat) (α : Type u) [DecidableEq α] extends LatinRectangle n n α where
  /-- Each column contains each symbol exactly once. -/
  once_per_column : once_per_column M 
  /-- If each column contains each symbol exactly once, then there are no repeats across columns. -/
  distinct_col_entries := latin_square_col_implies_latin_rectangle_col 
    M exactly_n_symbols once_per_column
  m_le_n := by rfl

instance {n : Nat} {α : Type*} [DecidableEq α] [ToString α] :
  Repr (LatinSquare n α) where
    reprPrec L prec := Repr.reprPrec L.toLatinRectangle prec
/-- Every Finite Group's Cayley table is an example of a Latin Square. -/

@[to_additive]
def group_to_cayley_table {G : Type*} [DecidableEq G] [Group G] [Fintype G]
  {n : Nat} [NeZero n]
  (ordering : Fin n ≃ G)
  (h : n = Fintype.card G := by simp) :
  LatinSquare n G := {
    M := fun i j ↦ (ordering i) * (ordering j),
    exactly_n_symbols := by 
      simp [exactly_n_symbols,symbols]
      conv =>
        rhs
        rw [h]
      congr
      ext a
      constructor 
      · simp
      · intro h'
        rw [Finset.mem_image]
        set i' := ordering.symm a
        set j' := ordering.symm 1
        use (i',j')
        simp [i', j']
    once_per_row := by 
      simp [once_per_row]
      intro i g x y z
      set g' := ordering i
      set j := ordering.symm (g'⁻¹*g)
      use j
      simp [g',j]
      intro k h' 
      have hia : (ordering i)⁻¹ * ((ordering i) * (ordering k)) = (ordering i)⁻¹ * g := by
       rw [mul_right_inj (ordering i)⁻¹ (b := (ordering i)*(ordering k)) (c := g)]
       exact h'
      simp at hia
      rw [<- hia]
      simp
    once_per_column := by 
      simp [once_per_column]
      intro i g x y z
      set g' := ordering i
      set j := ordering.symm (g*g'⁻¹)
      use j
      simp [g',j]
      intro k h' 
      have hia : (ordering k) * (ordering i) * (ordering i)⁻¹ = g * (ordering i)⁻¹  := by
       rw [mul_left_inj (ordering i)⁻¹ (b := (ordering k)*(ordering i)) (c := g)]
       exact h'
      simp at hia
      rw [<- hia]
      simp
  }

-- Cyclic Example
-- We construct an infinite family of Latin Squares from the infinite family of Cyclic Groups

-- For example, addGroup_to_cayley_table (ZMod.finEquiv 5).toEquiv

instance nonempty {n : Nat} [NeZero n] : LatinSquare n (ZMod n) :=
  addGroup_to_cayley_table (ZMod.finEquiv n).toEquiv

section Isotopy

structure LatinSquareIsotopy
  {α : Type u} [DecidableEq α] [Nonempty α]
  {β : Type u} [DecidableEq β] [Nonempty β]
  {n : Nat}
  (L₁ : LatinSquare n α)
  (L₂ : LatinSquare n β)
  where
    symbol_map : α → β
    reindex_row : Fin n ≃ Fin n
    reindex_col : Fin n ≃ Fin n
    intertwine : ∀ i, ∀ j, symbol_map (L₁.M (reindex_row i) (reindex_col j)) = L₂.M i j

def reflLatinSquareIsotopy {n : Nat} {α : Type u} [DecidableEq α] [Nonempty α]
  (L : LatinSquare n α) : LatinSquareIsotopy L L := {
    symbol_map := Equiv.refl α,
    reindex_row := Equiv.refl (Fin n),
    reindex_col := Equiv.refl (Fin n),
    intertwine := by simp
  }

end Isotopy

section Completion 

def is_subrect {m n m' n' : Nat}
  (A : LatinRectangle m n α)
  (B : LatinRectangle m' n' α)
  (h₁ : m ≤ m' := by omega)
  (h₂ : n ≤ n' := by omega) := 
  ∀ (i : Fin m), ∀ (j : Fin n), A.M i j = B.M ⟨i, by omega⟩ ⟨j, by omega⟩ 
 
theorem latin_rectangle_extends
  {k n : Nat} [NeZero k] [NeZero n]
  (A : LatinRectangle k n α)
  (h : k < n := by omega) :
  ∃ (A' : LatinRectangle (k + 1) n α), is_subrect A A' := by 
  -- #check hallMatchingsOn.nonempty
  sorry

end Completion

end LatinSquare
