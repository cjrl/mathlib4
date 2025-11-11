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

/-! 
# LatinSquare

Description of Latin Squares

## Main definitions

## Main results

## TODO

* Add theorem that a k-1 × n Latin rectangle can be completed to a k × n Latin rectangle.
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
  m_le_n : m ≤ n := by decide

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

end LatinSquare
