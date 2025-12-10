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
import Mathlib

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

def symbols_not_in
{k n : Nat} [NeZero k] [NeZero n]
 (A : LatinRectangle k n α) (j : Fin n) :=
  let D := Finset.image (fun i => A.M i j) Finset.univ
  (symbols A.M) \ D

lemma count_by_group_or_element_indicator
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (B : ι → Finset α)
  (s : Finset ι)
  : ∑ j ∈ s, (Finset.card (B j)) =
  ∑ x ∈ (s.biUnion B), Finset.card {j | j ∈ s ∧ x ∈ B j} := by
    let E : Finset (ι × (s.biUnion B)) := {b | b.1 ∈ s ∧ ↑(b.2) ∈ (B b.1)}
    let amb : E → ι × (s.biUnion B) := fun b => (b : ι × (s.biUnion B))
    let p1 : E → ι := Prod.fst ∘ amb
    have hp1 : Set.MapsTo p1 (Finset.univ : Finset E) (Finset.univ : Finset ι) := by simp
    have h1 := Finset.card_eq_sum_card_fiberwise hp1
    have j_not_in_s_zero_summand : ∀ j ∈ sᶜ, Finset.card {a | p1 a = j} = 0 := by 
      intro j hjc
      rw [Finset.card_eq_zero]
      ext b
      constructor 
      · intro hm
        simp at hm
        simp [p1,amb] at hm
        have hb := b.property 
        simp only [E] at hb
        rw [Finset.mem_def] at hb
        simp at hb
        have hj := hb.1
        rw [hm] at hj
        simp at hjc 
        contradiction
      · simp
    have s_s_complement_disj : Disjoint s (sᶜ) := by 
      simp [Disjoint]
      intro x hx hxc
      have h := Finset.subset_inter hx hxc
      simp at h
      exact h
    have h1_split := Finset.sum_union s_s_complement_disj (f := fun j => Finset.card {a | p1 a = j})
    replace j_not_in_s_zero_summand := Finset.sum_congr (by rfl) j_not_in_s_zero_summand
    conv at j_not_in_s_zero_summand =>
      rhs
      simp
    rw [j_not_in_s_zero_summand] at h1_split
    simp at h1_split
    simp at h1
    rw [h1_split] at h1
    have p1_im : ∀ j ∈ s, {a | p1 a = j} ≃ B j := by 
      intro j hj
      refine ⟨fun x => ⟨x.val.1.2.val, by 
                have h := x.val.property
                unfold E at h
                rw [Finset.mem_def] at h
                simp at h
                replace h := h.right
                have j' := x.property
                dsimp [p1,amb] at j'
                rw [j'] at h
                exact h⟩,
              fun x => ⟨⟨(j, ⟨x.val, by 
                have h := x.property
                rw [Finset.mem_biUnion]
                use j ⟩), by simp [E]; exact hj ⟩, 
              by simp [p1,amb]⟩,
              ?left_inv,
              ?right_inv⟩ 
      · simp [Function.LeftInverse]
        intros _ _ _ _ _ _ hp1
        simp [p1,amb] at hp1
        exact hp1.symm
      · simp [Function.RightInverse, Function.LeftInverse]
    have h1'set : ∀ j ∈ s, Finset.card {a | p1 a = j} = (B j).card := by
      intro j hj
      specialize p1_im j hj
      simp at p1_im
      apply Finset.card_eq_of_equiv
      simp
      exact p1_im
    have h1'' := Finset.sum_congr (by rfl) h1'set
      (f := fun j => Finset.card {a | p1 a = j}) (g := fun j => Finset.card (B j))
    rw [←h1'']
    simp
    rw [←h1]
    -- Second half is E.card
    clear h1 h1'' hp1 h1_split p1_im h1'set s_s_complement_disj j_not_in_s_zero_summand
    let p2 : E → s.biUnion B := Prod.snd ∘ amb
    have hp2 : Set.MapsTo p2 (Finset.univ : Finset E)
      (Finset.univ : Finset (s.biUnion B)) := by simp
    have h2 := Finset.card_eq_sum_card_fiberwise hp2
    have h2' : ∀ x, {a | p2 a = x} ≃ {j | j ∈ s ∧ ↑x ∈ B j} := by 
      intro x
      simp [p2,amb]
      sorry

    have h2'set : ∀ x ∈ (s.biUnion B),
      Finset.card {a | p2 a = x} = Finset.card {j | j ∈ s ∧ ↑x ∈ B j} := by 
        intro x hx
        apply Finset.card_eq_of_equiv
        specialize h2' ⟨ x, hx ⟩ 
        simp at h2'
        simp
        apply Equiv.trans (α := { a // ↑(p2 a) = x }) 
          (γ := { j // j ∈ s ∧ x ∈ B j}) 
          (β := { a // p2 a = ⟨x, hx⟩ })
        have hl a: ↑(p2 a) = x ↔ p2 a = ⟨x, hx⟩ := by 
          have h := Subtype.coe_eq_iff (a := p2 a) (b := x)
          rw [h]
          constructor 
          · simp
          · intro hp2a
            use hx
        conv =>
          lhs 
          congr
          ext a
          rw [hl a]
        exact h2'
    have h2'' := Finset.sum_congr
      (s₁ := s.biUnion B) (s₂ := s.biUnion B) (by rfl) h2'set
      (f := fun x => Finset.card  {a | p2 a = x})
      (g := fun x => Finset.card  {j | j ∈ s ∧ ↑x ∈ B j})
    rw [←h2'']
    simp
    simp at h2
    have hfin : ∑ x ∈ (s.biUnion B).attach, {a ∈ E.attach | p2 a = x}.card =
                ∑ x ∈ s.biUnion B, {a ∈ E.attach | ↑(p2 a) = x}.card := by 
         have h := Finset.sum_attach (s.biUnion B) (fun x => {a ∈ E.attach | p2 a = x}.card )
         rw [<- h]
         congr
         ext x
         congr
         ext a
         rw [SetCoe.ext_iff]
    rw[← hfin]
    exact h2

lemma exists_larger_subset
  {B : Fin n → Finset α}
  {s : Finset (Fin n)}
  {k : Nat} [nek : NeZero k]
  (h₁ : ∀ j, Finset.card (B j) = k)
  (h₂ : (s.biUnion B).card < (s.card)) :
      ∃ (x : α), k < (Finset.card {j | j ∈ s ∧ x ∈ B j}) := by
      by_contra hc
      simp at hc
      have pullback : ∀ i ∈ (s.biUnion B),
        ∃ x, ∀ j, (j ∈ s ∧ i ∈ B j) ↔ (j ∈ s ∧ x ∈ B j) := by
          intro i hi
          use i
          simp
      have hc' : (∀ i ∈ s.biUnion B, Finset.card {j | j ∈ s ∧ i ∈ B j} ≤ k) := by
        intro i
        intro h
        specialize pullback i
        apply pullback at h
        obtain ⟨ x , hx ⟩ := h
        specialize hc x
        conv =>
          lhs
          congr
          congr
          ext
          rw[hx]
        exact hc
      have g := Finset.sum_le_sum  (s := s.biUnion B) (ι := α)
        (f := fun x => Finset.card {j | j ∈ s ∧ x ∈ B j})
        (g := fun _ => k)
      apply g at hc'
      simp at hc'
      have _ : 0 < k := by
        have _ := nek.out
        omega
      have _ : (Finset.card (s.biUnion B))*k < s.card*k := by
        rw [Nat.mul_lt_mul_right]
        omega
        assumption
      replace hc' : ∑ i ∈ s.biUnion B, Finset.card {j | j ∈ s ∧ i ∈ B j} < (s.card) * k := by omega
      have h' : ∑ j ∈ s, (Finset.card (B j)) =
        ∑ x ∈ (s.biUnion B), Finset.card {j | j ∈ s ∧ x ∈ B j} := 
        count_by_group_or_element_indicator B s 
      rw[←h'] at hc'
      simp[h₁] at hc'


lemma hall_property
  {B : Fin n → Finset α}
  {h : ∃ k, ∀ j, Finset.card (B j) = k} :
  ∀ (s : Finset (Fin n)), (Finset.card s) ≤ (Finset.card (s.biUnion B)) := by sorry

theorem latin_rectangle_extends
  {k n : Nat} [NeZero k] [NeZero n]
    (A : LatinRectangle k n α)
    (h : k < n := by omega) :
    ∃ (A' : LatinRectangle (k + 1) n α), is_subrect A A' := by
  let B := symbols_not_in A
  have ls_excl (i : Fin k) (j : Fin n) : A.M i j ∉ B j := by sorry
  have Bj_size (j : Fin n) : Finset.card (B j) = n-k := by sorry
  have exact_i : ∀ x ∈ symbols A.M, ∀ (t : Finset (Fin n)),
    (Finset.card {j | j ∈ t ∧ x ∈ B j}) ≤ n-k := by
    intro x hx t
    simp [B, symbols_not_in]
    -- Properties of latin rectangle
    sorry
  have h : ∀ (s : Finset (Fin n)), (Finset.card s) ≤ (Finset.card (s.biUnion B)) := by
    intro s
    set l := s.card with hl
    have h1 : ∑ j ∈ s, (Finset.card (B j)) = l*(n-k) := by
      conv =>
        congr
        arg 2
        ext j
        rw [Bj_size]
      simp [hl]
    by_contra hc
    simp at hc
    have _ : NeZero (n-k) := {
      out := by omega
    }
    have hcount := exists_larger_subset Bj_size hc
    obtain ⟨ x, hx ⟩ := hcount
    specialize exact_i x
    have hxsym : x ∈ symbols A.M := by sorry
    apply exact_i at hxsym
    specialize hxsym s
    omega
  let halls := hallMatchingsOn.nonempty (B) h (Finset.univ)
  set f := Classical.choice halls with hx
  simp [hallMatchingsOn] at f
  obtain ⟨ f', hf⟩ := f
  let M' : Fin (k+1) → (Fin n) → α := fun i j =>
    if hif : i < k then A.M ⟨i, hif⟩ j else (f' ⟨j, by simp⟩ )
  let A' : LatinRectangle (k+1) n α := {
    M := M'
    exactly_n_symbols := sorry
    once_per_row := sorry
    distinct_col_entries := sorry
    m_le_n := by omega
  }
  use A'
  unfold is_subrect
  unfold LatinRectangle.M
  simp[A', M']
  intro i j
  rfl

end Completion

#check Finset.sum_le_sum

end LatinSquare
