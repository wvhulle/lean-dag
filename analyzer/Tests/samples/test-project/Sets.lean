/-! # Set Theory Proofs - Requires Mathlib -/

import Mathlib.Data.Set.Basic

open Set

theorem inter_comm_set (s t : Set Nat) : s ∩ t = t ∩ s := by
  ext x
  constructor
  · intro h
    rw [mem_inter_iff] at h ⊢
    exact ⟨h.2, h.1⟩
  · intro h
    rw [mem_inter_iff] at h ⊢
    exact ⟨h.2, h.1⟩

theorem union_comm_set (s t : Set Nat) : s ∪ t = t ∪ s := by
  ext x
  simp only [mem_union]
  constructor
  · intro h
    cases h with
    | inl hs => exact Or.inr hs
    | inr ht => exact Or.inl ht
  · intro h
    cases h with
    | inl ht => exact Or.inr ht
    | inr hs => exact Or.inl hs

theorem subset_refl_set (s : Set Nat) : s ⊆ s := by
  intro x hx
  exact hx

theorem empty_subset_set (s : Set Nat) : ∅ ⊆ s := by
  intro x hx
  exact False.elim hx
