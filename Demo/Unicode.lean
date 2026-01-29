/-! # Unicode Test Cases -/

-- Greek letters in identifiers
theorem αβγ_test (α β : Nat) : α + β = β + α := by
  rw [Nat.add_comm]

-- Subscripts and superscripts
theorem sub_test (x₁ x₂ : Nat) : x₁ + x₂ = x₂ + x₁ := by
  rw [Nat.add_comm]

-- Mathematical symbols
theorem arrow_test (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  exact h hp

-- Longer unicode: emoji-like (though not typically used)
theorem lambda_test (f : Nat → Nat) (n : Nat) : f n = f n := by
  rfl

-- Mixed ASCII and unicode on same line
theorem mixed_αβ_abc (α : Nat) (a : Nat) : α + a = a + α := by
  rw [Nat.add_comm]
