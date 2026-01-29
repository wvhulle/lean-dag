/-! # Induction Proofs -/

theorem nat_add_zero (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [Nat.add_zero]

theorem nat_zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k _ => simp

theorem list_length_nil : ([] : List α).length = 0 := by
  rfl

theorem list_length_cons (x : α) (xs : List α) : (x :: xs).length = xs.length + 1 := by
  rfl

theorem nat_le_refl (n : Nat) : n ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ k ih => exact Nat.le_refl (k + 1)

theorem simple_cases (n : Nat) : n = 0 ∨ n > 0 := by
  cases n with
  | zero => exact Or.inl rfl
  | succ k => exact Or.inr (Nat.succ_pos k)

