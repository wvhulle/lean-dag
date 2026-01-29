/-! # Edge Case Proofs for LSP Testing -/

-- Term-mode proof (no tactics)
theorem term_mode_proof : 1 = 1 := rfl

-- Empty proof with sorry
theorem sorry_proof : 2 = 2 := by sorry

-- Very short proof
theorem one_tactic : True := by trivial

-- Proof with nested tactics (conv block)
theorem nested_conv (a b : Nat) : a + b = b + a := by
  conv_lhs => rw [Nat.add_comm]

-- Proof with calc block
theorem calc_proof (a b c : Nat) : a + b + c = c + b + a := by
  calc a + b + c
      = (a + b) + c := by rfl
    _ = c + (a + b) := by rw [Nat.add_comm]
    _ = c + (b + a) := by rw [Nat.add_comm a b]
    _ = c + b + a := by rfl

-- Proof with have/show
theorem have_show_proof (n : Nat) : n + 0 = n := by
  have h : 0 + n = n := Nat.zero_add n
  show n + 0 = n
  exact Nat.add_zero n

-- Multiple rewrites in one tactic
theorem multi_rw (a b c : Nat) : (a + b) + c = c + (b + a) := by
  rw [Nat.add_comm a b, Nat.add_comm]

-- Deep nesting with cases
theorem deep_cases (p q r : Prop) (h : p ∨ q ∨ r) : r ∨ q ∨ p := by
  cases h with
  | inl hp =>
    right
    right
    exact hp
  | inr hqr =>
    cases hqr with
    | inl hq =>
      right
      left
      exact hq
    | inr hr =>
      left
      exact hr

-- Proof with repeat/iterate
theorem repeat_example (a : Nat) : a + 0 + 0 + 0 = a := by
  repeat rw [Nat.add_zero]

-- Proof ending with assumption
theorem assumption_proof (p : Prop) (h : p) : p := by
  assumption

-- Proof with simp and lemmas
theorem simp_proof (a b : Nat) : a + 0 + (b + 0) = a + b := by
  simp only [Nat.add_zero]

-- Proof with inline by block (potential orphan)
theorem inline_by_proof (n : Nat) : n + 0 = n := by
  have h : 0 + n = n := by rw [Nat.zero_add]
  rw [Nat.add_comm, h]

-- Proof with constructor (two independent subgoals)
theorem and_intro_proof (a b : Nat) : a = a ∧ b = b := by
  constructor
  · rfl
  · rfl
