/-! # Basic Proofs - No external dependencies -/

theorem and_comm_basic (p q : Prop) (h : p ∧ q) : q ∧ p := by
  obtain ⟨hp, hq⟩ := h
  exact ⟨hq, hp⟩

theorem impl_basic (p q : Prop) (h : p → q) (hp : p) : q := by
  apply h
  exact hp

theorem or_comm_basic (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

theorem exists_pred (n : Nat) (h : n > 0) : ∃ m, m + 1 = n := by
  cases n with
  | zero => contradiction
  | succ m => exact ⟨m, rfl⟩

theorem intro_example (n : Nat) : n = n := by
  rfl

theorem have_example (n : Nat) : n + 0 = n := by
  have h : n + 0 = n := Nat.add_zero n
  exact h

theorem calc_example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  calc a = b := h1
       _ = c := h2
