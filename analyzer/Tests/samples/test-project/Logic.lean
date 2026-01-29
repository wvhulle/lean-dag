/-! # Logic Proofs - Classical and Constructive -/

theorem contrapositive (p q : Prop) (h : p → q) : ¬q → ¬p := by
  intro hnq hp
  exact hnq (h hp)

theorem double_neg_intro (p : Prop) (hp : p) : ¬¬p := by
  intro hnp
  exact hnp hp

theorem and_assoc_logic (p q r : Prop) : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  · intro h
    obtain ⟨⟨hp, hq⟩, hr⟩ := h
    exact ⟨hp, hq, hr⟩
  · intro h
    obtain ⟨hp, hq, hr⟩ := h
    exact ⟨⟨hp, hq⟩, hr⟩

theorem or_assoc_logic (p q r : Prop) : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor
  · intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | inl hp => exact Or.inl hp
      | inr hq => exact Or.inr (Or.inl hq)
    | inr hr => exact Or.inr (Or.inr hr)
  · intro h
    cases h with
    | inl hp => exact Or.inl (Or.inl hp)
    | inr hqr =>
      cases hqr with
      | inl hq => exact Or.inl (Or.inr hq)
      | inr hr => exact Or.inr hr

theorem de_morgan_and (p q : Prop) : ¬(p ∧ q) ↔ ¬p ∨ ¬q := by
  constructor
  · intro h
    by_cases hp : p
    · by_cases hq : q
      · exact False.elim (h ⟨hp, hq⟩)
      · exact Or.inr hq
    · exact Or.inl hp
  · intro h hpq
    cases h with
    | inl hnp => exact hnp hpq.1
    | inr hnq => exact hnq hpq.2

theorem iff_intro_example (p q : Prop) (hpq : p → q) (hqp : q → p) : p ↔ q := by
  constructor
  · exact hpq
  · exact hqp
