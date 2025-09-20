section propositional

variable (P Q R : Prop)


------------------------------------------------
-- Double negation
------------------------------------------------

theorem doubleneg_intro :
  P → ¬ ¬ P  := by
  intro hp
  intro hnp
  exact hnp hp


theorem doubleneg_elim :
  ¬ ¬ P → P  := by
  intro hnnp
  by_cases h : P
  . exact h
  . exfalso
    apply hnnp
    exact h

theorem doubleneg_law :
  ¬ ¬ P ↔ P  := by
  constructor
  . intro hnnp -- Lado-L
    by_cases h : P
    . exact h
    . exfalso
      exact hnnp h
  . intro hp -- Lado-R
    intro hnp
    exact hnp hp


------------------------------------------------
-- Commutativity of ∨,∧
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  := by
  intro hor
  cases hor with
  | inl hp =>
    right
    exact hp
  | inr hq =>
    left
    exact hq


theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  := by
  intro hpeq
  constructor
  . have hq : Q := hpeq.right
    exact hq
  . have hp : P := hpeq.left
    exact hp

------------------------------------------------
-- Interdefinability of →,∨
------------------------------------------------

theorem impl_as_disj_converse :
  (¬ P ∨ Q) → (P → Q)  := by
  intro hnporq
  intro hp
  cases hnporq with
  | inl hpc =>
    exfalso
    exact hpc hp
  | inr hq =>
    exact hq


theorem disj_as_impl :
  (P ∨ Q) → (¬ P → Q)  := by
  intro hporq
  intro hnp
  cases hporq with
  | inl hp =>
    exfalso
    exact hnp hp
  | inr hq =>
    exact hq


------------------------------------------------
-- Contrapositive
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬ Q → ¬ P)  := by
  intro hpq
  intro hnq
  intro hp
  have hq : Q := hpq hp
  exact hnq hq

theorem impl_as_contrapositive_converse :
  (¬ Q → ¬ P) → (P → Q)  := by
  intro hnqnp
  intro hp
  by_cases hq : Q
  . exact hq
  . exfalso
    have hnp : ¬P := hnqnp hq
    exact hnp hp


theorem contrapositive_law :
  (P → Q) ↔ (¬ Q → ¬ P)  := by
  constructor
  . intro hpq
    intro hnq
    intro hp
    have hq : Q := hpq hp
    exact hnq hq
  . intro hnqnp
    intro hp
    by_cases hnq : Q
    . exact hnq
    . exfalso
      have hnp : ¬P := hnqnp hnq
      exact hnp hp


------------------------------------------------
-- Irrefutability of LEM[P]
------------------------------------------------

theorem lem_irrefutable :
  ¬ ¬ (P ∨ ¬ P)  := by
  intro h
  have hnp : ¬P := by
    intro hp
    have hpnp : P ∨ ¬P := Or.inl hp
    exact h hpnp
  have hpnp : P ∨ ¬P := Or.inr hnp
  exact h hpnp


------------------------------------------------
-- Peirce's law
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬ ¬ P  := by
  intro hpqp
  intro hnp
  have hpq : P → Q := by
    intro hp
    exfalso
    exact hnp hp
  have hp : P := hpqp hpq
  exact hnp hp


------------------------------------------------
-- Linearity of →
------------------------------------------------

theorem impl_linear :
  (P → Q) ∨ (Q → P)  := by
  by_cases h : Q
  . left
    intro hp
    exact h
  . right
    intro hq
    exfalso
    exact h hq


------------------------------------------------
-- Interdefinability of ∨,∧
------------------------------------------------

theorem disj_as_negconj :
  P ∨ Q → ¬ (¬ P ∧ ¬ Q)  := by
  intro hporq
  intro hnpnq
  have hnq : ¬Q := hnpnq.right
  have hnp : ¬P := hnpnq.left

  cases hporq with
  | inl hp =>
    exact hnp hp
  | inr hq =>
    exact hnq hq

theorem conj_as_negdisj :
  P ∧ Q → ¬ (¬ P ∨ ¬ Q)  := by
  intro hpeq
  intro hnpnp
  have hp : P := hpeq.left
  have hq : Q := hpeq.right

  cases hnpnp with
  | inl hnp =>
    exact hnp hp
  | inr hnq =>
    exact hnq hq

------------------------------------------------
-- De Morgan laws for ∨,∧
------------------------------------------------

theorem demorgan_disj :
  ¬ (P ∨ Q) → (¬ P ∧ ¬ Q)  := by
  intro hnpq
  constructor
  . intro hp
    apply hnpq
    exact Or.inl hp
  . intro hq
    apply hnpq
    exact Or.inr hq

theorem demorgan_disj_converse :
  (¬ P ∧ ¬ Q) → ¬ (P ∨ Q)  := by
  intro hnpenq
  intro hpeq
  have hnp : ¬P := hnpenq.left
  have hnq : ¬Q := hnpenq.right

  cases hpeq with
  | inl hp =>
    exact hnp hp
  | inr hq =>
    exact hnq hq

theorem demorgan_conj :
  ¬ (P ∧ Q) → (¬ Q ∨ ¬ P)  := by
  intro hnpeq
  by_cases hq : Q
  . by_cases hp : P
    . exfalso
      exact hnpeq ⟨hp, hq⟩
    . right
      exact hp
  . left
    exact hq

theorem demorgan_conj_converse :
  (¬ Q ∨ ¬ P) → ¬ (P ∧ Q)  := by
  intro hnqornp
  intro hpeq
  cases hnqornp with
  | inl hnq =>
    apply hnq
    have hq : Q := hpeq.right
    exact hq
  | inr hnp =>
    apply hnp
    have hp : P := hpeq.left
    exact hp

theorem demorgan_conj_law :
  ¬ (P ∧ Q) ↔ (¬ Q ∨ ¬ P)  := by
  constructor
  . intro hnpeq
    by_cases hq : Q
    . by_cases hp : P
      . exfalso
        exact hnpeq ⟨hp, hq⟩
      . right
        exact hp
    . left
      exact hq
  . intro hnqornp
    intro hpeq
    cases hnqornp with
    | inl hnq =>
      apply hnq
      have hq : Q := hpeq.right
      exact hq
    | inr hnp =>
      apply hnp
      have hp : P := hpeq.left
      exact hp

theorem demorgan_disj_law :
  ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q)  := by
  constructor
  . intro hnporq
    constructor
    . intro hp
      apply hnporq
      left
      exact hp
    . intro hq
      apply hnporq
      right
      exact hq
  . intro hnpeq
    intro hporq
    cases hporq with
    | inl hp =>
      have hnp : ¬P := hnpeq.left
      exact hnp hp
    | inr hq =>
      have hnq : ¬Q := hnpeq.right
      exact hnq hq


------------------------------------------------
-- Distributivity laws between ∨,∧
------------------------------------------------

theorem distr_conj_disj :
  P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)  := by
  intro h
  have hp : P := h.left
  have hqorr := h.right
  cases hqorr with
  | inl hq =>
    left
    constructor
    . exact hp
    . exact hq
  | inr hr =>
    right
    constructor
    . exact hp
    . exact hr

theorem distr_conj_disj_converse :
  (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)  := by
  intro h
  cases h with
  | inl hpq =>
    constructor
    . have hp := hpq.left
      exact hp
    . left
      have hq := hpq.right
      exact hq
  | inr hpr =>
    constructor
    . have hp := hpr.left
      exact hp
    . right
      have hr := hpr.right
      exact hr

theorem distr_disj_conj :
  P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)  := by
  intro h
  constructor
  . cases h with
    | inl hp =>
      left
      exact hp
    | inr hqr =>
      have hq := hqr.left
      right
      exact hq
  . cases h with
    | inl hp =>
      left
      exact hp
    | inr hqr =>
      right
      have hr := hqr.right
      exact hr

theorem distr_disj_conj_converse :
  (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)  := by
  intro h
  have hpq := h.left
  have hpr := h.right
  cases hpq with
  | inl hp =>
    left
    exact hp
  | inr hq =>
    cases hpr with
    | inl hp =>
      left
      exact hp
    | inr hr =>
      right
      constructor
      . exact hq
      . exact hr


------------------------------------------------
-- Currying
------------------------------------------------

theorem curry_prop :
  ((P ∧ Q) → R) → (P → (Q → R))  := by
  intro h
  intro hp
  intro hq
  apply h
  exact ⟨hp, hq⟩

theorem uncurry_prop :
  (P → (Q → R)) → ((P ∧ Q) → R)  := by
  intro h
  intro hpq
  have hp := hpq.left
  have hq := hpq.right
  apply h
  . exact hp
  . exact hq


------------------------------------------------
-- Reflexivity of →
------------------------------------------------

theorem impl_refl :
  P → P  := by
  intro h
  exact h


------------------------------------------------
-- Weakening and contraction
------------------------------------------------

theorem weaken_disj_right :
  P → (P ∨ Q)  := by
  intro hp
  left
  exact hp

theorem weaken_disj_left :
  Q → (P ∨ Q)  := by
  intro hq
  right
  exact hq

theorem weaken_conj_right :
  (P ∧ Q) → P  := by
  intro hpq
  have hp := hpq.left
  exact hp

theorem weaken_conj_left :
  (P ∧ Q) → Q  := by
  intro hpq
  have hq := hpq.right
  exact hq


------------------------------------------------
-- Idempotence of ∨,∧
------------------------------------------------

theorem disj_idem :
  (P ∨ P) ↔ P  := by
  constructor
  . intro hpp
    cases hpp with
    | inl hp =>
      exact hp
    | inr hp =>
      exact hp
  . intro hp
    left
    exact hp

theorem conj_idem :
  (P ∧ P) ↔ P := by
  constructor
  . intro hpp
    have hp := hpp.left
    exact hp
  . intro hp
    constructor
    . exact hp
    . exact hp


------------------------------------------------
-- Bottom, Top
------------------------------------------------

theorem false_bottom :
  False → P := by
  intro h
  contradiction

theorem true_top :
  P → True  := by
  intro h
  trivial


end propositional

----------------------------------------------------------------

section predicate

variable (U : Type)
variable (P Q : U → Type)


------------------------------------------------
-- De Morgan laws for ∃,∀
------------------------------------------------

theorem demorgan_exists :
  ¬ (∃ x, P x) → (∀ x, ¬ P x)  := by
  sorry

theorem demorgan_exists_converse :
  (∀ x, ¬ P x) → ¬ (∃ x, P x)  := by
  sorry

theorem demorgan_forall :
  ¬ (∀ x, P x) → (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_forall_converse :
  (∃ x, ¬ P x) → ¬ (∀ x, P x)  := by
  sorry

theorem demorgan_forall_law :
  ¬ (∀ x, P x) ↔ (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_exists_law :
  ¬ (∃ x, P x) ↔ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
-- Interdefinability of ∃,∀
------------------------------------------------

theorem exists_as_neg_forall :
  (∃ x, P x) → ¬ (∀ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists :
  (∀ x, P x) → ¬ (∃ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists_converse :
  ¬ (∃ x, ¬ P x) → (∀ x, P x)  := by
  sorry

theorem exists_as_neg_forall_converse :
  ¬ (∀ x, ¬ P x) → (∃ x, P x)  := by
  sorry

theorem forall_as_neg_exists_law :
  (∀ x, P x) ↔ ¬ (∃ x, ¬ P x)  := by
  sorry

theorem exists_as_neg_forall_law :
  (∃ x, P x) ↔ ¬ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
--  Distributivity between quantifiers
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists :
  (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists_converse :
  (∃ x, P x) ∨ (∃ x, Q x) → (∃ x, P x ∨ Q x)  := by
  sorry

theorem forall_conj_as_conj_forall :
  (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x)  := by
  sorry

theorem forall_conj_as_conj_forall_converse :
  (∀ x, P x) ∧ (∀ x, Q x) → (∀ x, P x ∧ Q x)  := by
  sorry

theorem forall_disj_as_disj_forall_converse :
  (∀ x, P x) ∨ (∀ x, Q x) → (∀ x, P x ∨ Q x)  := by
  sorry


end predicate

------------------------------------------------

section bonus

------------------------------------------------
--  Drinker's paradox
------------------------------------------------

variable (D : U → Prop)

-- There is a person p such that:
-- if p drinks, then everybody drinks
-- p: «person»
-- D x: «x drinks»
theorem drinker :
  ∃ p, (D p → ∀ x, D x)  := by
  sorry

------------------------------------------------
--  Russell's paradox
------------------------------------------------

variable (S : U → U → Prop)

-- It is impossible to have a barber b such that
-- b shaves exactly those people who do not shave themselves
-- b: «barber»
-- S x y: «x shaves y»
theorem russell :
  ¬ ∃ b, ∀ x, (S b x ↔ ¬ S x x)  := by
  sorry


end bonus


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x)  := by
  sorry

theorem exists_conj_as_conj_exists_converse :
  (∃ x, P x) ∧ (∃ x, Q x) → (∃ x, P x ∧ Q x)  := by
  sorry

---------------------------------------------- -/
