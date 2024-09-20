/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic

math2001_init
set_option pp.funBinderTypes true


example {P Q : Prop} (h1 : P ∨ Q) (h2 : ¬ Q) : P := by
  obtain hP | hQ := h1
  · apply hP
  · contradiction


example (P Q : Prop) : P → (P ∨ ¬ Q) := by
  intro hP
  left
  apply hP


#truth_table ¬(P ∧ ¬ Q)

#truth_table P ↔ (¬P ∨ Q)

example (P : Prop) : (P ∨ P) ↔ P := by
  constructor
  · intro h
    obtain h1 | h2 := h
    · apply h1
    · apply h2
  · intro h
    left
    apply h


example (P Q R : Prop) : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
  constructor
  · intro h
    obtain ⟨h1, h2 | h2⟩ := h
    · left
      constructor
      · apply h1
      · apply h2
    · right
      constructor
      · apply h1
      · apply h2
  · intro h
    obtain h | h := h
    obtain ⟨h1, h2⟩ := h
    constructor
    apply h1
    left
    apply h2
    obtain ⟨h1, h2⟩ := h
    constructor
    apply h1
    right
    apply h2



#truth_table P ∧ (Q ∨ R)
#truth_table (P ∧ Q) ∨ (P ∧ R)


example {P Q : α → Prop} (h1 : ∀ x : α, P x) (h2 : ∀ x : α, Q x) :
    ∀ x : α, P x ∧ Q x := by
  intro x
  constructor
  · apply h1
  · apply h2


example {P : α → β → Prop} (h : ∃ x : α, ∀ y : β, P x y) :
    ∀ y : β, ∃ x : α, P x y := by
  obtain ⟨x, hx⟩ := h
  intro y
  use x
  apply hx


example (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := by
  constructor
  · intro h a ha
    have : ∃ x, P x
    · use a
      apply ha
    contradiction
  · intro h h'
    obtain ⟨x, hx⟩ := h'
    have : ¬ P x := h x
    contradiction

/-! # Exercises -/


example {P Q : Prop} (h : P ∧ Q) : P ∨ Q := by
  obtain ⟨h1, h2⟩ := h
  left
  apply h1

example {P Q R : Prop} (h1 : P → Q) (h2 : P → R) (h3 : P) : Q ∧ R := by
  have h4 : Q := by
    apply h1
    apply h3
  have h5 : R := by
    apply h2
    apply h3
  constructor
  apply h4
  apply h5

example (P : Prop) : ¬(P ∧ ¬ P) := by
  intro h
  obtain ⟨h1, h2⟩ := h
  contradiction

example {P Q : Prop} (h1 : P ↔ ¬ Q) (h2 : Q) : ¬ P := by
  obtain ⟨h3, h4⟩ := h1
  intro h
  have h5 : ¬ Q := by
    apply h3
    apply h
  contradiction

example {P Q : Prop} (h1 : P ∨ Q) (h2 : Q → P) : P := by
  obtain h1 | h1 := h1
  apply h1
  apply h2
  apply h1

example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  . intro h3
    obtain ⟨h4, h5⟩ := h3
    have h6 : Q := by
      apply h1
      apply h4
    constructor
    apply h6
    apply h5
  . intro h3
    obtain ⟨h4, h5⟩ := h3
    have h6 : P := by
      apply h2
      apply h4
    constructor
    apply h6
    apply h5

example (P : Prop) : (P ∧ P) ↔ P := by
  constructor
  . intro h
    obtain ⟨h1, h2⟩ := h
    apply h1
  . intro h
    constructor
    apply h
    apply h


example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor
  . intro h
    obtain h | h := h
    right
    apply h
    left
    apply h
  . intro h
    obtain h | h := h
    right
    apply h
    left
    apply h

example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  . intro h
    constructor
    . intro hp
      have hpq : P ∨ Q := by
        left
        apply hp
      contradiction
    . intro hq
      have hpq : P ∨ Q := by
        right
        apply hq
      contradiction
  . intro h1 h2
    obtain ⟨h3, h4⟩ := h1
    obtain h2 | h2 := h2
    contradiction
    contradiction

example {P Q : α → Prop} (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  intro y
  apply h1
  apply h2

example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  . intro h1
    obtain ⟨y, h2⟩ := h1
    use y
    have h3 : P y ↔ Q y := by
      apply h
    obtain ⟨h4, h5⟩ := h3
    apply h4
    apply h2
  . intro h1
    obtain ⟨y, h2⟩ := h1
    use y
    have h3 : P y ↔ Q y := by
      apply h
    obtain ⟨h4, h5⟩ := h3
    apply h5
    apply h2

example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  . intro h
    obtain ⟨r, s, h1⟩ := h
    use s
    use r
    apply h1
  . intro h
    obtain ⟨r, s, h1⟩ := h
    use s
    use r
    apply h1


example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  . intro h r s
    apply h s r
  . intro h r s
    apply h s r



example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  . intro h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨y, h3⟩ := h1
    use y
    constructor
    apply h3
    apply h2
  . intro h
    obtain ⟨y, h1⟩ := h
    obtain ⟨h2, h3⟩ := h1
    constructor
    use y
    apply h2
    apply h3
