/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

/-! # Homework 6

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-6,
for clearer statements and any special instructions. -/


@[autograded 4]
theorem problem1 (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
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



@[autograded 5]
theorem problem2 (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  . intro h
    obtain ⟨l, hl⟩ := h
    obtain ⟨p, hp⟩ := l
    use p
    constructor
    apply hp
    apply hl
  . intro h
    obtain ⟨l, hl⟩ := h
    obtain ⟨l1, l2⟩ := hl
    constructor
    use l
    apply l1
    apply l2




--------- Lemmas for the next example
lemma iff_help (P Q : Prop) : (P ↔ Q) ↔ (¬ P ↔ ¬ Q) := by
  constructor
  . intro h
    obtain ⟨h1, h2⟩ := h
    constructor
    . intro h3
      by_cases hQ : Q
      . have h4 := h2 hQ
        contradiction
      apply hQ
    . intro h3
      by_cases hP : P
      . have h4 := h1 hP
        contradiction
      apply hP
  . intro h
    obtain ⟨h1, h2⟩ := h
    constructor
    . intro h3
      by_cases hQ : Q
      . apply hQ
      . have h4 := h2 hQ
        contradiction
    . intro h3
      by_cases hP : P
      . apply hP
      . have h4 := h1 hP
        contradiction


lemma double_ne_help (P : Prop) : ¬ (¬ P) ↔ P := by
  constructor
  . intro h
    by_cases hP : P
    · apply hP
    · contradiction
  . intro h
    intro h1
    contradiction
---------

@[autograded 5]
theorem problem3 (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  . intro a
    constructor
    . by_cases p : P
      apply p
      have ac : P → Q := by
        intro x
        contradiction
      contradiction
    . intro h
      have ac : P → Q := by
        by_cases p : P
        intro hh
        apply h
        intro hh
        contradiction
      contradiction
  intro h0
  intro h1
  obtain ⟨h2, h3⟩ := h0
  have h4 := h1 h2
  contradiction




@[autograded 3]
theorem problem4 : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  push_neg
  use 0.5
  numbers

@[autograded 4]
theorem problem5 : ¬ Int.Even 7 := by
  dsimp [Int.Even]
  push_neg
  intro k
  have h0 := le_or_succ_le k 3
  obtain h0 | h0 := h0
  apply ne_of_gt
  calc
    2 * k ≤ 2 * 3 := by rel [h0]
    _ < 7 := by numbers
  apply ne_of_lt
  calc
    7 < 2 * 4 := by numbers
    _ ≤ 2 * k := by rel [h0]


@[autograded 4]
theorem problem6 {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  have h0 := le_or_succ_le p 1
  obtain h0 | h0 := h0
  have h1 : p < 2 := by addarith[h0]
  left
  apply h1
  right
  use k
  constructor
  apply hk
  constructor
  apply hk1
  apply hkp
