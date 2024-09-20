/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel

math2001_init
set_option pp.funBinderTypes true


example (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      have hPQ : P ∧ Q
      · constructor
        · apply hP
        · apply hQ
      contradiction
    · left
      apply hP
  · intro h
    intro h1
    obtain h | h := h
    obtain ⟨h2, h3⟩ := h1
    contradiction
    obtain ⟨h2, h3⟩ := h1
    contradiction

example :
    ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m :=
  calc ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
      ↔ ∃ m : ℤ, ¬(m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) := by rel [not_forall]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ¬(∃ n : ℤ, n ^ 2 = m) := by rel [not_imp]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m := by rel [not_exists]


example : ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
    ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 :=
  calc
    ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
    ↔ ∃ n : ℤ, ¬(∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2) := by rel [not_forall]
    _ ↔ ∃ n : ℤ, ∀ m : ℤ, ¬(n ^ 2 < m ∧ m < (n + 1) ^ 2) := by rel [not_exists]
    _ ↔ ∃ n : ℤ, ∀ m : ℤ, ¬(n ^ 2 < m) ∨  ¬ (m < (n + 1) ^ 2) := by rel [not_and_or]
    _ ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 := by rel [not_lt]


#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
  -- ∃ m : ℤ, m ≠ 2 ∧ ∀ (n : ℤ), n ^ 2 ≠ m

#push_neg ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
  -- ∃ n : ℤ, ∀ m : ℤ, m ≤ n ^ 2 ∨ (n + 1) ^ 2 ≤ m


#push_neg ¬(∃ m n : ℤ, ∀ t : ℝ, m < t ∧ t < n)
#push_neg ¬(∀ a : ℕ, ∃ x y : ℕ, x * y ∣ a → x ∣ a ∧ y ∣ a)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc
     2 < 2 ^ 2 := by numbers
     _ ≤ n ^ 2 := by rel [hn]

/-! # Exercises -/


example (P : Prop) : ¬ (¬ P) ↔ P := by
  constructor
  . intro h
    by_cases hP : P
    · apply hP
    · contradiction
  . intro h
    intro h1
    contradiction

example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  . intro h
    constructor
    . by_cases hP : P
      . apply hP
      . have h1 : (P → Q) := by
          intro h2
          contradiction
        contradiction
    . intro hQ
      have h1 : (P → Q) := by
          intro h2
          apply hQ
      contradiction
  . intro h
    obtain ⟨h1, h2⟩ := h
    intro h3
    have h4 := h3 h1
    contradiction

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

example (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  have e1 : (¬ (∀ x, P x) ↔ ∃ x, ¬ P x) ↔ (¬(¬ (∀ x, P x)) ↔ ¬(∃ x, ¬ P x)) := by rel [iff_help]
  have e2 : (¬(¬ (∀ x, P x)) ↔ ¬(∃ x, ¬ P x)) ↔ ((∀ x, P x) ↔ ¬(∃ x, ¬ P x)) := by rel [double_ne_help]
  have e3 : (∀ x, P x) ↔ ¬ ∃ x, ¬ P x := by
    constructor
    · intro h h'
      obtain ⟨x, hx⟩ := h'
      have : P x := h x
      contradiction
    · intro h
      intro a
      by_cases ha : P a
      . apply ha
      . have h1 : ∃ (x : α), ¬P x := by
          use a
          apply ha
        contradiction
  obtain ⟨e21, e22⟩ := e2
  obtain ⟨e11, e12⟩ := e1
  have h1 := e22 e3
  have h2 := e12 h1
  apply h2

example : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 :=
  calc
    (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1) ↔ (∃ a : ℤ, ¬(∀ b : ℤ, (a * b = 1 → a = 1 ∨ b = 1))) := by rel [not_forall]
    _ ↔ (∃ a b : ℤ, ¬(a * b = 1 → a = 1 ∨ b = 1)) := by rel [not_forall]
    _ ↔ (∃ a b : ℤ, a * b = 1 ∧  ¬(a = 1 ∨ b = 1)) := by rel [not_imp]
    _ ↔ (∃ a b : ℤ, a * b = 1 ∧  ¬(a = 1 ∨ b = 1)) := by rel [not_imp]
    _ ↔ (∃ a b : ℤ, a * b = 1 ∧  (a ≠ 1 ∧ b ≠ 1)) := by rel [not_or]

example : (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x) ↔ (∀ x : ℝ, ∃ y : ℝ, y > x) :=
  calc
    (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x) ↔ (∀ x : ℝ, ¬ (∀ y : ℝ, y ≤ x)) := by rel [not_exists]
    _ ↔ (∀ x : ℝ, ∃ y : ℝ, ¬ (y ≤ x)) := by rel [not_forall]
    _ ↔ (∀ x : ℝ, ∃ y : ℝ, y > x) := by rel [not_le]

example : ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5) ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 :=
  calc
    ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5) ↔ ∀ m : ℤ, ¬ (∀ n : ℤ, m = n + 5) := by rel [not_exists]
    _ ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 := by rel [not_forall]


#push_neg ¬(∀ n : ℕ, n > 0 → ∃ k l : ℕ, k < n ∧ l < n ∧ k ≠ l)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
#push_neg ¬(∃ x : ℝ, ∀ y : ℝ, ∃ m : ℤ, x < y * m ∧ y * m < m)
#push_neg ¬(∃ x : ℝ, ∀ q : ℝ, q > x → ∃ m : ℕ, q ^ m > x)


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  push_neg
  use 1 / 2
  numbers

example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  intro t
  obtain h | h := le_or_lt t (9 / 2)
  . right
    calc
      t ≤ 9 / 2 := h
      _ < 5 := by numbers
  . left
    calc
      t > 9 / 2 := h
      _ > 4 := by numbers


example : ¬ Int.Even 7 := by
  dsimp [Int.Even]
  push_neg
  intro k h
  have h1 := le_or_succ_le k 3
  obtain h1 | h1 := h1
  . have h2 : (7 : ℤ)  ≤ (6 : ℤ) := by
      calc
        7 = 2 * k := h
        _ ≤ 2 * 3 := by rel [h1]
        _ = 6 := by ring
    numbers at h2
  . have h2 : (8 : ℤ)  ≤ (7 : ℤ) := by
      calc
        7 = 2 * k := h
        _ ≥ 2 * 4 := by rel [h1]
        _ = 8 := by ring
    numbers at h2

example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  right
  use k
  constructor
  apply hk
  constructor
  apply hk1
  apply hkp

example : ¬ ∃ a : ℤ, ∀ n : ℤ, 2 * a ^ 3 ≥ n * a + 7 := by
  push_neg
  intro h
  use 2 * h ^ 2
  calc
    2 * h ^ 3 = 2 * h ^ 2 * h := by ring
    _ < 2 * h ^ 2 * h + 7 := by extra

example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro H
    have hn : Prime p := by
      apply prime_test
      apply hp2
      apply H
    contradiction
  push_neg at  H
  apply H
