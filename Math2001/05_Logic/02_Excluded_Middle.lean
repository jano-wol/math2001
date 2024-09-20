/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


def Superpowered (k : ℕ) : Prop := ∀ n : ℕ, Prime (k ^ k ^ n + 1)


#eval 0 ^ 0 ^ 0 + 1 -- 1
#eval 0 ^ 0 ^ 1 + 1 -- 2
#eval 0 ^ 0 ^ 2 + 1 -- 2


theorem not_superpowered_zero : ¬ Superpowered 0 := by
  intro h
  have one_prime : Prime (0 ^ 0 ^ 0 + 1) := h 0
  conv at one_prime => numbers -- simplifies that statement to `Prime 1`
  have : ¬ Prime 1 := not_prime_one
  contradiction


#eval 1 ^ 1 ^ 0 + 1 -- 2
#eval 1 ^ 1 ^ 1 + 1 -- 2
#eval 1 ^ 1 ^ 2 + 1 -- 2


theorem superpowered_one : Superpowered 1 := by
  intro n
  conv => ring -- simplifies goal from `Prime (1 ^ 1 ^ n + 1)` to `Prime 2`
  apply prime_two


#eval 2 ^ 2 ^ 0 + 1 -- 3
#eval 2 ^ 2 ^ 1 + 1 -- 5
#eval 2 ^ 2 ^ 2 + 1 -- 17
#eval 2 ^ 2 ^ 3 + 1 -- 257
#eval 2 ^ 2 ^ 4 + 1 -- 65537


#eval 3 ^ 3 ^ 0 + 1 -- 4
#eval 3 ^ 3 ^ 1 + 1 -- 28
#eval 3 ^ 3 ^ 2 + 1 -- 19684


theorem not_superpowered_three : ¬ Superpowered 3 := by
  intro h
  dsimp [Superpowered] at h
  have four_prime : Prime (3 ^ 3 ^ 0 + 1) := h 0
  conv at four_prime => numbers -- simplifies that statement to `Prime 4`
  have four_not_prime : ¬ Prime 4
  · apply not_prime 2 2
    · numbers -- show `2 ≠ 1`
    · numbers -- show `2 ≠ 4`
    · numbers -- show `4 = 2 * 2`
  contradiction


example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  by_cases h2 : Superpowered 2
  · use 2
    constructor
    · apply h2
    · apply not_superpowered_three
  · use 1
    constructor
    · apply superpowered_one
    · apply h2


example {P : Prop} (hP : ¬¬P) : P := by
  by_cases hP : P
  · apply hP
  · contradiction

/-! # Exercises -/


def Tribalanced (x : ℝ) : Prop := ∀ n : ℕ, (1 + x / n) ^ n < 3

example : ∃ x : ℝ, Tribalanced x ∧ ¬ Tribalanced (x + 1) := by
  have h0 : Tribalanced 0 := by
    dsimp [Tribalanced] at *
    intro n
    calc
      (1 + 0 / (n : ℝ)) ^ n = (1) ^ n := by ring
      _ = 1 := by ring
      _ < 3 := by numbers
  have h2 : ¬ Tribalanced 2 := by
    dsimp [Tribalanced] at *
    intro h
    have h3 := h 2
    numbers at h3
  by_cases h1 : Tribalanced 1
  . use 1
    constructor
    apply h1
    have h4 : ¬ Tribalanced (1 + 1) := by
      conv => numbers
      apply h2
    apply h4
  . use 0
    constructor
    apply h0
    have h4 : ¬ Tribalanced (0 + 1) := by
      conv => numbers
      apply h1
    apply h4


example (P Q : Prop) : (¬P → ¬Q) ↔ (Q → P) := by
  constructor
  . intro h1
    intro h2
    by_cases h3 : P
    .  apply h3
    .  have h4 : ¬Q := by
         apply h1
         apply h3
       contradiction
  . intro h1
    intro h2
    intro h3
    have h4 := h1 h3
    contradiction


example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  use 1
  constructor
  . apply superpowered_one
  . intro h
    dsimp [Superpowered] at h
    have hf := h 5
    conv at hf => numbers
    have four_not_prime : ¬ Prime 4294967297 := by
      · apply not_prime 641 6700417
        · numbers -- show `641 ≠ 1`
        · numbers -- show `641 ≠ 4294967297`
        · numbers -- show `4294967297 = 641 * 6700417`
    contradiction
