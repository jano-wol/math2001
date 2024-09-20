/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

-- BOTH:
math2001_init

/-! # Homework 5

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-5,
for clearer statements and any special instructions. -/

@[autograded 4]
theorem problem1 : ∃ a : ℝ, ∀ b : ℝ, ∃ c : ℝ, a + c < b := by
  use -1
  intro b
  use b
  addarith[]

@[autograded 4]
theorem problem2 : forall_sufficiently_large x : ℝ, x ^ 3 - 3 * x ≥ 12 * x ^ 2 := by
  dsimp
  use 30
  intro x
  intro h1
  have h : 3 * x ≤ x ^ 2 := by
    calc
    3 * x ≤ 3 * x + 27 * x := by extra
    _ = 30 * x := by ring
    _ ≤ x * x := by rel [h1]
    _ = x ^ 2 := by ring
  have h2 : 0 ≤ x ^ 2 - 3 * x := by addarith [h]
  calc
    12 * x ^ 2 ≤ 12 * x ^ 2 + (x ^ 2 - 3 * x) := by extra
    _ ≤ 12 * x ^ 2 + (x ^ 2 - 3 * x) + 17 * x ^ 2 := by extra
    _ = 30 * x ^ 2 - 3 * x := by ring
    _ ≤ x * x ^ 2 - 3 * x := by rel [h1]
    _ = x ^ 3 - 3 * x := by ring

@[autograded 3]
theorem problem3 (x : ℝ) : 3 * x + 1 = 10 ↔ x = 3 := by
  constructor
  intro h
  calc
    x = (3 * x + 1) / 3 - 1 / 3 := by ring
    _ = 10 / 3 - 1 / 3 := by rw [h]
    _ = 3 := by ring
  intro h
  calc
    3 * x + 1 = 3 * 3 + 1 := by rw [h]
    _ = 10 := by ring

@[autograded 6]
theorem problem4 (n : ℤ) : n ^ 2 + n + 3 ≡ 0 [ZMOD 5] ↔ n ≡ 1 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  constructor
  intro h
  mod_cases hn : n % 5
  . have h1 :=
      calc
        0 ≡ n ^ 2 + n + 3 [ZMOD 5] := by rel [h]
        _ ≡ 0 ^ 2 + 0 + 3 [ZMOD 5] := by rel [hn]
        _ = 3 + 5 * 0 := by ring
        _ ≡ 3 [ZMOD 5] := by extra
    numbers at h1
  . left
    apply hn
  . have h1 :=
      calc
        0 ≡ n ^ 2 + n + 3 [ZMOD 5] := by rel [h]
        _ ≡ 2 ^ 2 + 2 + 3 [ZMOD 5] := by rel [hn]
        _ = 4 + 5 * 1 := by ring
        _ ≡ 4 [ZMOD 5] := by extra
    numbers at h1
  . right
    apply hn
  . have h1 :=
      calc
        0 ≡ n ^ 2 + n + 3 [ZMOD 5] := by rel [h]
        _ ≡ 4 ^ 2 + 4 + 3 [ZMOD 5] := by rel [hn]
        _ = 3 + 5 * 4 := by ring
        _ ≡ 3 [ZMOD 5] := by extra
    numbers at h1
  intro h
  obtain h1 | h1 := h
  calc
     n ^ 2 + n + 3 ≡ 1 ^ 2 + 1 + 3 [ZMOD 5] := by rel [h1]
     _ = 0 + 5 * 1 := by ring
     _ ≡ 0 [ZMOD 5] := by extra
  calc
     n ^ 2 + n + 3 ≡ 3 ^ 2 + 3 + 3 [ZMOD 5] := by rel [h1]
     _ = 0 + 5 * 3 := by ring
     _ ≡ 0 [ZMOD 5] := by extra

@[autograded 4]
theorem problem5 : ¬ (∃ t : ℝ, 2 * t ≤ 8 ∧ t ≥ 5) := by
  intro h
  obtain ⟨v, h1⟩ := h
  obtain ⟨h2, h3⟩ := h1
  have h2 : v ≤ 4 := by
    calc
      v = (2 * v) / 2 := by ring
      _ ≤ 8 / 2 := by rel [h2]
      _ = 4 := by ring
  have h4 : (5 : ℝ) ≤ (4 : ℝ) := by
    calc
      5 ≤ v := h3
      _ ≤ 4 := h2
  numbers at h4

@[autograded 4]
theorem problem6 : ¬ (∃ a : ℝ, ∀ b : ℝ, a ≤ b) := by
  intro h
  obtain ⟨a, h1⟩ := h
  have h2 : a ≤ (a - 1) := h1 (a - 1)
  have h3 : (0 : ℝ) ≤ (-1 : ℝ) := by
    calc
      0 = a - a := by ring
      _ ≤ (a - 1) - a := by rel [h2]
      _ = -1 := by ring
  numbers at h3
