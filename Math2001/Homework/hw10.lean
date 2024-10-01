/- Copyright (c) Heather Macbeth, 2023-4.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init
set_option quotPrecheck false


/-! # Homework 10

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-10,
for clearer statements and any special instructions. -/


@[autograded 4]
theorem problem1a : { m : ℤ | m ≥ 10 } ⊆ { n : ℤ | n ^ 3 - 8 * n ^ 2 ≥ 2 * n } := by
  dsimp [Set.subset_def]
  intro x hx
  calc
    x ^ 3 - 8 * x ^ 2 = x * x ^ 2 - 8 * x ^ 2 := by ring
    _ ≥ 10 * x ^ 2 - 8 * x ^ 2 := by rel [hx]
    _ = 2 * x ^ 2:= by ring
    _ = x * (2 * x) := by ring
    _ ≥ 10 * (2 * x) := by rel [hx]
    _ = 20 * x := by ring
    _ = 2 * x + (18 * x) := by ring
    _ ≥ 2 * x := by extra

@[autograded 4]
theorem problem1b : { m : ℤ | m ≥ 10 } ⊈ { n : ℤ | n ^ 3 - 8 * n ^ 2 ≥ 2 * n } := by
  sorry


@[autograded 4]
theorem problem2a : { t : ℝ | t ^ 2 - 5 * t + 6 = 0 } = { s : ℝ | s = 2 } := by
  sorry

@[autograded 4]
theorem problem2b : { t : ℝ | t ^ 2 - 5 * t + 6 = 0 } ≠ { s : ℝ | s = 2 } := by
  ext
  dsimp
  push_neg
  use 3
  left
  constructor
  numbers
  numbers



@[autograded 4]
theorem problem3a : {1, 2, 3} = {1, 2} := by
  sorry

@[autograded 4]
theorem problem3b : {1, 2, 3} ≠ {1, 2} := by
  ext
  dsimp
  push_neg
  use 3
  left
  constructor
  right
  right
  numbers
  constructor
  numbers
  numbers


@[autograded 4]
theorem problem4 : { r : ℤ | r ≡ 8 [ZMOD 10] }
    ⊆ { s : ℤ | s ≡ 0 [ZMOD 2] } ∩ { t : ℤ | t ≡ 3 [ZMOD 5] } := by
  dsimp [Set.subset_def]
  intro x hx
  constructor
  obtain ⟨k, hk⟩ := hx
  calc
    x = (x - 8) + 8 := by ring
    _ = 10 * k + 8 := by rw [hk]
    _ = 0 + 2 * (5 * k + 4) := by ring
    _ ≡ 0 [ZMOD 2] := by extra
  obtain ⟨k, hk⟩ := hx
  calc
    x = (x - 8) + 8 := by ring
    _ = 10 * k + 8 := by rw [hk]
    _ = 3 + 5 * (2 * k + 1) := by ring
    _ ≡ 3 [ZMOD 5] := by extra


/-! ### Problem 5 starts here -/

infix:50 "∼" => fun (x y : ℤ) ↦ x + y ≡ 0 [ZMOD 3]

@[autograded 2]
theorem problem51a : Reflexive (· ∼ ·) := by
  sorry

@[autograded 2]
theorem problem51b : ¬ Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  push_neg
  use 1
  numbers

@[autograded 2]
theorem problem52a : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  intro x y h1
  calc
    y + x = x + y := by ring
    _ ≡ 0 [ZMOD 3] := h1

@[autograded 2]
theorem problem52b : ¬ Symmetric (· ∼ ·) := by
  sorry

@[autograded 2]
theorem problem53a : AntiSymmetric (· ∼ ·) := by
  sorry

@[autograded 2]
theorem problem53b : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  push_neg
  use 1, 2
  constructor
  calc
    1 + 2 = 0 + 3 * 1 := by numbers
    _ ≡ 0 [ZMOD 3] := by extra
  constructor
  calc
    2 + 1 = 0 + 3 * 1 := by numbers
    _ ≡ 0 [ZMOD 3] := by extra
  numbers


@[autograded 2]
theorem problem54a : Transitive (· ∼ ·) := by
  sorry

@[autograded 2]
theorem problem54b : ¬ Transitive (· ∼ ·) := by
  dsimp [Transitive]
  push_neg
  use 1, 2, 1
  constructor
  calc
    1 + 2 = 0 + 3 * 1 := by numbers
    _ ≡ 0 [ZMOD 3] := by extra
  constructor
  calc
    2 + 1 = 0 + 3 * 1 := by numbers
    _ ≡ 0 [ZMOD 3] := by extra
  numbers


/-! ### Problem 6 starts here -/

infix:50 "≺" => fun ((x1, y1) : ℝ × ℝ) (x2, y2) ↦ (x1 ≤ x2 ∧ y1 ≤ y2)

@[autograded 2]
theorem problem61a : Reflexive (· ≺ ·) := by
  dsimp [Reflexive]
  intro x
  constructor
  extra
  extra

@[autograded 2]
theorem problem61b : ¬ Reflexive (· ≺ ·) := by
  sorry

@[autograded 2]
theorem problem62a : Symmetric (· ≺ ·) := by
  sorry

@[autograded 2]
theorem problem62b : ¬ Symmetric (· ≺ ·) := by
  dsimp [Symmetric]
  push_neg
  use (0, 0), (1, 1)
  constructor
  constructor
  numbers
  numbers
  left
  numbers

@[autograded 2]
theorem problem63a : AntiSymmetric (· ≺ ·) := by
  dsimp [AntiSymmetric]
  intro (a, b) (c, d) h1
  obtain ⟨h2, h3⟩ := h1
  dsimp at *
  intro h4
  obtain ⟨h5, h6⟩ := h4
  constructor
  apply le_antisymm
  apply h2
  apply h5
  apply le_antisymm
  apply h3
  apply h6

@[autograded 2]
theorem problem63b : ¬ AntiSymmetric (· ≺ ·) := by
  sorry

@[autograded 2]
theorem problem64a : Transitive (· ≺ ·) := by
  dsimp [Transitive]
  intro (a, b) (c, d) (e, f) h1 h2
  dsimp at *
  obtain ⟨h3, h4⟩ := h1
  obtain ⟨h5, h6⟩ := h2
  constructor
  calc
    a ≤ c := h3
    _ ≤ e := h5
  calc
    b ≤ d := h4
    _ ≤ f := h6

@[autograded 2]
theorem problem64b : ¬ Transitive (· ≺ ·) := by
  sorry
