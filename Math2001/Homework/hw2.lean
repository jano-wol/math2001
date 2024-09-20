/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import AutograderLib

math2001_init

/-! # Homework 2

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-2,
for clearer statements and any special instructions. -/


@[autograded 4]
theorem problem1 {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h : x * (x + 2) = 2 * (x + 2) := by
    calc
      x * (x + 2) = x ^ 2 + 2 * x := by ring
      _ = 4 + 2 * x := by rw [h1]
      _ = 2 * (x + 2) := by ring
  cancel (x + 2) at h


@[autograded 5]
theorem problem2 {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by
  apply le_antisymm
  calc
    s = (3 * s) / 3 := by ring
    _ ≤ -6 / 3 := by rel [h1]
    _ = -2 := by numbers
  calc
    s = (2 * s) / 2 := by ring
    _ ≥ -4 / 2 := by rel [h2]
    _ = -2 := by numbers

@[autograded 2]
theorem problem3 {a b : ℝ} (h : a = 2 - b) : a + b = 2 ∨ a + b = 8 := by
  left
  addarith [h]

@[autograded 4]
theorem problem4 {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
    obtain h | h := h
    calc
      t ^ 2 - t - 6 = (-2) ^ 2 - (-2) - 6 := by rw [h]
      _ = 0 := by ring
    calc
      t ^ 2 - t - 6 = (3) ^ 2 - (3) - 6 := by rw [h]
      _ = 0 := by ring

@[autograded 5]
theorem problem5 {x : ℤ} : 2 * x ≠ 7 := by
  have H := le_or_gt x 3
  obtain hx | hx := H
  apply ne_of_lt
  calc
    2 * x ≤ 2 * 3 := by rel[hx]
    _ < 7 := by numbers
  have h2 : 4 ≤ x := by exact hx
  apply ne_of_gt
  calc
    2 * x ≥ 2 * 4 := by rel[h2]
    _ > 7 := by numbers

@[autograded 5]
theorem problem6 {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have h : t ^ 2 * (t - 1) = 0 := by
    calc
      t ^ 2 * (t - 1) = t ^ 3 - t ^ 2 := by ring
      _ = t ^ 2 - t ^ 2 := by rw [ht]
      _ = 0 := by ring
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h
  obtain h3 | h3 := h2
  cancel 2 at h3
  right
  apply h3
  left
  addarith [h3]
