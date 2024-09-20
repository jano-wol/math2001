/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import AutograderLib

math2001_init

open Nat

/-! # Homework 3

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-3,
for clearer statements and any special instructions. -/


@[autograded 3]
theorem problem1 : ∃ x : ℚ, x < 0 ∧ x ^ 2 < 1 := by
  use - 1 / 2
  constructor
  numbers
  numbers

@[autograded 5]
theorem problem2 (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  have h := le_or_gt x 1
  obtain hx | hx := h
  use 2
  calc
    x ≤ 1 := hx
    _ < 2 ^ 2 := by numbers
  use 2 * x
  have h1 : 0 < x - 1 := by addarith [hx]
  have h2 : 0 < (x - 1) * (x + 1) := by extra
  have h3 : 0 < x ^ 2 - 1 := by
    calc
    0 < (x - 1) * (x + 1) := h2
    _ = x ^ 2 - 1 := by ring
  calc
    x ≤ x + (x - 1 / 2) ^ 2 := by extra
    _ = x ^ 2 + 1 / 4 := by ring
    _ < x ^ 2 + 1 / 4 + 3 / 4 := by extra
    _ = x ^ 2 + 1 := by ring
    _ < x ^ 2 + 1 + (x ^ 2 - 1) := by extra
    _ = x ^ 2 + x ^ 2 := by ring
    _ < x ^ 2 + x ^ 2 + 2 * x ^ 2 := by extra
    _ = (2 * x) ^ 2 := by ring



@[autograded 4]
theorem problem3 {x : ℕ} (hx : Odd x) : Odd (x ^ 3) := by
  obtain ⟨n, hn⟩ := hx
  use 4 * n ^ 3 + 6 * n ^ 2 + 3 * n
  calc
    x ^ 3 = (2 * n + 1) ^ 3 := by rw [hn]
    _ = 8 * n ^ 3 + 12 * n ^ 2 + 6 * n + 1 := by ring
    _ = 2 * (4 * n ^ 3 + 6 * n ^ 2 + 3 * n) + 1 := by ring

@[autograded 5]
theorem problem4 (n : ℕ) : ∃ m ≥ n, Odd m := by
  use 2 * n + 1
  constructor
  calc
    n ≤ n + n := by extra
    _ ≤ n + n + 1 := by extra
    _ = 2 * n + 1 := by ring
  use n
  ring



@[autograded 2]
theorem problem5 : (4 : ℤ) ∣ -12 := by
  use -3
  numbers

@[autograded 2]
theorem problem6 : ¬(3 : ℤ) ∣ -11 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use -4
  constructor
  numbers
  numbers

@[autograded 4]
theorem problem7 {a b c : ℤ} (hab : a ^ 2 ∣ b) (hbc : b ^ 3 ∣ c) : a ^ 6 ∣ c := by
  obtain ⟨x, hx⟩ := hab
  obtain ⟨y, hy⟩ := hbc
  use (x ^ 3 * y)
  calc
    c = b ^ 3 * y := by rw [hy]
    _ = (a ^ 2 * x) ^ 3 * y := by rw [hx]
    _ = a ^ 6 * (x ^ 3 * y) := by ring
