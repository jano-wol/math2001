/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init


/-! # Homework 4

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-4,
for clearer statements and any special instructions. -/


@[autograded 4]
theorem problem1 (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) : a ≡ c [ZMOD n] := by
  calc
    a ≡ b [ZMOD n] := h1
    _ ≡ c [ZMOD n] := h2

@[autograded 4]
theorem problem2 {t : ℤ} (h : t ≡ 2 [ZMOD 4]) :
    3 * (t ^ 2 + t - 8) ≡ 3 * (2 ^ 2 + 2 - 8) [ZMOD 4] := by
  apply Int.ModEq.mul
  extra
  apply Int.ModEq.sub
  apply Int.ModEq.add
  rel [h]
  rel [h]
  extra


@[autograded 4]
theorem problem3 {a : ℤ} (ha : a ≡ 3 [ZMOD 5]) :
    a ^ 3 + 4 * a ^ 2 + 3 ≡ 1 [ZMOD 5] := by
  calc
    a ^ 3 + 4 * a ^ 2 + 3 ≡ 3 ^ 3 + 4 * 3 ^ 2 + 3 [ZMOD 5] := by rel [ha]
    _ = 1 + 5 * 13 := by ring
    _ ≡ 1 [ZMOD 5] := by extra


@[autograded 4]
theorem problem4 : ∃ k : ℤ, k > 50 ∧ k ≡ 2 [ZMOD 5] ∧ 5 * k ≡ 6 [ZMOD 8] := by
  use 62
  constructor
  numbers
  constructor
  use 12
  numbers
  use 38
  numbers


@[autograded 5]
theorem problem5 {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by
  mod_cases hn : x % 5
  . calc
      x ^ 5 ≡ 0 ^ 5 [ZMOD 5] := by rel [hn]
      _ = 0 := by ring
      _ ≡ x [ZMOD 5] := by rel [hn]
  . calc
      x ^ 5 ≡ 1 ^ 5 [ZMOD 5] := by rel [hn]
      _ = 1 := by ring
      _ ≡ x [ZMOD 5] := by rel [hn]
  . calc
      x ^ 5 ≡ 2 ^ 5 [ZMOD 5] := by rel [hn]
      _ = 2 + 5 * 6 := by ring
      _ ≡ 2 [ZMOD 5] := by extra
      _ ≡ x [ZMOD 5] := by rel [hn]
  . calc
      x ^ 5 ≡ 3 ^ 5 [ZMOD 5] := by rel [hn]
      _ = 3 + 5 * 48 := by ring
      _ ≡ 3 [ZMOD 5] := by extra
      _ ≡ x [ZMOD 5] := by rel [hn]
  . calc
      x ^ 5 ≡ 4 ^ 5 [ZMOD 5] := by rel [hn]
      _ = 4 + 5 * 204 := by ring
      _ ≡ 4 [ZMOD 5] := by extra
      _ ≡ x [ZMOD 5] := by rel [hn]


@[autograded 4]
theorem problem6 {n : ℤ} (h1 : 5 ∣ n) (h2 : 12 ∣ n) : 60 ∣ n := by
  obtain ⟨v, h3⟩ := h1
  obtain ⟨w, h4⟩ := h2
  use 3 * v - 7 * w
  calc
   n = 36 * n - 35 * n := by ring
   _ = 36 * (5 * v) - 35 * n := by rw [h3]
   _ = 36 * (5 * v) - 35 * (12 * w) := by rw [h4]
   _ = 60 * (3 * v - 7 * w) := by ring
