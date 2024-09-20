/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra


example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  have hxt1 : 0 < (-x) * t := by addarith[hxt]
  have hxt2 : 0 < x * (-t) := by
    calc
        0 < (-x) * t := hxt1
        _ = x * (-t) := by ring
  cancel x at hxt2
  have hl : t < 0 := by addarith [hxt2]
  apply ne_of_lt
  apply hl




example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers


example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra


example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6
  use 5
  numbers

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1
  use a
  ring

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  constructor
  calc
    p = (p + p) / 2 := by ring
    _ < (p + q) / 2 := by rel[h]
  calc
    q = (q + q) / 2 := by ring
    _ > (p + q) / 2 := by rel[h]

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  numbers

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 2
  use 9
  numbers

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -0.5
  constructor
  numbers
  numbers


example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 0
  use 0
  numbers

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use x + 1 / 2
  calc
    (x + 1 / 2) ^ 2 = x + x ^ 2 + 1 / 4 := by ring
    _ > x + x ^ 2 := by extra
    _ ≥ x := by extra

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨a, ha⟩ := h
  have H := le_or_gt a 1
  obtain hx | hx := H
  have hxt : 0 < (1 - a) * (-(1 - t)) := by
    calc
      (1 - a) * (-(1 - t)) = (a + t) - a * t - 1 := by ring
      _ > (a * t + 1) - a * t - 1 := by rel [ha]
      _ = 0 := by ring
  have hxt2 : 0 ≤ 1 - a := by addarith[hx]
  cancel (1 - a) at hxt
  apply ne_of_gt
  calc
    t = -(1 - t) + 1 := by ring
    _ > 0 + 1 := by rel[hxt]
    _ = 1 := by ring
  have hxt : 0 < (a - 1) * (1 - t) := by
    calc
      (a - 1) * (1 - t) = (a + t) - a * t - 1 := by ring
      _ > (a * t + 1) - a * t - 1 := by rel [ha]
      _ = 0 := by ring
  have hxt2 : 0 < a - 1 := by addarith[hx]
  cancel (a - 1) at hxt
  apply ne_of_lt
  calc
    1 = 1 - t + t := by ring
    _ > 0 + t := by rel[hxt]
    _ = t := by ring



example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a, ha⟩ := h
  have H := le_or_gt a 2
  obtain hx | hx := H
  apply ne_of_lt
  calc
    m = 2 * a := by rw[ha]
    _ ≤ 2 * 2 := by rel[hx]
    _ < 5 := by numbers
  have h2 : 3 ≤ a := by exact hx
  apply ne_of_gt
  calc
    m = 2 * a := by rw[ha]
    _ ≥ 2 * 3 := by rel[h2]
    _ > 5 := by numbers





example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  have H := le_or_gt n 5
  obtain hx | hx := H
  use 3
  calc
    n * 3 + 7 ≤ 5 * 3 + 7 := by rel[hx]
    _ ≤ 2 * 3 ^ 3 := by numbers
  use n + 4
  have h0 : 7 < n + 4 := by
    calc
      n + 4 > 5 + 4 := by rel [hx]
      _ > 7 := by numbers
  have hyp1 : n * (n + 4) + 7 ≤ (n + 1) * (n + 4) := by
    calc
      n * (n + 4) + 7 ≤ n * (n + 4) + (n + 4) := by rel[h0]
      _ = (n + 1) * (n + 4) := by ring
  have hyp2 : 0 ≤ 2 * (n + 4) ^ 2 - (n + 1) := by
    calc
      2 * (n + 4) ^ 2 - (n + 1) = 2 * n ^ 2 + 15 * n + 31 := by ring
      _ ≥ 0 := by extra
  have hyp3 : 2 * (n + 4) ^ 3 - ((n + 1) * (n + 4)) ≥ 0 :=
  calc
    2 * (n + 4) ^ 3 - ((n + 1) * (n + 4)) = (n + 4) * (2 * (n + 4) ^ 2 - (n + 1)) := by ring
    _ ≥ 0 := by extra
  calc
    n * (n + 4) + 7 ≤ (n + 1) * (n + 4) := by rel[hyp1]
    _ ≤ (n + 1) * (n + 4) + (2 * (n + 4) ^ 3 - ((n + 1) * (n + 4))) := by extra
    _ = 2 * (n + 4) ^ 3 := by ring



example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  use (-a + b + c) / 2
  use (a - b + c) / 2
  use (a + b - c) / 2
  have ha1 : 0 ≤ -a + b + c := by addarith [ha]
  have hb1 : 0 ≤ a - b + c := by addarith [hb]
  have hc1 : 0 ≤ a + b - c := by addarith [hc]
  constructor
  calc
    (-a + b + c) / 2 ≥ 0 / 2 := by rel [ha1]
    _ = 0 := by ring
  constructor
  calc
    (a - b + c) / 2 ≥ 0 / 2 := by rel [hb1]
    _ = 0 := by ring
  constructor
  calc
    (a + b - c) / 2 ≥ 0 / 2 := by rel [hc1]
    _ = 0 := by ring
  constructor
  ring
  constructor
  ring
  ring
