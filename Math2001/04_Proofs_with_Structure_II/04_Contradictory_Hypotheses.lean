/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init


example {y : ℝ} (x : ℝ) (h : 0 < x * y) (hx : 0 ≤ x) : 0 < y := by
  obtain hneg | hpos : y ≤ 0 ∨ 0 < y := le_or_lt y 0
  · -- the case `y ≤ 0`
    have : ¬0 < x * y
    · apply not_lt_of_ge
      calc
        0 = x * 0 := by ring
        _ ≥ x * y := by rel [hneg]
    contradiction
  · -- the case `0 < y`
    apply hpos


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  have : ¬(7 : ℤ) < 3 := by numbers
  contradiction


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  numbers at H -- this is a contradiction!


example (n : ℤ) (hn : n ^ 2 + n + 1 ≡ 1 [ZMOD 3]) :
    n ≡ 0 [ZMOD 3] ∨ n ≡ 2 [ZMOD 3] := by
  mod_cases h : n % 3
  · -- case 1: `n ≡ 0 [ZMOD 3]`
    left
    apply h
  · -- case 2: `n ≡ 1 [ZMOD 3]`
    have H :=
      calc 0 ≡ 0 + 3 * 1 [ZMOD 3] := by extra
      _ = 1 ^ 2 + 1 + 1 := by numbers
      _ ≡ n ^ 2 + n + 1 [ZMOD 3] := by rel [h]
      _ ≡ 1 [ZMOD 3] := hn
    numbers at H -- contradiction!
  · -- case 3: `n ≡ 2 [ZMOD 3]`
    right
    apply h


example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  -- the case `1 < m`
  have h : m ≤ p := by apply Nat.le_of_dvd hp' hmp
  obtain ha | hb : m = p ∨ m < p := eq_or_lt_of_le h
  right
  addarith [ha]
  have hc : ¬m ∣ p := by
    apply H
    apply hm_left
    apply hb
  contradiction


example : Prime 5 := by
  apply prime_test
  · numbers
  intro m hm_left hm_right
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 2
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers


example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  have ha1 := le_or_succ_le a 2
  obtain ha2 | ha3 := ha1
  have hb1 := le_or_succ_le b 1
  obtain hb2 | hb3 := hb1
  have hc1 : c ^ 2 < 3 ^ 2 := by
    calc
      c ^ 2 = a ^ 2 + b ^ 2 := by rw [h_pyth]
      _ ≤ 2 ^ 2 + b ^ 2 := by rel [ha2]
      _ ≤ 2 ^ 2 + 1 ^ 2 := by rel [hb2]
      _ < 3 ^ 2 := by numbers
  cancel 2 at hc1
  have ha3 : a = 1 ∨ a = 2 := by
    interval_cases a
    left
    numbers
    right
    numbers
  have hb3 : b = 1 := by
    interval_cases b
    numbers
  have hc3 : c = 1 ∨ c = 2 := by
    interval_cases c
    left
    numbers
    right
    numbers
  obtain ha4 | ha4 := ha3
  obtain hc4 | hc4 := hc3
  have H :=
    calc
      2 = 1 ^ 2 + 1 ^ 2 := by ring
      _ = a ^ 2 + b ^ 2 := by rw [ha4, hb3]
      _ = c ^ 2 := by rw [h_pyth]
      _ = 1 ^ 2 := by rw [hc4]
      _ = 1 := by ring
  have R :  2 ≠ 1 := by numbers
  contradiction
  have H :=
    calc
      2 = 1 ^ 2 + 1 ^ 2 := by ring
      _ = a ^ 2 + b ^ 2 := by rw [ha4, hb3]
      _ = c ^ 2 := by rw [h_pyth]
      _ = 2 ^ 2 := by rw [hc4]
      _ = 4 := by ring
  have R :  2 ≠ 4 := by numbers
  contradiction
  obtain hc4 | hc4 := hc3
  have H :=
    calc
      5 = 2 ^ 2 + 1 ^ 2 := by ring
      _ = a ^ 2 + b ^ 2 := by rw [ha4, hb3]
      _ = c ^ 2 := by rw [h_pyth]
      _ = 1 ^ 2 := by rw [hc4]
      _ = 1 := by ring
  have R : 5 ≠ 1 := by numbers
  contradiction
  have H :=
    calc
      5 = 2 ^ 2 + 1 ^ 2 := by ring
      _ = a ^ 2 + b ^ 2 := by rw [ha4, hb3]
      _ = c ^ 2 := by rw [h_pyth]
      _ = 2 ^ 2 := by rw [hc4]
      _ = 4 := by ring
  have R : 5 ≠ 4 := by numbers
  contradiction
  have hbc1 : b ^ 2 < c ^ 2 := by
    calc
      b ^ 2 < a ^ 2 + b ^ 2 := by extra
      _ = c ^ 2 := by rw [h_pyth]
  cancel 2 at hbc1
  have hbc2 : b + 1 ≤ c := by addarith [hbc1]
  have hbc3 : c ^ 2 < (b + 1) ^ 2 := by
    calc
      c ^ 2 = a ^ 2 + b ^ 2 := by rw [h_pyth]
      _ ≤ 2 ^ 2 + b ^ 2 := by rel [ha2]
      _ = b ^ 2 + 2 * 2 := by ring
      _ ≤ b ^ 2 + 2 * b := by rel [hb3]
      _ < b ^ 2 + 2 * b + 1 := by extra
      _ = (b + 1) ^ 2 := by ring
  cancel 2 at hbc3
  have hb5 : b + 1 = b + 1 := by ring
  have hb6 : b + 1 ≠ b + 1 := by
    apply ne_of_lt
    calc
      b + 1 ≤ c := hbc2
      _ < b + 1 := hbc3
  contradiction
  apply ha3

/-! # Exercises -/


example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  have h1 := le_or_gt y x
  obtain h2 | h2 := h1
  apply h2
  have h3 : x ^ n < y ^ n := by rel [h2]
  have hc1 : x ^ n = x ^ n := by ring
  have hc2 : x ^ n ≠ x ^ n := by
    apply ne_of_lt
    calc
      x ^ n < y ^ n := h3
      _ ≤ x ^ n := h
  contradiction


example (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  mod_cases h : n % 5
  . have H :=
      calc
        4 ≡ n ^ 2 [ZMOD 5] := by rel [hn]
        _ ≡ 0 ^ 2 [ZMOD 5] := by rel [h]
        _ ≡ 0 [ZMOD 5] := by numbers
    numbers at H
  . have H :=
      calc
        4 ≡ n ^ 2 [ZMOD 5] := by rel [hn]
        _ ≡ 1 ^ 2 [ZMOD 5] := by rel [h]
        _ ≡ 1 [ZMOD 5] := by numbers
    numbers at H
  . left
    apply h
  . right
    apply h
  . have H :=
      calc
        4 ≡ n ^ 2 [ZMOD 5] := by rel [hn]
        _ ≡ 4 ^ 2 [ZMOD 5] := by rel [h]
        _ ≡ 1 + 3 * 5 [ZMOD 5] := by numbers
        _ ≡ 1 [ZMOD 5] := by extra
    numbers at H

example : Prime 7 := by
  apply prime_test
  numbers
  intro m hm_left hm_right
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  use 3
  constructor
  numbers
  numbers
  use 2
  constructor
  numbers
  numbers
  use 1
  constructor
  numbers
  numbers
  use 1
  constructor
  numbers
  numbers
  use 1
  constructor
  numbers
  numbers

example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 + 2 * x - 2 * x - 4 := by ring
      _ = 0 := by addarith [h1]
  rw [mul_eq_zero] at h3
  obtain h3 | h3 := h3
  have h4 : x = -2 := by addarith [h3]
  have h5 : x ≠ -2 := by
    apply ne_of_gt
    calc
      -2 < 1 := by numbers
      _ < x := h2
  contradiction
  addarith [h3]

namespace Nat

example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  dsimp [Prime] at *
  obtain ⟨hand1, hand2⟩ := h
  have h2 := le_or_succ_le p 2
  obtain h2 | h2 := h2
  left
  apply le_antisymm
  apply h2
  apply hand1
  right
  have h3 := Nat.even_or_odd p
  obtain h3 | h3 := h3
  have h4 : 2 ∣ p := by
    dsimp [(· ∣ ·)]
    obtain ⟨x, hx⟩ := h3
    use x
    addarith [hx]
  have h5: 2 = 1 ∨ 2 = p := by
    apply hand2
    apply h4
  obtain h5 | h5 := h5
  have h6 : 2 ≠ 1 := by numbers
  contradiction
  have h7 : 2 = 2 := by numbers
  have h8 : 2 < p := by addarith[h2]
  have h9: 2 ≠ 2 := by
    apply ne_of_gt
    calc
      2 < p := h8
      _ = 2 := by rw [h5]
  contradiction
  apply h3
