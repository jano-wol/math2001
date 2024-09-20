/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Int


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  intro h
  have : 0.5 ^ 2 ≥ 0.5 := h 0.5
  numbers at this


example : ¬ 3 ∣ 13 := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain h4 | h5 := le_or_succ_le k 4
  · have h :=
    calc 13 = 3 * k := hk
      _ ≤ 3 * 4 := by rel [h4]
    numbers at h
  · have h :=
    calc 13 = 3 * k := hk
      _ ≥ 3 * 5 := by rel [h5]
    numbers at h

example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  intro h
  obtain ⟨hx, hy⟩ := h
  have H :=
  calc 0 = x + y := by rw [h]
    _ > 0 := by extra
  numbers at H


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro H
  obtain ⟨a, ha⟩ := H
  obtain h1 | h1 := le_or_succ_le a 1
  . have h :=
      calc
        2 = a ^ 2 := by addarith[ha]
        _ ≤ 1 ^ 2 := by rel[h1]
        _ = 1 := by ring
    numbers at h
  . have h :=
      calc
        2 = a ^ 2 := by addarith[ha]
        _ ≥ 2 ^ 2 := by rel[h1]
        _ = 4 := by ring
    numbers at h

example (n : ℤ) : Int.Even n ↔ ¬ Int.Odd n := by
  constructor
  · intro h1 h2
    rw [Int.even_iff_modEq] at h1
    rw [Int.odd_iff_modEq] at h2
    have h :=
    calc 0 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 1 [ZMOD 2] := by rel [h2]
    numbers at h -- contradiction!
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · apply h1
    · contradiction


example (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  . intro h1 h2
    rw [Int.even_iff_modEq] at h2
    rw [Int.odd_iff_modEq] at h1
    have h :=
    calc 0 ≡ n [ZMOD 2] := by rel [h2]
      _ ≡ 1 [ZMOD 2] := by rel [h1]
    numbers at h -- contradiction!
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · contradiction
    · apply h2

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have h :=
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h1 :=
    calc (1:ℤ) = 1 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h1 -- contradiction!
  · have h1 :=
    calc (1:ℤ) ≡ 1 + 3 * 1 [ZMOD 3]:= by extra
      _ = 2 ^ 2 := by ring
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h1 -- contradiction!

example {p : ℕ} (k l : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hkl : p = k * l) :
    ¬(Prime p) := by
  have hk : k ∣ p
  · use l
    apply hkl
  intro h
  obtain ⟨h2, hfact⟩ := h
  have : k = 1 ∨ k = p := hfact k hk
  obtain hk1' | hkp' := this
  · contradiction
  · contradiction


example (a b : ℤ) (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain ⟨q, hq₁, hq₂⟩ := h
  have hb :=
  calc 0 = a - a := by ring
    _ < b * (q + 1) - b * q := by rel [hq₁, hq₂]
    _ = b := by ring
  have h1 :=
  calc b * k = a := by rw [hk]
    _ < b * (q + 1) := hq₂
  cancel b at h1
  have h2 :=
  calc b * k = a := by rw [hk]
    _ > b * q := hq₁
  cancel b at h2
  have h3 : k ≤ q := by addarith [h1]
  have h4 : q < q := by
    calc
      q < k := h2
      _ ≤ q := h3
  have h5 : q = q := by ring
  have h6 : q ≠ q := by
    apply ne_of_lt
    apply h4
  contradiction

example {p : ℕ} (hp : 2 ≤ p)  (T : ℕ) (hTp : p < T ^ 2)
    (H : ∀ (m : ℕ), 1 < m → m < T → ¬ (m ∣ p)) :
    Prime p := by
  apply prime_test hp
  intro m hm1 hmp
  obtain hmT | hmT := lt_or_le m T
  · apply H m hm1 hmT
  intro h_div
  obtain ⟨l, hl⟩ := h_div
  have : l ∣ p
  · have hl2 : p = l * m := by
      calc
        p = m * l := hl
        _ = l * m := by ring
    use m
    apply hl2
  have hl1 :=
    calc m * 1 = m := by ring
      _ < p := hmp
      _ = m * l := hl
  cancel m at hl1
  have hl2 : T * l < T * T := by
    calc
     T * l ≤ m * l := by rel [hmT]
     _ = p := by rw [hl]
     _ <  T ^ 2 := hTp
     _ = T * T := by ring
  cancel T at hl2
  have : ¬ l ∣ p := H l hl1 hl2
  contradiction


example : Prime 79 := by
  apply better_prime_test (T := 9)
  · numbers
  · numbers
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 39
    constructor <;> numbers
  · use 26
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · use 15
    constructor <;> numbers
  · use 13
    constructor <;> numbers
  · use 11
    constructor <;> numbers
  · use 9
    constructor <;> numbers

/-! # Exercises -/


example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  intro h
  obtain ⟨x, h2⟩ := h
  obtain ⟨h2, h3⟩ := h2
  have h6 : 5 ≤ x := by rel [h3]
  have hr : (5 : ℝ) ≤ (4 : ℝ) := by
    calc
      5 ≤ x := h6
      _ ≤ 4 := h2
  numbers at hr


example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  intro h
  obtain ⟨x, h2⟩ := h
  obtain ⟨h2, h3⟩ := h2
  have hx : x ^ 2 ≤ 3 ^ 2 := by
    calc
      x ^ 2 ≤ 8 := h2
      _ ≤ 3 ^ 2 := by numbers
  cancel 2 at hx
  have h2 : x ^ 3 ≤ 27 := by
    calc
      x ^ 3 = x * x ^ 2 := by ring
      _  ≤ 3 * x ^ 2 := by rel [hx]
      _ ≤  3 * 8 := by rel [h2]
      _ ≤ 27 := by numbers
  have hr : (30 : ℝ) ≤ (27 : ℝ) := by
    calc
      30 ≤ x ^ 3 := h3
      _ ≤ 27 := h2
  numbers at hr

example : ¬ Int.Even 7 := by
  intro h
  dsimp [Int.Even] at *
  obtain ⟨k, hk⟩ := h
  have H := le_or_gt k 3
  obtain hx | hx := H
  . have hr : (7 : ℤ) ≤ (6 : ℤ) := by
      calc
        7 = 2 * k := hk
        _ ≤ 2 * 3 := by rel [hx]
        _ = 6 := by ring
    numbers at hr
  have hk2 : 4 ≤ k := by addarith [hx]
  . have hr : (8 : ℤ) ≤ (7 : ℤ) := by
      calc
        7 = 2 * k := hk
        _ ≥ 2 * 4 := by rel [hk2]
        _ = 8 := by ring
    numbers at hr


example {n : ℤ} (hn : n + 3 = 7) : ¬ (Int.Even n ∧ n ^ 2 = 10) := by
  have h : n = 4 := by addarith [hn]
  intro H
  obtain ⟨h1, h2⟩ := H
  have h2 : (16 : ℤ) = (10 : ℤ) := by
    calc
      16 = 4 ^ 2 := by ring
      _ = n ^ 2 := by rw [h]
      _ = 10 := by rw [h2]
  numbers at h2

example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  intro H
  obtain h | h := H
  . have h1 : 3 ≤ -x := by addarith [h]
    have h2 : (9 : ℝ) < (9 : ℝ) := by
      calc
        9 > x ^ 2 := hx
        _ = (-x) * (-x) := by ring
        _ ≥ 3 * (-x) := by rel [h1]
        _ ≥ 3 * 3 := by rel [h1]
        _ = 9 := by ring
    numbers at h2
  . have h2 : (9 : ℝ) < (9 : ℝ) := by
      calc
        9 > x ^ 2 := hx
        _ = (x) * (x) := by ring
        _ ≥ 3 * (x) := by rel [h]
        _ ≥ 3 * 3 := by rel [h]
        _ = 9 := by ring
    numbers at h2

example : ¬ (∃ N : ℕ, ∀ k > N, Nat.Even k) := by
  intro H
  obtain ⟨N, h2⟩ := H
  obtain h1 | h2 := Nat.even_or_odd N
  . obtain ⟨r, hr⟩ := h1
    have o : Nat.Odd (N + 1) := by
      use r
      rw [hr]
    have eq : N + 1 > N := by extra
    have e : Nat.Even (N + 1) := h2 (N + 1) eq
    obtain ⟨v, ho⟩ := o
    obtain ⟨w, he⟩ := e
    obtain h1 | h1 := le_or_gt w v
    . have h4: 2 * v < 2 * w := by
        calc
          2 * v < 2 * v + 1 := by extra
          _ = N + 1 := by rw [ho]
          _ = 2 * w := by rw [he]
      cancel 2 at h4
      have h5 : w < w := by
        calc
          w ≤ v := h1
          _ < w := h4
      have h6 : w = w := by ring
      have h7 : w ≠ w := by
        apply ne_of_lt
        apply h5
      contradiction
    . have h1 : v + 1 ≤ w := by addarith [h1]
      have h4: 2 * w < 2 * (v + 1) := by
        calc
          2 * w = N + 1 := by rw [he]
          _ = 2 * v + 1 := by rw [ho]
          _ < 2 * v + 1 + 1 := by extra
          _ = 2 * (v + 1) := by ring
      cancel 2 at h4
      have h5 : w < w := by
        calc
          w < v + 1 := h4
          _ ≤ w := h1
      have h6 : w = w := by ring
      have h7 : w ≠ w := by
        apply ne_of_lt
        apply h5
      contradiction
  . obtain ⟨r, hr⟩ := h2
    have o : Nat.Odd (N + 2) := by
      use r + 1
      calc
        N + 2 = 2 * r + 1 + 2 := by rw [hr]
        _ = 2 * (r + 1) + 1 := by ring
    have eq : N + 2 > N := by extra
    have e : Nat.Even (N + 2) := h2 (N + 2) eq
    obtain ⟨v, ho⟩ := o
    obtain ⟨w, he⟩ := e
    obtain h1 | h1 := le_or_gt w v
    . have h4: 2 * v < 2 * w := by
        calc
          2 * v < 2 * v + 1 := by extra
          _ = N + 2 := by rw [ho]
          _ = 2 * w := by rw [he]
      cancel 2 at h4
      have h5 : w < w := by
        calc
          w ≤ v := h1
          _ < w := h4
      have h6 : w = w := by ring
      have h7 : w ≠ w := by
        apply ne_of_lt
        apply h5
      contradiction
    . have h1 : v + 1 ≤ w := by addarith [h1]
      have h4: 2 * w < 2 * (v + 1) := by
        calc
          2 * w = N + 2 := by rw [he]
          _ = 2 * v + 1 := by rw [ho]
          _ < 2 * v + 1 + 1 := by extra
          _ = 2 * (v + 1) := by ring
      cancel 2 at h4
      have h5 : w < w := by
        calc
          w < v + 1 := h4
          _ ≤ w := h1
      have h6 : w = w := by ring
      have h7 : w ≠ w := by
        apply ne_of_lt
        apply h5
      contradiction

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  intro h
  mod_cases hn : n % 4
  . have t :=
      calc
        2 ≡ n ^ 2 [ZMOD 4] := by rel [h]
        _ ≡ 0 ^ 2 [ZMOD 4] := by rel [hn]
        _ = 0 := by ring
    numbers at t
  . have t :=
      calc
        2 ≡ n ^ 2 [ZMOD 4] := by rel [h]
        _ ≡ 1 ^ 2 [ZMOD 4] := by rel [hn]
        _ = 1 := by ring
    numbers at t
  . have t :=
      calc
        2 ≡ n ^ 2 [ZMOD 4] := by rel [h]
        _ ≡ 2 ^ 2 [ZMOD 4] := by rel [hn]
        _ = 0 + 4 * 1 := by ring
        _ ≡ 0 [ZMOD 4] := by extra
    numbers at t
  . have t :=
      calc
        2 ≡ n ^ 2 [ZMOD 4] := by rel [h]
        _ ≡ 3 ^ 2 [ZMOD 4] := by rel [hn]
        _ = 1 + 4 * 2 := by ring
        _ ≡ 1 [ZMOD 4] := by extra
    numbers at t


example : ¬ Prime 1 := by
  intro h
  dsimp [Prime] at h
  obtain ⟨h1, h2⟩ := h
  numbers at h1

example : Prime 97 := by
  apply better_prime_test (T := 10)
  · numbers
  · numbers
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 48
    constructor <;> numbers
  · use 32
    constructor <;> numbers
  · use 24
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · use 16
    constructor <;> numbers
  · use 13
    constructor <;> numbers
  · use 12
    constructor <;> numbers
  · use 10
    constructor <;> numbers
