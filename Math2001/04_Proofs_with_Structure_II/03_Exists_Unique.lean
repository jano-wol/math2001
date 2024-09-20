/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

namespace Int


example : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2
  dsimp
  constructor
  · numbers
  intro y hy
  calc
    y = (3 * y + 1 - 1) / 3 := by ring
    _ = (7 - 1) / 3 := by rw [hy]
    _ = 2 := by numbers


example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor
  intro a g h
  have g1 : -1 ≤ a - 2 := by addarith [g]
  have h1 : a - 2 ≤ 1 := by addarith [h]
  have h2 : (a - 2) ^ 2 ≤ 1 ^ 2 := by
    apply sq_le_sq'
    apply g1
    apply h1
  calc
    (a - 2) ^ 2 ≤ 1 ^ 2 := h2
    _ = 1 := by ring
  intro y
  intro g
  have h1 : (1 - y) ^ 2 ≤ 1 := by
    apply g
    numbers
    numbers
  have h2 : (3 - y) ^ 2 ≤ 1 := by
    apply g
    numbers
    numbers
  have h3 : (y - 2) ^ 2 = 0 := by
    apply le_antisymm
    calc
      (y - 2) ^ 2 = ((1 - y) ^ 2 + (3 - y) ^ 2 - 2) / 2 := by ring
      _ ≤ (1 + (3 - y) ^ 2 - 2) / 2 := by rel [h1]
      _ ≤ (1 + 1 - 2) / 2 := by rel [h2]
      _ = 0 := by numbers
    extra
  cancel 2 at h3
  addarith [h3]

example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1, ha2⟩ := hx
  have h1 : -a = a
  · apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  have h2 :=
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring


example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ 14 ≡ r [ZMOD 5] := by
  use 4
  dsimp
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 2
    numbers
  intro r hr
  obtain ⟨hr1, hr2, q, hr3⟩ := hr
  have :=
    calc
      5 * 1 < 14 - r := by addarith [hr2]
      _ = 5 * q := by rw [hr3]
  cancel 5 at this
  have :=
    calc
      5 * q = 14 - r := by rw [hr3]
      _ < 5 * 3 := by addarith [hr1]
  cancel 5 at this
  interval_cases q
  addarith [hr3]

/-! # Exercises -/


example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  dsimp
  constructor
  numbers
  intro y h
  calc
    y = (4 * y - 3) / 4 + 3 / 4 := by ring
    _ = 9 / 4 + 3 / 4 := by rw [h]
    _ = 3 := by numbers


example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  intro x
  extra
  intro x h
  have h1 :  x ≤ 0 := by
    apply h
  have h2 : 0 ≤ x := by extra
  apply le_antisymm
  apply h1
  apply h2

example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by
  use 2
  dsimp
  constructor
  constructor
  numbers
  constructor
  numbers
  use 3
  numbers
  intro n hn
  obtain ⟨hr1, hr2, q, hr3⟩ := hn
  have h1 : 3 * 2 < 11 - n := by addarith [hr2]
  have h2 : 11 - n < 3 * 4 := by addarith [hr1]
  have h3 : 3 * 2 < 3 * q := by
   calc
     3 * 2 < 11 - n := by rel [h1]
     _ = 3 * q := by rw [hr3]
  cancel 3 at h3
  have h4 : 3 * q < 3 * 4 := by
   calc
     3 * q = 11 - n := by rw [hr3]
     _ < 3 * 4 := by rel [h2]
  cancel 3 at h4
  interval_cases q
  addarith [hr3]
