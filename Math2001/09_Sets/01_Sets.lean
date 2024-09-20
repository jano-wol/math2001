/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Set


#check {n : ℤ | n ≤ 3}


example : 1 ∈ {n : ℤ | n ≤ 3} := by
  dsimp
  numbers


namespace Nat
example : 10 ∉ {n : ℕ | Odd n} := by
  dsimp
  rw [← even_iff_not_odd]
  use 5
  numbers
end Nat


example : {a : ℕ | 4 ∣ a} ⊆ {b : ℕ | 2 ∣ b} := by
  dsimp [Set.subset_def] -- optional
  intro a ha
  obtain ⟨k, hk⟩ := ha
  use 2 * k
  calc a = 4 * k := hk
    _ = 2 * (2 * k) := by ring


example : {x : ℝ | 0 ≤ x ^ 2} ⊈ {t : ℝ | 0 ≤ t} := by
  dsimp [Set.subset_def]
  push_neg
  use -3
  constructor
  · numbers
  · numbers


example : {x : ℤ | Int.Odd x} = {a : ℤ | ∃ k, a = 2 * k - 1} := by
  ext x
  dsimp
  constructor
  · intro h
    obtain ⟨l, hl⟩ := h
    use l + 1
    calc x = 2 * l + 1 := by rw [hl]
      _ = 2 * (l + 1) - 1 := by ring
  · intro h
    obtain ⟨k, hk⟩ := h
    use k - 1
    calc x = 2 * k - 1 := by rw [hk]
      _ = 2 * (k - 1) + 1 := by ring


example : {a : ℕ | 4 ∣ a} ≠ {b : ℕ | 2 ∣ b} := by
  ext
  dsimp
  push_neg
  use 6
  right
  constructor
  · apply Nat.not_dvd_of_exists_lt_and_lt
    use 1
    constructor <;> numbers
  · use 3
    numbers


example : {k : ℤ | 8 ∣ 5 * k} = {l : ℤ | 8 ∣ l} := by
  ext n
  dsimp
  constructor
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 5 * a
    calc 5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring


example : {x : ℝ | x ^ 2 - x - 2 = 0} = {-1, 2} := by
  ext x
  dsimp
  constructor
  · intro h
    have hx :=
    calc
      (x + 1) * (x - 2) = x ^ 2 - x - 2 := by ring
        _ = 0 := by rw [h]
    rw [mul_eq_zero] at hx
    obtain hx | hx := hx
    · left
      addarith [hx]
    · right
      addarith [hx]
  · intro h
    obtain h | h := h
    · calc x ^ 2 - x - 2 = (-1) ^ 2 - (-1) - 2 := by rw [h]
        _ = 0 := by numbers
    · calc x ^ 2 - x - 2 = 2 ^ 2 - 2 - 2 := by rw [h]
        _ = 0 := by numbers


example : {1, 3, 6} ⊆ {t : ℚ | t < 10} := by
  dsimp [Set.subset_def]
  intro t ht
  obtain h1 | h3 | h6 := ht
  · addarith [h1]
  · addarith [h3]
  · addarith [h6]

/-! # Exercises -/


example : 4 ∈ {a : ℚ | a < 3} := by
  sorry

example : 4 ∉ {a : ℚ | a < 3} := by
  dsimp
  push_neg
  numbers

example : 6 ∈ {n : ℕ | n ∣ 42} := by
  dsimp
  use 7
  numbers

example : 6 ∉ {n : ℕ | n ∣ 42} := by
  sorry


example : 8 ∈ {k : ℤ | 5 ∣ k} := by
  sorry

example : 8 ∉ {k : ℤ | 5 ∣ k} := by
  dsimp
  apply Int.not_dvd_of_exists_lt_and_lt
  use 1
  constructor
  numbers
  numbers


example : 11 ∈ {n : ℕ | Odd n} := by
  dsimp
  dsimp [Odd]
  use 5
  numbers


example : 11 ∉ {n : ℕ | Odd n} := by
  sorry


example : -3 ∈ {x : ℝ | ∀ y : ℝ, x ≤ y ^ 2} := by
  dsimp
  intro y
  calc
    -3 ≤ 0 := by numbers
    _ ≤ y ^ 2 := by extra

example : -3 ∉ {x : ℝ | ∀ y : ℝ, x ≤ y ^ 2} := by
  sorry


example : {a : ℕ | 20 ∣ a} ⊆ {x : ℕ | 5 ∣ x} := by
  dsimp [Set.subset_def]
  intro x hx
  obtain ⟨k, hk⟩ := hx
  use 4 * k
  calc
    x = 20 * k := hk
    _ = 5 * (4 * k) := by ring


example : {a : ℕ | 20 ∣ a} ⊈ {x : ℕ | 5 ∣ x} := by
  sorry


example : {a : ℕ | 5 ∣ a} ⊆ {x : ℕ | 20 ∣ x} := by
  sorry

example : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
  dsimp [Set.subset_def]
  push_neg
  use 5
  constructor
  use 1
  numbers
  apply Nat.not_dvd_of_exists_lt_and_lt
  use 0
  constructor <;> numbers


example : {r : ℤ | 3 ∣ r} ⊆ {s : ℤ | 0 ≤ s} := by
  sorry

example : {r : ℤ | 3 ∣ r} ⊈ {s : ℤ | 0 ≤ s} := by
  dsimp [Set.subset_def]
  push_neg
  use -3
  constructor
  use -1
  numbers
  numbers

example : {m : ℤ | m ≥ 10} ⊆ {n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n} := by
  dsimp [Set.subset_def]
  intro x hx
  calc
    x ^ 3 - 7 * x ^ 2 = x * x ^ 2 - 7 * x ^ 2 := by ring
    _ ≥ 10 * x ^ 2 - 7 * x ^ 2 := by rel[hx]
    _ = 3 * (x * x) := by ring
    _ ≥ 3 * (10 * x) := by rel [hx]
    _ = 4 * x + 26 * x := by ring
    _ ≥ 4 * x := by extra


example : {m : ℤ | m ≥ 10} ⊈ {n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n} := by
  sorry


namespace Int
example : {n : ℤ | Even n} = {a : ℤ | a ≡ 6 [ZMOD 2]} := by
  ext n
  constructor
  intro hn
  dsimp
  obtain ⟨k, hk⟩ := hn
  calc
    n = 2 * k := hk
    _ = 6 + 2 * (k - 3) := by ring
    _ ≡ 6 [ZMOD 2] := by extra
  intro ha
  dsimp
  obtain ⟨k, hk⟩ := ha
  use k + 3
  calc
    n = (n - 6) + 6 := by ring
    _ = 2 * k + 6 := by rw [hk]
    _ = 2 * (k + 3) := by ring

example : {n : ℤ | Even n} ≠ {a : ℤ | a ≡ 6 [ZMOD 2]} := by
  sorry
end Int


example : {t : ℝ | t ^ 2 - 5 * t + 4 = 0} = {4} := by
  sorry

example : {t : ℝ | t ^ 2 - 5 * t + 4 = 0} ≠ {4} := by
  ext
  dsimp
  push_neg
  use 1
  left
  constructor
  numbers
  numbers


example : {k : ℤ | 8 ∣ 6 * k} = {l : ℤ | 8 ∣ l} := by
  sorry

example : {k : ℤ | 8 ∣ 6 * k} ≠ {l : ℤ | 8 ∣ l} := by
  ext
  dsimp
  push_neg
  use 4
  left
  constructor
  use 3
  numbers
  apply Int.not_dvd_of_exists_lt_and_lt
  use 0
  constructor <;> numbers


example : {k : ℤ | 7 ∣ 9 * k} = {l : ℤ | 7 ∣ l} := by
  ext k
  constructor
  intro hk
  obtain ⟨l, hl⟩ := hk
  dsimp
  use (4 * l - 5 * k)
  calc
    k = 4 * (9 * k) - 35 * k := by ring
    _ = 4 * (7 * l) - 35 * k := by rw [hl]
    _ = 7 * (4 * l - 5 * k) := by ring
  intro hk
  obtain ⟨l, hl⟩ := hk
  dsimp
  use 9 * l
  calc
    9 * k = 9 * (7 * l) := by rw [hl]
    _ = 7 * (9 * l) := by ring


example : {k : ℤ | 7 ∣ 9 * k} ≠ {l : ℤ | 7 ∣ l} := by
  sorry


example : {1, 2, 3} = {1, 2} := by
  sorry

example : {1, 2, 3} ≠ {1, 2} := by
  ext
  push_neg
  use 3
  left
  constructor
  dsimp
  right
  right
  numbers
  dsimp
  push_neg
  constructor
  numbers
  numbers



example : {x : ℝ | x ^ 2 + 3 * x + 2 = 0} = {-1, -2} := by
  ext x
  constructor
  intro h
  dsimp
  dsimp at h
  have h2 : (x + 1) * (x + 2) = 0 := by
    calc
      (x + 1) * (x + 2)  = x ^ 2 + 3 * x + 2 := by ring
      _ = 0 := h
  rw [mul_eq_zero] at h2
  obtain h3 | h3 := h2
  left
  addarith [h3]
  right
  addarith [h3]
  intro h
  dsimp
  dsimp at h
  obtain h3 | h3 := h
  calc
    x ^ 2 + 3 * x + 2 = (-1) ^ 2 + 3 * (-1) + 2 := by rw [h3]
    _ = 0 := by numbers
  calc
    x ^ 2 + 3 * x + 2 = (-2) ^ 2 + 3 * (-2) + 2 := by rw [h3]
    _ = 0 := by numbers
