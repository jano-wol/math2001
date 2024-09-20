/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init

open Set



example (t : ℝ) : t ∈ {x : ℝ | -1 < x} ∪ {x : ℝ | x < 1} := by
  dsimp
  obtain h | h := le_or_lt t 0
  · right
    addarith [h]
  · left
    addarith [h]


example : {1, 2} ∪ {2, 4} = {1, 2, 4} := by
  ext n
  dsimp
  constructor
  · intro h
    obtain (h | h) | (h | h) := h
    · left
      apply h
    · right
      left
      apply h
  -- and much, much more
    · right
      left
      apply h
    · right
      right
      apply h
  · intro h
    obtain h | (h | h) := h
    left
    left
    apply h
    left
    right
    apply h
    right
    right
    apply h


example : {2, 1} ∪ {2, 4} = {1, 2, 4} := by
  ext n
  dsimp
  exhaust


example : {-2, 3} ∩ {x : ℚ | x ^ 2 = 9} ⊆ {a : ℚ | 0 < a} := by
  dsimp [Set.subset_def]
  intro t h
  obtain ⟨(h1 | h1), h2⟩ := h
  · have :=
    calc (-2) ^ 2 = t ^ 2 := by rw [h1]
      _ = 9 := by rw [h2]
    numbers at this
  · addarith [h1]


example : {n : ℕ | 4 ≤ n} ∩ {n : ℕ | n < 7} ⊆ {4, 5, 6} := by
  dsimp [Set.subset_def]
  intro n h
  obtain ⟨h1, h2⟩ := h
  interval_cases n <;> exhaust


namespace Int
example : {n : ℤ | Even n}ᶜ = {n : ℤ | Odd n} := by
  ext n
  dsimp
  rw [odd_iff_not_even]
end Int


example (x : ℤ) : x ∉ ∅ := by
  dsimp
  exhaust

example (U : Set ℤ) : ∅ ⊆ U := by
  dsimp [Set.subset_def]
  intro x
  exhaust


example : {n : ℤ | n ≡ 1 [ZMOD 5]} ∩ {n : ℤ | n ≡ 2 [ZMOD 5]} = ∅ := by
  ext x
  dsimp
  constructor
  · intro hx
    obtain ⟨hx1, hx2⟩ := hx
    have :=
    calc 1 ≡ x [ZMOD 5] := by rel [hx1]
      _ ≡ 2 [ZMOD 5] := by rel [hx2]
    numbers at this
  · intro hx
    contradiction


example : {n : ℤ | n ≡ 1 [ZMOD 5]} ∩ {n : ℤ | n ≡ 2 [ZMOD 5]} = ∅ := by
  ext x
  dsimp
  suffices ¬(x ≡ 1 [ZMOD 5] ∧ x ≡ 2 [ZMOD 5]) by exhaust
  intro hx
  obtain ⟨hx1, hx2⟩ := hx
  have :=
  calc 1 ≡ x [ZMOD 5] := by rel [hx1]
    _ ≡ 2 [ZMOD 5] := by rel [hx2]
  numbers at this


example (x : ℤ) : x ∈ univ := by dsimp

example (U : Set ℤ) : U ⊆ univ := by
  dsimp [Set.subset_def]
  intro x
  exhaust


example : {x : ℝ | -1 < x} ∪ {x : ℝ | x < 1} = univ := by
  ext t
  dsimp
  suffices -1 < t ∨ t < 1 by exhaust
  obtain h | h := le_or_lt t 0
  · right
    addarith [h]
  · left
    addarith [h]

/-! # Exercises -/


macro "check_equality_of_explicit_sets" : tactic => `(tactic| (ext; dsimp; exhaust))


example : {-1, 2, 4, 4} ∪ {3, -2, 2} = {-1, 2, 4, 3, -2} := by check_equality_of_explicit_sets

example : {0, 1, 2, 3, 4} ∩ {0, 2, 4, 6, 8} = {0, 2, 4} := by
  check_equality_of_explicit_sets

example : {1, 2} ∩ {3} = ∅  := by check_equality_of_explicit_sets

example : {3, 4, 5}ᶜ ∩ {1, 3, 5, 7, 9} = {1, 7, 9} := by
  check_equality_of_explicit_sets

example : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  dsimp [Set.subset_def]
  intro x hx
  obtain ⟨t, ht2⟩ := hx
  have ht : x = 10 * t + 7 := by addarith[ht2]
  constructor
  calc
    x = 10 * t + 7 := ht
    _ = 1 + 2 * (5 * t + 3) := by ring
    _ ≡ 1 [ZMOD 2] := by extra
  calc
    x = 10 * t + 7 := ht
    _ = 2 + 5 * (2 * t + 1) := by ring
    _ ≡ 2 [ZMOD 5] := by extra


example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  dsimp [Set.subset_def]
  intro x hx
  obtain ⟨t1, t2⟩ := hx
  obtain ⟨r, ht1⟩ := t1
  obtain ⟨s, ht2⟩ := t2
  use (2 * r - 3 * s)
  calc
    x = 16 * x - 15 * x := by ring
    _ = 16 * (5 * r) - 15 * (x) := by rw [ht1]
    _ = 16 * (5 * r) - 15 * (8 * s) := by rw [ht2]
    _ = 40 * (2 * r - 3 * s) := by ring

example :
    {n : ℤ | 3 ∣ n} ∪ {n : ℤ | 2 ∣ n} ⊆ {n : ℤ | n ^ 2 ≡ 1 [ZMOD 6]}ᶜ := by
  dsimp [Set.subset_def]
  intro x hx
  intro con
  obtain hx | hx := hx
  . obtain ⟨t, ht⟩ := con
    have ht2 : x ^ 2 = 6 * t + 1 := by addarith[ht]
    have con2: x ^ 2 ≡ 1 [ZMOD 3] := by
      calc
        x ^ 2 = 6 * t + 1 := ht2
        _ = 1 + 3  * (2 * t) := by ring
        _ ≡ 1 [ZMOD 3] := by extra
    obtain ⟨s, hs⟩ := hx
    have :=
    calc
      1 ≡ x ^ 2 [ZMOD 3] := by rel[con2]
      _ = (3 * s) ^ 2 := by rw [hs]
      _ = 0 + 3 * (3 * s ^ 2) := by ring
      _ ≡ 0 [ZMOD 3] := by extra
    numbers at this
  . obtain ⟨t, ht⟩ := con
    have ht2 : x ^ 2 = 6 * t + 1 := by addarith[ht]
    have con2: x ^ 2 ≡ 1 [ZMOD 2] := by
      calc
        x ^ 2 = 6 * t + 1 := ht2
        _ = 1 + 2  * (3 * t) := by ring
        _ ≡ 1 [ZMOD 2] := by extra
    obtain ⟨s, hs⟩ := hx
    have :=
    calc
      1 ≡ x ^ 2 [ZMOD 2] := by rel[con2]
      _ = (2 * s) ^ 2 := by rw [hs]
      _ = 0 + 2 * (2 * s ^ 2) := by ring
      _ ≡ 0 [ZMOD 2] := by extra
    numbers at this




def SizeAtLeastTwo (s : Set X) : Prop := ∃ x1 x2 : X, x1 ≠ x2 ∧ x1 ∈ s ∧ x2 ∈ s
def SizeAtLeastThree (s : Set X) : Prop :=
  ∃ x1 x2 x3 : X, x1 ≠ x2 ∧ x1 ≠ x3 ∧ x2 ≠ x3 ∧ x1 ∈ s ∧ x2 ∈ s ∧ x3 ∈ s

example {s t : Set X} (hs : SizeAtLeastTwo s) (ht : SizeAtLeastTwo t)
    (hst : ¬ SizeAtLeastTwo (s ∩ t)) :
    SizeAtLeastThree (s ∪ t) := by
  dsimp [SizeAtLeastTwo] at *
  dsimp [SizeAtLeastThree] at *
  push_neg at hst
  obtain ⟨s1, s2, hs⟩ := hs
  obtain ⟨t1, t2, ht⟩ := ht
  obtain ⟨s3, s4, s5⟩ := hs
  obtain ⟨t3, t4, t5⟩ := ht
  obtain h1 | h1 := hst s1 t1
  . obtain h2 | h2 := hst s2 t2
    . obtain h3 | h3 := hst s1 s2
      . contradiction
      . exhaust
    . obtain (h2 | h2) | h2 | h2 := h2
      . exhaust
      . use t1, t2, s2
        exhaust
      . use s1, s2, t2
        exhaust
      . contradiction
  . obtain (h1 | h1) | h1 := h1
    . contradiction
    . use t1, t2, s1
      exhaust
    . obtain h1 | h1 := h1
      . use s1, s2, t1
        exhaust
      . contradiction
