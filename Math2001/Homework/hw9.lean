/- Copyright (c) Heather Macbeth, 2023-4.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.InjectiveSurjective
import Library.Basic
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

open Function


/-! # Homework 9

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-9,
for clearer statements and any special instructions. -/

@[autograded 3]
theorem problem1 {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  dsimp [Injective] at *
  intro x1 x2 h
  have h2 := hg h
  have h3 := hf h2
  apply h3


@[autograded 4]
theorem problem2a : Bijective (fun (x : ℝ) ↦ 5 + 3 * x) := by
  constructor
  dsimp [Injective]
  intro a1 a2 h
  have h2 : 3 * a1 = 3 * a2 := by addarith [h]
  cancel 3 at h2
  dsimp [Surjective]
  intro b
  use (b / 3 - 5 / 3)
  ring

@[autograded 4]
theorem problem2b : ¬ Bijective (fun (x : ℝ) ↦ 5 + 3 * x) := by
  sorry

@[autograded 5]
theorem problem3 :
    ¬Injective (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ (x + y + z, x - 2 * y + z)) := by
  dsimp [Injective]
  push_neg
  use (0, 0, 0), (1, 0, -1)
  constructor
  dsimp
  numbers
  intro h
  obtain ⟨h1, h2, h3⟩ := h
  numbers at h1

@[autograded 4]
theorem problem4 : Bijective (fun ((r, s) : ℚ × ℚ) ↦ (s, r + 2 * s)) := by
  rw [bijective_iff_exists_inverse]
  use fun (a, b) ↦ (b - 2 * a, a)
  dsimp
  dsimp [Inverse]
  constructor
  ext ⟨x, y⟩
  dsimp
  constructor
  ring
  ring
  ext ⟨x, y⟩
  dsimp
  constructor
  ring
  ring

@[autograded 4]
theorem problem5 : ¬ Surjective (fun ((x, y) : ℚ × ℚ) ↦ x ^ 2 + y ^ 2) := by
  dsimp [Surjective]
  push_neg
  use -1
  intro (x, y) h
  dsimp at h
  have h2 : x ^ 2 + y ^ 2 ≠ -1 := by
    apply ne_of_gt
    calc
      -1 < 0 := by numbers
      _ ≤ x ^ 2 + y ^ 2 := by extra
  contradiction


@[autograded 5]
theorem problem6 : Surjective (fun ((x, y) : ℚ × ℚ) ↦ x ^ 2 - y ^ 2) := by
  dsimp [Surjective]
  intro a
  use (a / 2 + 1 / 2 , a / 2 - 1 / 2)
  dsimp
  ring
