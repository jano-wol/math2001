/- Copyright (c) Heather Macbeth, 2024.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic
import AutograderLib

math2001_init

/-! # Homework 8

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-8,
for clearer statements and any special instructions. -/


-- 1 = -18 * 66 + 29 * 41
-- 1 = -16 * 101 + 49 * 33

@[autograded 4]
theorem problem3 (m : ℤ) (hn : 66 ∣ 41 * m) : 66 ∣ m := by
  obtain ⟨k, hk⟩ := hn
  use (-18 * m + 29 * k)
  calc
    m = (-18 * 66 + 29 * 41) * m := by ring
    _ = -18 * 66 * m + 29 * (41 * m) := by ring
    _ = -18 * 66 * m + 29 * (66 * k) := by rw [hk]
    _ = 66 * (-18 * m + 29 * k) := by ring



@[autograded 6]
theorem problem4 (a : ℤ) : 3333 ∣ a ↔ (101 ∣ a ∧ 33 ∣ a) := by
  constructor
  . intro hn
    obtain ⟨k, hk⟩ := hn
    constructor
    use 33 * k
    calc
      a = 3333 * k := hk
      _ = 101 * (33 * k) := by ring
    use 101 * k
    calc
      a = 3333 * k := hk
      _ = 33 * (101 * k) := by ring
  . intro hn
    obtain ⟨h1, h2⟩ := hn
    obtain ⟨k1, hk1⟩ := h1
    obtain ⟨k2, hk2⟩ := h2
    use (-16 * k2 + 49 * k1)
    calc
      a = (-16 * 101 + 49 * 33) * a := by ring
      _ = -16 * 101 * a + 49 * 33 * a := by ring
      _ = -16 * 101 * (33 * k2) + 49 * 33 * a := by rw [hk2]
      _ = -16 * 101 * (33 * k2) + 49 * 33 * (101 * k1) := by rw [hk1]
      _ = 3333 * (-16 * k2 + 49 * k1) := by ring
