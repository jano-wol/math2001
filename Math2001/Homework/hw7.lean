/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init


/-! # Homework 7

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-7,
for clearer statements and any special instructions. -/



@[autograded 4]
theorem problem1 (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by
  simple_induction n with k IH
  · -- base case
    left
    numbers
  · -- inductive step
    obtain hk | hk := IH
    · right
      calc (5:ℤ) ^ (k + 1) = 5 * 5 ^ k := by ring
        _ ≡ 5 * 1 [ZMOD 8] := by rel [hk]
        _ = 5 := by numbers
    · left
      calc (5:ℤ) ^ (k + 1) = 5 * 5 ^ k := by ring
        _ ≡ 5 * 5 [ZMOD 8] := by rel [hk]
        _ = 1 + 8 * 3 := by numbers
        _ ≡ 1 [ZMOD 8] := by extra

@[autograded 4]
theorem problem2 : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 5
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc
      (3:ℤ) ^ (k + 1) = 3 * (3 ^ k) := by ring
      _ ≥ 3 * (2 ^ k + 100) := by rel [IH]
      _ = 2 ^ (k + 1) + 2 ^ k + 100 + 200 := by ring
      _ ≥ 2 ^ (k + 1) + 2 ^ k + 100 := by extra
      _ ≥ 2 ^ (k + 1) + 100 := by extra


def y : ℕ → ℕ
  | 0 => 2
  | n + 1 => (y n) ^ 2

@[autograded 4]
theorem problem3 (n : ℕ) : y n = 2 ^ (2 ^ n) := by
  simple_induction n with k IH
  calc
    y 0 = 2 := by rw [y]
    _ = 2 ^ 2 ^ 0 := by numbers
  calc
    y (k + 1) = (y k) ^ 2 := by rw [y]
    _ = (2 ^ 2 ^ k) ^ 2 := by rw [IH]
    _ = 2 ^ 2 ^ (k + 1) := by ring


def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

@[autograded 4]
theorem problem4 (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  simple_induction n with k IH
  calc
    B 0 = 0 := by rw [B]
    _ = 0 * (0 + 1) * (2 * 0 + 1) / 6 := by numbers
  calc
    B (k + 1) = B k + (k + 1 : ℚ) ^ 2 := by rw [B]
    _ = k * (k + 1) * (2 * k + 1) / 6 + (k + 1 : ℚ) ^ 2 := by rw [IH]
    _ = (k + 1) * (k + 1 + 1) * (2 * (k + 1) + 1) / 6 := by ring

def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 5 * b (n + 1) - 6 * b n

@[autograded 4]
theorem problem5 (n : ℕ) : b n = 3 ^ n - 2 ^ n := by
  two_step_induction n with k IH1 IH2
  . calc b 0 = 0 := by rw [b]
      _ = 3 ^ 0 - 2 ^ 0 := by numbers
  . calc b 1 = 1 := by rw [b]
      _ = 3 ^ 1 - 2 ^ 1 := by numbers
  calc
    b (k + 2) = 5 * b (k + 1) - 6 * b k := by rw [b]
    _ = 5 * (3 ^ (k + 1) - 2 ^ (k + 1)) - 6 * (3 ^ k - 2 ^ k) := by rw [IH1, IH2]
    _ = 3 ^ (k + 2) - 2 ^ (k + 2) := by ring

def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

#eval r 8

@[autograded 5]
theorem problem6 : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
  dsimp
  use 7
  intro n hn
  two_step_induction_from_starting_point n, hn with k hk IH1 IH2
  · calc r 7 = 140 := by rfl
      _ ≥ 2 ^ 7 := by numbers
  · calc r 8 = 338 := by rfl
      _ ≥ 2 ^ 8 := by numbers
  calc r (k + 2) = 2 * r (k + 1) + r k := by rw [r]
    _ ≥ 2 * 2 ^ (k + 1) + 2 ^ k := by rel [IH1, IH2]
    _ = 2 ^ (k + 2) + 2 ^ k := by ring
    _ ≥ 2 ^ (k + 2) := by extra
