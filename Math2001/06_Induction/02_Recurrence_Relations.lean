/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int


def a (n : ℕ) : ℕ := 2 ^ n


#eval a 20 -- infoview displays `1048576`


def b : ℕ → ℤ
  | 0 => 3
  | n + 1 => b n ^ 2 - 2


#eval b 7 -- infoview displays `316837008400094222150776738483768236006420971486980607`


example (n : ℕ) : Odd (b n) := by
  simple_induction n with k hk
  · -- base case
    use 1
    calc b 0 = 3 := by rw [b]
      _ = 2 * 1 + 1 := by numbers
  · -- inductive step
    obtain ⟨x, hx⟩ := hk
    use 2 * x ^ 2 + 2 * x - 1
    calc b (k + 1) = b k ^ 2 - 2 := by rw [b]
      _ = (2 * x + 1) ^ 2 - 2 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 2 * x - 1) + 1 := by ring


def x : ℕ → ℤ
  | 0 => 5
  | n + 1 => 2 * x n - 1


example (n : ℕ) : x n ≡ 1 [ZMOD 4] := by
  simple_induction n with k IH
  · -- base case
    calc
      x 0 = 5 := by rw [x]
      _ ≡ 1 + 4 * 1 [ZMOD 4] := by numbers
      _ ≡ 1 [ZMOD 4] := by extra
  · -- inductive step
    calc
      x (k + 1) = 2 * x k - 1 := by rw [x]
      _ ≡ 2 * 1 - 1 [ZMOD 4] := by rel [IH]
      _ ≡ 1[ZMOD 4] := by numbers

example (n : ℕ) : x n = 2 ^ (n + 2) + 1 := by
  simple_induction n with k IH
  · -- base case
    calc x 0 = 5 := by rw [x]
      _ = 2 ^ (0 + 2) + 1 := by numbers
  · -- inductive step
    calc x (k + 1) = 2 * x k - 1 := by rw [x]
      _ = 2 * (2 ^ (k + 2) + 1) - 1 := by rw [IH]
      _ = 2 ^ ((k + 1) + 2) + 1 := by ring


def A : ℕ → ℚ
  | 0 => 0
  | n + 1 => A n + (n + 1)


example (n : ℕ) : A n = n * (n + 1) / 2 := by
  simple_induction n with k IH
  · -- base case
    calc A 0 = 0 := by rw [A]
      _ = 0 * (0 + 1) / 2 := by numbers
  · -- inductive step
    calc
      A (k + 1) = A k + (k + 1) := by rw [A]
      _ = k * (k + 1) / 2 + (k + 1) := by rw [IH]
      _ = (k + 1) * (k + 1 + 1) / 2 := by ring



def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

#eval 1 !


example (n : ℕ) : ∀ d, 1 ≤ d → d ≤ n → d ∣ n ! := by
  simple_induction n with k IH
  · -- base case
    intro k hk1 hk
    interval_cases k
  · -- inductive step
    intro d hk1 hk
    obtain hk | hk : d = k + 1 ∨ d < k + 1 := eq_or_lt_of_le hk
    · -- case 1: `d = k + 1`
      use (k !)
      calc
        (k + 1) ! = (k + 1) * (k !) := by rw[factorial]
        _ = d * k ! := by rw [hk]
    · -- case 2: `d < k + 1`
      have hk2 : d ≤ k := by addarith [hk]
      have div := IH d hk1 hk2
      obtain ⟨s, hs⟩ := div
      use s * (k + 1)
      calc
        (k + 1)! = (k + 1) * k ! := by rw [factorial]
        _ = (k + 1) * (d * s) := by rw [hs]
        _ = d * (s * (k + 1)) := by ring


example (n : ℕ) : (n + 1)! ≥ 2 ^ n := by
  have one_fact : (0 + 1) ! = 1 := by
    rw [factorial]
    rw [factorial]
  simple_induction n with k IH
  . calc
      (0 + 1) ! = 1 := by rw [one_fact]
      _ ≥ 2 ^ 0 := by numbers
  . calc
      (k + 1 + 1)! = ((k + 1) + 1) * (k + 1) ! := by rw [factorial]
      _ ≥ ((k + 1) + 1) * 2 ^ k := by rel [IH]
      _ =  2 ^ (k + 1) + k * 2 ^ k := by ring
      _ ≥ 2 ^ (k + 1) := by extra




/-! # Exercises -/


def c : ℕ → ℤ
  | 0 => 7
  | n + 1 => 3 * c n - 10

example (n : ℕ) : Odd (c n) := by
  dsimp [Odd] at *
  simple_induction n with k IH
  . use 3
    calc
      c 0 = 7 := by rw [c]
      _ = 2 * 3 + 1 := by numbers
  . obtain ⟨s, hs⟩ := IH
    use (3 * s - 4)
    calc
      c (k + 1) = 3 * c k - 10 := by rw [c]
      _ = 3 * (2 * s + 1) - 10 := by rw [hs]
      _ = 2 * (3 * s - 4) + 1 := by ring

example (n : ℕ) : c n = 2 * 3 ^ n + 5 := by
  simple_induction n with k IH
  . calc
      c 0 = 7 := by rw [c]
      _ = 2 * 3 ^ 0 + 5 := by numbers
  . calc
      c (k + 1) = 3 * c k - 10 := by rw [c]
      _ = 3 * (2 * 3 ^ k + 5) - 10 := by rw [IH]
      _ = 2 * 3 ^ (k + 1) + 5 := by ring

def y : ℕ → ℕ
  | 0 => 2
  | n + 1 => (y n) ^ 2

example (n : ℕ) : y n = 2 ^ (2 ^ n) := by
  simple_induction n with k IH
  . calc
      y 0 = 2 := by rw [y]
      _ = 2 ^ 2 ^ 0 := by numbers
  . calc
      y (k + 1) = (y k) ^ 2 := by rw [y]
      _ = (2 ^ 2 ^ k) ^ 2 := by rw [IH]
      _ = 2 ^ 2 ^ (k + 1) := by ring

def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

example (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  simple_induction n with k IH
  . calc
      B 0 = 0 := by rw [B]
      _ = 0 * (0 + 1) * (2 * 0 + 1) / 6 := by numbers
  . calc
      B (k + 1) = B k + (k + 1) ^ 2 := by rw [B]
      _ = k * (k + 1) * (2 * k + 1) / 6 + (k + 1) ^ 2 := by rw [IH]
      _ = (k + 1) * (k + 1 + 1) * (2 * (k + 1) + 1) / 6 := by ring

def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)

example (n : ℕ) : S n = 2 - 1 / 2 ^ n := by
  simple_induction n with k IH
  . calc
      S 0 = 1 := by rw [S]
      _ = 2 - 1 / 2 ^ 0 := by numbers
  . calc
      S (k + 1) = S k + (1 / 2 ^ (k + 1)) := by rw [S]
      _ = (2 - 1 / 2 ^ k) + (1 / 2 ^ (k + 1)) := by rw [IH]
      _ = 2 - 1 / 2 ^ (k + 1) := by ring

example (n : ℕ) : 0 < n ! := by
  simple_induction n with k IH
  . calc
      0 ! = 1 := by rw [factorial]
      _ > 0 := by numbers
  . calc
      (k + 1) ! = (k + 1) * (k !) := by rw[factorial]
      _ > (k + 1) * 0 := by rel [IH]
      _ = 0 := by ring

example {n : ℕ} (hn : 2 ≤ n) : Nat.Even (n !) := by
  induction_from_starting_point n, hn with k hk IH
  . have two_fact : (2) ! = 2 := by
      rw [factorial]
      rw [factorial]
      rw [factorial]
    use 1
    calc
      2 ! = 2 := by rw [two_fact]
      _ = 2 * 1 := by numbers
  . obtain ⟨l, hl⟩ := IH
    use (l * (k + 1))
    calc
      (k + 1) ! = (k + 1) * (k !) := by rw[factorial]
      _ = (k + 1) * (2 * l) := by rw [hl]
      _ = 2 * (l * (k + 1)) := by ring



example (n : ℕ) : (n + 1) ! ≤ (n + 1) ^ n := by
  have one_fact : (0 + 1) ! = 1 := by
    rw [factorial]
    rw [factorial]
  simple_induction n with k IH
  . calc
      (0 + 1) ! = 1 := by rw [one_fact]
      _ ≤ (0 + 1) ^ 0 := by numbers
  . have p0 : k + 1 ≤ k + 2 := by addarith[]
    have p : (k + 1) ^ k ≤ (k + 2) ^ k := by rel [p0]
    calc
      (k + 1 + 1)! = ((k + 1) + 1) * (k + 1) ! := by rw [factorial]
      _ ≤ ((k + 1) + 1) * (k + 1) ^ k := by rel [IH]
      _ ≤ ((k + 1) + 1) * (k + 2) ^ k := by rel [p]
      _ = (k + 1 + 1) ^ (k + 1) := by ring
