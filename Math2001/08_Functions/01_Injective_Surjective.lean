/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq
import Library.Theory.ParityModular

math2001_init
set_option pp.funBinderTypes true

open Function
namespace Int


def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n

#eval F 5 -- infoview displays `8`


#check @F -- infoview displays `F : ℕ → ℤ`


def q (x : ℝ) : ℝ := x + 3


#check @q -- infoview displays `q : ℝ → ℝ`


#check fun (x : ℝ) ↦ x ^ 2 -- infoview displays `fun x ↦ x ^ 2 : ℝ → ℝ`


example : Injective q := by
  dsimp [Injective]
  intro x1 x2 h
  dsimp [q] at h
  addarith [h]


example : ¬ Injective (fun x : ℝ ↦ x ^ 2) := by
  dsimp [Injective]
  push_neg
  use -1, 1
  constructor
  · numbers
  · numbers


def s (a : ℚ) : ℚ := 3 * a + 2

example : Surjective s := by
  dsimp [Surjective]
  intro y
  use (y - 2) / 3
  calc s ((y - 2) / 3) = 3 * ((y - 2) / 3) + 2 := by rw [s]
    _ = y := by ring


example : ¬ Surjective (fun x : ℝ ↦ x ^ 2) := by
  dsimp [Surjective]
  push_neg
  use -1
  intro x
  apply ne_of_gt
  calc -1 < 0 := by numbers
    _ ≤ x ^ 2 := by extra


inductive Musketeer
  | athos
  | porthos
  | aramis
  deriving DecidableEq

open Musketeer


def f : Musketeer → Musketeer
  | athos => aramis
  | porthos => aramis
  | aramis => athos


example : ¬ Injective f := by
  dsimp [Injective]
  push_neg
  use athos, porthos
  dsimp [f] -- optional
  exhaust


example : ¬ Surjective f := by
  dsimp [Surjective]
  push_neg
  use porthos
  intro a
  cases a
  · exhaust
  · exhaust
  · exhaust


-- better (more automated) version of the previous proof
example : ¬ Surjective f := by
  dsimp [Surjective]
  push_neg
  use porthos
  intro a
  cases a <;> exhaust


def g : Musketeer → Musketeer
  | athos => porthos
  | porthos => aramis
  | aramis => athos


example : Injective g := by
  dsimp [Injective]
  intro x1 x2 hx
  cases x1 <;> cases x2 <;> exhaust


example : Surjective g := by
  dsimp [Surjective]
  intro y
  cases y
  · use aramis
    exhaust
  · use athos
    exhaust
  · use porthos
    exhaust



example : Injective (fun (x:ℝ) ↦ x ^ 3) := by
  intro x1 x2 hx
  dsimp at hx
  have H : (x1 - x2) * (x1 ^ 2 + x1 * x2 + x2 ^ 2) = 0
  · calc (x1 - x2) * (x1 ^ 2 + x1 * x2 + x2 ^ 2) = x1 ^ 3 - x2 ^ 3 := by ring
      _ = x1 ^ 3 - x1 ^ 3 := by rw [hx]
      _ = 0 := by ring
  rw [mul_eq_zero] at H
  obtain H1 | H2 := H
  · -- case 1: x1 - x2 = 0
    addarith [H1]
  · -- case 2: x1 ^2 + x1 * x2 + x2 ^ 2  = 0
    by_cases hx1 : x1 = 0
    · -- case 2a: x1 = 0
      have hx2 :=
      calc x2 ^ 3 = x1 ^ 3 := by rw [hx]
        _ = 0 ^ 3 := by rw [hx1]
        _ = 0 := by numbers
      cancel 3 at hx2
      calc x1 = 0 := by rw [hx1]
        _ = x2 := by rw [hx2]
    · -- case 2b: x1 ≠ 0
      have :=
      calc 0 < x1 ^ 2 + ((x1 + x2) ^ 2 + x2 ^ 2) := by extra
          _ = 2 * (x1 ^ 2 + x1 * x2 + x2 ^ 2) := by ring
          _ = 2 * 0 := by rw [H2]
          _ = 0 := by ring
      numbers at this -- contradiction!

/-! # Exercises -/


example : Injective (fun (x : ℚ) ↦ x - 12) := by
  dsimp[Injective]
  intro x y hxy
  addarith[hxy]

example : ¬ Injective (fun (x : ℚ) ↦ x - 12) := by
  sorry


example : Injective (fun (x : ℝ) ↦ 3) := by
  sorry

example : ¬ Injective (fun (x : ℝ) ↦ 3) := by
  dsimp[Injective]
  push_neg
  use 0, 1
  constructor
  · numbers
  · numbers

example : Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
  dsimp[Injective]
  intro x y hxy
  have h : 3 * x = 3 * y := by addarith [hxy]
  cancel 3 at h

example : ¬ Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
  sorry


example : Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
  dsimp[Injective]
  intro x y hxy
  have h : 3 * x = 3 * y := by addarith [hxy]
  cancel 3 at h

example : ¬ Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
  sorry


example : Surjective (fun (x : ℝ) ↦ 2 * x) := by
  dsimp[Surjective]
  intro x
  use (x / 2)
  ring

example : ¬ Surjective (fun (x : ℝ) ↦ 2 * x) := by
  sorry


example : Surjective (fun (x : ℤ) ↦ 2 * x) := by
  sorry

example : ¬ Surjective (fun (x : ℤ) ↦ 2 * x) := by
  dsimp[Surjective]
  push_neg
  use 1
  intro k
  by_cases hk : 1 ≤ k
  apply ne_of_gt
  calc
    2 * k ≥ 2 * 1 := by rel [hk]
    _ > 1 := by numbers
  push_neg at hk
  have hk1 : k ≤ 0 := by addarith[hk]
  apply ne_of_lt
  calc
    2 * k ≤ 2 * 0 := by rel [hk1]
    _ < 1 := by numbers



example : Surjective (fun (n : ℕ) ↦ n ^ 2) := by
  sorry

example : ¬ Surjective (fun (n : ℕ) ↦ n ^ 2) := by
  dsimp[Surjective]
  push_neg
  use 2
  intro k
  by_cases hk : 2 ≤ k
  apply ne_of_gt
  calc
    k ^ 2 ≥ 2 ^ 2 := by rel [hk]
    _ > 2 := by numbers
  push_neg at hk
  have hk1 : k ≤ 1 := by addarith[hk]
  apply ne_of_lt
  calc
    k ^ 2 ≤  1 ^ 2 := by rel [hk1]
    _ < 2 := by numbers


inductive White
  | meg
  | jack
  deriving DecidableEq

open White

def h : Musketeer → White
  | athos => jack
  | porthos => meg
  | aramis => jack

example : Injective h := by
  sorry

example : ¬ Injective h := by
  dsimp [Injective]
  push_neg
  use athos, aramis
  exhaust

example : Surjective h := by
  dsimp [Surjective]
  intro x
  cases x
  use porthos
  rw [h]
  use athos
  rw [h]

example : ¬ Surjective h := by
  sorry


def l : White → Musketeer
  | meg => aramis
  | jack => porthos

example : Injective l := by
  dsimp [Injective]
  intro x y h
  cases x <;> cases y <;> exhaust

example : ¬ Injective l := by
  sorry


example : Surjective l := by
  sorry

example : ¬ Surjective l := by
  dsimp [Surjective]
  push_neg
  use athos
  intro x
  cases x <;> exhaust

example (f : X → Y) : Injective f ↔ ∀ x1 x2 : X, x1 ≠ x2 → f x1 ≠ f x2 := by
  dsimp [Injective]
  constructor
  intro inj
  intro x y
  push_neg
  intro neqq
  have h : f x = f y → x = y := by
    exact fun (a : f x = f y) ↦ inj a
  intro neqq2
  have := h neqq2
  contradiction
  intro inj
  intro x y
  have := inj x y
  intro p
  by_cases c : x = y
  apply c
  push_neg at c
  have h := this c
  contradiction



example : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  intro f hf
  dsimp [Injective] at *
  intro x y hxy
  have hxy2 : f x = f y := by addarith[hxy]
  have h : f x = f y → x = y := by
    exact fun (a : f x = f y) ↦ hf a
  have h3 := h hxy2
  apply h3


example : ¬ ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  sorry


example : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + x) := by
  sorry

def c (x : ℚ) : ℚ := -x
example : ¬ ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + x) := by
  push_neg
  use c
  constructor
  dsimp[Injective]
  intro x y h
  rw[c] at h
  rw[c] at h
  addarith [h]
  dsimp[Injective]
  push_neg
  use 0, 1
  constructor
  rw [c]
  rw [c]
  numbers
  numbers


def d (x : ℤ) : ℤ := x
example : ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
  sorry

example : ¬ ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
  push_neg
  use d
  constructor
  dsimp [Surjective] at *
  intro x
  use x
  rw [d]
  dsimp [Surjective] at *
  push_neg
  use 1
  intro b
  have h0 : ¬ (2 ∣ (1 : ℤ)) := by
    intro h
    obtain ⟨k, hr1⟩ := h
    have hr2 : 1 ≠ 2 * k := by
      by_cases hk : 1 ≤ k
      apply ne_of_lt
      calc
        2 * k ≥ 2 * 1 := by rel [hk]
        _ > 1 := by numbers
      push_neg at hk
      have hk1 : k ≤ 0 := by addarith[hk]
      apply ne_of_gt
      calc
        2 * k ≤ 2 * 0 := by rel [hk1]
        _ < 1 := by numbers
    contradiction
  intro b2
  have h1 : (2 ∣ (1 : ℤ)) := by
    use (d b)
    addarith [b2]
  contradiction

example : ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  sorry

example : ¬ ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  dsimp [Surjective]
  push_neg
  use 0
  use 1
  intro a
  intro k
  have h : (0 : ℝ) = 1 := by
    calc
      0 = 0 * a := by ring
      _ = 1 := k
  numbers at h


example {f : ℚ → ℚ} (hf : ∀ x y, x < y → f x < f y) : Injective f := by
  dsimp [Injective]
  intro x y h
  have h := lt_trichotomy x y
  obtain h1 | h1 | h1 := h
  . have h4 := hf x y h1
    have h5 : f x ≠ f y := by
      apply ne_of_lt
      apply h4
    contradiction
  . apply h1
  . have h4 := hf y x h1
    have h5 : f x ≠ f y := by
      apply ne_of_gt
      apply h4
    contradiction


example {f : X → ℕ} {x0 : X} (h0 : f x0 = 0) {i : X → X}
    (hi : ∀ x, f (i x) = f x + 1) : Surjective f := by
  dsimp [Surjective]
  intro b
  simple_induction b with k IH
  . use x0
    apply h0
  . obtain ⟨t, ht⟩ := IH
    use i (t)
    have h1 := hi t
    calc
      f (i t) = f t + 1 := h1
      _ = k + 1 := by rw [ht]
