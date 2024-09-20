/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init


def fmod (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fmod (n + d) d
  else if h2 : 0 < d * (n - d) then
    fmod (n - d) d
  else if h3 : n = d then
    0
  else
    n
termination_by _ n d => 2 * n - d

def fdiv (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fdiv (n + d) d - 1
  else if 0 < d * (n - d) then
    fdiv (n - d) d + 1
  else if h3 : n = d then
    1
  else
    0
termination_by _ n d => 2 * n - d


#eval fmod 11 4 -- infoview displays `3`
#eval fdiv 11 4 -- infoview displays `2`
#eval fdiv (- 11) 4 -- infoview displays `2`
#eval fmod (- 11) 4 -- infoview displays `2`
#eval fmod 11 (-4) -- infoview displays `2`


theorem fmod_add_fdiv (n d : ℤ) : fmod n d + d * fdiv n d = n := by
  rw [fdiv, fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_add_fdiv (n + d) d -- inductive hypothesis
    calc fmod (n + d) d + d * (fdiv (n + d) d - 1)
        = (fmod (n + d) d + d * fdiv (n + d) d) - d := by ring
      _ = (n + d) - d := by rw [IH]
      _ = n := by ring
  · -- case `0 < d * (n - d)`
    have IH := fmod_add_fdiv (n - d) d -- inductive hypothesis
    calc fmod (n - d) d + d * (fdiv (n - d) d + 1)
        = (fmod (n - d) d + d * fdiv (n - d) d) + d := by ring
        _ = n := by addarith [IH]
  · -- case `n = d`
    calc 0 + d * 1 = d := by ring
      _ = n := by rw [h3]
  · -- last case
    ring
termination_by _ n d => 2 * n - d



theorem fmod_nonneg_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : 0 ≤ fmod n d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_nonneg_of_pos (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_nonneg_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    extra
  · -- last case
    cancel d at h1
termination_by _ n d hd => 2 * n - d


theorem fmod_lt_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : fmod n d < d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_lt_of_pos (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_lt_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    apply hd
  · -- last case
    have h4 :=
    calc 0 ≤ - d * (n - d) := by addarith [h2]
      _ = d * (d - n) := by ring
    cancel d at h4
    apply lt_of_le_of_ne
    · addarith [h4]
    · apply h3
termination_by _ n d hd => 2 * n - d


example (a b : ℤ) (h : 0 < b) : ∃ r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  use fmod a b
  constructor
  · apply fmod_nonneg_of_pos a h
  constructor
  · apply fmod_lt_of_pos a h
  · use fdiv a b
    have Hab : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
    addarith [Hab]

/-! # Exercises -/


theorem lt_fmod_of_neg (n : ℤ) {d : ℤ} (hd : d < 0) : d < fmod n d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := lt_fmod_of_neg (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := lt_fmod_of_neg (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    apply hd
  · -- last case
    have h4 :=
    calc 0 ≤ - d * (n - d) := by addarith [h2]
      _ = (- d) * (n - d) := by ring
    have h5 : 0 < (- d) := by addarith [hd]
    cancel (- d) at h4
    have h7 : d ≠ n := by exact id (Ne.symm h3)
    apply lt_of_le_of_ne
    · addarith [h4]
    · apply h7
termination_by _ n d hd => 2 * n - d

def T (n : ℤ) : ℤ :=
  if 0 < n then
    T (1 - n) + 2 * n - 1
  else if 0 < - n then
    T (-n)
  else
    0
termination_by T n => 3 * n - 1

theorem T_eq (n : ℤ) : T n = n ^ 2 := by
  rw [T]
  split_ifs with h1 h2 <;> push_neg at *
  · -- case `0 < n`
    have IH := T_eq (1 - n) -- inductive hypothesis
    calc
      T (1 - n) + 2 * n - 1 = (1 - n) ^ 2 + 2 * n - 1 := by rw [IH]
      _ = n ^ 2 := by ring
  · -- case `n < 0`
    have IH := T_eq (-n) -- inductive hypothesis
    calc
      T (-n) = (-n) ^ 2 := by rw [IH]
      _ = n ^ 2 := by ring
  · -- case `n = 0`
    have h3 : 0 ≤ n := by addarith [h2]
    have h4 : n = 0 := by exact Int.le_antisymm h1 h3
    calc
    0 = 0 ^ 2 := by ring
    _ = n ^ 2 := by rw [h4]
termination_by _ n => 3 * n - 1

theorem uniqueness (a b : ℤ) (h : 0 < b) {r s : ℤ}
    (hr : 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b])
    (hs : 0 ≤ s ∧ s < b ∧ a ≡ s [ZMOD b]) : r = s := by
  obtain ⟨h1, h2, h3⟩ := hr
  obtain ⟨x, h5⟩ := h3
  obtain ⟨h6, h7, h8⟩ := hs
  obtain ⟨y, h9⟩ := h8
  have h10: r - s = b * (y - x) := by
    calc
      r - s = (a - s) - (a - r) := by ring
      _ = b * y - b * x := by rw [h9, h5]
      _ = b * (y - x) := by ring
  have h12: b ∣ (r - s) := by
    use (y - x)
    apply h10
  have h13: r - s < b := by
    calc
      r - s ≤ r - 0 := by rel [h6]
      _ = r := by ring
      _ < b := h2
  have h14: -b < r - s := by
    calc
      r - s ≥ 0 - s := by rel [h1]
      _ = -s := by ring
      _ > -b := by addarith[h7]
  have h11: r - s ≠ 0 -> ¬ b ∣ (r - s) := by
    intro h20
    have H := le_or_gt (r - s) 0
    obtain hx | hx := H
    . have h21: r - s < 0 := by
        apply lt_of_le_of_ne
        apply hx
        apply h20
      apply Int.not_dvd_of_exists_lt_and_lt
      use -1
      constructor
      calc
        b * -1 = - b := by ring
        _ < r - s := h14
      calc
        r - s < 0 := h21
        _ = b * (-1 + 1) := by ring
    . apply Int.not_dvd_of_exists_lt_and_lt
      use 0
      constructor
      calc
        b * 0 = 0 := by ring
        _ < r - s := hx
      calc
        r - s < b := h13
        _ = b * (0 + 1) := by ring
  if hh : r - s = 0 then
    addarith[hh]
  else
    push_neg at hh
    have h15 := h11 hh
    contradiction

example (a b : ℤ) (h : 0 < b) : ∃! r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  use fmod a b
  dsimp
  constructor
  constructor
  · apply fmod_nonneg_of_pos a h
  constructor
  · apply fmod_lt_of_pos a h
  · use fdiv a b
    have Hab : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
    addarith [Hab]
  intro y h1
  have h2 : 0 ≤ fmod a b ∧ fmod a b < b ∧ a ≡ fmod a b [ZMOD b] := by
    constructor
    apply fmod_nonneg_of_pos a h
    constructor
    apply fmod_lt_of_pos
    apply h
    use fdiv a b
    have Hab : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
    addarith [Hab]
  have h3 := uniqueness a b h h1 h2
  apply h3
