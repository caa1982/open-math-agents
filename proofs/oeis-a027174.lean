import OMAStatements.S_oeis_a027174
import Mathlib

open OMA.S_oeis_a027174

namespace P027174

theorem ch (N k : ℕ) (h : k ≤ N) : ((N.choose k : ℕ) : ℚ) = (N.factorial : ℚ) / (k.factorial * (N - k).factorial) :=
  Nat.cast_choose ℚ h

noncomputable def E (n : ℕ) : ℚ := ((Nat.choose (2 * n + 4) n : ℕ) : ℚ)

theorem Epos (n : ℕ) : E n ≠ 0 := by
  unfold E; exact_mod_cast (Nat.choose_pos (by omega)).ne'

theorem b1_0 (n : ℕ) : ((Nat.choose (2 * n + 5) n : ℕ) : ℚ) = (E n * ((2 * (n : ℚ) + 5)) / (((n : ℚ) + 5))) := by
  rw [ch _ _ (by omega), show 2 * n + 5 - n = n + 5 by omega]
  unfold E
  rw [ch _ _ (by omega), show 2 * n + 4 - n = n + 4 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  try ring

theorem b1_1 (n : ℕ) : ((Nat.choose (2 * n + 5) (n + 1) : ℕ) : ℚ) = (E n * ((2 * (n : ℚ) + 5)) / (((n : ℚ) + 1))) := by
  rw [ch _ _ (by omega), show 2 * n + 5 - (n + 1) = n + 4 by omega]
  unfold E
  rw [ch _ _ (by omega), show 2 * n + 4 - n = n + 4 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  try ring

theorem b2_1 (n : ℕ) : ((Nat.choose (2 * n + 6) (n + 1) : ℕ) : ℚ) = (E n * ((2 * (n : ℚ) + 5) * (2 * (n : ℚ) + 6)) / (((n : ℚ) + 1) * ((n : ℚ) + 5))) := by
  rw [ch _ _ (by omega), show 2 * n + 6 - (n + 1) = n + 5 by omega]
  unfold E
  rw [ch _ _ (by omega), show 2 * n + 4 - n = n + 4 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  try ring

theorem b3_1 (n : ℕ) : ((Nat.choose (2 * n + 7) (n + 1) : ℕ) : ℚ) = (E n * ((2 * (n : ℚ) + 5) * (2 * (n : ℚ) + 6) * (2 * (n : ℚ) + 7)) / (((n : ℚ) + 1) * ((n : ℚ) + 5) * ((n : ℚ) + 6))) := by
  rw [ch _ _ (by omega), show 2 * n + 7 - (n + 1) = n + 6 by omega]
  unfold E
  rw [ch _ _ (by omega), show 2 * n + 4 - n = n + 4 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  try ring

theorem b3_2 (n : ℕ) : ((Nat.choose (2 * n + 7) (n + 2) : ℕ) : ℚ) = (E n * ((2 * (n : ℚ) + 5) * (2 * (n : ℚ) + 6) * (2 * (n : ℚ) + 7)) / (((n : ℚ) + 1) * ((n : ℚ) + 2) * ((n : ℚ) + 5))) := by
  rw [ch _ _ (by omega), show 2 * n + 7 - (n + 2) = n + 5 by omega]
  unfold E
  rw [ch _ _ (by omega), show 2 * n + 4 - n = n + 4 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  try ring

theorem b4_2 (n : ℕ) : ((Nat.choose (2 * n + 8) (n + 2) : ℕ) : ℚ) = (E n * ((2 * (n : ℚ) + 5) * (2 * (n : ℚ) + 6) * (2 * (n : ℚ) + 7) * (2 * (n : ℚ) + 8)) / (((n : ℚ) + 1) * ((n : ℚ) + 2) * ((n : ℚ) + 5) * ((n : ℚ) + 6))) := by
  rw [ch _ _ (by omega), show 2 * n + 8 - (n + 2) = n + 6 by omega]
  unfold E
  rw [ch _ _ (by omega), show 2 * n + 4 - n = n + 4 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  try ring

theorem b5_2 (n : ℕ) : ((Nat.choose (2 * n + 9) (n + 2) : ℕ) : ℚ) = (E n * ((2 * (n : ℚ) + 5) * (2 * (n : ℚ) + 6) * (2 * (n : ℚ) + 7) * (2 * (n : ℚ) + 8) * (2 * (n : ℚ) + 9)) / (((n : ℚ) + 1) * ((n : ℚ) + 2) * ((n : ℚ) + 5) * ((n : ℚ) + 6) * ((n : ℚ) + 7))) := by
  rw [ch _ _ (by omega), show 2 * n + 9 - (n + 2) = n + 7 by omega]
  unfold E
  rw [ch _ _ (by omega), show 2 * n + 4 - n = n + 4 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  try ring

theorem b5_3 (n : ℕ) : ((Nat.choose (2 * n + 9) (n + 3) : ℕ) : ℚ) = (E n * ((2 * (n : ℚ) + 5) * (2 * (n : ℚ) + 6) * (2 * (n : ℚ) + 7) * (2 * (n : ℚ) + 8) * (2 * (n : ℚ) + 9)) / (((n : ℚ) + 1) * ((n : ℚ) + 2) * ((n : ℚ) + 3) * ((n : ℚ) + 5) * ((n : ℚ) + 6))) := by
  rw [ch _ _ (by omega), show 2 * n + 9 - (n + 3) = n + 6 by omega]
  unfold E
  rw [ch _ _ (by omega), show 2 * n + 4 - n = n + 4 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  try ring

theorem b6_3 (n : ℕ) : ((Nat.choose (2 * n + 10) (n + 3) : ℕ) : ℚ) = (E n * ((2 * (n : ℚ) + 5) * (2 * (n : ℚ) + 6) * (2 * (n : ℚ) + 7) * (2 * (n : ℚ) + 8) * (2 * (n : ℚ) + 9) * (2 * (n : ℚ) + 10)) / (((n : ℚ) + 1) * ((n : ℚ) + 2) * ((n : ℚ) + 3) * ((n : ℚ) + 5) * ((n : ℚ) + 6) * ((n : ℚ) + 7))) := by
  rw [ch _ _ (by omega), show 2 * n + 10 - (n + 3) = n + 7 by omega]
  unfold E
  rw [ch _ _ (by omega), show 2 * n + 4 - n = n + 4 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  try ring

theorem A0 (n : ℕ) : (a n : ℚ) = (E n * ((2 * (n : ℚ) + 5) * (2 * (n : ℚ) + 6)) / (((n : ℚ) + 1) * ((n : ℚ) + 5))) + (E n * ((2 * (n : ℚ) + 5)) / (((n : ℚ) + 5))) + (E n * ((2 * (n : ℚ) + 5)) / (((n : ℚ) + 1))) + E n - 4 := by
  unfold a
  
  push_cast
  rw [b2_1, b1_0, b1_1]
  try rfl

theorem A1 (n : ℕ) : (a (n + 1) : ℚ) = (E n * ((2 * (n : ℚ) + 5) * (2 * (n : ℚ) + 6) * (2 * (n : ℚ) + 7) * (2 * (n : ℚ) + 8)) / (((n : ℚ) + 1) * ((n : ℚ) + 2) * ((n : ℚ) + 5) * ((n : ℚ) + 6))) + (E n * ((2 * (n : ℚ) + 5) * (2 * (n : ℚ) + 6) * (2 * (n : ℚ) + 7)) / (((n : ℚ) + 1) * ((n : ℚ) + 5) * ((n : ℚ) + 6))) + (E n * ((2 * (n : ℚ) + 5) * (2 * (n : ℚ) + 6) * (2 * (n : ℚ) + 7)) / (((n : ℚ) + 1) * ((n : ℚ) + 2) * ((n : ℚ) + 5))) + (E n * ((2 * (n : ℚ) + 5) * (2 * (n : ℚ) + 6)) / (((n : ℚ) + 1) * ((n : ℚ) + 5))) - 4 := by
  unfold a
  rw [show 2 * (n + 1) + 6 = 2 * n + 8 by ring, show 2 * (n + 1) + 5 = 2 * n + 7 by ring, show 2 * (n + 1) + 4 = 2 * n + 6 by ring, show (n + 1) + 1 = n + 2 by ring]
  push_cast
  rw [b4_2, b3_1, b3_2, b2_1]
  try rfl

theorem A2 (n : ℕ) : (a (n + 2) : ℚ) = (E n * ((2 * (n : ℚ) + 5) * (2 * (n : ℚ) + 6) * (2 * (n : ℚ) + 7) * (2 * (n : ℚ) + 8) * (2 * (n : ℚ) + 9) * (2 * (n : ℚ) + 10)) / (((n : ℚ) + 1) * ((n : ℚ) + 2) * ((n : ℚ) + 3) * ((n : ℚ) + 5) * ((n : ℚ) + 6) * ((n : ℚ) + 7))) + (E n * ((2 * (n : ℚ) + 5) * (2 * (n : ℚ) + 6) * (2 * (n : ℚ) + 7) * (2 * (n : ℚ) + 8) * (2 * (n : ℚ) + 9)) / (((n : ℚ) + 1) * ((n : ℚ) + 2) * ((n : ℚ) + 5) * ((n : ℚ) + 6) * ((n : ℚ) + 7))) + (E n * ((2 * (n : ℚ) + 5) * (2 * (n : ℚ) + 6) * (2 * (n : ℚ) + 7) * (2 * (n : ℚ) + 8) * (2 * (n : ℚ) + 9)) / (((n : ℚ) + 1) * ((n : ℚ) + 2) * ((n : ℚ) + 3) * ((n : ℚ) + 5) * ((n : ℚ) + 6))) + (E n * ((2 * (n : ℚ) + 5) * (2 * (n : ℚ) + 6) * (2 * (n : ℚ) + 7) * (2 * (n : ℚ) + 8)) / (((n : ℚ) + 1) * ((n : ℚ) + 2) * ((n : ℚ) + 5) * ((n : ℚ) + 6))) - 4 := by
  unfold a
  rw [show 2 * (n + 2) + 6 = 2 * n + 10 by ring, show 2 * (n + 2) + 5 = 2 * n + 9 by ring, show 2 * (n + 2) + 4 = 2 * n + 8 by ring, show (n + 2) + 1 = n + 3 by ring]
  push_cast
  rw [b6_3, b5_2, b5_3, b4_2]
  try rfl

end P027174

set_option maxRecDepth 100000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a027174.main := by
  intro n
  simp only
  have h := P027174.Epos n
  have e : (((-2 * (((n : ℤ) + 4) + 3) * (139 * ((n : ℤ) + 4) - 175) * a (n + 2) +
      (1279 * ((n : ℤ) + 4) ^ 2 + 1334 * ((n : ℤ) + 4) - 1089) * a (n + 1) -
      2 * (167 * ((n : ℤ) + 4) + 121) * (2 * ((n : ℤ) + 4) - 3) * a n +
      12 * (111 * ((n : ℤ) + 4) ^ 2 + 456 * ((n : ℤ) + 4) + 229)) : ℤ) : ℚ) = 0 := by
    push_cast
    rw [P027174.A2, P027174.A1, P027174.A0]
    field_simp
    ring
  exact_mod_cast e
