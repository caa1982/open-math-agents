import OMAStatements.S_oeis_a255932
import Mathlib

open OMA.S_oeis_a255932

namespace OMA.P_oeis_a255932

open Finset

def P (n : ℕ) : ℕ := ∏ i ∈ range n, (2 * i + 1)

theorem G (n : ℕ) : Real.Gamma ((n : ℝ) + 1 / 2) = (P n : ℝ) / 2 ^ n * Real.sqrt Real.pi := by
  induction n with
  | zero => simp only [P, Finset.range_zero, Finset.prod_empty, Nat.cast_zero, zero_add, Nat.cast_one, pow_zero, div_one, one_mul]; exact Real.Gamma_one_half_eq
  | succ n ih =>
    have h : ((n + 1 : ℕ) : ℝ) + 1 / 2 = ((n : ℝ) + 1 / 2) + 1 := by push_cast; ring
    rw [h, Real.Gamma_add_one (by positivity), ih]
    unfold P
    rw [Finset.prod_range_succ]
    push_cast
    ring

theorem den_le (N D : ℕ) (hD : 0 < D) : ((N : ℚ) / (D : ℚ)).den ≤ D := by
  have h := Rat.den_dvd (N : ℤ) (D : ℤ)
  rw [Rat.divInt_eq_div] at h
  push_cast at h
  have := Int.le_of_dvd (by exact_mod_cast hD) h
  exact_mod_cast this

theorem pow_ge (n : ℕ) (hn : 1 ≤ n) : n ≤ 2 ^ (n - 1) := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have := ih hm
      rw [show m + 1 - 1 = (m - 1) + 1 by omega, pow_succ]
      omega

end OMA.P_oeis_a255932

open OMA.P_oeis_a255932 in
theorem OMA.solution : type_of% @OMA.S_oeis_a255932.main := by
  intro n hn
  refine ⟨((P n ^ 2 : ℕ) : ℚ) / ((2 ^ (2 * n + 1) * n : ℕ) : ℚ), ?_, ?_⟩
  · unfold value
    rw [G n]
    have hpi : 0 < Real.pi := Real.pi_pos
    have hs : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt hpi.le
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    push_cast
    field_simp
    rw [hs]
    ring
  · refine le_trans (den_le _ _ (by positivity)) ?_
    have := pow_ge n hn
    calc 2 ^ (2 * n + 1) * n ≤ 2 ^ (2 * n + 1) * 2 ^ (n - 1) := Nat.mul_le_mul_left _ this
      _ = 2 ^ (3 * n) := by rw [← pow_add]; congr 1; omega
