import OMAStatements.S_oeis_a063140
import Mathlib

open OMA.S_oeis_a063140 PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a063140.main := by
  have hr : (20 + X + 4 * PowerSeries.exp ℚ * (6 * X - 5) : PowerSeries ℚ) =
      C (20 : ℚ) + X ^ 1 + C (24 : ℚ) * (PowerSeries.exp ℚ * X ^ 1) - C (20 : ℚ) * PowerSeries.exp ℚ := by
    simp only [map_ofNat, pow_one]; ring
  rw [hr]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_exp, coeff_X_pow, coeff_C]
  rcases n with _ | _ | m
  · simp [a]
  · simp [a]; norm_num
  · simp only [show m + 1 + 1 ≠ 0 by omega, show m + 1 + 1 ≠ 1 by omega, show 1 ≤ m + 1 + 1 by omega,
      if_true, if_false, show m + 1 + 1 - 1 = m + 1 by omega]
    simp only [a, show m + 1 + 1 ≠ 0 by omega, show m + 1 + 1 ≠ 1 by omega, if_false]
    rw [Nat.factorial_succ (m + 1)]
    push_cast
    have h1 : ((m + 1).factorial : ℚ) ≠ 0 := by positivity
    have h2 : (m : ℚ) + 1 + 1 ≠ 0 := by positivity
    field_simp
    ring
