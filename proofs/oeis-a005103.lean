import OMAStatements.S_oeis_a005103
import Mathlib

open OMA.S_oeis_a005103
open PowerSeries

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a005103.main) := by
  intro h
  have hl : ((1 : PowerSeries ℤ) - 2 * PowerSeries.X + 2 * PowerSeries.X ^ 3) * PowerSeries.mk (fun n => (a005103 n : ℤ)) = PowerSeries.mk (fun n => (a005103 n : ℤ)) - C 2 * (PowerSeries.mk (fun n => (a005103 n : ℤ)) * X ^ 1) + C 2 * (PowerSeries.mk (fun n => (a005103 n : ℤ)) * X ^ 3) := by
    simp only [map_ofNat]; ring
  have hr : (1 + PowerSeries.X + 2 * PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3 + 6 * PowerSeries.X ^ 4 : PowerSeries ℤ) = 1 + X ^ 1 + C 2 * X ^ 2 + C 2 * X ^ 3 + C 6 * X ^ 4 := by
    simp only [map_ofNat, pow_one]
  rw [hl, hr] at h
  have e0 := congrArg (coeff 0) h
  have e1 := congrArg (coeff 1) h
  have e2 := congrArg (coeff 2) h
  have e3 := congrArg (coeff 3) h
  have e4 := congrArg (coeff 4) h
  have e5 := congrArg (coeff 5) h
  have e6 := congrArg (coeff 6) h
  have e7 := congrArg (coeff 7) h
  have e8 := congrArg (coeff 8) h
  have e9 := congrArg (coeff 9) h
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_C_mul_X_pow, coeff_X_pow,
    coeff_one, coeff_C] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  norm_num at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  have hnn : (0 : ℤ) ≤ (a005103 9 : ℤ) := Nat.cast_nonneg _
  linarith
