import OMAStatements.S_oeis_a006186
import Mathlib

open OMA.S_oeis_a006186
open PowerSeries

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a006186.main) := by
  intro h
  have hl : ((PowerSeries.X - 1) * (PowerSeries.X ^ 2 - PowerSeries.X - 1) : PowerSeries ℤ) * PowerSeries.mk (fun n => (a006186 (n + 4) : ℤ)) = PowerSeries.mk (fun n => (a006186 (n + 4) : ℤ)) - C 2 * (PowerSeries.mk (fun n => (a006186 (n + 4) : ℤ)) * X ^ 2) + PowerSeries.mk (fun n => (a006186 (n + 4) : ℤ)) * X ^ 3 := by
    simp only [map_ofNat]; ring
  have hr : ((1 : PowerSeries ℤ) + 5 * PowerSeries.X + 6 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3 : PowerSeries ℤ) = 1 + C 5 * X ^ 1 + C 6 * X ^ 2 + X ^ 3 := by
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
  have e10 := congrArg (coeff 10) h
  have e11 := congrArg (coeff 11) h
  have e12 := congrArg (coeff 12) h
  have e13 := congrArg (coeff 13) h
  have e14 := congrArg (coeff 14) h
  have e15 := congrArg (coeff 15) h
  have e16 := congrArg (coeff 16) h
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_C_mul_X_pow, coeff_X_pow,
    coeff_one, coeff_C] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16
  norm_num at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16
  have hnn : (0 : ℤ) ≤ (a006186 (16 + 4) : ℤ) := Nat.cast_nonneg _
  linarith
