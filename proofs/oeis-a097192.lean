import OMAStatements.S_oeis_a097192
import Mathlib

open PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a097192.main := by
  intro G hG0 hG n hn
  have hd := congrArg (d⁄dX ℚ) hG
  simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, Derivation.map_one_eq_zero,
    nsmul_eq_mul, show 8 - 1 = 7 from rfl, show 9 - 1 = 8 from rfl] at hd
  have hlin : d⁄dX ℚ (1 - 27 * X : PowerSeries ℚ) = -27 := by
    rw [map_sub, show (27 : PowerSeries ℚ) = C 27 from (map_ofNat C 27).symm, Derivation.leibniz,
      derivative_C, derivative_X, Derivation.map_one_eq_zero]
    simp
  rw [hlin] at hd
  have hne : (G ^ 8 * (1 - 27 * X) ^ 7 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    rw [coeff_zero_eq_constantCoeff_apply] at hG0
    simp [hG0] at this
  have key : (G ^ 8 * (1 - 27 * X) ^ 7) * (9 * (1 - 27 * X) * d⁄dX ℚ G - 216 * G) = 0 := by
    linear_combination hd
  have ode := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have e := congrArg (coeff k) ode
  rw [show (9 : PowerSeries ℚ) = C 9 from (map_ofNat C 9).symm,
    show (216 : PowerSeries ℚ) = C 216 from (map_ofNat C 216).symm,
    show (27 : PowerSeries ℚ) = C 27 from (map_ofNat C 27).symm] at e
  simp only [mul_sub, sub_mul, one_mul, mul_assoc, map_sub, coeff_C_mul] at e
  rcases k with _ | k
  · simp only [coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_X, zero_mul, mul_zero, sub_zero] at e
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative] at e
    simp at e ⊢
    linarith
  · rw [coeff_succ_X_mul, coeff_derivative, coeff_derivative] at e
    simp only [show k + 1 + 1 - 1 = k + 1 by omega]
    push_cast at e ⊢
    linarith
