import OMAStatements.S_oeis_a104624
import Mathlib

open OMA.S_oeis_a104624 PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a104624.main := by
  intro S G hS hS0 hG n hn
  have e1 : d⁄dX ℚ (S ^ 2) = 2 * S * d⁄dX ℚ S := by
    rw [derivative_pow]; norm_num
  have e2 : d⁄dX ℚ (1 + 4 * X ^ 2 : ℚ⟦X⟧) = 8 * X := by
    rw [show (1 + 4 * X ^ 2 : ℚ⟦X⟧) = C 1 + C 4 * X ^ 2 by simp only [map_one, map_ofNat], map_add, derivative_C,
      Derivation.leibniz, derivative_pow, derivative_C, derivative_X]
    simp only [smul_eq_mul, mul_zero, add_zero, zero_add, map_ofNat]
    norm_num
    ring
  have hd := congrArg (d⁄dX ℚ) hS
  rw [e1, e2] at hd
  have ode : C 2 * d⁄dX ℚ S + C 8 * (X ^ 2 * d⁄dX ℚ S) = C 8 * (X * S) := by
    simp only [map_ofNat]
    linear_combination S * hd - 2 * d⁄dX ℚ S * hS
  have r0 : coeff 2 S * 2 * 2 = 8 * coeff 0 S := by
    have e := congrArg (coeff 1) ode
    simp only [map_add, coeff_C_mul, coeff_derivative, coeff_X_pow_mul', coeff_succ_X_mul] at e
    norm_num at e
    rw [← coeff_zero_eq_constantCoeff_apply] at e
    linarith
  have r1 : ∀ k : ℕ, 2 * (coeff (k + 3) S * ((k : ℚ) + 3)) + 8 * (coeff (k + 1) S * ((k : ℚ) + 1)) =
      8 * coeff (k + 1) S := by
    intro k
    have e := congrArg (coeff (k + 2)) ode
    rw [show k + 2 = (k + 1) + 1 by ring] at e
    simp only [map_add, coeff_C_mul, coeff_derivative, coeff_X_pow_mul', coeff_succ_X_mul] at e
    simp only [show 2 ≤ k + 1 + 1 by omega, if_true, show k + 1 + 1 - 2 = k by omega] at e
    push_cast at e
    rw [show k + 1 + 1 + 1 = k + 3 by ring] at e
    linarith
  have hR : ∀ j : ℕ, ((j : ℚ) + 2) * coeff (j + 2) S + (4 * (j : ℚ) - 4) * coeff j S = 0 := by
    intro j
    rcases j with _ | k
    · push_cast; linarith
    · have := r1 k
      rw [show k + 1 + 2 = k + 3 by ring]
      push_cast
      linarith
  rw [show (2 : ℚ⟦X⟧) = C 2 from (map_ofNat C 2).symm] at hG
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega, hG, map_sub, coeff_C_mul, coeff_X]
  have a1 := hR (k + 1)
  have a0 := hR k
  rw [show k + 1 + 2 = k + 3 by ring] at a1
  push_cast at a1 ⊢
  rcases k with _ | _ | k
  · norm_num at a1 a0 ⊢; (try rw [← coeff_zero_eq_constantCoeff_apply] at a0 ⊢); linarith
  · norm_num at a1 a0 ⊢; (try rw [← coeff_zero_eq_constantCoeff_apply] at a0 ⊢); linarith
  · simp only [show k + 2 + 3 ≠ 1 by omega, show k + 2 + 2 ≠ 1 by omega, show k + 2 + 1 ≠ 1 by omega,
      show k + 2 ≠ 1 by omega, if_false]
    push_cast at a1 a0 ⊢
    linarith
