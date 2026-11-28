import OMAStatements.S_oeis_a202020
import Mathlib

open OMA.S_oeis_a202020
open PowerSeries

namespace Pa202020

theorem nC (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : PowerSeries ℚ) = C (OfNat.ofNat n : ℚ) :=
  (map_ofNat C n).symm

theorem cXd (F : PowerSeries ℚ) (k : ℕ) : coeff k (X * d⁄dX ℚ F) = coeff k F * k := by
  rcases k with _ | k
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

theorem sq_step (S E : PowerSeries ℚ) (h : S ^ 2 = E) : 2 * E * d⁄dX ℚ S = d⁄dX ℚ E * S := by
  have h1 := congrArg (d⁄dX ℚ) h
  simp only [pow_two, Derivation.leibniz, smul_eq_mul] at h1
  linear_combination (-2 * d⁄dX ℚ S) * h + S * h1

theorem th_step (P B U V S : PowerSeries ℚ) (h : P * B = U + V * S) :
    d⁄dX ℚ P * B + P * d⁄dX ℚ B = d⁄dX ℚ U + d⁄dX ℚ V * S + V * d⁄dX ℚ S := by
  have h1 := congrArg (d⁄dX ℚ) h
  simp only [Derivation.leibniz, map_add, smul_eq_mul] at h1
  linear_combination h1

theorem ne_of_coeff (p : PowerSeries ℚ) (m : ℕ) (h : coeff m p ≠ 0) : p ≠ 0 := by
  intro h0; rw [h0, map_zero] at h; exact h rfl

set_option maxHeartbeats 2000000 in
theorem ode (S A : PowerSeries ℚ) (hS : S ^ 2 = 1 - 8 * X + 12 * X ^ 2)
    (hL : (4 * X ^ 2 - 8 * X ^ 3 + 2 * X ^ 4) * A = (1 - 4 * X + 2 * X ^ 2) + (-1) * S) :
    (4 - 36 * X + 108 * X ^ 2 - 124 * X ^ 3 + 36 * X ^ 4) * (A) + (2 - 20 * X + 57 * X ^ 2 - 56 * X ^ 3 + 12 * X ^ 4) * (X * d⁄dX ℚ A) = 4 - 12 * X + 12 * X ^ 2 := by
  have hdD : d⁄dX ℚ (1 - 8 * X + 12 * X ^ 2 : PowerSeries ℚ) = -8 + 24 * X := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have hS1 := sq_step S _ hS
  rw [hdD] at hS1
  have L0 := hL
  have dP1 : d⁄dX ℚ (4 * X ^ 2 - 8 * X ^ 3 + 2 * X ^ 4 : PowerSeries ℚ) = 8 * X - 24 * X ^ 2 + 8 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (1 - 4 * X + 2 * X ^ 2 : PowerSeries ℚ) = -4 + 4 * X := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (-1 : PowerSeries ℚ) = 0 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (4 * X ^ 2 - 48 * X ^ 3 + 196 * X ^ 4 - 360 * X ^ 5 + 305 * X ^ 6 - 104 * X ^ 7 + 12 * X ^ 8) * (X * d⁄dX ℚ A) = (-2 + 26 * X - 122 * X ^ 2 + 274 * X ^ 3 - 298 * X ^ 4 + 136 * X ^ 5 - 24 * X ^ 6) + (2 - 18 * X + 54 * X ^ 2 - 62 * X ^ 3 + 18 * X ^ 4) * S := by
    have hg : (4 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (4 * X - 40 * X ^ 2 + 114 * X ^ 3 - 112 * X ^ 4 + 24 * X ^ 5) * E1 + (-8 + 88 * X - 296 * X ^ 2 + 352 * X ^ 3 - 96 * X ^ 4) * L0 + (-2 * X + 4 * X ^ 2 - X ^ 3) * hS1
  have key : (8 * X ^ 2 - 96 * X ^ 3 + 392 * X ^ 4 - 720 * X ^ 5 + 610 * X ^ 6 - 208 * X ^ 7 + 24 * X ^ 8) * (((4 - 36 * X + 108 * X ^ 2 - 124 * X ^ 3 + 36 * X ^ 4) * (A) + (2 - 20 * X + 57 * X ^ 2 - 56 * X ^ 3 + 12 * X ^ 4) * (X * d⁄dX ℚ A)) - (4 - 12 * X + 12 * X ^ 2)) = 0 := by
    linear_combination (8 - 152 * X + 1164 * X ^ 2 - 4684 * X ^ 3 + 10772 * X ^ 4 - 14268 * X ^ 5 + 10292 * X ^ 6 - 3504 * X ^ 7 + 432 * X ^ 8) * L0 + (4 - 40 * X + 114 * X ^ 2 - 112 * X ^ 3 + 24 * X ^ 4) * L1
  have hne : (8 * X ^ 2 - 96 * X ^ 3 + 392 * X ^ 4 - 720 * X ^ 5 + 610 * X ^ 6 - 208 * X ^ 7 + 24 * X ^ 8 : PowerSeries ℚ) ≠ 0 := by
    apply ne_of_coeff _ 2
    simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

end Pa202020

theorem OMA.solution : type_of% @OMA.S_oeis_a202020.main := by
  intro S G hS hS0 hL n hn
  have hL' : (4 * X ^ 2 - 8 * X ^ 3 + 2 * X ^ 4) * G = (1 - 4 * X + 2 * X ^ 2) + (-1) * S := by
    linear_combination hL
  have e := congrArg (coeff n) (Pa202020.ode S G hS hL')
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega, show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega]
  norm_num only at e ⊢
  simp only [Pa202020.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa202020.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
