import OMAStatements.S_oeis_a095981
import Mathlib

open OMA.S_oeis_a095981
open PowerSeries

namespace Pa095981

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
theorem ode (S A : PowerSeries ℚ) (hS : S ^ 2 = 1 - 4 * X + 2 * X ^ 2 + 6 * X ^ 3 - 7 * X ^ 4 + 2 * X ^ 5 + X ^ 6)
    (hL : (-2 * X ^ 2 + 2 * X ^ 3) * A = (-1 + 2 * X + X ^ 2 - X ^ 3) + (1) * S) :
    (2 - 9 * X + 12 * X ^ 2 - X ^ 3 - 9 * X ^ 4 + 6 * X ^ 5 - 2 * X ^ 6) * (A) + (1 - 5 * X + 6 * X ^ 2 + 4 * X ^ 3 - 13 * X ^ 4 + 9 * X ^ 5 - X ^ 6 - X ^ 7) * (X * d⁄dX ℚ A) = 4 * X ^ 2 - 9 * X ^ 3 + 6 * X ^ 4 - X ^ 5 + X ^ 6 := by
  have hdD : d⁄dX ℚ (1 - 4 * X + 2 * X ^ 2 + 6 * X ^ 3 - 7 * X ^ 4 + 2 * X ^ 5 + X ^ 6 : PowerSeries ℚ) = -4 + 4 * X + 18 * X ^ 2 - 28 * X ^ 3 + 10 * X ^ 4 + 6 * X ^ 5 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have hS1 := sq_step S _ hS
  rw [hdD] at hS1
  have L0 := hL
  have dP1 : d⁄dX ℚ (-2 * X ^ 2 + 2 * X ^ 3 : PowerSeries ℚ) = -4 * X + 6 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (-1 + 2 * X + X ^ 2 - X ^ 3 : PowerSeries ℚ) = 2 + 2 * X - 3 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (1 : PowerSeries ℚ) = 0 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (2 * X ^ 2 - 12 * X ^ 3 + 22 * X ^ 4 - 4 * X ^ 5 - 34 * X ^ 6 + 44 * X ^ 7 - 20 * X ^ 8 + 2 * X ^ 10) * (X * d⁄dX ℚ A) = (-2 + 13 * X - 28 * X ^ 2 + 14 * X ^ 3 + 36 * X ^ 4 - 63 * X ^ 5 + 36 * X ^ 6 - 3 * X ^ 7 - 4 * X ^ 8) + (2 - 9 * X + 12 * X ^ 2 - X ^ 3 - 9 * X ^ 4 + 6 * X ^ 5 - 2 * X ^ 6) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (-2 * X + 10 * X ^ 2 - 12 * X ^ 3 - 8 * X ^ 4 + 26 * X ^ 5 - 18 * X ^ 6 + 2 * X ^ 7 + 2 * X ^ 8) * E1 + (4 - 22 * X + 32 * X ^ 2 + 12 * X ^ 3 - 64 * X ^ 4 + 50 * X ^ 5 - 8 * X ^ 6 - 6 * X ^ 7) * L0 + (-X + X ^ 2) * hS1
  have key : (2 * X ^ 2 - 12 * X ^ 3 + 22 * X ^ 4 - 4 * X ^ 5 - 34 * X ^ 6 + 44 * X ^ 7 - 20 * X ^ 8 + 2 * X ^ 10) * (((2 - 9 * X + 12 * X ^ 2 - X ^ 3 - 9 * X ^ 4 + 6 * X ^ 5 - 2 * X ^ 6) * (A) + (1 - 5 * X + 6 * X ^ 2 + 4 * X ^ 3 - 13 * X ^ 4 + 9 * X ^ 5 - X ^ 6 - X ^ 7) * (X * d⁄dX ℚ A)) - (4 * X ^ 2 - 9 * X ^ 3 + 6 * X ^ 4 - X ^ 5 + X ^ 6)) = 0 := by
    linear_combination (-2 + 19 * X - 69 * X ^ 2 + 107 * X ^ 3 - 6 * X ^ 4 - 228 * X ^ 5 + 329 * X ^ 6 - 138 * X ^ 7 - 117 * X ^ 8 + 178 * X ^ 9 - 90 * X ^ 10 + 15 * X ^ 11 + 4 * X ^ 12 - 2 * X ^ 13) * L0 + (1 - 5 * X + 6 * X ^ 2 + 4 * X ^ 3 - 13 * X ^ 4 + 9 * X ^ 5 - X ^ 6 - X ^ 7) * L1
  have hne : (2 * X ^ 2 - 12 * X ^ 3 + 22 * X ^ 4 - 4 * X ^ 5 - 34 * X ^ 6 + 44 * X ^ 7 - 20 * X ^ 8 + 2 * X ^ 10 : PowerSeries ℚ) ≠ 0 := by
    apply ne_of_coeff _ 2
    simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

end Pa095981

theorem OMA.solution : type_of% @OMA.S_oeis_a095981.main := by
  intro S G hS hS0 hL n hn
  have hL' : (-2 * X ^ 2 + 2 * X ^ 3) * G = (-1 + 2 * X + X ^ 2 - X ^ 3) + (1) * S := by
    linear_combination hL
  have e := congrArg (coeff n) (Pa095981.ode S G hS hL')
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  simp only [show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega, show k + 7 - 3 = k + 4 by omega, show k + 7 - 4 = k + 3 by omega, show k + 7 - 5 = k + 2 by omega, show k + 7 - 6 = k + 1 by omega, show k + 7 - 7 = k by omega]
  norm_num only at e ⊢
  simp only [Pa095981.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa095981.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
