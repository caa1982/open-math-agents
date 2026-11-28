import OMAStatements.S_oeis_a106271
import Mathlib

open OMA.S_oeis_a106271
open PowerSeries

namespace P106271

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
theorem ode (S A : PowerSeries ℚ) (hS : S ^ 2 = 1 - 4 * X)
    (hL : (2 * X - 2 * X ^ 2) * A = (-1 + 4 * X) + (1) * S) :
    (1 - 4 * X + 6 * X ^ 2) * (A) + (1 - 5 * X + 4 * X ^ 2) * (X * d⁄dX ℚ A) = 1 - 4 * X := by
  have hdD : d⁄dX ℚ (1 - 4 * X : PowerSeries ℚ) = -4 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have hS1 := sq_step S _ hS
  rw [hdD] at hS1
  have L0 := hL
  have dP1 : d⁄dX ℚ (2 * X - 2 * X ^ 2 : PowerSeries ℚ) = 2 - 4 * X := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (-1 + 4 * X : PowerSeries ℚ) = 4 := by
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
  have L1 : (2 * X - 12 * X ^ 2 + 18 * X ^ 3 - 8 * X ^ 4) * (X * d⁄dX ℚ A) = (1 - 6 * X + 12 * X ^ 2 - 16 * X ^ 3) + (-1 + 4 * X - 6 * X ^ 2) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (2 * X - 10 * X ^ 2 + 8 * X ^ 3) * E1 + (-2 + 12 * X - 16 * X ^ 2) * L0 + (X - X ^ 2) * hS1
  have key : (-2 * X + 12 * X ^ 2 - 18 * X ^ 3 + 8 * X ^ 4) * (((1 - 4 * X + 6 * X ^ 2) * (A) + (1 - 5 * X + 4 * X ^ 2) * (X * d⁄dX ℚ A)) - (1 - 4 * X)) = 0 := by
    linear_combination (-1 + 9 * X - 30 * X ^ 2 + 46 * X ^ 3 - 24 * X ^ 4) * L0 + (-1 + 5 * X - 4 * X ^ 2) * L1
  have hne : (-2 * X + 12 * X ^ 2 - 18 * X ^ 3 + 8 * X ^ 4 : PowerSeries ℚ) ≠ 0 := by
    apply ne_of_coeff _ 1
    simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

end P106271

theorem OMA.solution : type_of% @OMA.S_oeis_a106271.main := by
  intro S c G hS hS0 hc hG n hn
  have hL : (2 * X - 2 * X ^ 2) * G = (-1 + 4 * X) + (1) * S := by
    linear_combination (S) * hc + (2 * X) * hG - hS
  have e := congrArg (coeff n) (P106271.ode S G hS hL)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simp only [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
  norm_num only at e ⊢
  simp only [P106271.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, P106271.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
