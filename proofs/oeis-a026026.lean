import OMAStatements.S_oeis_a026026
import Mathlib

open OMA.S_oeis_a026026
open PowerSeries

namespace Pa026026

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
    (hL : (128 * X ^ 3) * A = (64 - 448 * X + 960 * X ^ 2 - 640 * X ^ 3) + (-64 + 320 * X - 448 * X ^ 2 + 128 * X ^ 3) * S) :
    (114 - 306 * X - 16 * X ^ 2) * (A) + (5 - 32 * X + 84 * X ^ 2) * (X * d⁄dX ℚ A) + (-11 + 70 * X - 104 * X ^ 2) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = 80 * X ^ 2 := by
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
  have dP1 : d⁄dX ℚ (128 * X ^ 3 : PowerSeries ℚ) = 384 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (64 - 448 * X + 960 * X ^ 2 - 640 * X ^ 3 : PowerSeries ℚ) = -448 + 1920 * X - 1920 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (-64 + 320 * X - 448 * X ^ 2 + 128 * X ^ 3 : PowerSeries ℚ) = 320 - 896 * X + 384 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (2 * X ^ 3 - 8 * X ^ 4) * (X * d⁄dX ℚ A) = (-3 + 26 * X - 71 * X ^ 2 + 60 * X ^ 3) + (3 - 20 * X + 37 * X ^ 2 - 14 * X ^ 3 - 4 * X ^ 4) * S := by
    have hg : (64 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (X - 4 * X ^ 2) * E1 + (-3 + 12 * X) * L0 + (-32 * X + 160 * X ^ 2 - 224 * X ^ 3 + 64 * X ^ 4) * hS1
  have dP2 : d⁄dX ℚ (2 * X ^ 3 - 8 * X ^ 4 : PowerSeries ℚ) = 6 * X ^ 2 - 32 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU2 : d⁄dX ℚ (-3 + 26 * X - 71 * X ^ 2 + 60 * X ^ 3 : PowerSeries ℚ) = 26 - 142 * X + 180 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV2 : d⁄dX ℚ (3 - 20 * X + 37 * X ^ 2 - 14 * X ^ 3 - 4 * X ^ 4 : PowerSeries ℚ) = -20 + 74 * X - 42 * X ^ 2 - 16 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E2 := th_step _ _ _ _ _ L1
  simp only [dP2, dU2, dV2] at E2
  have L2 : (-2 * X ^ 3 + 16 * X ^ 4 - 32 * X ^ 5) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = (-9 + 100 * X - 383 * X ^ 2 + 568 * X ^ 3 - 240 * X ^ 4) + (9 - 82 * X + 237 * X ^ 2 - 222 * X ^ 3 + 32 * X ^ 4 - 8 * X ^ 5) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (-2 * X + 8 * X ^ 2) * E2 + (6 - 32 * X) * L1 + (-3 * X + 20 * X ^ 2 - 37 * X ^ 3 + 14 * X ^ 4 + 4 * X ^ 5) * hS1
  have key : (128 * X ^ 3 - 1024 * X ^ 4 + 2048 * X ^ 5) * (((114 - 306 * X - 16 * X ^ 2) * (A) + (5 - 32 * X + 84 * X ^ 2) * (X * d⁄dX ℚ A) + (-11 + 70 * X - 104 * X ^ 2) * (X * d⁄dX ℚ (X * d⁄dX ℚ A))) - (80 * X ^ 2)) = 0 := by
    linear_combination (114 - 1218 * X + 4256 * X ^ 2 - 4768 * X ^ 3 - 256 * X ^ 4) * L0 + (320 - 3328 * X + 13568 * X ^ 2 - 21504 * X ^ 3) * L1 + (704 - 4480 * X + 6656 * X ^ 2) * L2
  have hne : (128 * X ^ 3 - 1024 * X ^ 4 + 2048 * X ^ 5 : PowerSeries ℚ) ≠ 0 := by
    apply ne_of_coeff _ 3
    simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

end Pa026026

theorem OMA.solution : type_of% @OMA.S_oeis_a026026.main := by
  intro S c G hS hS0 hc hG n hn
  have h7 : X ^ 4 * ((128 * X ^ 3) * G) = X ^ 4 * ((64 - 448 * X + 960 * X ^ 2 - 640 * X ^ 3) + (-64 + 320 * X - 448 * X ^ 2 + 128 * X ^ 3) * S) := by
    rw [hG]
    linear_combination (16 * X ^ 6 * ((2 * X * c) ^ 2 + (2 * X * c) * (1 - S) + (1 - S) ^ 2)
      + X ^ 4 * ((2 * X * c) ^ 6 + (2 * X * c) ^ 5 * (1 - S) + (2 * X * c) ^ 4 * (1 - S) ^ 2
        + (2 * X * c) ^ 3 * (1 - S) ^ 3 + (2 * X * c) ^ 2 * (1 - S) ^ 4 + (2 * X * c) * (1 - S) ^ 5
        + (1 - S) ^ 6)) * hc + X ^ 4 * ((63 - 196 * X + 160 * X ^ 2) * S ^ 0 + (-57 + 92 * X - 32 * X ^ 2) * S ^ 1 + (42 - 28 * X) * S ^ 2 + (-22 + 4 * X) * S ^ 3 + (7) * S ^ 4 + (-1) * S ^ 5) * hS
  have hL := mul_left_cancel₀ (pow_ne_zero 4 PowerSeries.X_ne_zero) h7
  have hL' : (128 * X ^ 3) * G = (64 - 448 * X + 960 * X ^ 2 - 640 * X ^ 3) + (-64 + 320 * X - 448 * X ^ 2 + 128 * X ^ 3) * S := by
    linear_combination hL
  have e := congrArg (coeff n) (Pa026026.ode S G hS hL')
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega]
  norm_num only at e ⊢
  simp only [Pa026026.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa026026.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
