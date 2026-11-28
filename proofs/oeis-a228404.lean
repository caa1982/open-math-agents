import OMAStatements.S_oeis_a228404
import Mathlib

open OMA.S_oeis_a228404
open PowerSeries

namespace Pa228404

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
    (hL : (2) * A = (1 - 4 * X + 4 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4) + (-1 + 2 * X - 2 * X ^ 2) * S) :
    (80 * X + 240 * X ^ 2 + 720 * X ^ 3 + 82496 * X ^ 4 - 248520 * X ^ 5 + 273000 * X ^ 6) * (A) + (25 + 15 * X + 5 * X ^ 2 + 20029 * X ^ 3 - 104163 * X ^ 4 + 130133 * X ^ 5 - 177450 * X ^ 6) * (X * d⁄dX ℚ A) + (-5 - 5 * X - 5 * X ^ 2 - 5 * X ^ 3 - 5 * X ^ 4 - 5 * X ^ 5 + 27300 * X ^ 6) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = 30 * X ^ 3 + 120 * X ^ 4 + 330 * X ^ 5 + 60642 * X ^ 6 - 72966 * X ^ 7 + 247002 * X ^ 8 - 258282 * X ^ 9 := by
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
  have dP1 : d⁄dX ℚ (2 : PowerSeries ℚ) = 0 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (1 - 4 * X + 4 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4 : PowerSeries ℚ) = -4 + 8 * X - 6 * X ^ 2 - 8 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (-1 + 2 * X - 2 * X ^ 2 : PowerSeries ℚ) = 2 - 4 * X := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (1 - 4 * X) * (X * d⁄dX ℚ A) = (-2 * X + 12 * X ^ 2 - 19 * X ^ 3 + 8 * X ^ 4 + 16 * X ^ 5) + (2 * X - 8 * X ^ 2 + 10 * X ^ 3) * S := by
    have hg : (4 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (2 * X - 8 * X ^ 2) * E1 + (0) * L0 + (-X + 2 * X ^ 2 - 2 * X ^ 3) * hS1
  have dP2 : d⁄dX ℚ (1 - 4 * X : PowerSeries ℚ) = -4 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU2 : d⁄dX ℚ (-2 * X + 12 * X ^ 2 - 19 * X ^ 3 + 8 * X ^ 4 + 16 * X ^ 5 : PowerSeries ℚ) = -2 + 24 * X - 57 * X ^ 2 + 32 * X ^ 3 + 80 * X ^ 4 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV2 : d⁄dX ℚ (2 * X - 8 * X ^ 2 + 10 * X ^ 3 : PowerSeries ℚ) = 2 - 16 * X + 30 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E2 := th_step _ _ _ _ _ L1
  simp only [dP2, dU2, dV2] at E2
  have L2 : (-1 + 8 * X - 16 * X ^ 2) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = (2 * X - 24 * X ^ 2 + 105 * X ^ 3 - 184 * X ^ 4 + 16 * X ^ 5 + 256 * X ^ 6) + (-2 * X + 20 * X ^ 2 - 78 * X ^ 3 + 100 * X ^ 4) * S := by
    linear_combination (-X + 4 * X ^ 2) * E2 + (-4 * X) * L1 + (-X ^ 2 + 4 * X ^ 3 - 5 * X ^ 4) * hS1
  have key : (2 - 16 * X + 32 * X ^ 2) * (((80 * X + 240 * X ^ 2 + 720 * X ^ 3 + 82496 * X ^ 4 - 248520 * X ^ 5 + 273000 * X ^ 6) * (A) + (25 + 15 * X + 5 * X ^ 2 + 20029 * X ^ 3 - 104163 * X ^ 4 + 130133 * X ^ 5 - 177450 * X ^ 6) * (X * d⁄dX ℚ A) + (-5 - 5 * X - 5 * X ^ 2 - 5 * X ^ 3 - 5 * X ^ 4 - 5 * X ^ 5 + 27300 * X ^ 6) * (X * d⁄dX ℚ (X * d⁄dX ℚ A))) - (30 * X ^ 3 + 120 * X ^ 4 + 330 * X ^ 5 + 60642 * X ^ 6 - 72966 * X ^ 7 + 247002 * X ^ 8 - 258282 * X ^ 9)) = 0 := by
    linear_combination (80 * X - 400 * X ^ 2 + 80 * X ^ 3 + 80576 * X ^ 4 - 896968 * X ^ 5 + 3581096 * X ^ 6 - 6160320 * X ^ 7 + 4368000 * X ^ 8) * L0 + (50 - 170 * X - 110 * X ^ 2 + 40018 * X ^ 3 - 368558 * X ^ 4 + 1093570 * X ^ 5 - 1395964 * X ^ 6 + 1419600 * X ^ 7) * L1 + (10 + 10 * X + 10 * X ^ 2 + 10 * X ^ 3 + 10 * X ^ 4 + 10 * X ^ 5 - 54600 * X ^ 6) * L2
  have hne : (2 - 16 * X + 32 * X ^ 2 : PowerSeries ℚ) ≠ 0 := by
    apply ne_of_coeff _ 0
    simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

theorem S_sq : S ^ 2 = 1 - 4 * X := by
  have hB : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = (1 + X : PowerSeries ℚ) := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    norm_num
    simpa using binomialSeries_nat (A := ℚ) (R := ℚ) 1
  have h0 : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])
  unfold S
  rw [← subst_pow h0, hB, ← coe_substAlgHom h0, map_add, map_one,
    coe_substAlgHom, subst_X h0, R]
  ring

theorem gf_eq : (2) * ((1 - 4 * X + 4 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4 + (-1 + 2 * X - 2 * X ^ 2) * S) * (2 : PowerSeries ℚ)⁻¹) = 1 - 4 * X + 4 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4 + (-1 + 2 * X - 2 * X ^ 2) * S := by
  have hd : constantCoeff (2 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, map_zero, constantCoeff_C]
    norm_num
  have hinv := PowerSeries.mul_inv_cancel (2 : PowerSeries ℚ) hd
  linear_combination (1 - 4 * X + 4 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4 + (-1 + 2 * X - 2 * X ^ 2) * S) * hinv

end Pa228404

theorem OMA.solution : type_of% @OMA.S_oeis_a228404.main := by
  intro n hn
  have hL := Pa228404.gf_eq
  have ha : ∀ m, a m = coeff ((m + 3)) ((1 - 4 * X + 4 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4 + (-1 + 2 * X - 2 * X ^ 2) * S) * (2 : PowerSeries ℚ)⁻¹) := fun m => rfl
  generalize ((1 - 4 * X + 4 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4 + (-1 + 2 * X - 2 * X ^ 2) * S) * (2 : PowerSeries ℚ)⁻¹) = A at hL ha
  have hL' : (2) * A = (1 - 4 * X + 4 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4) + (-1 + 2 * X - 2 * X ^ 2) * S := by
    linear_combination hL
  have e := congrArg (coeff ((n + 3))) (Pa228404.ode S A Pa228404.S_sq hL')
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  simp only [show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega, show k + 7 - 3 = k + 4 by omega, show k + 7 - 4 = k + 3 by omega, show k + 7 - 5 = k + 2 by omega, show k + 7 - 6 = k + 1 by omega]
  simp only [ha, add_assoc]
  norm_num only at e ⊢
  simp only [Pa228404.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa228404.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
