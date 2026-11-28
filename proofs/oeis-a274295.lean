import OMAStatements.S_oeis_a274295
import Mathlib

open OMA.S_oeis_a274295
open PowerSeries

namespace Pa274295

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
    (hL : (1 - 7 * X + 15 * X ^ 2 - 13 * X ^ 3 + 4 * X ^ 4) * A = (1 - 6 * X + 10 * X ^ 2 - 9 * X ^ 3 + 8 * X ^ 4 - 16 * X ^ 5) + (X ^ 2 - 2 * X ^ 3 + 2 * X ^ 5 - X ^ 6) * S) :
    (2 - 11 * X + 14 * X ^ 2 + 14 * X ^ 3 - 46 * X ^ 4 + 37 * X ^ 5 - 10 * X ^ 6) * (A) + (-1 + 7 * X - 14 * X ^ 2 + 6 * X ^ 3 + 11 * X ^ 4 - 13 * X ^ 5 + 4 * X ^ 6) * (X * d⁄dX ℚ A) = 2 - 10 * X + 10 * X ^ 2 + 17 * X ^ 3 - 40 * X ^ 4 + 55 * X ^ 5 + 14 * X ^ 6 + 24 * X ^ 7 := by
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
  have dP1 : d⁄dX ℚ (1 - 7 * X + 15 * X ^ 2 - 13 * X ^ 3 + 4 * X ^ 4 : PowerSeries ℚ) = -7 + 30 * X - 39 * X ^ 2 + 16 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (1 - 6 * X + 10 * X ^ 2 - 9 * X ^ 3 + 8 * X ^ 4 - 16 * X ^ 5 : PowerSeries ℚ) = -6 + 20 * X - 27 * X ^ 2 + 32 * X ^ 3 - 80 * X ^ 4 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (X ^ 2 - 2 * X ^ 3 + 2 * X ^ 5 - X ^ 6 : PowerSeries ℚ) = 2 * X - 6 * X ^ 2 + 10 * X ^ 4 - 6 * X ^ 5 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (-1 + 12 * X - 54 * X ^ 2 + 116 * X ^ 3 - 129 * X ^ 4 + 72 * X ^ 5 - 16 * X ^ 6) * (X * d⁄dX ℚ A) = (-X + 8 * X ^ 2 - 15 * X ^ 3 - 24 * X ^ 4 + 148 * X ^ 5 - 288 * X ^ 6 + 64 * X ^ 7) + (-2 * X ^ 2 + 11 * X ^ 3 - 14 * X ^ 4 - 14 * X ^ 5 + 46 * X ^ 6 - 37 * X ^ 7 + 10 * X ^ 8) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (-2 * X + 10 * X ^ 2 - 8 * X ^ 3) * E1 + (-14 * X + 32 * X ^ 2) * L0 + (-X ^ 3 + 3 * X ^ 4 - 2 * X ^ 5 - 2 * X ^ 6 + 3 * X ^ 7 - X ^ 8) * hS1
  have key : (-1 + 12 * X - 54 * X ^ 2 + 116 * X ^ 3 - 129 * X ^ 4 + 72 * X ^ 5 - 16 * X ^ 6) * (((2 - 11 * X + 14 * X ^ 2 + 14 * X ^ 3 - 46 * X ^ 4 + 37 * X ^ 5 - 10 * X ^ 6) * (A) + (-1 + 7 * X - 14 * X ^ 2 + 6 * X ^ 3 + 11 * X ^ 4 - 13 * X ^ 5 + 4 * X ^ 6) * (X * d⁄dX ℚ A)) - (2 - 10 * X + 10 * X ^ 2 + 17 * X ^ 3 - 40 * X ^ 4 + 55 * X ^ 5 + 14 * X ^ 6 + 24 * X ^ 7)) = 0 := by
    linear_combination (-2 + 21 * X - 77 * X ^ 2 + 100 * X ^ 3 + 60 * X ^ 4 - 323 * X ^ 5 + 379 * X ^ 6 - 198 * X ^ 7 + 40 * X ^ 8) * L0 + (-1 + 7 * X - 14 * X ^ 2 + 6 * X ^ 3 + 11 * X ^ 4 - 13 * X ^ 5 + 4 * X ^ 6) * L1
  have hne : (-1 + 12 * X - 54 * X ^ 2 + 116 * X ^ 3 - 129 * X ^ 4 + 72 * X ^ 5 - 16 * X ^ 6 : PowerSeries ℚ) ≠ 0 := by
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

theorem gf_eq : (1 - 7 * X + 15 * X ^ 2 - 13 * X ^ 3 + 4 * X ^ 4) * ((1 - 6 * X + 10 * X ^ 2 - 9 * X ^ 3 + 8 * X ^ 4 - 16 * X ^ 5 + (X ^ 2 - 2 * X ^ 3 + 2 * X ^ 5 - X ^ 6) * S) * (1 - 7 * X + 15 * X ^ 2 - 13 * X ^ 3 + 4 * X ^ 4 : PowerSeries ℚ)⁻¹) = 1 - 6 * X + 10 * X ^ 2 - 9 * X ^ 3 + 8 * X ^ 4 - 16 * X ^ 5 + (X ^ 2 - 2 * X ^ 3 + 2 * X ^ 5 - X ^ 6) * S := by
  have hd : constantCoeff (1 - 7 * X + 15 * X ^ 2 - 13 * X ^ 3 + 4 * X ^ 4 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, map_zero, constantCoeff_C]
    norm_num
  have hinv := PowerSeries.mul_inv_cancel (1 - 7 * X + 15 * X ^ 2 - 13 * X ^ 3 + 4 * X ^ 4 : PowerSeries ℚ) hd
  linear_combination (1 - 6 * X + 10 * X ^ 2 - 9 * X ^ 3 + 8 * X ^ 4 - 16 * X ^ 5 + (X ^ 2 - 2 * X ^ 3 + 2 * X ^ 5 - X ^ 6) * S) * hinv

end Pa274295

theorem OMA.solution : type_of% @OMA.S_oeis_a274295.main := by
  intro n hn
  have hL := Pa274295.gf_eq
  have ha : ∀ m, a m = coeff m ((1 - 6 * X + 10 * X ^ 2 - 9 * X ^ 3 + 8 * X ^ 4 - 16 * X ^ 5 + (X ^ 2 - 2 * X ^ 3 + 2 * X ^ 5 - X ^ 6) * S) * (1 - 7 * X + 15 * X ^ 2 - 13 * X ^ 3 + 4 * X ^ 4 : PowerSeries ℚ)⁻¹) := fun m => rfl
  generalize ((1 - 6 * X + 10 * X ^ 2 - 9 * X ^ 3 + 8 * X ^ 4 - 16 * X ^ 5 + (X ^ 2 - 2 * X ^ 3 + 2 * X ^ 5 - X ^ 6) * S) * (1 - 7 * X + 15 * X ^ 2 - 13 * X ^ 3 + 4 * X ^ 4 : PowerSeries ℚ)⁻¹) = A at hL ha
  have hL' : (1 - 7 * X + 15 * X ^ 2 - 13 * X ^ 3 + 4 * X ^ 4) * A = (1 - 6 * X + 10 * X ^ 2 - 9 * X ^ 3 + 8 * X ^ 4 - 16 * X ^ 5) + (X ^ 2 - 2 * X ^ 3 + 2 * X ^ 5 - X ^ 6) * S := by
    linear_combination hL
  have e := congrArg (coeff n) (Pa274295.ode S A Pa274295.S_sq hL')
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
  simp only [show k + 8 - 1 = k + 7 by omega, show k + 8 - 2 = k + 6 by omega, show k + 8 - 3 = k + 5 by omega, show k + 8 - 4 = k + 4 by omega, show k + 8 - 5 = k + 3 by omega, show k + 8 - 6 = k + 2 by omega]
  simp only [ha, add_assoc]
  norm_num only at e ⊢
  simp only [Pa274295.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa274295.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
