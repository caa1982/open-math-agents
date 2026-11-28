import OMAStatements.S_oeis_a257300
import Mathlib

open OMA.S_oeis_a257300
open PowerSeries

namespace Pa257300

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
theorem ode (S A : PowerSeries ℚ) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hL : (2 - 6 * X + 6 * X ^ 2 - 2 * X ^ 3 + 2 * X ^ 4) * A = (3 - 5 * X + 2 * X ^ 2 - 2 * X ^ 3) + (-1) * S) :
    (-2 * X + 12 * X ^ 2 - 12 * X ^ 3 - X ^ 5 - 9 * X ^ 6) * (A) + (1 - 5 * X + 6 * X ^ 2 + 2 * X ^ 3 - 6 * X ^ 4 + X ^ 5 - 3 * X ^ 6) * (X * d⁄dX ℚ A) = -X + 9 * X ^ 2 - 6 * X ^ 3 + 2 * X ^ 4 + 6 * X ^ 5 := by
  have hdD : d⁄dX ℚ (1 - 2 * X - 3 * X ^ 2 : PowerSeries ℚ) = -2 - 6 * X := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have hS1 := sq_step S _ hS
  rw [hdD] at hS1
  have L0 := hL
  have dP1 : d⁄dX ℚ (2 - 6 * X + 6 * X ^ 2 - 2 * X ^ 3 + 2 * X ^ 4 : PowerSeries ℚ) = -6 + 12 * X - 6 * X ^ 2 + 8 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (3 - 5 * X + 2 * X ^ 2 - 2 * X ^ 3 : PowerSeries ℚ) = -5 + 4 * X - 6 * X ^ 2 := by
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
  have L1 : (2 - 16 * X + 48 * X ^ 2 - 64 * X ^ 3 + 24 * X ^ 4 + 28 * X ^ 5 - 40 * X ^ 6 + 40 * X ^ 7 - 32 * X ^ 8 + 8 * X ^ 9 - 6 * X ^ 10) * (X * d⁄dX ℚ A) = (4 * X - 22 * X ^ 2 + 28 * X ^ 3 + 8 * X ^ 4 - 5 * X ^ 5 + 4 * X ^ 6 - 23 * X ^ 7 + 8 * X ^ 8 - 6 * X ^ 9) + (-2 * X + 12 * X ^ 2 - 12 * X ^ 3 - X ^ 5 - 9 * X ^ 6) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (2 * X - 10 * X ^ 2 + 12 * X ^ 3 + 4 * X ^ 4 - 12 * X ^ 5 + 2 * X ^ 6 - 6 * X ^ 7) * E1 + (6 * X - 24 * X ^ 2 + 12 * X ^ 3 + 16 * X ^ 4 - 2 * X ^ 5 + 24 * X ^ 6) * L0 + (-X + 3 * X ^ 2 - 3 * X ^ 3 + X ^ 4 - X ^ 5) * hS1
  have key : (2 - 16 * X + 48 * X ^ 2 - 64 * X ^ 3 + 24 * X ^ 4 + 28 * X ^ 5 - 40 * X ^ 6 + 40 * X ^ 7 - 32 * X ^ 8 + 8 * X ^ 9 - 6 * X ^ 10) * (((-2 * X + 12 * X ^ 2 - 12 * X ^ 3 - X ^ 5 - 9 * X ^ 6) * (A) + (1 - 5 * X + 6 * X ^ 2 + 2 * X ^ 3 - 6 * X ^ 4 + X ^ 5 - 3 * X ^ 6) * (X * d⁄dX ℚ A)) - (-X + 9 * X ^ 2 - 6 * X ^ 3 + 2 * X ^ 4 + 6 * X ^ 5)) = 0 := by
    linear_combination (-2 * X + 22 * X ^ 2 - 84 * X ^ 3 + 128 * X ^ 4 - 37 * X ^ 5 - 102 * X ^ 6 + 129 * X ^ 7 - 104 * X ^ 8 + 24 * X ^ 9 + 53 * X ^ 10 - 6 * X ^ 11 + 27 * X ^ 12) * L0 + (1 - 5 * X + 6 * X ^ 2 + 2 * X ^ 3 - 6 * X ^ 4 + X ^ 5 - 3 * X ^ 6) * L1
  have hne : (2 - 16 * X + 48 * X ^ 2 - 64 * X ^ 3 + 24 * X ^ 4 + 28 * X ^ 5 - 40 * X ^ 6 + 40 * X ^ 7 - 32 * X ^ 8 + 8 * X ^ 9 - 6 * X ^ 10 : PowerSeries ℚ) ≠ 0 := by
    apply ne_of_coeff _ 0
    simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

theorem S_sq : S ^ 2 = 1 - 2 * X - 3 * X ^ 2 := by
  have hB : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = (1 + X : PowerSeries ℚ) := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    norm_num
    simpa using binomialSeries_nat (A := ℚ) (R := ℚ) 1
  have h0 : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])
  unfold S
  rw [← subst_pow h0, hB, ← coe_substAlgHom h0, map_add, map_one,
    coe_substAlgHom, subst_X h0, R]
  ring

theorem gf_eq : (2 - 6 * X + 6 * X ^ 2 - 2 * X ^ 3 + 2 * X ^ 4) * ((3 - 5 * X + 2 * X ^ 2 - 2 * X ^ 3 - S) * (2 - 6 * X + 6 * X ^ 2 - 2 * X ^ 3 + 2 * X ^ 4 : PowerSeries ℚ)⁻¹) = 3 - 5 * X + 2 * X ^ 2 - 2 * X ^ 3 - S := by
  have hd : constantCoeff (2 - 6 * X + 6 * X ^ 2 - 2 * X ^ 3 + 2 * X ^ 4 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, map_zero, constantCoeff_C]
    norm_num
  have hinv := PowerSeries.mul_inv_cancel (2 - 6 * X + 6 * X ^ 2 - 2 * X ^ 3 + 2 * X ^ 4 : PowerSeries ℚ) hd
  linear_combination (3 - 5 * X + 2 * X ^ 2 - 2 * X ^ 3 - S) * hinv

end Pa257300

theorem OMA.solution : type_of% @OMA.S_oeis_a257300.main := by
  intro n hn
  have hL := Pa257300.gf_eq
  have ha : ∀ m, a m = coeff (m) ((3 - 5 * X + 2 * X ^ 2 - 2 * X ^ 3 - S) * (2 - 6 * X + 6 * X ^ 2 - 2 * X ^ 3 + 2 * X ^ 4 : PowerSeries ℚ)⁻¹) := fun m => rfl
  generalize ((3 - 5 * X + 2 * X ^ 2 - 2 * X ^ 3 - S) * (2 - 6 * X + 6 * X ^ 2 - 2 * X ^ 3 + 2 * X ^ 4 : PowerSeries ℚ)⁻¹) = A at hL ha
  have hL' : (2 - 6 * X + 6 * X ^ 2 - 2 * X ^ 3 + 2 * X ^ 4) * A = (3 - 5 * X + 2 * X ^ 2 - 2 * X ^ 3) + (-1) * S := by
    linear_combination hL
  have e := congrArg (coeff (n)) (Pa257300.ode S A Pa257300.S_sq hL')
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  simp only [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega, show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega, show k + 6 - 5 = k + 1 by omega, show k + 6 - 6 = k by omega]
  simp only [ha, add_assoc]
  norm_num only at e ⊢
  simp only [Pa257300.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa257300.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
