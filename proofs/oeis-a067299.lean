import OMAStatements.S_oeis_a067299
import Mathlib

open OMA.S_oeis_a067299
open PowerSeries

namespace Pa067299

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
theorem ode (S A : PowerSeries ℚ) (hS : S ^ 2 = 1 - 16 * X)
    (hL : (2 + 16 * X + 48 * X ^ 2 + 64 * X ^ 3 + 32 * X ^ 4) * A = (7 + 33 * X + 48 * X ^ 2 + 20 * X ^ 3) + (-3 - 15 * X - 24 * X ^ 2 - 12 * X ^ 3) * S) :
    (110 * X - 704 * X ^ 2) * (A) + (-7 + 64 * X - 1680 * X ^ 2) * (X * d⁄dX ℚ A) + (17 - 238 * X - 544 * X ^ 2) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = 270 * X := by
  have hdD : d⁄dX ℚ (1 - 16 * X : PowerSeries ℚ) = -16 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have hS1 := sq_step S _ hS
  rw [hdD] at hS1
  have L0 := hL
  have dP1 : d⁄dX ℚ (2 + 16 * X + 48 * X ^ 2 + 64 * X ^ 3 + 32 * X ^ 4 : PowerSeries ℚ) = 16 + 96 * X + 192 * X ^ 2 + 128 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (7 + 33 * X + 48 * X ^ 2 + 20 * X ^ 3 : PowerSeries ℚ) = 33 + 96 * X + 60 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (-3 - 15 * X - 24 * X ^ 2 - 12 * X ^ 3 : PowerSeries ℚ) = -15 - 48 * X - 36 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (2 - 20 * X - 168 * X ^ 2 - 368 * X ^ 3 - 256 * X ^ 4) * (X * d⁄dX ℚ A) = (-23 * X + 358 * X ^ 2 + 160 * X ^ 3) + (33 * X - 66 * X ^ 2 - 48 * X ^ 3) * S := by
    have hg : (2 + 8 * X + 8 * X ^ 2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (2 * X - 28 * X ^ 2 - 64 * X ^ 3) * E1 + (-16 * X + 256 * X ^ 2) * L0 + (-3 * X - 21 * X ^ 2 - 54 * X ^ 3 - 60 * X ^ 4 - 24 * X ^ 5) * hS1
  have dP2 : d⁄dX ℚ (2 - 20 * X - 168 * X ^ 2 - 368 * X ^ 3 - 256 * X ^ 4 : PowerSeries ℚ) = -20 - 336 * X - 1104 * X ^ 2 - 1024 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU2 : d⁄dX ℚ (-23 * X + 358 * X ^ 2 + 160 * X ^ 3 : PowerSeries ℚ) = -23 + 716 * X + 480 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV2 : d⁄dX ℚ (33 * X - 66 * X ^ 2 - 48 * X ^ 3 : PowerSeries ℚ) = 33 - 132 * X - 144 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E2 := th_step _ _ _ _ _ L1
  simp only [dP2, dU2, dV2] at E2
  have L2 : (-2 + 48 * X - 48 * X ^ 2 - 2624 * X ^ 3 - 10272 * X ^ 4 - 15360 * X ^ 5 - 8192 * X ^ 6) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = (23 * X - 808 * X ^ 2 + 8172 * X ^ 3 - 17792 * X ^ 4 - 5120 * X ^ 5) + (-33 * X + 528 * X ^ 2 - 4212 * X ^ 3 + 1248 * X ^ 4 + 768 * X ^ 5) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (-2 * X + 28 * X ^ 2 + 64 * X ^ 3) * E2 + (-20 * X - 256 * X ^ 2) * L1 + (-33 * X ^ 2 + 180 * X ^ 4 + 96 * X ^ 5) * hS1
  have key : (2 - 48 * X + 48 * X ^ 2 + 2624 * X ^ 3 + 10272 * X ^ 4 + 15360 * X ^ 5 + 8192 * X ^ 6) * (((110 * X - 704 * X ^ 2) * (A) + (-7 + 64 * X - 1680 * X ^ 2) * (X * d⁄dX ℚ A) + (17 - 238 * X - 544 * X ^ 2) * (X * d⁄dX ℚ (X * d⁄dX ℚ A))) - (270 * X)) = 0 := by
    linear_combination (110 * X - 4224 * X ^ 2 + 50688 * X ^ 3 - 180224 * X ^ 4) * L0 + (-7 + 162 * X - 2352 * X ^ 2 + 21472 * X ^ 3 + 53760 * X ^ 4) * L1 + (-17 + 238 * X + 544 * X ^ 2) * L2
  have hne : (2 - 48 * X + 48 * X ^ 2 + 2624 * X ^ 3 + 10272 * X ^ 4 + 15360 * X ^ 5 + 8192 * X ^ 6 : PowerSeries ℚ) ≠ 0 := by
    apply ne_of_coeff _ 0
    simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

theorem S_sq : S ^ 2 = 1 - 16 * X := by
  have hB : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = (1 + X : PowerSeries ℚ) := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    norm_num
    simpa using binomialSeries_nat (A := ℚ) (R := ℚ) 1
  have h0 : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])
  unfold S
  rw [← subst_pow h0, hB, ← coe_substAlgHom h0, map_add, map_one,
    coe_substAlgHom, subst_X h0, R]
  ring

theorem gf_eq : (2 + 16 * X + 48 * X ^ 2 + 64 * X ^ 3 + 32 * X ^ 4) * ((7 + 33 * X + 48 * X ^ 2 + 20 * X ^ 3 + (-3 - 15 * X - 24 * X ^ 2 - 12 * X ^ 3) * S) * (2 + 16 * X + 48 * X ^ 2 + 64 * X ^ 3 + 32 * X ^ 4 : PowerSeries ℚ)⁻¹) = 7 + 33 * X + 48 * X ^ 2 + 20 * X ^ 3 + (-3 - 15 * X - 24 * X ^ 2 - 12 * X ^ 3) * S := by
  have hd : constantCoeff (2 + 16 * X + 48 * X ^ 2 + 64 * X ^ 3 + 32 * X ^ 4 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, map_zero, constantCoeff_C]
    norm_num
  have hinv := PowerSeries.mul_inv_cancel (2 + 16 * X + 48 * X ^ 2 + 64 * X ^ 3 + 32 * X ^ 4 : PowerSeries ℚ) hd
  linear_combination (7 + 33 * X + 48 * X ^ 2 + 20 * X ^ 3 + (-3 - 15 * X - 24 * X ^ 2 - 12 * X ^ 3) * S) * hinv

end Pa067299

theorem OMA.solution : type_of% @OMA.S_oeis_a067299.main := by
  intro n hn
  have hL := Pa067299.gf_eq
  have ha : ∀ m, a m = coeff m ((7 + 33 * X + 48 * X ^ 2 + 20 * X ^ 3 + (-3 - 15 * X - 24 * X ^ 2 - 12 * X ^ 3) * S) * (2 + 16 * X + 48 * X ^ 2 + 64 * X ^ 3 + 32 * X ^ 4 : PowerSeries ℚ)⁻¹) := fun m => rfl
  generalize ((7 + 33 * X + 48 * X ^ 2 + 20 * X ^ 3 + (-3 - 15 * X - 24 * X ^ 2 - 12 * X ^ 3) * S) * (2 + 16 * X + 48 * X ^ 2 + 64 * X ^ 3 + 32 * X ^ 4 : PowerSeries ℚ)⁻¹) = A at hL ha
  have hL' : (2 + 16 * X + 48 * X ^ 2 + 64 * X ^ 3 + 32 * X ^ 4) * A = (7 + 33 * X + 48 * X ^ 2 + 20 * X ^ 3) + (-3 - 15 * X - 24 * X ^ 2 - 12 * X ^ 3) * S := by
    linear_combination hL
  have e := congrArg (coeff n) (Pa067299.ode S A Pa067299.S_sq hL')
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simp only [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
  simp only [ha, add_assoc]
  norm_num only at e ⊢
  simp only [Pa067299.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa067299.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
