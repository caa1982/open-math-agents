import OMAStatements.S_oeis_a191796
import Mathlib

open OMA.S_oeis_a191796
open PowerSeries

namespace Pa191796

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
theorem ode (S A : PowerSeries ℚ) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hL : (2 - 4 * X - 8 * X ^ 2 + 16 * X ^ 3) * A = (1 - 7 * X ^ 2 - X ^ 3 + 12 * X ^ 4 + 4 * X ^ 5) + (-1 + 5 * X ^ 2 + X ^ 3 - 4 * X ^ 4) * S) :
    (-293120 * X + 661260 * X ^ 2 + 220272 * X ^ 3 - 317616 * X ^ 4) * (A) + (159996 - 231053 * X - 779356 * X ^ 2 + 259832 * X ^ 3 + 875448 * X ^ 4) * (X * d⁄dX ℚ A) + (-10909 + 68000 * X + 77622 * X ^ 2 - 221460 * X ^ 3 - 237024 * X ^ 4) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) + (-2527 - 2527 * X + 25270 * X ^ 2 + 10108 * X ^ 3 - 60648 * X ^ 4) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A))) = 211380 * X ^ 5 := by
  have hdD : d⁄dX ℚ (1 - 4 * X ^ 2 : PowerSeries ℚ) = -8 * X := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have hS1 := sq_step S _ hS
  rw [hdD] at hS1
  have L0 := hL
  have dP1 : d⁄dX ℚ (2 - 4 * X - 8 * X ^ 2 + 16 * X ^ 3 : PowerSeries ℚ) = -4 - 16 * X + 48 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (1 - 7 * X ^ 2 - X ^ 3 + 12 * X ^ 4 + 4 * X ^ 5 : PowerSeries ℚ) = -14 * X - 3 * X ^ 2 + 48 * X ^ 3 + 20 * X ^ 4 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (-1 + 5 * X ^ 2 + X ^ 3 - 4 * X ^ 4 : PowerSeries ℚ) = 10 * X + 3 * X ^ 2 - 16 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (2 - 4 * X - 16 * X ^ 2 + 32 * X ^ 3 + 32 * X ^ 4 - 64 * X ^ 5) * (X * d⁄dX ℚ A) = (2 * X - 2 * X ^ 2 - 17 * X ^ 3 + 18 * X ^ 4 + 44 * X ^ 5 - 40 * X ^ 6 - 32 * X ^ 7) + (-2 * X + 2 * X ^ 2 + 13 * X ^ 3 - 14 * X ^ 4 - 12 * X ^ 5 + 32 * X ^ 6) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (2 * X - 8 * X ^ 3) * E1 + (4 * X + 24 * X ^ 2) * L0 + (-X + 5 * X ^ 3 + X ^ 4 - 4 * X ^ 5) * hS1
  have dP2 : d⁄dX ℚ (2 - 4 * X - 16 * X ^ 2 + 32 * X ^ 3 + 32 * X ^ 4 - 64 * X ^ 5 : PowerSeries ℚ) = -4 - 32 * X + 96 * X ^ 2 + 128 * X ^ 3 - 320 * X ^ 4 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU2 : d⁄dX ℚ (2 * X - 2 * X ^ 2 - 17 * X ^ 3 + 18 * X ^ 4 + 44 * X ^ 5 - 40 * X ^ 6 - 32 * X ^ 7 : PowerSeries ℚ) = 2 - 4 * X - 51 * X ^ 2 + 72 * X ^ 3 + 220 * X ^ 4 - 240 * X ^ 5 - 224 * X ^ 6 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV2 : d⁄dX ℚ (-2 * X + 2 * X ^ 2 + 13 * X ^ 3 - 14 * X ^ 4 - 12 * X ^ 5 + 32 * X ^ 6 : PowerSeries ℚ) = -2 + 4 * X + 39 * X ^ 2 - 56 * X ^ 3 - 60 * X ^ 4 + 192 * X ^ 5 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E2 := th_step _ _ _ _ _ L1
  simp only [dP2, dU2, dV2] at E2
  have L2 : (-2 + 4 * X + 24 * X ^ 2 - 48 * X ^ 3 - 96 * X ^ 4 + 192 * X ^ 5 + 128 * X ^ 6 - 256 * X ^ 7) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = (-2 * X + 23 * X ^ 3 - 14 * X ^ 4 - 120 * X ^ 5 + 80 * X ^ 6 + 304 * X ^ 7 - 96 * X ^ 8 - 256 * X ^ 9) + (2 * X - 19 * X ^ 3 + 14 * X ^ 4 + 36 * X ^ 5 - 168 * X ^ 6 - 112 * X ^ 7 + 256 * X ^ 8) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (-2 * X + 8 * X ^ 3) * E2 + (-4 * X - 40 * X ^ 2) * L1 + (2 * X ^ 2 - 2 * X ^ 3 - 13 * X ^ 4 + 14 * X ^ 5 + 12 * X ^ 6 - 32 * X ^ 7) * hS1
  have dP3 : d⁄dX ℚ (-2 + 4 * X + 24 * X ^ 2 - 48 * X ^ 3 - 96 * X ^ 4 + 192 * X ^ 5 + 128 * X ^ 6 - 256 * X ^ 7 : PowerSeries ℚ) = 4 + 48 * X - 144 * X ^ 2 - 384 * X ^ 3 + 960 * X ^ 4 + 768 * X ^ 5 - 1792 * X ^ 6 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU3 : d⁄dX ℚ (-2 * X + 23 * X ^ 3 - 14 * X ^ 4 - 120 * X ^ 5 + 80 * X ^ 6 + 304 * X ^ 7 - 96 * X ^ 8 - 256 * X ^ 9 : PowerSeries ℚ) = -2 + 69 * X ^ 2 - 56 * X ^ 3 - 600 * X ^ 4 + 480 * X ^ 5 + 2128 * X ^ 6 - 768 * X ^ 7 - 2304 * X ^ 8 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV3 : d⁄dX ℚ (2 * X - 19 * X ^ 3 + 14 * X ^ 4 + 36 * X ^ 5 - 168 * X ^ 6 - 112 * X ^ 7 + 256 * X ^ 8 : PowerSeries ℚ) = 2 - 57 * X ^ 2 + 56 * X ^ 3 + 180 * X ^ 4 - 1008 * X ^ 5 - 784 * X ^ 6 + 2048 * X ^ 7 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E3 := th_step _ _ _ _ _ L2
  simp only [dP3, dU3, dV3] at E3
  have L3 : (2 - 4 * X - 32 * X ^ 2 + 64 * X ^ 3 + 192 * X ^ 4 - 384 * X ^ 5 - 512 * X ^ 6 + 1024 * X ^ 7 + 512 * X ^ 8 - 1024 * X ^ 9) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A))) = (2 * X + 4 * X ^ 2 - 21 * X ^ 3 + 10 * X ^ 4 + 260 * X ^ 5 - 72 * X ^ 6 - 1328 * X ^ 7 - 160 * X ^ 8 + 2496 * X ^ 9 + 128 * X ^ 10 - 2048 * X ^ 11) + (-2 * X - 4 * X ^ 2 + 17 * X ^ 3 - 18 * X ^ 4 + 20 * X ^ 5 + 824 * X ^ 6 + 976 * X ^ 7 - 1824 * X ^ 8 - 960 * X ^ 9 + 2048 * X ^ 10) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (-2 * X + 8 * X ^ 3) * E3 + (-4 * X - 56 * X ^ 2) * L2 + (-2 * X ^ 2 + 19 * X ^ 4 - 14 * X ^ 5 - 36 * X ^ 6 + 168 * X ^ 7 + 112 * X ^ 8 - 256 * X ^ 9) * hS1
  have key : (2 - 4 * X - 32 * X ^ 2 + 64 * X ^ 3 + 192 * X ^ 4 - 384 * X ^ 5 - 512 * X ^ 6 + 1024 * X ^ 7 + 512 * X ^ 8 - 1024 * X ^ 9) * (((-293120 * X + 661260 * X ^ 2 + 220272 * X ^ 3 - 317616 * X ^ 4) * (A) + (159996 - 231053 * X - 779356 * X ^ 2 + 259832 * X ^ 3 + 875448 * X ^ 4) * (X * d⁄dX ℚ A) + (-10909 + 68000 * X + 77622 * X ^ 2 - 221460 * X ^ 3 - 237024 * X ^ 4) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) + (-2527 - 2527 * X + 25270 * X ^ 2 + 10108 * X ^ 3 - 60648 * X ^ 4) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A)))) - (211380 * X ^ 5)) = 0 := by
    linear_combination (-293120 * X + 661260 * X ^ 2 + 3737712 * X ^ 3 - 8252736 * X ^ 4 - 16713024 * X ^ 5 + 35551872 * X ^ 6 + 29332736 * X ^ 7 - 57566208 * X ^ 8 - 14097408 * X ^ 9 + 20327424 * X ^ 10) * L0 + (159996 - 231053 * X - 2059324 * X ^ 2 + 2108256 * X ^ 3 + 9670232 * X ^ 4 - 5775504 * X ^ 5 - 19473280 * X ^ 6 + 4157312 * X ^ 7 + 14007168 * X ^ 8) * L1 + (10909 - 68000 * X - 121258 * X ^ 2 + 493460 * X ^ 3 + 547512 * X ^ 4 - 885840 * X ^ 5 - 948096 * X ^ 6) * L2 + (-2527 - 2527 * X + 25270 * X ^ 2 + 10108 * X ^ 3 - 60648 * X ^ 4) * L3
  have hne : (2 - 4 * X - 32 * X ^ 2 + 64 * X ^ 3 + 192 * X ^ 4 - 384 * X ^ 5 - 512 * X ^ 6 + 1024 * X ^ 7 + 512 * X ^ 8 - 1024 * X ^ 9 : PowerSeries ℚ) ≠ 0 := by
    apply ne_of_coeff _ 0
    simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

theorem S_sq : S ^ 2 = 1 - 4 * X ^ 2 := by
  have hB : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = (1 + X : PowerSeries ℚ) := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    norm_num
    simpa using binomialSeries_nat (A := ℚ) (R := ℚ) 1
  have h0 : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])
  unfold S
  rw [← subst_pow h0, hB, ← coe_substAlgHom h0, map_add, map_one,
    coe_substAlgHom, subst_X h0, R]
  ring

theorem gf_eq : (2 - 4 * X - 8 * X ^ 2 + 16 * X ^ 3) * ((1 - 7 * X ^ 2 - X ^ 3 + 12 * X ^ 4 + 4 * X ^ 5 + (-1 + 5 * X ^ 2 + X ^ 3 - 4 * X ^ 4) * S) * (2 - 4 * X - 8 * X ^ 2 + 16 * X ^ 3 : PowerSeries ℚ)⁻¹) = 1 - 7 * X ^ 2 - X ^ 3 + 12 * X ^ 4 + 4 * X ^ 5 + (-1 + 5 * X ^ 2 + X ^ 3 - 4 * X ^ 4) * S := by
  have hd : constantCoeff (2 - 4 * X - 8 * X ^ 2 + 16 * X ^ 3 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, map_zero, constantCoeff_C]
    norm_num
  have hinv := PowerSeries.mul_inv_cancel (2 - 4 * X - 8 * X ^ 2 + 16 * X ^ 3 : PowerSeries ℚ) hd
  linear_combination (1 - 7 * X ^ 2 - X ^ 3 + 12 * X ^ 4 + 4 * X ^ 5 + (-1 + 5 * X ^ 2 + X ^ 3 - 4 * X ^ 4) * S) * hinv

end Pa191796

theorem OMA.solution : type_of% @OMA.S_oeis_a191796.main := by
  intro n hn
  have hL := Pa191796.gf_eq
  have ha : ∀ m, a m = coeff (m + 1) ((1 - 7 * X ^ 2 - X ^ 3 + 12 * X ^ 4 + 4 * X ^ 5 + (-1 + 5 * X ^ 2 + X ^ 3 - 4 * X ^ 4) * S) * (2 - 4 * X - 8 * X ^ 2 + 16 * X ^ 3 : PowerSeries ℚ)⁻¹) := fun m => rfl
  generalize ((1 - 7 * X ^ 2 - X ^ 3 + 12 * X ^ 4 + 4 * X ^ 5 + (-1 + 5 * X ^ 2 + X ^ 3 - 4 * X ^ 4) * S) * (2 - 4 * X - 8 * X ^ 2 + 16 * X ^ 3 : PowerSeries ℚ)⁻¹) = A at hL ha
  have hL' : (2 - 4 * X - 8 * X ^ 2 + 16 * X ^ 3) * A = (1 - 7 * X ^ 2 - X ^ 3 + 12 * X ^ 4 + 4 * X ^ 5) + (-1 + 5 * X ^ 2 + X ^ 3 - 4 * X ^ 4) * S := by
    linear_combination hL
  have e := congrArg (coeff (n + 1)) (Pa191796.ode S A Pa191796.S_sq hL')
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega, show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega]
  simp only [ha, add_assoc]
  norm_num only at e ⊢
  simp only [Pa191796.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa191796.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
