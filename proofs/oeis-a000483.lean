import OMAStatements.S_oeis_a000483
import Mathlib

open OMA.S_oeis_a000483
open PowerSeries

namespace P000483

theorem nC (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : PowerSeries ℚ) = C (OfNat.ofNat n : ℚ) :=
  (map_ofNat C n).symm

theorem cXd (F : PowerSeries ℚ) (k : ℕ) : coeff k (X * d⁄dX ℚ F) = coeff k F * k := by
  rcases k with _ | k
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

theorem ne_of_cc (p : PowerSeries ℚ) (h : constantCoeff p ≠ 0) : p ≠ 0 := by
  intro h0; rw [h0, map_zero] at h; exact h rfl

namespace Fq

set_option maxHeartbeats 4000000 in
theorem ode (F L : PowerSeries ℚ) (hF : 6 * F = -(X + L) ^ 3) (hL : (1 - X) * d⁄dX ℚ L = -1)  :
    (-2 * X ^ 3 + 11 * X ^ 2 - 17 * X + 8) * (X * d⁄dX ℚ F) + (3 * X ^ 3 - 12 * X ^ 2 + 15 * X - 6) * (X * d⁄dX ℚ (X * d⁄dX ℚ F)) + (-X ^ 3 + 3 * X ^ 2 - 3 * X + 1) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ F))) = X ^ 6 := by
  have hF1 := congrArg (d⁄dX ℚ) hF
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hF1
  try simp only [map_ofNat] at hF1
  try push_cast at hF1
  have hF2 := congrArg (d⁄dX ℚ) hF1
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hF2
  try simp only [map_ofNat] at hF2
  try push_cast at hF2
  have hF3 := congrArg (d⁄dX ℚ) hF2
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hF3
  try simp only [map_ofNat] at hF3
  try push_cast at hF3
  have hL1 := congrArg (d⁄dX ℚ) hL
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hL1
  try simp only [map_ofNat] at hL1
  try push_cast at hL1
  have hL2 := congrArg (d⁄dX ℚ) hL1
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hL2
  try simp only [map_ofNat] at hL2
  try push_cast at hL2
  have hL3 := congrArg (d⁄dX ℚ) hL2
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hL3
  try simp only [map_ofNat] at hL3
  try push_cast at hL3
  have key : (X ^ 0 * (6)) ^ 3 * (X ^ 0 * (-X + 1)) ^ 5 * (-X ^ 6 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ F))) - X ^ 6 + 3 * X ^ 5 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ F))) - 3 * X ^ 4 * (d⁄dX ℚ (d⁄dX ℚ F)) - 3 * X ^ 4 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ F))) + 2 * X ^ 3 * (d⁄dX ℚ F) + 6 * X ^ 3 * (d⁄dX ℚ (d⁄dX ℚ F)) + X ^ 3 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ F))) - 5 * X ^ 2 * (d⁄dX ℚ F) - 3 * X ^ 2 * (d⁄dX ℚ (d⁄dX ℚ F)) + 3 * X * (d⁄dX ℚ F)) = 0 := by
    linear_combination (216 * X ^ 10 * (d⁄dX ℚ L) ^ 2 + 216 * X ^ 10 - 648 * X ^ 9 * L * (d⁄dX ℚ L) - 216 * X ^ 9 * L - 1512 * X ^ 9 * (d⁄dX ℚ L) ^ 2 + 216 * X ^ 9 * (d⁄dX ℚ L) - 972 * X ^ 9 + 216 * X ^ 8 * L ^ 2 + 4536 * X ^ 8 * L * (d⁄dX ℚ L) + 1296 * X ^ 8 * L + 4536 * X ^ 8 * (d⁄dX ℚ L) ^ 2 - 1296 * X ^ 8 * (d⁄dX ℚ L) + 1512 * X ^ 8 - 1620 * X ^ 7 * L ^ 2 - 13608 * X ^ 7 * L * (d⁄dX ℚ L) - 3240 * X ^ 7 * L - 7560 * X ^ 7 * (d⁄dX ℚ L) ^ 2 + 3240 * X ^ 7 * (d⁄dX ℚ L) - 540 * X ^ 7 + 5184 * X ^ 6 * L ^ 2 + 22680 * X ^ 6 * L * (d⁄dX ℚ L) + 4320 * X ^ 6 * L + 7560 * X ^ 6 * (d⁄dX ℚ L) ^ 2 - 4320 * X ^ 6 * (d⁄dX ℚ L) - 1080 * X ^ 6 - 9180 * X ^ 5 * L ^ 2 - 22680 * X ^ 5 * L * (d⁄dX ℚ L) - 3240 * X ^ 5 * L - 4536 * X ^ 5 * (d⁄dX ℚ L) ^ 2 + 3240 * X ^ 5 * (d⁄dX ℚ L) + 1404 * X ^ 5 + 9720 * X ^ 4 * L ^ 2 + 13608 * X ^ 4 * L * (d⁄dX ℚ L) + 1296 * X ^ 4 * L + 1512 * X ^ 4 * (d⁄dX ℚ L) ^ 2 - 1296 * X ^ 4 * (d⁄dX ℚ L) - 648 * X ^ 4 - 6156 * X ^ 3 * L ^ 2 - 4536 * X ^ 3 * L * (d⁄dX ℚ L) - 216 * X ^ 3 * L - 216 * X ^ 3 * (d⁄dX ℚ L) ^ 2 + 216 * X ^ 3 * (d⁄dX ℚ L) + 108 * X ^ 3 + 2160 * X ^ 2 * L ^ 2 + 648 * X ^ 2 * L * (d⁄dX ℚ L) - 324 * X * L ^ 2) * hL + (648 * X ^ 11 * (d⁄dX ℚ L) + 432 * X ^ 11 + 648 * X ^ 10 * L * (d⁄dX ℚ L) + 216 * X ^ 10 * L - 4536 * X ^ 10 * (d⁄dX ℚ L) - 2916 * X ^ 10 - 216 * X ^ 9 * L ^ 2 - 4536 * X ^ 9 * L * (d⁄dX ℚ L) - 1296 * X ^ 9 * L + 13608 * X ^ 9 * (d⁄dX ℚ L) + 8424 * X ^ 9 + 1620 * X ^ 8 * L ^ 2 + 13608 * X ^ 8 * L * (d⁄dX ℚ L) + 3240 * X ^ 8 * L - 22680 * X ^ 8 * (d⁄dX ℚ L) - 13500 * X ^ 8 - 5184 * X ^ 7 * L ^ 2 - 22680 * X ^ 7 * L * (d⁄dX ℚ L) - 4320 * X ^ 7 * L + 22680 * X ^ 7 * (d⁄dX ℚ L) + 12960 * X ^ 7 + 9180 * X ^ 6 * L ^ 2 + 22680 * X ^ 6 * L * (d⁄dX ℚ L) + 3240 * X ^ 6 * L - 13608 * X ^ 6 * (d⁄dX ℚ L) - 7452 * X ^ 6 - 9720 * X ^ 5 * L ^ 2 - 13608 * X ^ 5 * L * (d⁄dX ℚ L) - 1296 * X ^ 5 * L + 4536 * X ^ 5 * (d⁄dX ℚ L) + 2376 * X ^ 5 + 6156 * X ^ 4 * L ^ 2 + 4536 * X ^ 4 * L * (d⁄dX ℚ L) + 216 * X ^ 4 * L - 648 * X ^ 4 * (d⁄dX ℚ L) - 324 * X ^ 4 - 2160 * X ^ 3 * L ^ 2 - 648 * X ^ 3 * L * (d⁄dX ℚ L) + 324 * X ^ 2 * L ^ 2) * hL1 + (108 * X ^ 12 + 216 * X ^ 11 * L - 756 * X ^ 11 + 108 * X ^ 10 * L ^ 2 - 1512 * X ^ 10 * L + 2268 * X ^ 10 - 756 * X ^ 9 * L ^ 2 + 4536 * X ^ 9 * L - 3780 * X ^ 9 + 2268 * X ^ 8 * L ^ 2 - 7560 * X ^ 8 * L + 3780 * X ^ 8 - 3780 * X ^ 7 * L ^ 2 + 7560 * X ^ 7 * L - 2268 * X ^ 7 + 3780 * X ^ 6 * L ^ 2 - 4536 * X ^ 6 * L + 756 * X ^ 6 - 2268 * X ^ 5 * L ^ 2 + 1512 * X ^ 5 * L - 108 * X ^ 5 + 756 * X ^ 4 * L ^ 2 - 216 * X ^ 4 * L - 108 * X ^ 3 * L ^ 2) * hL2 + (-72 * X ^ 8 + 540 * X ^ 7 - 1728 * X ^ 6 + 3060 * X ^ 5 - 3240 * X ^ 4 + 2052 * X ^ 3 - 720 * X ^ 2 + 108 * X) * hF1 + (108 * X ^ 9 - 756 * X ^ 8 + 2268 * X ^ 7 - 3780 * X ^ 6 + 3780 * X ^ 5 - 2268 * X ^ 4 + 756 * X ^ 3 - 108 * X ^ 2) * hF2 + (36 * X ^ 11 - 288 * X ^ 10 + 1008 * X ^ 9 - 2016 * X ^ 8 + 2520 * X ^ 7 - 2016 * X ^ 6 + 1008 * X ^ 5 - 288 * X ^ 4 + 36 * X ^ 3) * hF3
  have hf0 : (X ^ 0 * (6) : PowerSeries ℚ) ≠ 0 := ne_of_cc _ (by simp [nC, constantCoeff_C] <;> norm_num)
  have hf1 : (X ^ 0 * (-X + 1) : PowerSeries ℚ) ≠ 0 := ne_of_cc _ (by simp [nC, constantCoeff_C] <;> norm_num)
  have hE := (mul_eq_zero.mp key).resolve_left (mul_ne_zero (pow_ne_zero _ hf0) (pow_ne_zero _ hf1))
  have th2 : X * d⁄dX ℚ (X * d⁄dX ℚ F) = 1 * X ^ 1 * (d⁄dX ℚ F) + 1 * X ^ 2 * (d⁄dX ℚ (d⁄dX ℚ F)) := by
    simp only [Derivation.leibniz, derivative_X, smul_eq_mul, map_add, map_mul, nC, derivative_C]
    try simp only [map_ofNat]
    ring
  have th3 : X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ F)) = 1 * X ^ 1 * (d⁄dX ℚ F) + 3 * X ^ 2 * (d⁄dX ℚ (d⁄dX ℚ F)) + 1 * X ^ 3 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ F))) := by
    simp only [Derivation.leibniz, derivative_X, smul_eq_mul, th2, Derivation.map_one_eq_zero, map_add, map_mul, nC, derivative_C]
    try simp only [map_ofNat]
    ring
  rw [th3, th2]
  linear_combination hE

end Fq

theorem recF (L F : PowerSeries ℚ) (hF : 6 * F = -(X + L) ^ 3) (hL : (1 - X) * d⁄dX ℚ L = -1) :
    ∀ n : ℕ, 7 ≤ n → (8 * (n : ℚ) - 6 * (n : ℚ) ^ 2 + (n : ℚ) ^ 3) * coeff n F + (35 - 56 * (n : ℚ) + 24 * (n : ℚ) ^ 2 - 3 * (n : ℚ) ^ 3) * coeff (n - 1) F + (-94 + 95 * (n : ℚ) - 30 * (n : ℚ) ^ 2 + 3 * (n : ℚ) ^ 3) * coeff (n - 2) F + (60 - 47 * (n : ℚ) + 12 * (n : ℚ) ^ 2 - (n : ℚ) ^ 3) * coeff (n - 3) F = 0 := by
  intro n hn
  have e := congrArg (coeff n) (Fq.ode F L hF hL)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  simp only [show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega, show k + 7 - 3 = k + 4 by omega]
  norm_num only at e ⊢
  simp only [nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e

theorem fsucc (x : ℕ) : ((x + 1).factorial : ℚ) = ((x : ℚ) + 1) * (x.factorial : ℚ) := by
  rw [Nat.factorial_succ]; push_cast; ring

end P000483

theorem OMA.solution : type_of% @OMA.S_oeis_a000483.main := by
  intro L F hL0 hL hF n hn
  have e := P000483.recF L F hF hL n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  simp only [show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega,
    show k + 7 - 3 = k + 4 by omega] at e ⊢
  have f5 : ((k + 5).factorial : ℚ) = ((k : ℚ) + 5) * ((k + 4).factorial : ℚ) := by
    rw [show k + 5 = (k + 4) + 1 by ring, P000483.fsucc]; push_cast; ring
  have f6 : ((k + 6).factorial : ℚ) = ((k : ℚ) + 6) * ((k : ℚ) + 5) * ((k + 4).factorial : ℚ) := by
    rw [show k + 6 = (k + 5) + 1 by ring, P000483.fsucc, f5]; push_cast; ring
  have f7 : ((k + 7).factorial : ℚ) = ((k : ℚ) + 7) * ((k : ℚ) + 6) * ((k : ℚ) + 5) * ((k + 4).factorial : ℚ) := by
    rw [show k + 7 = (k + 6) + 1 by ring, P000483.fsucc, f6]; push_cast; ring
  simp only [a, f5, f6, f7]
  push_cast at e ⊢
  linear_combination (((k : ℚ) + 6) * ((k : ℚ) + 5) * ((k + 4).factorial : ℚ)) * e
