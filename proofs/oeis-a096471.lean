import OMAStatements.S_oeis_a096471
import Mathlib

open OMA.S_oeis_a096471
open PowerSeries

namespace P096471

theorem nC (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : PowerSeries ℚ) = C (OfNat.ofNat n : ℚ) :=
  (map_ofNat C n).symm

theorem cXd (F : PowerSeries ℚ) (k : ℕ) : coeff k (X * d⁄dX ℚ F) = coeff k F * k := by
  rcases k with _ | k
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

theorem ne_of_cc (p : PowerSeries ℚ) (h : constantCoeff p ≠ 0) : p ≠ 0 := by
  intro h0; rw [h0, map_zero] at h; exact h rfl

set_option maxHeartbeats 4000000 in
theorem ode (G S L : PowerSeries ℚ) (hG : 2 * G = -(S * L)) (hS : (1 - X ^ 2) * d⁄dX ℚ S = S) (hL : (1 - X ^ 2) * d⁄dX ℚ L = -(2 * X))  :
    (X ^ 4 + 3 * X ^ 3 + 10 * X ^ 2 + 18 * X + 24) * (X * d⁄dX ℚ G) + (-2 * X ^ 5 - X ^ 4 - 4 * X ^ 3 - 15 * X ^ 2 - 33 * X - 50) * (X * d⁄dX ℚ (X * d⁄dX ℚ G)) + (-3 * X ^ 5 + X ^ 4 - 3 * X ^ 3 + X ^ 2 + 18 * X + 35) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ G))) + (-X ^ 5 + 4 * X ^ 4 + 4 * X ^ 3 + 6 * X ^ 2 - 3 * X - 10) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ G)))) + (X ^ 4 - 2 * X ^ 2 + 1) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ G))))) = 0 := by
  have hG1 := congrArg (d⁄dX ℚ) hG
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hG1
  try simp only [map_ofNat] at hG1
  try push_cast at hG1
  have hG2 := congrArg (d⁄dX ℚ) hG1
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hG2
  try simp only [map_ofNat] at hG2
  try push_cast at hG2
  have hG3 := congrArg (d⁄dX ℚ) hG2
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hG3
  try simp only [map_ofNat] at hG3
  try push_cast at hG3
  have hG4 := congrArg (d⁄dX ℚ) hG3
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hG4
  try simp only [map_ofNat] at hG4
  try push_cast at hG4
  have hG5 := congrArg (d⁄dX ℚ) hG4
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hG5
  try simp only [map_ofNat] at hG5
  try push_cast at hG5
  have hS1 := congrArg (d⁄dX ℚ) hS
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hS1
  try simp only [map_ofNat] at hS1
  try push_cast at hS1
  have hS2 := congrArg (d⁄dX ℚ) hS1
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hS2
  try simp only [map_ofNat] at hS2
  try push_cast at hS2
  have hS3 := congrArg (d⁄dX ℚ) hS2
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hS3
  try simp only [map_ofNat] at hS3
  try push_cast at hS3
  have hS4 := congrArg (d⁄dX ℚ) hS3
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hS4
  try simp only [map_ofNat] at hS4
  try push_cast at hS4
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
  have hL4 := congrArg (d⁄dX ℚ) hL3
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hL4
  try simp only [map_ofNat] at hL4
  try push_cast at hL4
  have key : (X ^ 0 * (2)) ^ 5 * (X ^ 0 * (-X ^ 2 + 1)) ^ 10 * (-X ^ 9 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ G)))) + X ^ 9 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ G))))) - 9 * X ^ 8 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ G))) + 14 * X ^ 8 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ G)))) - 18 * X ^ 7 * (d⁄dX ℚ (d⁄dX ℚ G)) + 50 * X ^ 7 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ G))) + 4 * X ^ 7 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ G)))) - 2 * X ^ 7 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ G))))) - 6 * X ^ 6 * (d⁄dX ℚ G) + 45 * X ^ 6 * (d⁄dX ℚ (d⁄dX ℚ G)) + 21 * X ^ 6 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ G))) - 14 * X ^ 6 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ G)))) + 6 * X ^ 5 * (d⁄dX ℚ G) + 15 * X ^ 5 * (d⁄dX ℚ (d⁄dX ℚ G)) - 13 * X ^ 5 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ G))) - 3 * X ^ 5 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ G)))) + X ^ 5 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ G)))))) = 0 := by
    linear_combination (-48 * X ^ 22 * S + 384 * X ^ 20 * S - 1344 * X ^ 18 * S + 2688 * X ^ 16 * S - 3360 * X ^ 14 * S + 2688 * X ^ 12 * S - 1344 * X ^ 10 * S + 384 * X ^ 8 * S - 48 * X ^ 6 * S) * hL + (48 * X ^ 23 * S - 384 * X ^ 21 * S + 1344 * X ^ 19 * S - 2688 * X ^ 17 * S + 3360 * X ^ 15 * S - 2688 * X ^ 13 * S + 1344 * X ^ 11 * S - 384 * X ^ 9 * S + 48 * X ^ 7 * S) * hL1 + (-48 * X ^ 26 * S + 96 * X ^ 25 * S + 384 * X ^ 24 * S - 912 * X ^ 23 * S - 1296 * X ^ 22 * S + 3888 * X ^ 21 * S + 2304 * X ^ 20 * S - 9792 * X ^ 19 * S - 2016 * X ^ 18 * S + 16128 * X ^ 17 * S - 18144 * X ^ 15 * S + 2016 * X ^ 14 * S + 14112 * X ^ 13 * S - 2304 * X ^ 12 * S - 7488 * X ^ 11 * S + 1296 * X ^ 10 * S + 2592 * X ^ 9 * S - 384 * X ^ 8 * S - 528 * X ^ 7 * S + 48 * X ^ 6 * S + 48 * X ^ 5 * S) * hL2 + (-16 * X ^ 27 * S + 96 * X ^ 26 * S + 128 * X ^ 25 * S - 960 * X ^ 24 * S - 400 * X ^ 23 * S + 4320 * X ^ 22 * S + 480 * X ^ 21 * S - 11520 * X ^ 20 * S + 480 * X ^ 19 * S + 20160 * X ^ 18 * S - 2688 * X ^ 17 * S - 24192 * X ^ 16 * S + 4704 * X ^ 15 * S + 20160 * X ^ 14 * S - 4800 * X ^ 13 * S - 11520 * X ^ 12 * S + 3120 * X ^ 11 * S + 4320 * X ^ 10 * S - 1280 * X ^ 9 * S - 960 * X ^ 8 * S + 304 * X ^ 7 * S + 96 * X ^ 6 * S - 32 * X ^ 5 * S) * hL3 + (16 * X ^ 27 * S - 176 * X ^ 25 * S + 880 * X ^ 23 * S - 2640 * X ^ 21 * S + 5280 * X ^ 19 * S - 7392 * X ^ 17 * S + 7392 * X ^ 15 * S - 5280 * X ^ 13 * S + 2640 * X ^ 11 * S - 880 * X ^ 9 * S + 176 * X ^ 7 * S - 16 * X ^ 5 * S) * hL4 + (-64 * X ^ 27 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) + 80 * X ^ 27 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L)))) - 240 * X ^ 26 * (d⁄dX ℚ (d⁄dX ℚ L)) + 576 * X ^ 26 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) - 96 * X ^ 25 * (d⁄dX ℚ L) + 768 * X ^ 25 * (d⁄dX ℚ (d⁄dX ℚ L)) + 672 * X ^ 25 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) - 880 * X ^ 25 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L)))) + 144 * X ^ 24 * (d⁄dX ℚ L) + 2208 * X ^ 24 * (d⁄dX ℚ (d⁄dX ℚ L)) - 5760 * X ^ 24 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) + 864 * X ^ 23 * (d⁄dX ℚ L) - 7344 * X ^ 23 * (d⁄dX ℚ (d⁄dX ℚ L)) - 3200 * X ^ 23 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) + 4400 * X ^ 23 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L)))) - 1392 * X ^ 22 * (d⁄dX ℚ L) - 9072 * X ^ 22 * (d⁄dX ℚ (d⁄dX ℚ L)) + 25920 * X ^ 22 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) - 3456 * X ^ 21 * (d⁄dX ℚ L) + 31536 * X ^ 21 * (d⁄dX ℚ (d⁄dX ℚ L)) + 9120 * X ^ 21 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) - 13200 * X ^ 21 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L)))) + 5952 * X ^ 20 * (d⁄dX ℚ L) + 21888 * X ^ 20 * (d⁄dX ℚ (d⁄dX ℚ L)) - 69120 * X ^ 20 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) + 8064 * X ^ 19 * (d⁄dX ℚ L) - 80064 * X ^ 19 * (d⁄dX ℚ (d⁄dX ℚ L)) - 17280 * X ^ 19 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) + 26400 * X ^ 19 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L)))) - 14784 * X ^ 18 * (d⁄dX ℚ L) - 34272 * X ^ 18 * (d⁄dX ℚ (d⁄dX ℚ L)) + 120960 * X ^ 18 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) - 12096 * X ^ 17 * (d⁄dX ℚ L) + 133056 * X ^ 17 * (d⁄dX ℚ (d⁄dX ℚ L)) + 22848 * X ^ 17 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) - 36960 * X ^ 17 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L)))) + 23520 * X ^ 16 * (d⁄dX ℚ L) + 36288 * X ^ 16 * (d⁄dX ℚ (d⁄dX ℚ L)) - 145152 * X ^ 16 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) + 12096 * X ^ 15 * (d⁄dX ℚ L) - 151200 * X ^ 15 * (d⁄dX ℚ (d⁄dX ℚ L)) - 21504 * X ^ 15 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) + 36960 * X ^ 15 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L)))) - 24864 * X ^ 14 * (d⁄dX ℚ L) - 26208 * X ^ 14 * (d⁄dX ℚ (d⁄dX ℚ L)) + 120960 * X ^ 14 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) - 8064 * X ^ 13 * (d⁄dX ℚ L) + 118944 * X ^ 13 * (d⁄dX ℚ (d⁄dX ℚ L)) + 14400 * X ^ 13 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) - 26400 * X ^ 13 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L)))) + 17472 * X ^ 12 * (d⁄dX ℚ L) + 12672 * X ^ 12 * (d⁄dX ℚ (d⁄dX ℚ L)) - 69120 * X ^ 12 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) + 3456 * X ^ 11 * (d⁄dX ℚ L) - 63936 * X ^ 11 * (d⁄dX ℚ (d⁄dX ℚ L)) - 6720 * X ^ 11 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) + 13200 * X ^ 11 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L)))) - 7872 * X ^ 10 * (d⁄dX ℚ L) - 3888 * X ^ 10 * (d⁄dX ℚ (d⁄dX ℚ L)) + 25920 * X ^ 10 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) - 864 * X ^ 9 * (d⁄dX ℚ L) + 22464 * X ^ 9 * (d⁄dX ℚ (d⁄dX ℚ L)) + 2080 * X ^ 9 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) - 4400 * X ^ 9 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L)))) + 2064 * X ^ 8 * (d⁄dX ℚ L) + 672 * X ^ 8 * (d⁄dX ℚ (d⁄dX ℚ L)) - 5760 * X ^ 8 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) + 96 * X ^ 7 * (d⁄dX ℚ L) - 4656 * X ^ 7 * (d⁄dX ℚ (d⁄dX ℚ L)) - 384 * X ^ 7 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) + 880 * X ^ 7 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L)))) - 240 * X ^ 6 * (d⁄dX ℚ L) - 48 * X ^ 6 * (d⁄dX ℚ (d⁄dX ℚ L)) + 576 * X ^ 6 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) + 432 * X ^ 5 * (d⁄dX ℚ (d⁄dX ℚ L)) + 32 * X ^ 5 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) - 80 * X ^ 5 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))))) * hS + (-96 * X ^ 27 * (d⁄dX ℚ (d⁄dX ℚ L)) + 160 * X ^ 27 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) - 176 * X ^ 26 * (d⁄dX ℚ L) + 704 * X ^ 26 * (d⁄dX ℚ (d⁄dX ℚ L)) + 320 * X ^ 25 * (d⁄dX ℚ L) + 1088 * X ^ 25 * (d⁄dX ℚ (d⁄dX ℚ L)) - 1760 * X ^ 25 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) + 1728 * X ^ 24 * (d⁄dX ℚ L) - 7040 * X ^ 24 * (d⁄dX ℚ (d⁄dX ℚ L)) - 3136 * X ^ 23 * (d⁄dX ℚ L) - 5600 * X ^ 23 * (d⁄dX ℚ (d⁄dX ℚ L)) + 8800 * X ^ 23 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) - 7632 * X ^ 22 * (d⁄dX ℚ L) + 31680 * X ^ 22 * (d⁄dX ℚ (d⁄dX ℚ L)) + 13824 * X ^ 21 * (d⁄dX ℚ L) + 17280 * X ^ 21 * (d⁄dX ℚ (d⁄dX ℚ L)) - 26400 * X ^ 21 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) + 19968 * X ^ 20 * (d⁄dX ℚ L) - 84480 * X ^ 20 * (d⁄dX ℚ (d⁄dX ℚ L)) - 36096 * X ^ 19 * (d⁄dX ℚ L) - 35520 * X ^ 19 * (d⁄dX ℚ (d⁄dX ℚ L)) + 52800 * X ^ 19 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) - 34272 * X ^ 18 * (d⁄dX ℚ L) + 147840 * X ^ 18 * (d⁄dX ℚ (d⁄dX ℚ L)) + 61824 * X ^ 17 * (d⁄dX ℚ L) + 51072 * X ^ 17 * (d⁄dX ℚ (d⁄dX ℚ L)) - 73920 * X ^ 17 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) + 40320 * X ^ 16 * (d⁄dX ℚ L) - 177408 * X ^ 16 * (d⁄dX ℚ (d⁄dX ℚ L)) - 72576 * X ^ 15 * (d⁄dX ℚ L) - 52416 * X ^ 15 * (d⁄dX ℚ (d⁄dX ℚ L)) + 73920 * X ^ 15 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) - 32928 * X ^ 14 * (d⁄dX ℚ L) + 147840 * X ^ 14 * (d⁄dX ℚ (d⁄dX ℚ L)) + 59136 * X ^ 13 * (d⁄dX ℚ L) + 38400 * X ^ 13 * (d⁄dX ℚ (d⁄dX ℚ L)) - 52800 * X ^ 13 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) + 18432 * X ^ 12 * (d⁄dX ℚ L) - 84480 * X ^ 12 * (d⁄dX ℚ (d⁄dX ℚ L)) - 33024 * X ^ 11 * (d⁄dX ℚ L) - 19680 * X ^ 11 * (d⁄dX ℚ (d⁄dX ℚ L)) + 26400 * X ^ 11 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) - 6768 * X ^ 10 * (d⁄dX ℚ L) + 31680 * X ^ 10 * (d⁄dX ℚ (d⁄dX ℚ L)) + 12096 * X ^ 9 * (d⁄dX ℚ L) + 6720 * X ^ 9 * (d⁄dX ℚ (d⁄dX ℚ L)) - 8800 * X ^ 9 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) + 1472 * X ^ 8 * (d⁄dX ℚ L) - 7040 * X ^ 8 * (d⁄dX ℚ (d⁄dX ℚ L)) - 2624 * X ^ 7 * (d⁄dX ℚ L) - 1376 * X ^ 7 * (d⁄dX ℚ (d⁄dX ℚ L)) + 1760 * X ^ 7 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L))) - 144 * X ^ 6 * (d⁄dX ℚ L) + 704 * X ^ 6 * (d⁄dX ℚ (d⁄dX ℚ L)) + 256 * X ^ 5 * (d⁄dX ℚ L) + 128 * X ^ 5 * (d⁄dX ℚ (d⁄dX ℚ L)) - 160 * X ^ 5 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ L)))) * hS1 + (-64 * X ^ 27 * (d⁄dX ℚ L) + 160 * X ^ 27 * (d⁄dX ℚ (d⁄dX ℚ L)) - 48 * X ^ 26 * L + 416 * X ^ 26 * (d⁄dX ℚ L) + 48 * X ^ 25 * L + 752 * X ^ 25 * (d⁄dX ℚ L) - 1760 * X ^ 25 * (d⁄dX ℚ (d⁄dX ℚ L)) + 480 * X ^ 24 * L - 4160 * X ^ 24 * (d⁄dX ℚ L) - 480 * X ^ 23 * L - 4000 * X ^ 23 * (d⁄dX ℚ L) + 8800 * X ^ 23 * (d⁄dX ℚ (d⁄dX ℚ L)) - 2160 * X ^ 22 * L + 18720 * X ^ 22 * (d⁄dX ℚ L) + 2160 * X ^ 21 * L + 12720 * X ^ 21 * (d⁄dX ℚ L) - 26400 * X ^ 21 * (d⁄dX ℚ (d⁄dX ℚ L)) + 5760 * X ^ 20 * L - 49920 * X ^ 20 * (d⁄dX ℚ L) - 5760 * X ^ 19 * L - 26880 * X ^ 19 * (d⁄dX ℚ L) + 52800 * X ^ 19 * (d⁄dX ℚ (d⁄dX ℚ L)) - 10080 * X ^ 18 * L + 87360 * X ^ 18 * (d⁄dX ℚ L) + 10080 * X ^ 17 * L + 39648 * X ^ 17 * (d⁄dX ℚ L) - 73920 * X ^ 17 * (d⁄dX ℚ (d⁄dX ℚ L)) + 12096 * X ^ 16 * L - 104832 * X ^ 16 * (d⁄dX ℚ L) - 12096 * X ^ 15 * L - 41664 * X ^ 15 * (d⁄dX ℚ L) + 73920 * X ^ 15 * (d⁄dX ℚ (d⁄dX ℚ L)) - 10080 * X ^ 14 * L + 87360 * X ^ 14 * (d⁄dX ℚ L) + 10080 * X ^ 13 * L + 31200 * X ^ 13 * (d⁄dX ℚ L) - 52800 * X ^ 13 * (d⁄dX ℚ (d⁄dX ℚ L)) + 5760 * X ^ 12 * L - 49920 * X ^ 12 * (d⁄dX ℚ L) - 5760 * X ^ 11 * L - 16320 * X ^ 11 * (d⁄dX ℚ L) + 26400 * X ^ 11 * (d⁄dX ℚ (d⁄dX ℚ L)) - 2160 * X ^ 10 * L + 18720 * X ^ 10 * (d⁄dX ℚ L) + 2160 * X ^ 9 * L + 5680 * X ^ 9 * (d⁄dX ℚ L) - 8800 * X ^ 9 * (d⁄dX ℚ (d⁄dX ℚ L)) + 480 * X ^ 8 * L - 4160 * X ^ 8 * (d⁄dX ℚ L) - 480 * X ^ 7 * L - 1184 * X ^ 7 * (d⁄dX ℚ L) + 1760 * X ^ 7 * (d⁄dX ℚ (d⁄dX ℚ L)) - 48 * X ^ 6 * L + 416 * X ^ 6 * (d⁄dX ℚ L) + 48 * X ^ 5 * L + 112 * X ^ 5 * (d⁄dX ℚ L) - 160 * X ^ 5 * (d⁄dX ℚ (d⁄dX ℚ L))) * hS2 + (-16 * X ^ 27 * L + 80 * X ^ 27 * (d⁄dX ℚ L) + 96 * X ^ 26 * L + 192 * X ^ 25 * L - 880 * X ^ 25 * (d⁄dX ℚ L) - 960 * X ^ 24 * L - 1040 * X ^ 23 * L + 4400 * X ^ 23 * (d⁄dX ℚ L) + 4320 * X ^ 22 * L + 3360 * X ^ 21 * L - 13200 * X ^ 21 * (d⁄dX ℚ L) - 11520 * X ^ 20 * L - 7200 * X ^ 19 * L + 26400 * X ^ 19 * (d⁄dX ℚ L) + 20160 * X ^ 18 * L + 10752 * X ^ 17 * L - 36960 * X ^ 17 * (d⁄dX ℚ L) - 24192 * X ^ 16 * L - 11424 * X ^ 15 * L + 36960 * X ^ 15 * (d⁄dX ℚ L) + 20160 * X ^ 14 * L + 8640 * X ^ 13 * L - 26400 * X ^ 13 * (d⁄dX ℚ L) - 11520 * X ^ 12 * L - 4560 * X ^ 11 * L + 13200 * X ^ 11 * (d⁄dX ℚ L) + 4320 * X ^ 10 * L + 1600 * X ^ 9 * L - 4400 * X ^ 9 * (d⁄dX ℚ L) - 960 * X ^ 8 * L - 336 * X ^ 7 * L + 880 * X ^ 7 * (d⁄dX ℚ L) + 96 * X ^ 6 * L + 32 * X ^ 5 * L - 80 * X ^ 5 * (d⁄dX ℚ L)) * hS3 + (16 * X ^ 27 * L - 176 * X ^ 25 * L + 880 * X ^ 23 * L - 2640 * X ^ 21 * L + 5280 * X ^ 19 * L - 7392 * X ^ 17 * L + 7392 * X ^ 15 * L - 5280 * X ^ 13 * L + 2640 * X ^ 11 * L - 880 * X ^ 9 * L + 176 * X ^ 7 * L - 16 * X ^ 5 * L) * hS4 + (-96 * X ^ 26 + 96 * X ^ 25 + 960 * X ^ 24 - 960 * X ^ 23 - 4320 * X ^ 22 + 4320 * X ^ 21 + 11520 * X ^ 20 - 11520 * X ^ 19 - 20160 * X ^ 18 + 20160 * X ^ 17 + 24192 * X ^ 16 - 24192 * X ^ 15 - 20160 * X ^ 14 + 20160 * X ^ 13 + 11520 * X ^ 12 - 11520 * X ^ 11 - 4320 * X ^ 10 + 4320 * X ^ 9 + 960 * X ^ 8 - 960 * X ^ 7 - 96 * X ^ 6 + 96 * X ^ 5) * hG1 + (-288 * X ^ 27 + 720 * X ^ 26 + 3120 * X ^ 25 - 7200 * X ^ 24 - 15360 * X ^ 23 + 32400 * X ^ 22 + 45360 * X ^ 21 - 86400 * X ^ 20 - 89280 * X ^ 19 + 151200 * X ^ 18 + 122976 * X ^ 17 - 181440 * X ^ 16 - 120960 * X ^ 15 + 151200 * X ^ 14 + 84960 * X ^ 13 - 86400 * X ^ 12 - 41760 * X ^ 11 + 32400 * X ^ 10 + 13680 * X ^ 9 - 7200 * X ^ 8 - 2688 * X ^ 7 + 720 * X ^ 6 + 240 * X ^ 5) * hG2 + (-144 * X ^ 28 + 800 * X ^ 27 + 1776 * X ^ 26 - 8208 * X ^ 25 - 9840 * X ^ 24 + 38080 * X ^ 23 + 32400 * X ^ 22 - 105360 * X ^ 21 - 70560 * X ^ 20 + 192960 * X ^ 19 + 106848 * X ^ 18 - 245280 * X ^ 17 - 114912 * X ^ 16 + 220416 * X ^ 15 + 87840 * X ^ 14 - 139680 * X ^ 13 - 46800 * X ^ 12 + 60960 * X ^ 11 + 16560 * X ^ 10 - 17360 * X ^ 9 - 3504 * X ^ 8 + 2880 * X ^ 7 + 336 * X ^ 6 - 208 * X ^ 5) * hG3 + (-16 * X ^ 29 + 224 * X ^ 28 + 224 * X ^ 27 - 2464 * X ^ 26 - 1408 * X ^ 25 + 12320 * X ^ 24 + 5280 * X ^ 23 - 36960 * X ^ 22 - 13200 * X ^ 21 + 73920 * X ^ 20 + 23232 * X ^ 19 - 103488 * X ^ 18 - 29568 * X ^ 17 + 103488 * X ^ 16 + 27456 * X ^ 15 - 73920 * X ^ 14 - 18480 * X ^ 13 + 36960 * X ^ 12 + 8800 * X ^ 11 - 12320 * X ^ 10 - 2816 * X ^ 9 + 2464 * X ^ 8 + 544 * X ^ 7 - 224 * X ^ 6 - 48 * X ^ 5) * hG4 + (16 * X ^ 29 - 192 * X ^ 27 + 1056 * X ^ 25 - 3520 * X ^ 23 + 7920 * X ^ 21 - 12672 * X ^ 19 + 14784 * X ^ 17 - 12672 * X ^ 15 + 7920 * X ^ 13 - 3520 * X ^ 11 + 1056 * X ^ 9 - 192 * X ^ 7 + 16 * X ^ 5) * hG5
  have hf0 : (X ^ 0 * (2) : PowerSeries ℚ) ≠ 0 := ne_of_cc _ (by simp [nC, constantCoeff_C])
  have hf1 : (X ^ 0 * (-X ^ 2 + 1) : PowerSeries ℚ) ≠ 0 := ne_of_cc _ (by simp [nC, constantCoeff_C])
  have hE := (mul_eq_zero.mp key).resolve_left (mul_ne_zero (pow_ne_zero _ hf0) (pow_ne_zero _ hf1))
  have th2 : X * d⁄dX ℚ (X * d⁄dX ℚ G) = 1 * X ^ 1 * (d⁄dX ℚ G) + 1 * X ^ 2 * (d⁄dX ℚ (d⁄dX ℚ G)) := by
    simp only [Derivation.leibniz, Derivation.leibniz_pow, derivative_X, smul_eq_mul, nsmul_eq_mul, map_add, map_mul, nC, derivative_C, Derivation.map_one_eq_zero, map_zero, mul_zero, add_zero, zero_mul, zero_add]
    try simp only [map_ofNat]
    ring
  have th3 : X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ G)) = 1 * X ^ 1 * (d⁄dX ℚ G) + 3 * X ^ 2 * (d⁄dX ℚ (d⁄dX ℚ G)) + 1 * X ^ 3 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ G))) := by
    simp only [Derivation.leibniz, Derivation.leibniz_pow, derivative_X, smul_eq_mul, nsmul_eq_mul, th2, map_add, map_mul, nC, derivative_C, Derivation.map_one_eq_zero, map_zero, mul_zero, add_zero, zero_mul, zero_add]
    try simp only [map_ofNat]
    ring
  have th4 : X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ G))) = 1 * X ^ 1 * (d⁄dX ℚ G) + 7 * X ^ 2 * (d⁄dX ℚ (d⁄dX ℚ G)) + 6 * X ^ 3 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ G))) + 1 * X ^ 4 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ G)))) := by
    simp only [Derivation.leibniz, Derivation.leibniz_pow, derivative_X, smul_eq_mul, nsmul_eq_mul, th2, th3, map_add, map_mul, nC, derivative_C, Derivation.map_one_eq_zero, map_zero, mul_zero, add_zero, zero_mul, zero_add]
    try simp only [map_ofNat]
    ring
  have th5 : X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ G)))) = 1 * X ^ 1 * (d⁄dX ℚ G) + 15 * X ^ 2 * (d⁄dX ℚ (d⁄dX ℚ G)) + 25 * X ^ 3 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ G))) + 10 * X ^ 4 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ G)))) + 1 * X ^ 5 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ G))))) := by
    simp only [Derivation.leibniz, Derivation.leibniz_pow, derivative_X, smul_eq_mul, nsmul_eq_mul, th2, th3, th4, map_add, map_mul, nC, derivative_C, Derivation.map_one_eq_zero, map_zero, mul_zero, add_zero, zero_mul, zero_add]
    try simp only [map_ofNat]
    ring
  rw [th5, th4, th3, th2]
  linear_combination hE

lemma hS' (S : PowerSeries ℚ) (hS : S ^ 2 * (1 - X) = 1 + X) (hc : constantCoeff S = 1) :
    (1 - X ^ 2) * d⁄dX ℚ S = S := by
  have hS1 := congrArg (d⁄dX ℚ) hS
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hS1
  try simp only [map_ofNat] at hS1
  try push_cast at hS1
  have h2 : (2 * S) * ((1 - X ^ 2) * d⁄dX ℚ S - S) = 0 := by
    linear_combination (1 + X) * hS1 - hS
  have hne : (2 * S : PowerSeries ℚ) ≠ 0 := ne_of_cc _ (by simp [nC, constantCoeff_C, hc])
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hne)

lemma fac (k : ℕ) : ((k + 1).factorial : ℚ) = (k + 1) * k.factorial ∧
    ((k + 2).factorial : ℚ) = (k + 2) * (k + 1) * k.factorial ∧
    ((k + 3).factorial : ℚ) = (k + 3) * (k + 2) * (k + 1) * k.factorial ∧
    ((k + 4).factorial : ℚ) = (k + 4) * (k + 3) * (k + 2) * (k + 1) * k.factorial ∧
    ((k + 5).factorial : ℚ) = (k + 5) * (k + 4) * (k + 3) * (k + 2) * (k + 1) * k.factorial := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Nat.factorial_succ] <;> ring

end P096471

theorem OMA.solution : type_of% @OMA.S_oeis_a096471.main := by
  intro S L G hS hS0 _ hL hG n hn
  have hc : constantCoeff S = 1 := by rw [← coeff_zero_eq_constantCoeff_apply]; exact hS0
  have e := congrArg (coeff n) (P096471.ode G S L hG (P096471.hS' S hS hc) hL)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
    show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega,
    show k + 5 - 5 = k by omega]
  norm_num only at e ⊢
  simp only [P096471.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, P096471.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  unfold a
  obtain ⟨f1, f2, f3, f4, f5⟩ := P096471.fac k
  rw [f1, f2, f3, f4, f5]
  push_cast at e ⊢
  linear_combination (k.factorial : ℚ) * e
