import OMAStatements.S_oeis_a045743
import Mathlib

open OMA.S_oeis_a045743
open PowerSeries

namespace P045743

theorem nC (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : PowerSeries ℚ) = C (OfNat.ofNat n : ℚ) :=
  (map_ofNat C n).symm

theorem cXd (F : PowerSeries ℚ) (k : ℕ) : coeff k (X * d⁄dX ℚ F) = coeff k F * k := by
  rcases k with _ | k
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

theorem ne_of_cc (p : PowerSeries ℚ) (h : constantCoeff p ≠ 0) : p ≠ 0 := by
  intro h0; rw [h0, map_zero] at h; exact h rfl

set_option maxHeartbeats 4000000 in
theorem ode (G : PowerSeries ℚ) (hP : (1 : ℚ⟦X⟧) * X * G ^ 4 + (1 : ℚ⟦X⟧) * G ^ 3 + (-4 : ℚ⟦X⟧) * G ^ 2 + (4 : ℚ⟦X⟧) * G + (-1 : ℚ⟦X⟧) = 0) (hG : ((256 : ℚ⟦X⟧) * X ^ 7 + (512 : ℚ⟦X⟧) * X ^ 6 + (-32 : ℚ⟦X⟧) * X ^ 5 + (-5 : ℚ⟦X⟧) * X ^ 4) * d⁄dX ℚ G = (64 : ℚ⟦X⟧) * X ^ 6 * G ^ 3 + (64 : ℚ⟦X⟧) * X ^ 6 * G ^ 2 + (-64 : ℚ⟦X⟧) * X ^ 6 * G + (28 : ℚ⟦X⟧) * X ^ 5 * G ^ 3 + (144 : ℚ⟦X⟧) * X ^ 5 * G ^ 2 + (-352 : ℚ⟦X⟧) * X ^ 5 * G + (112 : ℚ⟦X⟧) * X ^ 5 + (23 : ℚ⟦X⟧) * X ^ 4 * G ^ 2 + (-40 : ℚ⟦X⟧) * X ^ 4 * G + (12 : ℚ⟦X⟧) * X ^ 4) :
    (52437120 * X ^ 4 - 218701272 * X ^ 3 - 141110640 * X ^ 2) * (G) + (420729344 * X ^ 4 - 1588953952 * X ^ 3 - 563017808 * X ^ 2 - 44286816 * X + 11489225) * (X * d⁄dX ℚ G) + (1104390656 * X ^ 4 - 3241717728 * X ^ 3 - 1870803168 * X ^ 2 - 10981232 * X - 6769090) * (X * d⁄dX ℚ (X * d⁄dX ℚ G)) + (1138376704 * X ^ 4 - 1664486912 * X ^ 3 - 2190304768 * X ^ 2 + 69088080 * X - 11489225) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ G))) + (386031616 * X ^ 4 + 425485824 * X ^ 3 - 741408768 * X ^ 2 + 35782496 * X + 6769090) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ G)))) = 4061664 * X ^ 3 - 54626922 * X ^ 2 := by
  have h1 : ((256 : ℚ⟦X⟧) * X ^ 7 + (512 : ℚ⟦X⟧) * X ^ 6 + (-32 : ℚ⟦X⟧) * X ^ 5 + (-5 : ℚ⟦X⟧) * X ^ 4) ^ 1 * ((1 : ℚ⟦X⟧) * X) ^ 0 * (d⁄dX ℚ G) = (64 : ℚ⟦X⟧) * X ^ 6 * G ^ 3 + (64 : ℚ⟦X⟧) * X ^ 6 * G ^ 2 + (-64 : ℚ⟦X⟧) * X ^ 6 * G + (28 : ℚ⟦X⟧) * X ^ 5 * G ^ 3 + (144 : ℚ⟦X⟧) * X ^ 5 * G ^ 2 + (-352 : ℚ⟦X⟧) * X ^ 5 * G + (112 : ℚ⟦X⟧) * X ^ 5 + (23 : ℚ⟦X⟧) * X ^ 4 * G ^ 2 + (-40 : ℚ⟦X⟧) * X ^ 4 * G + (12 : ℚ⟦X⟧) * X ^ 4 := by linear_combination hG
  have d1 := congrArg (d⁄dX ℚ) h1
  try simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at d1
  try simp only [map_ofNat] at d1
  try push_cast at d1
  have h2 : ((256 : ℚ⟦X⟧) * X ^ 7 + (512 : ℚ⟦X⟧) * X ^ 6 + (-32 : ℚ⟦X⟧) * X ^ 5 + (-5 : ℚ⟦X⟧) * X ^ 4) ^ 2 * ((1 : ℚ⟦X⟧) * X) ^ 3 * (d⁄dX ℚ (d⁄dX ℚ G)) = (-24576 : ℚ⟦X⟧) * X ^ 15 * G ^ 3 + (-28672 : ℚ⟦X⟧) * X ^ 15 * G ^ 2 + (20480 : ℚ⟦X⟧) * X ^ 15 * G + (-46080 : ℚ⟦X⟧) * X ^ 14 * G ^ 3 + (-114688 : ℚ⟦X⟧) * X ^ 14 * G ^ 2 + (169984 : ℚ⟦X⟧) * X ^ 14 * G + (-44032 : ℚ⟦X⟧) * X ^ 14 + (-18432 : ℚ⟦X⟧) * X ^ 13 * G ^ 3 + (-117888 : ℚ⟦X⟧) * X ^ 13 * G ^ 2 + (215552 : ℚ⟦X⟧) * X ^ 13 * G + (-64000 : ℚ⟦X⟧) * X ^ 13 + (768 : ℚ⟦X⟧) * X ^ 12 * G ^ 3 + (-7088 : ℚ⟦X⟧) * X ^ 12 * G ^ 2 + (13648 : ℚ⟦X⟧) * X ^ 12 * G + (-4224 : ℚ⟦X⟧) * X ^ 12 + (50 : ℚ⟦X⟧) * X ^ 11 * G ^ 3 + (728 : ℚ⟦X⟧) * X ^ 11 * G ^ 2 + (-840 : ℚ⟦X⟧) * X ^ 11 * G + (212 : ℚ⟦X⟧) * X ^ 11 := by
    linear_combination ((1 : ℚ⟦X⟧) * X) ^ 2 * (((256 : ℚ⟦X⟧) * X ^ 7 + (512 : ℚ⟦X⟧) * X ^ 6 + (-32 : ℚ⟦X⟧) * X ^ 5 + (-5 : ℚ⟦X⟧) * X ^ 4) * ((1 : ℚ⟦X⟧) * X) * d1 + ((1 : ℚ⟦X⟧) * X) * ((192 : ℚ⟦X⟧) * X ^ 6 * G ^ 2 + (128 : ℚ⟦X⟧) * X ^ 6 * G + (-64 : ℚ⟦X⟧) * X ^ 6 + (84 : ℚ⟦X⟧) * X ^ 5 * G ^ 2 + (288 : ℚ⟦X⟧) * X ^ 5 * G + (-352 : ℚ⟦X⟧) * X ^ 5 + (46 : ℚ⟦X⟧) * X ^ 4 * G + (-40 : ℚ⟦X⟧) * X ^ 4) * hG - ((1792 : ℚ⟦X⟧) * X ^ 7 + (3072 : ℚ⟦X⟧) * X ^ 6 + (-160 : ℚ⟦X⟧) * X ^ 5 + (-20 : ℚ⟦X⟧) * X ^ 4) * h1) + ((12288 : ℚ⟦X⟧) * X ^ 14 * G + (20480 : ℚ⟦X⟧) * X ^ 14 + (10752 : ℚ⟦X⟧) * X ^ 13 * G + (42752 : ℚ⟦X⟧) * X ^ 13 + (2352 : ℚ⟦X⟧) * X ^ 12 * G + (16768 : ℚ⟦X⟧) * X ^ 12 + (868 : ℚ⟦X⟧) * X ^ 11) * hP
  have d2 := congrArg (d⁄dX ℚ) h2
  try simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at d2
  try simp only [map_ofNat] at d2
  try push_cast at d2
  have h3 : ((256 : ℚ⟦X⟧) * X ^ 7 + (512 : ℚ⟦X⟧) * X ^ 6 + (-32 : ℚ⟦X⟧) * X ^ 5 + (-5 : ℚ⟦X⟧) * X ^ 4) ^ 3 * ((1 : ℚ⟦X⟧) * X) ^ 6 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ G))) = (14942208 : ℚ⟦X⟧) * X ^ 24 * G ^ 3 + (19660800 : ℚ⟦X⟧) * X ^ 24 * G ^ 2 + (-11796480 : ℚ⟦X⟧) * X ^ 24 * G + (48218112 : ℚ⟦X⟧) * X ^ 23 * G ^ 3 + (113836032 : ℚ⟦X⟧) * X ^ 23 * G ^ 2 + (-126222336 : ℚ⟦X⟧) * X ^ 23 * G + (27721728 : ℚ⟦X⟧) * X ^ 23 + (55689216 : ℚ⟦X⟧) * X ^ 22 * G ^ 3 + (221294592 : ℚ⟦X⟧) * X ^ 22 * G ^ 2 + (-296681472 : ℚ⟦X⟧) * X ^ 22 * G + (76333056 : ℚ⟦X⟧) * X ^ 22 + (17581056 : ℚ⟦X⟧) * X ^ 21 * G ^ 3 + (141751296 : ℚ⟦X⟧) * X ^ 21 * G ^ 2 + (-221193216 : ℚ⟦X⟧) * X ^ 21 * G + (62791680 : ℚ⟦X⟧) * X ^ 21 + (-725952 : ℚ⟦X⟧) * X ^ 20 * G ^ 3 + (-6491904 : ℚ⟦X⟧) * X ^ 20 * G ^ 2 + (2962944 : ℚ⟦X⟧) * X ^ 20 * G + (-155904 : ℚ⟦X⟧) * X ^ 20 + (-48576 : ℚ⟦X⟧) * X ^ 19 * G ^ 3 + (123216 : ℚ⟦X⟧) * X ^ 19 * G ^ 2 + (-848256 : ℚ⟦X⟧) * X ^ 19 * G + (307008 : ℚ⟦X⟧) * X ^ 19 + (2400 : ℚ⟦X⟧) * X ^ 18 * G ^ 3 + (154464 : ℚ⟦X⟧) * X ^ 18 * G ^ 2 + (-231720 : ℚ⟦X⟧) * X ^ 18 * G + (65856 : ℚ⟦X⟧) * X ^ 18 + (750 : ℚ⟦X⟧) * X ^ 17 * G ^ 3 + (-3000 : ℚ⟦X⟧) * X ^ 17 * G ^ 2 + (3000 : ℚ⟦X⟧) * X ^ 17 * G + (-750 : ℚ⟦X⟧) * X ^ 17 := by
    linear_combination ((1 : ℚ⟦X⟧) * X) ^ 2 * (((256 : ℚ⟦X⟧) * X ^ 7 + (512 : ℚ⟦X⟧) * X ^ 6 + (-32 : ℚ⟦X⟧) * X ^ 5 + (-5 : ℚ⟦X⟧) * X ^ 4) * ((1 : ℚ⟦X⟧) * X) * d2 + ((1 : ℚ⟦X⟧) * X) * ((-73728 : ℚ⟦X⟧) * X ^ 15 * G ^ 2 + (-57344 : ℚ⟦X⟧) * X ^ 15 * G + (20480 : ℚ⟦X⟧) * X ^ 15 + (-138240 : ℚ⟦X⟧) * X ^ 14 * G ^ 2 + (-229376 : ℚ⟦X⟧) * X ^ 14 * G + (169984 : ℚ⟦X⟧) * X ^ 14 + (-55296 : ℚ⟦X⟧) * X ^ 13 * G ^ 2 + (-235776 : ℚ⟦X⟧) * X ^ 13 * G + (215552 : ℚ⟦X⟧) * X ^ 13 + (2304 : ℚ⟦X⟧) * X ^ 12 * G ^ 2 + (-14176 : ℚ⟦X⟧) * X ^ 12 * G + (13648 : ℚ⟦X⟧) * X ^ 12 + (150 : ℚ⟦X⟧) * X ^ 11 * G ^ 2 + (1456 : ℚ⟦X⟧) * X ^ 11 * G + (-840 : ℚ⟦X⟧) * X ^ 11) * hG - ((4352 : ℚ⟦X⟧) * X ^ 7 + (7680 : ℚ⟦X⟧) * X ^ 6 + (-416 : ℚ⟦X⟧) * X ^ 5 + (-55 : ℚ⟦X⟧) * X ^ 4) * h2) + ((-4718592 : ℚ⟦X⟧) * X ^ 23 * G + (-8388608 : ℚ⟦X⟧) * X ^ 23 + (-10911744 : ℚ⟦X⟧) * X ^ 22 * G + (-31031296 : ℚ⟦X⟧) * X ^ 22 + (-7409664 : ℚ⟦X⟧) * X ^ 21 * G + (-35741696 : ℚ⟦X⟧) * X ^ 21 + (-1400832 : ℚ⟦X⟧) * X ^ 20 * G + (-11094016 : ℚ⟦X⟧) * X ^ 20 + (74112 : ℚ⟦X⟧) * X ^ 19 * G + (166656 : ℚ⟦X⟧) * X ^ 19 + (4200 : ℚ⟦X⟧) * X ^ 18 * G + (41248 : ℚ⟦X⟧) * X ^ 18 + (-750 : ℚ⟦X⟧) * X ^ 17) * hP
  have d3 := congrArg (d⁄dX ℚ) h3
  try simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at d3
  try simp only [map_ofNat] at d3
  try push_cast at d3
  have h4 : ((256 : ℚ⟦X⟧) * X ^ 7 + (512 : ℚ⟦X⟧) * X ^ 6 + (-32 : ℚ⟦X⟧) * X ^ 5 + (-5 : ℚ⟦X⟧) * X ^ 4) ^ 4 * ((1 : ℚ⟦X⟧) * X) ^ 9 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ G)))) = (-12582912000 : ℚ⟦X⟧) * X ^ 33 * G ^ 3 + (-18371051520 : ℚ⟦X⟧) * X ^ 33 * G ^ 2 + (9814671360 : ℚ⟦X⟧) * X ^ 33 * G + (-56497274880 : ℚ⟦X⟧) * X ^ 32 * G ^ 3 + (-139670323200 : ℚ⟦X⟧) * X ^ 32 * G ^ 2 + (127213240320 : ℚ⟦X⟧) * X ^ 32 * G + (-24322768896 : ℚ⟦X⟧) * X ^ 32 + (-107778932736 : ℚ⟦X⟧) * X ^ 31 * G ^ 3 + (-402151440384 : ℚ⟦X⟧) * X ^ 31 * G ^ 2 + (431820374016 : ℚ⟦X⟧) * X ^ 31 * G + (-97662271488 : ℚ⟦X⟧) * X ^ 31 + (-88654479360 : ℚ⟦X⟧) * X ^ 30 * G ^ 3 + (-506593935360 : ℚ⟦X⟧) * X ^ 30 * G ^ 2 + (615704297472 : ℚ⟦X⟧) * X ^ 30 * G + (-154389184512 : ℚ⟦X⟧) * X ^ 30 + (-23971381248 : ℚ⟦X⟧) * X ^ 29 * G ^ 3 + (-209259528192 : ℚ⟦X⟧) * X ^ 29 * G ^ 2 + (295529545728 : ℚ⟦X⟧) * X ^ 29 * G + (-81083793408 : ℚ⟦X⟧) * X ^ 29 + (-1168146432 : ℚ⟦X⟧) * X ^ 28 * G ^ 3 + (33563197440 : ℚ⟦X⟧) * X ^ 28 * G ^ 2 + (-28660285440 : ℚ⟦X⟧) * X ^ 28 * G + (6193250304 : ℚ⟦X⟧) * X ^ 28 + (201696768 : ℚ⟦X⟧) * X ^ 27 * G ^ 3 + (-5602735872 : ℚ⟦X⟧) * X ^ 27 * G ^ 2 + (9294700800 : ℚ⟦X⟧) * X ^ 27 * G + (-2739032064 : ℚ⟦X⟧) * X ^ 27 + (640320 : ℚ⟦X⟧) * X ^ 26 * G ^ 3 + (-445940736 : ℚ⟦X⟧) * X ^ 26 * G ^ 2 + (664033920 : ℚ⟦X⟧) * X ^ 26 * G + (-188950464 : ℚ⟦X⟧) * X ^ 26 + (-5301600 : ℚ⟦X⟧) * X ^ 25 * G ^ 3 + (47636280 : ℚ⟦X⟧) * X ^ 25 * G ^ 2 + (-56020800 : ℚ⟦X⟧) * X ^ 25 * G + (14745120 : ℚ⟦X⟧) * X ^ 25 + (144000 : ℚ⟦X⟧) * X ^ 24 * G ^ 3 + (-396000 : ℚ⟦X⟧) * X ^ 24 * G ^ 2 + (351000 : ℚ⟦X⟧) * X ^ 24 * G + (-84000 : ℚ⟦X⟧) * X ^ 24 + (15000 : ℚ⟦X⟧) * X ^ 23 * G ^ 3 + (-60000 : ℚ⟦X⟧) * X ^ 23 * G ^ 2 + (60000 : ℚ⟦X⟧) * X ^ 23 * G + (-15000 : ℚ⟦X⟧) * X ^ 23 := by
    linear_combination ((1 : ℚ⟦X⟧) * X) ^ 2 * (((256 : ℚ⟦X⟧) * X ^ 7 + (512 : ℚ⟦X⟧) * X ^ 6 + (-32 : ℚ⟦X⟧) * X ^ 5 + (-5 : ℚ⟦X⟧) * X ^ 4) * ((1 : ℚ⟦X⟧) * X) * d3 + ((1 : ℚ⟦X⟧) * X) * ((44826624 : ℚ⟦X⟧) * X ^ 24 * G ^ 2 + (39321600 : ℚ⟦X⟧) * X ^ 24 * G + (-11796480 : ℚ⟦X⟧) * X ^ 24 + (144654336 : ℚ⟦X⟧) * X ^ 23 * G ^ 2 + (227672064 : ℚ⟦X⟧) * X ^ 23 * G + (-126222336 : ℚ⟦X⟧) * X ^ 23 + (167067648 : ℚ⟦X⟧) * X ^ 22 * G ^ 2 + (442589184 : ℚ⟦X⟧) * X ^ 22 * G + (-296681472 : ℚ⟦X⟧) * X ^ 22 + (52743168 : ℚ⟦X⟧) * X ^ 21 * G ^ 2 + (283502592 : ℚ⟦X⟧) * X ^ 21 * G + (-221193216 : ℚ⟦X⟧) * X ^ 21 + (-2177856 : ℚ⟦X⟧) * X ^ 20 * G ^ 2 + (-12983808 : ℚ⟦X⟧) * X ^ 20 * G + (2962944 : ℚ⟦X⟧) * X ^ 20 + (-145728 : ℚ⟦X⟧) * X ^ 19 * G ^ 2 + (246432 : ℚ⟦X⟧) * X ^ 19 * G + (-848256 : ℚ⟦X⟧) * X ^ 19 + (7200 : ℚ⟦X⟧) * X ^ 18 * G ^ 2 + (308928 : ℚ⟦X⟧) * X ^ 18 * G + (-231720 : ℚ⟦X⟧) * X ^ 18 + (2250 : ℚ⟦X⟧) * X ^ 17 * G ^ 2 + (-6000 : ℚ⟦X⟧) * X ^ 17 * G + (3000 : ℚ⟦X⟧) * X ^ 17) * hG - ((6912 : ℚ⟦X⟧) * X ^ 7 + (12288 : ℚ⟦X⟧) * X ^ 6 + (-672 : ℚ⟦X⟧) * X ^ 5 + (-90 : ℚ⟦X⟧) * X ^ 4) * h3) + ((2868903936 : ℚ⟦X⟧) * X ^ 32 * G + (5385486336 : ℚ⟦X⟧) * X ^ 32 + (10513022976 : ℚ⟦X⟧) * X ^ 31 * G + (28516024320 : ℚ⟦X⟧) * X ^ 31 + (14742650880 : ℚ⟦X⟧) * X ^ 30 * G + (56741068800 : ℚ⟦X⟧) * X ^ 30 + (8053456896 : ℚ⟦X⟧) * X ^ 29 * G + (46554365952 : ℚ⟦X⟧) * X ^ 29 + (1337425920 : ℚ⟦X⟧) * X ^ 28 * G + (10351841280 : ℚ⟦X⟧) * X ^ 28 + (-70306560 : ℚ⟦X⟧) * X ^ 27 * G + (-795045888 : ℚ⟦X⟧) * X ^ 27 + (-3619584 : ℚ⟦X⟧) * X ^ 26 * G + (26363328 : ℚ⟦X⟧) * X ^ 26 + (345600 : ℚ⟦X⟧) * X ^ 25 * G + (9714624 : ℚ⟦X⟧) * X ^ 25 + (63000 : ℚ⟦X⟧) * X ^ 24 * G + (-24000 : ℚ⟦X⟧) * X ^ 24 + (-11250 : ℚ⟦X⟧) * X ^ 23) * hP
  have key : ((1 : ℚ⟦X⟧) * X) ^ 0 * (((256 : ℚ⟦X⟧) * X ^ 7 + (512 : ℚ⟦X⟧) * X ^ 6 + (-32 : ℚ⟦X⟧) * X ^ 5 + (-5 : ℚ⟦X⟧) * X ^ 4) ^ 4 * ((1 : ℚ⟦X⟧) * X) ^ 9) * (((52437120 : ℚ⟦X⟧) * X ^ 4 + (-218701272 : ℚ⟦X⟧) * X ^ 3 + (-141110640 : ℚ⟦X⟧) * X ^ 2) * G + ((3049528320 : ℚ⟦X⟧) * X ^ 5 + (-6069672768 : ℚ⟦X⟧) * X ^ 4 + (-5365534512 : ℚ⟦X⟧) * X ^ 3 + (49602528 : ℚ⟦X⟧) * X ^ 2) * (d⁄dX ℚ G) + ((7221742080 : ℚ⟦X⟧) * X ^ 6 + (-5256777696 : ℚ⟦X⟧) * X ^ 5 + (-13631578848 : ℚ⟦X⟧) * X ^ 4 + (446760480 : ℚ⟦X⟧) * X ^ 3 + (6146865 : ℚ⟦X⟧) * X ^ 2) * (d⁄dX ℚ (d⁄dX ℚ G)) + ((3454566400 : ℚ⟦X⟧) * X ^ 7 + (888428032 : ℚ⟦X⟧) * X ^ 6 + (-6638757376 : ℚ⟦X⟧) * X ^ 5 + (283783056 : ℚ⟦X⟧) * X ^ 4 + (29125315 : ℚ⟦X⟧) * X ^ 3) * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ G))) + ((386031616 : ℚ⟦X⟧) * X ^ 8 + (425485824 : ℚ⟦X⟧) * X ^ 7 + (-741408768 : ℚ⟦X⟧) * X ^ 6 + (35782496 : ℚ⟦X⟧) * X ^ 5 + (6769090 : ℚ⟦X⟧) * X ^ 4) * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ G)))) - (4061664 * X ^ 3 - 54626922 * X ^ 2)) = 0 := by
    linear_combination ((1 : ℚ⟦X⟧) * X) ^ 0 * ((3049528320 : ℚ⟦X⟧) * X ^ 5 + (-6069672768 : ℚ⟦X⟧) * X ^ 4 + (-5365534512 : ℚ⟦X⟧) * X ^ 3 + (49602528 : ℚ⟦X⟧) * X ^ 2) * ((256 : ℚ⟦X⟧) * X ^ 7 + (512 : ℚ⟦X⟧) * X ^ 6 + (-32 : ℚ⟦X⟧) * X ^ 5 + (-5 : ℚ⟦X⟧) * X ^ 4) ^ 3 * ((1 : ℚ⟦X⟧) * X) ^ 9 * h1 + ((1 : ℚ⟦X⟧) * X) ^ 0 * ((7221742080 : ℚ⟦X⟧) * X ^ 6 + (-5256777696 : ℚ⟦X⟧) * X ^ 5 + (-13631578848 : ℚ⟦X⟧) * X ^ 4 + (446760480 : ℚ⟦X⟧) * X ^ 3 + (6146865 : ℚ⟦X⟧) * X ^ 2) * ((256 : ℚ⟦X⟧) * X ^ 7 + (512 : ℚ⟦X⟧) * X ^ 6 + (-32 : ℚ⟦X⟧) * X ^ 5 + (-5 : ℚ⟦X⟧) * X ^ 4) ^ 2 * ((1 : ℚ⟦X⟧) * X) ^ 6 * h2 + ((1 : ℚ⟦X⟧) * X) ^ 0 * ((3454566400 : ℚ⟦X⟧) * X ^ 7 + (888428032 : ℚ⟦X⟧) * X ^ 6 + (-6638757376 : ℚ⟦X⟧) * X ^ 5 + (283783056 : ℚ⟦X⟧) * X ^ 4 + (29125315 : ℚ⟦X⟧) * X ^ 3) * ((256 : ℚ⟦X⟧) * X ^ 7 + (512 : ℚ⟦X⟧) * X ^ 6 + (-32 : ℚ⟦X⟧) * X ^ 5 + (-5 : ℚ⟦X⟧) * X ^ 4) ^ 1 * ((1 : ℚ⟦X⟧) * X) ^ 3 * h3 + ((1 : ℚ⟦X⟧) * X) ^ 0 * ((386031616 : ℚ⟦X⟧) * X ^ 8 + (425485824 : ℚ⟦X⟧) * X ^ 7 + (-741408768 : ℚ⟦X⟧) * X ^ 6 + (35782496 : ℚ⟦X⟧) * X ^ 5 + (6769090 : ℚ⟦X⟧) * X ^ 4) * ((256 : ℚ⟦X⟧) * X ^ 7 + (512 : ℚ⟦X⟧) * X ^ 6 + (-32 : ℚ⟦X⟧) * X ^ 5 + (-5 : ℚ⟦X⟧) * X ^ 4) ^ 0 * ((1 : ℚ⟦X⟧) * X) ^ 0 * h4 - (0) * hP
  have hq : ((256 : ℚ⟦X⟧) * X ^ 7 + (512 : ℚ⟦X⟧) * X ^ 6 + (-32 : ℚ⟦X⟧) * X ^ 5 + (-5 : ℚ⟦X⟧) * X ^ 4) ≠ 0 := by
    rw [show ((256 : ℚ⟦X⟧) * X ^ 7 + (512 : ℚ⟦X⟧) * X ^ 6 + (-32 : ℚ⟦X⟧) * X ^ 5 + (-5 : ℚ⟦X⟧) * X ^ 4 : PowerSeries ℚ) = X ^ 4 * ((256 : ℚ⟦X⟧) * X ^ 3 + (512 : ℚ⟦X⟧) * X ^ 2 + (-32 : ℚ⟦X⟧) * X + (-5 : ℚ⟦X⟧)) by ring]
    exact mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (ne_of_cc _ (by simp [nC, constantCoeff_C]))
  have hl : ((1 : ℚ⟦X⟧) * X) ≠ 0 := by
    simp [PowerSeries.X_ne_zero]
  have hE := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left
    (mul_ne_zero (pow_ne_zero _ hl) (mul_ne_zero (pow_ne_zero _ hq) (pow_ne_zero _ hl))))
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
  rw [th4, th3, th2]
  linear_combination hE

set_option maxHeartbeats 4000000 in
lemma rel (G : PowerSeries ℚ) (hP : (1 : ℚ⟦X⟧) * X * G ^ 4 + (1 : ℚ⟦X⟧) * G ^ 3 + (-4 : ℚ⟦X⟧) * G ^ 2 + (4 : ℚ⟦X⟧) * G + (-1 : ℚ⟦X⟧) = 0) :
    ((256 : ℚ⟦X⟧) * X ^ 7 + (512 : ℚ⟦X⟧) * X ^ 6 + (-32 : ℚ⟦X⟧) * X ^ 5 + (-5 : ℚ⟦X⟧) * X ^ 4) * d⁄dX ℚ G = (64 : ℚ⟦X⟧) * X ^ 6 * G ^ 3 + (64 : ℚ⟦X⟧) * X ^ 6 * G ^ 2 + (-64 : ℚ⟦X⟧) * X ^ 6 * G + (28 : ℚ⟦X⟧) * X ^ 5 * G ^ 3 + (144 : ℚ⟦X⟧) * X ^ 5 * G ^ 2 + (-352 : ℚ⟦X⟧) * X ^ 5 * G + (112 : ℚ⟦X⟧) * X ^ 5 + (23 : ℚ⟦X⟧) * X ^ 4 * G ^ 2 + (-40 : ℚ⟦X⟧) * X ^ 4 * G + (12 : ℚ⟦X⟧) * X ^ 4 := by
  have hP1 := congrArg (d⁄dX ℚ) hP
  try simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hP1
  try simp only [map_ofNat] at hP1
  try push_cast at hP1
  linear_combination ((448 : ℚ⟦X⟧) * X ^ 7 * G ^ 3 + (192 : ℚ⟦X⟧) * X ^ 7 * G ^ 2 + (64 : ℚ⟦X⟧) * X ^ 7 * G + (-76 : ℚ⟦X⟧) * X ^ 6 * G ^ 3 + (368 : ℚ⟦X⟧) * X ^ 6 * G ^ 2 + (-1696 : ℚ⟦X⟧) * X ^ 6 * G + (976 : ℚ⟦X⟧) * X ^ 6 + (-8 : ℚ⟦X⟧) * X ^ 5 * G ^ 3 + (-83 : ℚ⟦X⟧) * X ^ 5 * G ^ 2 + (216 : ℚ⟦X⟧) * X ^ 5 * G + (-92 : ℚ⟦X⟧) * X ^ 5 + (-8 : ℚ⟦X⟧) * X ^ 4 * G ^ 2 + (25 : ℚ⟦X⟧) * X ^ 4 * G + (-12 : ℚ⟦X⟧) * X ^ 4) * hP1 + (((-1792 : ℚ⟦X⟧) * X ^ 7 * G ^ 2 + (-768 : ℚ⟦X⟧) * X ^ 7 * G + (-256 : ℚ⟦X⟧) * X ^ 7 + (304 : ℚ⟦X⟧) * X ^ 6 * G ^ 2 + (-1024 : ℚ⟦X⟧) * X ^ 6 * G + (3392 : ℚ⟦X⟧) * X ^ 6 + (32 : ℚ⟦X⟧) * X ^ 5 * G ^ 2 + (256 : ℚ⟦X⟧) * X ^ 5 * G + (-336 : ℚ⟦X⟧) * X ^ 5 + (24 : ℚ⟦X⟧) * X ^ 4 * G + (-43 : ℚ⟦X⟧) * X ^ 4) * d⁄dX ℚ G + ((-448 : ℚ⟦X⟧) * X ^ 6 * G ^ 3 + (-192 : ℚ⟦X⟧) * X ^ 6 * G ^ 2 + (-64 : ℚ⟦X⟧) * X ^ 6 * G + (76 : ℚ⟦X⟧) * X ^ 5 * G ^ 3 + (80 : ℚ⟦X⟧) * X ^ 5 * G ^ 2 + (96 : ℚ⟦X⟧) * X ^ 5 * G + (112 : ℚ⟦X⟧) * X ^ 5 + (8 : ℚ⟦X⟧) * X ^ 4 * G ^ 3 + (7 : ℚ⟦X⟧) * X ^ 4 * G ^ 2 + (8 : ℚ⟦X⟧) * X ^ 4 * G + (12 : ℚ⟦X⟧) * X ^ 4)) * hP

end P045743

theorem OMA.solution : type_of% @OMA.S_oeis_a045743.main := by
  intro G _ h n hn
  have hP' : (1 : ℚ⟦X⟧) * X * G ^ 4 + (1 : ℚ⟦X⟧) * G ^ 3 + (-4 : ℚ⟦X⟧) * G ^ 2 + (4 : ℚ⟦X⟧) * G + (-1 : ℚ⟦X⟧) = 0 := by linear_combination h
  have e := congrArg (coeff (n - 1)) (P045743.ode G hP' (P045743.rel G hP'))
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  simp only [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega,
    show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega,
    show k + 6 - 5 = k + 1 by omega] at e ⊢
  norm_num only at e ⊢
  simp only [P045743.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, P045743.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
