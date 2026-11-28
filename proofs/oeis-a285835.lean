import OMAStatements.S_oeis_a285835
import Mathlib

open OMA.S_oeis_a285835 PowerSeries

set_option maxRecDepth 10000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a285835.main) := by
  intro h
  have hg := h.1
  have hr := h.2.2.2
  have hp : (((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 - 2 * X ^ 2)) : PowerSeries ℤ) = 1 - C (7 : ℤ) * X ^ 2 + C (14 : ℤ) * X ^ 4 - C (8 : ℤ) * X ^ 6 := by
    (try simp only [map_ofNat, map_one, one_mul, pow_one]) <;> ring
  have hR : (1 + 3 * X - X ^ 2 - 6 * X ^ 3 - 16 * X ^ 4 + 16 * X ^ 6 + 192 * X ^ 8 - 448 * X ^ 10 + 256 * X ^ 12 : PowerSeries ℤ) = 1 + C (3 : ℤ) * X ^ 1 - X ^ 2 - C (6 : ℤ) * X ^ 3 - C (16 : ℤ) * X ^ 4 + C (16 : ℤ) * X ^ 6 + C (192 : ℤ) * X ^ 8 - C (448 : ℤ) * X ^ 10 + C (256 : ℤ) * X ^ 12 := by
    (try simp only [map_ofNat, map_one, one_mul, pow_one]) <;> ring
  have hq : ∀ F : PowerSeries ℤ, F * (1 - C (7 : ℤ) * X ^ 2 + C (14 : ℤ) * X ^ 4 - C (8 : ℤ) * X ^ 6) = F - C (7 : ℤ) * (F * X ^ 2) + C (14 : ℤ) * (F * X ^ 4) - C (8 : ℤ) * (F * X ^ 6) := fun F => by ring
  rw [hp, hR, hq] at hg
  have e := congrArg (coeff 8) hg
  simp only [map_sub, map_add, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_C_mul_X_pow,
    coeff_X_pow, coeff_one, coeff_C] at e
  simp (disch := decide) only [if_pos, if_neg, Nat.reduceSub, Int.reduceMul, Int.reduceAdd, Int.reduceNeg, mul_zero, sub_zero, add_zero, zero_add, mul_one] at e
  have r := hr 8 (by norm_num)
  simp only [Nat.reduceSub] at r
  linarith
