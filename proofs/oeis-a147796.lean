import OMAStatements.S_oeis_a147796
import Mathlib

open OMA.S_oeis_a147796 PowerSeries

theorem P147796.hc (m : ℕ) : (m.choose 3 : ℚ) = (m : ℚ) * ((m : ℚ) - 1) * ((m : ℚ) - 2) / 6 := by
  rcases Nat.lt_or_ge m 3 with h | h
  · interval_cases m <;> norm_num [Nat.choose]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
    have e := Nat.descFactorial_eq_factorial_mul_choose (k + 3) 3
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial, Nat.succ_eq_add_one] at e
    have e2 : (((k + 3 - 2) * ((k + 3 - 1) * ((k + 3 - 0) * 1)) : ℕ) : ℚ) =
        (((0 + 1) * ((1 + 1) * ((2 + 1) * 1)) * (k + 3).choose 3 : ℕ) : ℚ) := by rw [e]
    rw [show k + 3 - 2 = k + 1 by omega, show k + 3 - 1 = k + 2 by omega, show k + 3 - 0 = k + 3 by omega] at e2
    push_cast at e2 ⊢
    linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a147796.main := by
  refine ⟨?_, ?_⟩
  · have hL : (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - X) ^ 7 : PowerSeries ℚ) = PowerSeries.mk (fun n => (a n : ℚ)) - C (7 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1) + C (21 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2) - C (35 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3) + C (35 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 4) - C (21 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 5) + C (7 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 6) - (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 7) := by
      (try simp only [map_ofNat, map_one, map_neg, one_mul, pow_one]) <;> ring
    have hR : (2 * X ^ 3 * (3 + 55 * X + X ^ 2 + X ^ 3) : PowerSeries ℚ) = C (6 : ℚ) * X ^ 3 + C (110 : ℚ) * X ^ 4 + C (2 : ℚ) * X ^ 5 + C (2 : ℚ) * X ^ 6 := by
      (try simp only [map_ofNat, map_one, map_neg, one_mul, pow_one]) <;> ring
    rw [hL, hR]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk,
      coeff_C_mul_X_pow, coeff_X_pow, coeff_one, coeff_C]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | n
    · norm_num [a, Nat.choose]
    · norm_num [a, Nat.choose]
    · norm_num [a, Nat.choose]
    · norm_num [a, Nat.choose]
    · norm_num [a, Nat.choose]
    · norm_num [a, Nat.choose]
    · norm_num [a, Nat.choose]
    · norm_num [a, Nat.choose]
    · simp only [show n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 8 by omega]
      simp only [show n + 8 - 1 = n + 7 by omega, show n + 8 - 2 = n + 6 by omega, show n + 8 - 3 = n + 5 by omega, show n + 8 - 4 = n + 4 by omega, show n + 8 - 5 = n + 3 by omega, show n + 8 - 6 = n + 2 by omega, show n + 8 - 7 = n + 1 by omega]
      try simp only [show (n + 8 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 8 = 1) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 8 = 2) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 8 = 3) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 8 = 4) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 8 = 5) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 8 = 6) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 8 = 7) = False by simp only [eq_iff_iff, iff_false]; omega, if_false]
      simp only [a]
      push_cast
      simp only [P147796.hc]
      push_cast
      ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega, show m + 7 - 3 = m + 4 by omega,
      show m + 7 - 4 = m + 3 by omega, show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega,
      show m + 7 - 7 = m by omega]
    have key : ((a (m + 7) : ℤ) : ℚ) = ((7 * a (m + 6) - 21 * a (m + 5) + 35 * a (m + 4) - 35 * a (m + 3) +
        21 * a (m + 2) - 7 * a (m + 1) + a m : ℤ) : ℚ) := by
      simp only [a]
      push_cast
      simp only [P147796.hc]
      push_cast
      ring
    exact_mod_cast key
