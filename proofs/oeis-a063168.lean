import OMAStatements.S_oeis_a063168
import Mathlib

open OMA.S_oeis_a063168 PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a063168.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    simp only [a, show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega]
    simp only [show m + 4 ≠ 0 by omega, show m + 4 ≠ 1 by omega, show m + 3 ≠ 0 by omega,
      show m + 3 ≠ 1 by omega, show m + 2 ≠ 0 by omega, show m + 2 ≠ 1 by omega, if_false]
    push_cast
    ring
  · have hp : ((1 - X) ^ 2 : PowerSeries ℚ) = 1 - C (2 : ℚ) * X ^ 1 + X ^ 2 := by
      (try simp only [map_ofNat, map_one, one_mul, pow_one]) <;> ring
    have hR : (X * (X ^ 2 + 22 * X + 7) : PowerSeries ℚ) =
        C (7 : ℚ) * X ^ 1 + C (22 : ℚ) * X ^ 2 + X ^ 3 := by
      (try simp only [map_ofNat, map_one, one_mul, pow_one]) <;> ring
    have hq : ∀ F : PowerSeries ℚ, F * (1 - C (2 : ℚ) * X ^ 1 + X ^ 2) =
        F - C (2 : ℚ) * (F * X ^ 1) + F * X ^ 2 := fun F => by ring
    rw [hp, hR, hq]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk,
      coeff_C_mul_X_pow, coeff_X_pow, coeff_one, coeff_C]
    rcases n with _ | _ | _ | _ | n
    · simp [a]
    · simp [a]
    · norm_num [a]
    · norm_num [a]
    · simp only [show n + 1 + 1 + 1 + 1 - 1 = n + 3 by omega, show n + 1 + 1 + 1 + 1 - 2 = n + 2 by omega]
      simp [a]
      push_cast
      ring
