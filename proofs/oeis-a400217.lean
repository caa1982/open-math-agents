import OMAStatements.S_oeis_a400217
import Mathlib

open OMA.S_oeis_a400217
open PowerSeries

namespace P400217

theorem a_ge (m : ℕ) : a (m + 3) = (3 : ℚ) ^ m * v (m + 3) 1 := by
  unfold a
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [if_neg (by omega), show m + 3 - 3 = m by omega]

theorem rec (m : ℕ) : a (m + 7) = 2 * a (m + 6) + 6 * a (m + 5) + 18 * a (m + 4) - 81 * a (m + 3) := by
  rw [show m + 7 = (m + 4) + 3 by omega, show m + 6 = (m + 3) + 3 by omega,
    show m + 5 = (m + 2) + 3 by omega, show m + 4 = (m + 1) + 3 by omega, a_ge, a_ge, a_ge, a_ge, a_ge]
  have hv : v (m + 4 + 3) 1 = 2 / 3 * (v (m + 1 + 3) 1 + v (m + 2 + 3) 1 + v (m + 3 + 3) 1) - v (m + 3) 1 := by
    rw [show m + 4 + 3 = (m + 3) + 4 by omega, show m + 1 + 3 = (m + 3) + 1 by omega,
      show m + 2 + 3 = (m + 3) + 2 by omega, show m + 3 + 3 = (m + 3) + 3 by omega]
    rfl
  rw [hv]
  ring

theorem vals : a 0 = -1 ∧ a 1 = 1 ∧ a 2 = -1 ∧ a 3 = 1 ∧ a 4 = 5 ∧ a 5 = 1 ∧ a 6 = 77 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [a, v]

end P400217

theorem OMA.solution : type_of% @OMA.S_oeis_a400217.main := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6⟩ := P400217.vals
  have hp : ((3 * X - 1) ^ 2 * (9 * X ^ 2 + 4 * X + 1) : PowerSeries ℚ) =
      C 81 * X ^ 4 - C 18 * X ^ 3 - C 6 * X ^ 2 - C 2 * X + 1 := by simp only [map_ofNat]; ring
  have hq : ∀ F : PowerSeries ℚ, F * (C 81 * X ^ 4 - C 18 * X ^ 3 - C 6 * X ^ 2 - C 2 * X + 1) =
      C 81 * (F * X ^ 4) - C 18 * (F * X ^ 3) - C 6 * (F * X ^ 2) - C 2 * (F * X ^ 1) + F :=
    fun F => by ring
  have hr : (-54 * X ^ 6 + 84 * X ^ 5 - 90 * X ^ 4 + 15 * X ^ 3 + 3 * X ^ 2 + 3 * X - 1 : PowerSeries ℚ) =
      C (-54) * X ^ 6 + C 84 * X ^ 5 - C 90 * X ^ 4 + C 15 * X ^ 3 + C 3 * X ^ 2 + C 3 * X ^ 1 - 1 := by
    simp only [map_ofNat, map_neg, pow_one]
  rw [hp, hq, hr]
  clear hp hq hr
  ext n
  simp only [map_sub, map_add, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_C_mul_X_pow,
    coeff_X_pow, coeff_one, coeff_C]
  rcases Nat.lt_or_ge n 7 with hn | hn
  · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5, v6] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    have h := P400217.rec m
    simp (disch := omega) only [if_pos, if_neg]
    rw [show m + 7 - 4 = m + 3 by omega, show m + 7 - 3 = m + 4 by omega,
      show m + 7 - 2 = m + 5 by omega, show m + 7 - 1 = m + 6 by omega]
    linarith
