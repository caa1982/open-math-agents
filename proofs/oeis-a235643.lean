import OMAStatements.S_oeis_a235643
import Mathlib

open OMA.S_oeis_a235643

namespace OMA.P_oeis_a235643

theorem sum_step (a : ℕ → ℕ) (n : ℕ) (hn : 2 ≤ n) :
    ∑ i ∈ Finset.Icc 3 (n + 1), 2 * 3 ^ (n + 1 - i + 1) * a (i - 3) =
      3 * ∑ i ∈ Finset.Icc 3 n, 2 * 3 ^ (n - i + 1) * a (i - 3) + 6 * a (n - 2) := by
  rw [Finset.sum_Icc_succ_top (by omega), Finset.mul_sum]
  rw [show n + 1 - (n + 1) + 1 = 1 by omega, show n + 1 - 3 = n - 2 by omega]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [show n + 1 - i + 1 = (n - i + 1) + 1 by omega, pow_succ]
    ring

end OMA.P_oeis_a235643

open OMA.P_oeis_a235643 in
theorem OMA.solution : type_of% @OMA.S_oeis_a235643.main := by
  intro a h0 h1 hrec
  have h2 : a 2 = 68 := by
    rw [hrec 2 le_rfl, h1, h0]
    simp
  have rec3 : ∀ n : ℕ, 3 ≤ n → (a n : ℤ) = 6 * (a (n - 1) : ℤ) - 7 * (a (n - 2) : ℤ) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have e1 := hrec (m + 1) (by omega)
    have e0 := hrec m (by omega)
    rw [show m + 1 - 1 = m by omega, show m + 1 - 2 = m - 1 by omega, sum_step a m (by omega)] at e1
    rw [show m + 1 - 1 = m by omega, show m + 1 - 2 = m - 1 by omega]
    have e0' : (a m : ℤ) = 3 * a (m - 1) + 2 * a (m - 2) +
        ((∑ i ∈ Finset.Icc 3 m, 2 * 3 ^ (m - i + 1) * a (i - 3) : ℕ) : ℤ) := by
      exact_mod_cast e0
    have e1' : (a (m + 1) : ℤ) = 3 * a m + 2 * a (m - 1) +
        (3 * ((∑ i ∈ Finset.Icc 3 m, 2 * 3 ^ (m - i + 1) * a (i - 3) : ℕ) : ℤ) + 6 * a (m - 2)) := by
      exact_mod_cast e1
    linear_combination e1' - 3 * e0'
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have closed : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = Real.sqrt 2 * ((3 - Real.sqrt 2) ^ n * (-1 + Real.sqrt 2) +
      (1 + Real.sqrt 2) * (3 + Real.sqrt 2) ^ n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      rcases (by omega : n = 1 ∨ n = 2 ∨ 3 ≤ n) with rfl | rfl | h3
      · rw [h1]; push_cast
        linear_combination (-8 : ℝ) * hs
      · rw [h2]; push_cast
        linear_combination (-(2 * Real.sqrt 2 ^ 2 + 34)) * hs
      · have r := rec3 n h3
        have r' : (a n : ℝ) = 6 * (a (n - 1) : ℝ) - 7 * (a (n - 2) : ℝ) := by exact_mod_cast r
        rw [r', ih (n - 1) (by omega) (by omega), ih (n - 2) (by omega) (by omega)]
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
        rw [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
        rw [pow_succ (3 - Real.sqrt 2) (k + 1), pow_succ (3 - Real.sqrt 2) k,
          pow_succ (3 + Real.sqrt 2) (k + 1), pow_succ (3 + Real.sqrt 2) k]
        linear_combination (-(Real.sqrt 2 * ((-1 + Real.sqrt 2) * (3 - Real.sqrt 2) ^ k +
          (1 + Real.sqrt 2) * (3 + Real.sqrt 2) ^ k))) * hs
  refine ⟨closed, rec3, ?_⟩
  have hp : (7 * PowerSeries.X ^ 2 - 6 * PowerSeries.X + 1 : PowerSeries ℚ) =
      PowerSeries.C (7 : ℚ) * PowerSeries.X ^ 2 - PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 1 + 1 := by
    simp only [map_ofNat, pow_one]
  have hr : (4 * PowerSeries.X * (-7 * PowerSeries.X + 4) : PowerSeries ℚ) =
      PowerSeries.C (16 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (28 : ℚ) * PowerSeries.X ^ 2 := by
    simp only [map_ofNat, pow_one]; ring
  rw [hp, hr]
  have hq : ∀ F : PowerSeries ℚ, F * (PowerSeries.C (7 : ℚ) * PowerSeries.X ^ 2 -
      PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 1 + 1) =
      PowerSeries.C (7 : ℚ) * (F * PowerSeries.X ^ 2) - PowerSeries.C (6 : ℚ) * (F * PowerSeries.X ^ 1) + F :=
    fun F => by ring
  rw [hq]
  ext n
  simp only [map_sub, map_add, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
    PowerSeries.coeff_C_mul_X_pow]
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> simp [h1, h2] <;> norm_num
  · have h := rec3 n hn
    have h' : (a n : ℚ) = 6 * (a (n - 1) : ℚ) - 7 * (a (n - 2) : ℚ) := by exact_mod_cast h
    simp (disch := omega) only [if_pos, if_neg, PowerSeries.coeff_C]
    linarith
