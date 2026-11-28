import OMAStatements.S_oeis_a192747
import Mathlib

open OMA.S_oeis_a192747 Polynomial

namespace OMA.P_oeis_a192747

def uv : ℕ → ℤ × ℤ
  | 0 => (0, 1)
  | n + 1 => ((uv n).1 + (uv n).2, (uv n).1 + (3 * ((n : ℤ) + 1) + 2))

theorem qmonic : (X ^ 2 - X - 1 : ℤ[X]).Monic := by
  have h : (X ^ 2 - X - 1 : ℤ[X]) = X ^ 2 - (X + 1) := by ring
  rw [h]
  apply Monic.sub_of_left (monic_X_pow 2)
  rw [degree_X_pow]
  compute_degree!

theorem qdeg : (X ^ 2 - X - 1 : ℤ[X]).degree = 2 := by compute_degree!

theorem dv (n : ℕ) : (X ^ 2 - X - 1 : ℤ[X]) ∣ p n - (C (uv n).1 * X + C (uv n).2) := by
  induction n with
  | zero => simp [p, uv]
  | succ n ih =>
    have e : p (n + 1) - (C (uv (n + 1)).1 * X + C (uv (n + 1)).2) =
        X * (p n - (C (uv n).1 * X + C (uv n).2)) + C (uv n).1 * (X ^ 2 - X - 1) := by
      simp only [p, uv, map_add, map_mul, map_ofNat, map_natCast, map_one]
      ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right ih _) (dvd_mul_left _ _)

theorem red (n : ℕ) : p n %ₘ (X ^ 2 - X - 1) = C (uv n).1 * X + C (uv n).2 := by
  rw [modByMonic_eq_of_dvd_sub qmonic (dv n)]
  rw [(modByMonic_eq_self_iff qmonic).mpr]
  rw [qdeg]
  exact lt_of_le_of_lt degree_linear_le (by norm_num)

theorem a_eq (n : ℕ) : a (n + 1) = (uv n).1 := by
  unfold a
  rw [show n + 1 - 1 = n by omega, red, coeff_add, coeff_C_mul_X, coeff_C]
  simp

theorem urec (n : ℕ) : (uv (n + 2)).1 = (uv (n + 1)).1 + (uv n).1 + 3 * n + 5 := by
  simp only [uv]; push_cast; ring

end OMA.P_oeis_a192747

open OMA.P_oeis_a192747 in
theorem OMA.solution : type_of% @OMA.S_oeis_a192747.main := by
  refine ⟨?_, ?_⟩
  · have hF : PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
        ((PowerSeries.X ^ 2 + PowerSeries.X - 1) * (PowerSeries.X - 1) ^ 2) =
        PowerSeries.X * (-1 - 3 * PowerSeries.X + PowerSeries.X ^ 2) := by
      have hp : ((PowerSeries.X ^ 2 + PowerSeries.X - 1) * (PowerSeries.X - 1) ^ 2 : PowerSeries ℚ) =
          PowerSeries.X ^ 4 - PowerSeries.X ^ 3 - PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 2 +
            PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 1 - 1 := by
        simp only [map_ofNat, pow_one]; ring
      have hr : (PowerSeries.X * (-1 - 3 * PowerSeries.X + PowerSeries.X ^ 2) : PowerSeries ℚ) =
          PowerSeries.X ^ 3 - PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 2 - PowerSeries.X ^ 1 := by
        simp only [map_ofNat, pow_one]; ring
      rw [hp, hr]
      have hq : ∀ F : PowerSeries ℚ, F * (PowerSeries.X ^ 4 - PowerSeries.X ^ 3 -
          PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 1 - 1) =
          F * PowerSeries.X ^ 4 - F * PowerSeries.X ^ 3 - PowerSeries.C (2 : ℚ) * (F * PowerSeries.X ^ 2) +
            PowerSeries.C (3 : ℚ) * (F * PowerSeries.X ^ 1) - F := fun F => by ring
      rw [hq]
      ext m
      simp only [map_sub, map_add, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_C_mul,
        PowerSeries.coeff_mk, PowerSeries.coeff_X_pow, a_eq]
      rcases Nat.lt_or_ge m 4 with hm | hm
      · interval_cases m <;> simp [uv] <;> norm_num
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
        simp (disch := omega) only [if_pos, if_neg, PowerSeries.coeff_C]
        rw [show k + 4 - 4 = k by omega, show k + 4 - 3 = k + 1 by omega,
          show k + 4 - 2 = k + 2 by omega, show k + 4 - 1 = k + 3 by omega]
        have r1 := urec k
        have r2 := urec (k + 1)
        have r3 := urec (k + 2)
        have r1' : ((uv (k + 2)).1 : ℚ) = (uv (k + 1)).1 + (uv k).1 + 3 * k + 5 := by exact_mod_cast r1
        have r2' : ((uv (k + 1 + 2)).1 : ℚ) = (uv (k + 1 + 1)).1 + (uv (k + 1)).1 + 3 * ((k + 1 : ℕ) : ℚ) + 5 := by
          exact_mod_cast r2
        have r3' : ((uv (k + 2 + 2)).1 : ℚ) = (uv (k + 2 + 1)).1 + (uv (k + 2)).1 + 3 * ((k + 2 : ℕ) : ℚ) + 5 := by
          exact_mod_cast r3
        simp only [show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega,
          show k + 2 + 2 = k + 4 by omega, show k + 2 + 1 = k + 3 by omega] at r2' r3'
        push_cast at r2' r3'
        linarith
    rw [mul_assoc, hF]; ring
  · intro n
    rw [a_eq, a_eq, red, coeff_add, coeff_C_mul_X, coeff_C]
    simp [uv]
