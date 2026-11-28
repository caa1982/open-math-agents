import OMAStatements.S_oeis_a007857
import Mathlib

open OMA.S_oeis_a007857

namespace P007857

theorem hu (m : ℕ) : ((3 * (m + 1)).choose (m + 1) : ℚ) * ((2 * m + 2) * (2 * m + 1) * (m + 1)) =
    (3 * m + 3) * (3 * m + 2) * (3 * m + 1) * ((3 * m).choose m : ℚ) := by
  have h1 := Nat.add_one_mul_choose_eq (3 * m) m
  have h2 := Nat.choose_mul_succ_eq (3 * m + 1) (m + 1)
  have h3 := Nat.choose_mul_succ_eq (3 * m + 2) (m + 1)
  rw [show 3 * m + 1 + 1 - (m + 1) = 2 * m + 1 by omega] at h2
  rw [show 3 * m + 2 + 1 - (m + 1) = 2 * m + 2 by omega] at h3
  rw [show 3 * (m + 1) = 3 * m + 2 + 1 by ring]
  have q1 : ((3 * m + 1 : ℕ) : ℚ) * ((3 * m).choose m : ℚ) = ((3 * m + 1).choose (m + 1) : ℚ) * (m + 1) := by
    exact_mod_cast h1
  have q2 : ((3 * m + 1).choose (m + 1) : ℚ) * ((3 * m + 1 + 1 : ℕ) : ℚ) =
      ((3 * m + 1 + 1).choose (m + 1) : ℚ) * ((2 * m + 1 : ℕ) : ℚ) := by
    exact_mod_cast h2
  have q3 : ((3 * m + 2).choose (m + 1) : ℚ) * ((3 * m + 2 + 1 : ℕ) : ℚ) =
      ((3 * m + 2 + 1).choose (m + 1) : ℚ) * ((2 * m + 2 : ℕ) : ℚ) := by
    exact_mod_cast h3
  rw [show 3 * m + 1 + 1 = 3 * m + 2 by ring] at q2
  push_cast at q1 q2 q3
  linear_combination (-(2 * (m : ℚ) + 1) * (m + 1)) * q3 + (-(3 * (m : ℚ) + 3) * (m + 1)) * q2
    + (-(3 * (m : ℚ) + 3) * (3 * m + 2)) * q1

theorem hv (m : ℕ) : ((2 * (m + 1)).choose (m + 1) : ℚ) * (m + 1) =
    2 * (2 * m + 1) * ((2 * m).choose m : ℚ) := by
  have h := Nat.succ_mul_centralBinom_succ m
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
  have q : ((m + 1 : ℕ) : ℚ) * ((2 * (m + 1)).choose (m + 1) : ℚ) =
      ((2 * (2 * m + 1) : ℕ) : ℚ) * ((2 * m).choose m : ℚ) := by
    exact_mod_cast h
  push_cast at q
  linear_combination q

theorem eu (m : ℕ) : ((3 * (m + 1)).choose (m + 1) : ℚ) =
    (3 * m + 3) * (3 * m + 2) * (3 * m + 1) / ((2 * m + 2) * (2 * m + 1) * (m + 1)) *
      ((3 * m).choose m : ℚ) := by
  have := hu m
  rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
  linear_combination this

theorem ev (m : ℕ) : ((2 * (m + 1)).choose (m + 1) : ℚ) =
    2 * (2 * m + 1) / (m + 1) * ((2 * m).choose m : ℚ) := by
  have := hv m
  rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
  linear_combination this

end P007857

theorem OMA.solution : type_of% @OMA.S_oeis_a007857.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  simp only [a, show k + 4 - 1 = k + 3 by omega, show k + 4 - 1 - 1 = k + 2 by omega,
    show k + 4 - 2 - 1 = k + 1 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega, show k + 1 - 1 = k by omega, show k + 2 - 1 = k + 1 by omega, show k + 3 - 1 = k + 2 by omega]
  have e1 := P007857.eu k
  have e2 := P007857.eu (k + 1)
  have e3 := P007857.eu (k + 2)
  have f1 := P007857.ev k
  have f2 := P007857.ev (k + 1)
  have f3 := P007857.ev (k + 2)
  simp only [show k + 1 + 1 = k + 2 by ring, show k + 2 + 1 = k + 3 by ring] at e2 e3 f2 f3
  rw [e3, f3, e2, f2, e1, f1]
  push_cast
  field_simp
  ring
