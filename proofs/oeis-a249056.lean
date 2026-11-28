import OMAStatements.S_oeis_a249056
import Mathlib

open OMA.S_oeis_a249056

namespace P249056

theorem prodN : ∀ m r : ℕ, ((∏ i ∈ Finset.range m, ((m + r + 1 - (i + 1)) * (m + r + 1 + (i + 1))) : ℕ) : ℚ) =
    ((m + r).factorial : ℚ) / (r.factorial : ℚ) * ((2 * m + r + 1).factorial : ℚ) / ((m + r + 1).factorial : ℚ) := by
  intro m
  induction m with
  | zero => intro r; simp; field_simp
  | succ m ih =>
    intro r
    rw [Finset.prod_range_succ, show m + 1 + r + 1 = m + (r + 1) + 1 by ring, Nat.cast_mul, ih (r + 1),
      show m + (r + 1) + 1 - (m + 1) = r + 1 by omega]
    rw [show m + (r + 1) = m + r + 1 by ring, show 2 * m + (r + 1) + 1 = 2 * m + r + 2 by ring,
      show m + r + 1 + 1 = m + r + 2 by ring, show m + 1 + r = m + r + 1 by ring,
      show 2 * (m + 1) + r + 1 = (2 * m + r + 2) + 1 by ring]
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring

theorem A1 (t : ℕ) : (a (2 * t + 1) : ℚ) =
    ((t + (3 * t + 1)).factorial : ℚ) / ((3 * t + 1).factorial : ℚ) * ((2 * (t) + (3 * t + 1) + 1).factorial : ℚ) / ((t + (3 * t + 1) + 1).factorial : ℚ) := by
  unfold a
  rw [show (2 * t + 1) / 2 = t by omega, show 2 * (2 * t + 1) = t + (3 * t + 1) + 1 by omega]
  exact prodN _ _

theorem A2 (t : ℕ) : (a (2 * t + 2) : ℚ) =
    ((t + 1 + (3 * t + 2)).factorial : ℚ) / ((3 * t + 2).factorial : ℚ) * ((2 * (t + 1) + (3 * t + 2) + 1).factorial : ℚ) / ((t + 1 + (3 * t + 2) + 1).factorial : ℚ) := by
  unfold a
  rw [show (2 * t + 2) / 2 = t + 1 by omega, show 2 * (2 * t + 2) = t + 1 + (3 * t + 2) + 1 by omega]
  exact prodN _ _

theorem A3 (t : ℕ) : (a (2 * t + 3) : ℚ) =
    ((t + 1 + (3 * t + 4)).factorial : ℚ) / ((3 * t + 4).factorial : ℚ) * ((2 * (t + 1) + (3 * t + 4) + 1).factorial : ℚ) / ((t + 1 + (3 * t + 4) + 1).factorial : ℚ) := by
  unfold a
  rw [show (2 * t + 3) / 2 = t + 1 by omega, show 2 * (2 * t + 3) = t + 1 + (3 * t + 4) + 1 by omega]
  exact prodN _ _

theorem A4 (t : ℕ) : (a (2 * t + 4) : ℚ) =
    ((t + 2 + (3 * t + 5)).factorial : ℚ) / ((3 * t + 5).factorial : ℚ) * ((2 * (t + 2) + (3 * t + 5) + 1).factorial : ℚ) / ((t + 2 + (3 * t + 5) + 1).factorial : ℚ) := by
  unfold a
  rw [show (2 * t + 4) / 2 = t + 2 by omega, show 2 * (2 * t + 4) = t + 2 + (3 * t + 5) + 1 by omega]
  exact prodN _ _

theorem A5 (t : ℕ) : (a (2 * t + 5) : ℚ) =
    ((t + 2 + (3 * t + 7)).factorial : ℚ) / ((3 * t + 7).factorial : ℚ) * ((2 * (t + 2) + (3 * t + 7) + 1).factorial : ℚ) / ((t + 2 + (3 * t + 7) + 1).factorial : ℚ) := by
  unfold a
  rw [show (2 * t + 5) / 2 = t + 2 by omega, show 2 * (2 * t + 5) = t + 2 + (3 * t + 7) + 1 by omega]
  exact prodN _ _

end P249056

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a249056.main := by
  intro k
  simp only
  rcases Nat.even_or_odd k with ⟨t, ht⟩ | ⟨t, ht⟩
  · rcases t with _ | t
    · subst ht
      norm_num [a, c0, c1, c2, c3, Finset.prod_range_succ]
    · rw [show k = 2 * t + 2 by omega, show 2 * t + 2 + 3 = 2 * t + 5 by ring,
        show 2 * t + 2 + 2 = 2 * t + 4 by ring, show 2 * t + 2 + 1 = 2 * t + 3 by ring,
        P249056.A5, P249056.A4, P249056.A3, show 2 * t + 2 = 2 * t + 2 by rfl, P249056.A2]
      simp only [show t + 2 + (3 * t + 7) = 4 * t + 9 by ring, show 2 * (t + 2) + (3 * t + 7) + 1 = 5 * t + 12 by ring,
        show t + 2 + (3 * t + 7) + 1 = 4 * t + 10 by ring, show t + 2 + (3 * t + 5) = 4 * t + 7 by ring,
        show 2 * (t + 2) + (3 * t + 5) + 1 = 5 * t + 10 by ring, show t + 2 + (3 * t + 5) + 1 = 4 * t + 8 by ring,
        show t + 1 + (3 * t + 4) = 4 * t + 5 by ring, show 2 * (t + 1) + (3 * t + 4) + 1 = 5 * t + 7 by ring,
        show t + 1 + (3 * t + 4) + 1 = 4 * t + 6 by ring, show t + 1 + (3 * t + 2) = 4 * t + 3 by ring,
        show 2 * (t + 1) + (3 * t + 2) + 1 = 5 * t + 5 by ring, show t + 1 + (3 * t + 2) + 1 = 4 * t + 4 by ring,
        Nat.factorial_succ]
      unfold c0 c1 c2 c3
      push_cast
      field_simp
      ring
  · rw [show k = 2 * t + 1 by omega, show 2 * t + 1 + 3 = 2 * t + 4 by ring,
      show 2 * t + 1 + 2 = 2 * t + 3 by ring, show 2 * t + 1 + 1 = 2 * t + 2 by ring,
      P249056.A4, P249056.A3, P249056.A2, P249056.A1]
    simp only [show t + 2 + (3 * t + 5) = 4 * t + 7 by ring,
      show 2 * (t + 2) + (3 * t + 5) + 1 = 5 * t + 10 by ring, show t + 2 + (3 * t + 5) + 1 = 4 * t + 8 by ring,
      show t + 1 + (3 * t + 4) = 4 * t + 5 by ring, show 2 * (t + 1) + (3 * t + 4) + 1 = 5 * t + 7 by ring,
      show t + 1 + (3 * t + 4) + 1 = 4 * t + 6 by ring, show t + 1 + (3 * t + 2) = 4 * t + 3 by ring,
      show 2 * (t + 1) + (3 * t + 2) + 1 = 5 * t + 5 by ring, show t + 1 + (3 * t + 2) + 1 = 4 * t + 4 by ring,
      show t + (3 * t + 1) = 4 * t + 1 by ring, show 2 * t + (3 * t + 1) + 1 = 5 * t + 2 by ring,
      show t + (3 * t + 1) + 1 = 4 * t + 2 by ring, Nat.factorial_succ]
    unfold c0 c1 c2 c3
    push_cast
    field_simp
    ring
