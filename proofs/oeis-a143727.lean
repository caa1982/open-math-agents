import OMAStatements.S_oeis_a143727
import Mathlib

open OMA.S_oeis_a143727

theorem OMA.solution : type_of% @OMA.S_oeis_a143727.main := by
  intro n ⟨h1, h2, h3, h4, h5, h6⟩
  have key : ∀ q : ℕ, q.Prime → 6 ≤ q → q % 3 ≠ 0 ∧ q % 5 ≠ 0 := by
    intro q hq h6
    constructor
    · intro h
      have := (Nat.Prime.eq_one_or_self_of_dvd hq 3 (Nat.dvd_of_mod_eq_zero h))
      omega
    · intro h
      have := (Nat.Prime.eq_one_or_self_of_dvd hq 5 (Nat.dvd_of_mod_eq_zero h))
      omega
  rcases Nat.lt_or_ge n 20 with hn | hn
  · revert h1 h2 h3 h4 h5 h6
    interval_cases n <;> norm_num
  · have k1 := key _ h1 (by omega)
    have k2 := key _ h2 (by omega)
    have k3 := key _ h3 (by omega)
    have k4 := key _ h4 (by omega)
    have k5 := key _ h5 (by omega)
    have k6 := key _ h6 (by omega)
    omega
