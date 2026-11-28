import OMAStatements.S_oeis_a164704
import Mathlib

open OMA.S_oeis_a164704

theorem OMA.solution : type_of% @OMA.S_oeis_a164704.main := by
  rintro n ⟨-, ⟨m, q, r, -, -, hn, hsq⟩, -⟩
  have h10 : 10 ^ m % 9 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h1 : n ^ 2 % 9 = n % 9 := by
    rw [hsq, hn, Nat.add_mod, Nat.mul_mod, h10, mul_one, Nat.mod_mod, ← Nat.add_mod]
  rw [Nat.pow_mod] at h1
  have ht : n % 9 < 9 := Nat.mod_lt _ (by norm_num)
  generalize n % 9 = t at h1 ht ⊢
  interval_cases t <;> simp_all
