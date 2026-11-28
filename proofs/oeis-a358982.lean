import OMAStatements.S_oeis_a358982
import Mathlib

open OMA.S_oeis_a358982

theorem OMA.solution : type_of% @OMA.S_oeis_a358982.main := by
  have key : ∀ k : ℕ, digitSum (10 ^ k * 587) = 20 ∧
      digitSum ((10 ^ k * 587) ^ 3) = 17 := by
    intro k
    have e : (10 ^ k * 587) ^ 3 = 10 ^ (3 * k) * 202262003 := by ring
    refine ⟨?_, ?_⟩
    · unfold digitSum
      rw [Nat.digits_base_pow_mul (by norm_num) (by norm_num)]
      norm_num
    · unfold digitSum
      rw [e, Nat.digits_base_pow_mul (by norm_num) (by norm_num)]
      norm_num
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 10 ^ k * 587) ?_ ?_
  · intro a b h
    have h' : 10 ^ a = 10 ^ b := by simpa using h
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 10) h'
  · intro k
    show digitSum ((10 ^ k * 587) ^ 3) < digitSum (10 ^ k * 587)
    rw [(key k).1, (key k).2]
    norm_num
