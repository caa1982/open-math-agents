import OMAStatements.S_oeis_a059304
import Mathlib

open OMA.S_oeis_a059304

namespace OMA.P_oeis_a059304

open Finset

theorem L1 (n a : ℕ) (ha : a ≤ n) :
    ∑ j ∈ range (n + 1), n.choose j * j.choose a = n.choose a * 2 ^ (n - a) := by
  have hr : n + 1 = a + (n - a + 1) := by omega
  rw [hr, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (fun j hj => by
    rw [Finset.mem_range] at hj
    rw [Nat.choose_eq_zero_of_lt hj, mul_zero])]
  rw [zero_add, ← Nat.sum_range_choose (n - a), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.choose_mul (by omega)]
  congr 2
  omega

end OMA.P_oeis_a059304

open OMA.P_oeis_a059304 Finset in
theorem OMA.solution : type_of% @OMA.S_oeis_a059304.main := by
  intro n
  have hA : a n = 2 ^ n * (2 * n).choose n := by
    unfold a
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega] at h
    rw [← h, sq, show 2 ^ n * ((2 * n).choose n * n.factorial * n.factorial) =
      2 ^ n * (2 * n).choose n * (n.factorial * n.factorial) by ring]
    exact Nat.mul_div_cancel _ (by positivity)
  rw [hA]
  have step1 : ∀ j k : ℕ, n.choose j * n.choose k * (j + k).choose n =
      ∑ ab ∈ antidiagonal n, (n.choose j * j.choose ab.1) * (n.choose k * k.choose ab.2) := by
    intro j k
    rw [Nat.add_choose_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ab _
    ring
  simp_rw [step1]
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_comm), Finset.sum_comm]
  have step2 : ∀ ab ∈ antidiagonal n,
      ∑ j ∈ range (n + 1), ∑ k ∈ range (n + 1),
        (n.choose j * j.choose ab.1) * (n.choose k * k.choose ab.2) =
      2 ^ n * (n.choose ab.1 * n.choose ab.2) := by
    intro ab hab
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    rw [← Finset.sum_mul_sum, L1 n ab.1 (by omega), L1 n ab.2 (by omega)]
    have : 2 ^ n = 2 ^ (n - ab.1) * 2 ^ (n - ab.2) := by
      rw [← pow_add]; congr 1; omega
    rw [this]; ring
  rw [Finset.sum_congr rfl step2, ← Finset.mul_sum, two_mul, Nat.add_choose_eq]
