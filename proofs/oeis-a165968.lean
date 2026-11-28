import OMAStatements.S_oeis_a165968
import Mathlib

open OMA.S_oeis_a165968

namespace P165968

def T (f : ℕ → ℤ) (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * f k

lemma pascal (f : ℕ → ℤ) (n : ℕ) : T f (n + 1) = T f n + T (fun k => f (k + 1)) n := by
  simp only [T]
  rw [Finset.sum_range_succ' _ (n + 1)]
  simp only [Nat.choose_succ_succ, Nat.cast_add, add_mul, Finset.sum_add_distrib]
  have h : ∑ x ∈ Finset.range (n + 1), (n.choose x.succ : ℤ) * f (x + 1) + f 0 =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * f k := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun k => (n.choose k : ℤ) * f k)]
    simp
  rw [← h]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
  ring

lemma T_neg (f : ℕ → ℤ) (n : ℕ) : T (fun k => -f k) n = -T f n := by
  simp [T, Finset.sum_neg_distrib]

lemma T_mul (g : ℕ → ℤ) (n : ℕ) :
    T (fun k : ℕ => (k : ℤ) * g k) (n + 1) = (n + 1) * T (fun k => g (k + 1)) n := by
  simp only [T]
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have h := congrArg (fun x : ℕ => (x : ℤ)) (Nat.add_one_mul_choose_eq n k)
  push_cast at h ⊢
  linear_combination (-g (k + 1)) * h

def S (f : ℕ → ℤ) (n : ℕ) : ℤ := (-1) ^ n * T (fun k => (-1) ^ k * f k) n

lemma S_lin (u v : ℤ) (f g : ℕ → ℤ) (n : ℕ) :
    S (fun k => u * f k + v * g k) n = u * S f n + v * S g n := by
  simp only [S, T, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma L1 (f : ℕ → ℤ) (n : ℕ) : S f (n + 1) + S f n = S (fun k => f (k + 1)) n := by
  simp only [S]
  rw [pascal]
  have : (fun k => (-1 : ℤ) ^ (k + 1) * f (k + 1)) = fun k => -((-1) ^ k * f (k + 1)) := by
    funext k; rw [pow_succ]; ring
  rw [this, T_neg, pow_succ]
  ring

lemma L2 (f : ℕ → ℤ) (n : ℕ) :
    S (fun k : ℕ => (k : ℤ) * f k) (n + 1) = (n + 1) * S (fun k => f (k + 1)) n := by
  simp only [S]
  have : (fun k : ℕ => (-1 : ℤ) ^ k * ((k : ℤ) * f k)) = fun k : ℕ => (k : ℤ) * ((-1) ^ k * f k) := by
    funext k; ring
  rw [this, T_mul]
  have : (fun k => (-1 : ℤ) ^ (k + 1) * f (k + 1)) = fun k => -((-1) ^ k * f (k + 1)) := by
    funext k; rw [pow_succ]; ring
  rw [this, T_neg, pow_succ]
  ring

def d (k : ℕ) : ℤ := (Nat.doubleFactorial (2 * k + 1) : ℤ)

lemma d_succ : (fun k => d (k + 1)) = fun k : ℕ => 2 * ((k : ℤ) * d k) + 3 * d k := by
  funext k
  simp only [d, show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, Nat.doubleFactorial_add_two]
  push_cast; ring

lemma a_eq (m : ℕ) : a (m + 2) = S d m := by
  simp only [a, show ¬ (m + 2 < 2) by omega, if_false, show m + 2 - 1 = m + 1 by omega,
    show m + 2 - 2 = m by omega, S, T, d, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_add, pow_add]; ring

lemma crec (m : ℕ) : S d (m + 2) = 2 * (m + 2) * S d (m + 1) + 2 * (m + 1) * S d m := by
  have h1 := L1 d (m + 1)
  rw [d_succ, S_lin, L2, ← L1] at h1
  push_cast at h1
  linear_combination h1

end P165968

theorem OMA.solution : type_of% @OMA.S_oeis_a165968.main := by
  intro n hn
  rcases Nat.eq_or_lt_of_le hn with h | h
  · subst h
    simp [a, Nat.doubleFactorial, Finset.sum_range_succ]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [show m + 3 + 1 = (m + 2) + 2 by omega, show m + 3 = (m + 1) + 2 by omega,
      show m + 1 + 2 - 1 = m + 2 by omega, P165968.a_eq, P165968.a_eq, P165968.a_eq,
      P165968.crec]
    push_cast
    ring
