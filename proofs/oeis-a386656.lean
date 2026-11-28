import OMAStatements.S_oeis_a386656
import Mathlib

open OMA.S_oeis_a386656

namespace P386656

open Finset

def T (p : ℕ → ZMod 6) (n : ℕ) : ZMod 6 := ∑ j ∈ range (n + 1), (n.choose j : ZMod 6) * p j

lemma pascal (f : ℕ → ZMod 6) (n : ℕ) : T f (n + 1) = T f n + T (fun k => f (k + 1)) n := by
  simp only [T]
  rw [Finset.sum_range_succ' _ (n + 1)]
  simp only [Nat.choose_succ_succ, Nat.cast_add, add_mul, Finset.sum_add_distrib]
  have h : ∑ x ∈ Finset.range (n + 1), (n.choose x.succ : ZMod 6) * f (x + 1) + f 0 =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 6) * f k := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun k => (n.choose k : ZMod 6) * f k)]
    simp
  rw [← h]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
  ring

lemma shiftT (p : ℕ → ZMod 6) : ∀ m n, T p (n + m) = T (fun j => T (fun i => p (j + i)) m) n
  | 0, n => by simp [T]
  | m + 1, n => by
    rw [show n + (m + 1) = (n + 1) + m by ring, shiftT p m (n + 1), pascal]
    simp only [T, ← Finset.sum_add_distrib, ← mul_add]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    have := pascal (fun i => p (j + i)) m
    simp only [T] at this
    rw [this, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [show j + 1 + i = j + (i + 1) by ring]
    ring

lemma period (p : ℕ → ZMod 6) (hp : ∀ j, p (j + 6) = p j) (n : ℕ) : T p (n + 9) = T p (n + 3) := by
  rw [shiftT p 9, shiftT p 3]
  simp only [T]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h6 : p (j + 6) = p j := hp j
  have h7 : p (j + 7) = p (j + 1) := hp (j + 1)
  have h8 : p (j + 8) = p (j + 2) := hp (j + 2)
  have h9 : p (j + 9) = p (j + 3) := hp (j + 3)
  rw [h6, h7, h8, h9]
  have z : (6 : ZMod 6) = 0 := by decide
  norm_num [Nat.choose]
  linear_combination (14 * p (j + 0) + 7 * p (j + 1) + 7 * p (j + 2) + 14 * p (j + 3) + 21 * p (j + 4) + 21 * p (j + 5)) * z

lemma x3 : ∀ x : ZMod 6, x ^ 3 = x := by decide

lemma pr (x : ZMod 6) : ∀ e, 1 ≤ e → x ^ e = x ^ ((e + 1) % 2 + 1)
  | 0, h => absurd h (by omega)
  | 1, _ => by norm_num
  | 2, _ => by norm_num
  | e + 3, _ => by
    rw [show e + 3 + 1 = (e + 1 + 1) + 2 by ring, Nat.add_mod_right, ← pr x (e + 1) (by omega),
      pow_add, x3, ← pow_succ]

lemma qq : ∀ e, 1 ≤ e → (3 : ZMod 6) ^ e = 3
  | 0, h => absurd h (by omega)
  | 1, _ => by norm_num
  | e + 2, _ => by rw [pow_succ, qq (e + 1) (by omega)]; decide

def p (j : ℕ) : ZMod 6 := 3 * (3 - (j : ZMod 6)) ^ (j % 2 + 1)

lemma hp (j : ℕ) : p (j + 6) = p j := by
  simp only [p, show (j + 6) % 2 = j % 2 by omega]
  push_cast
  rw [show (6 : ZMod 6) = 0 by decide, add_zero]

def Φ (n : ℕ) : ZMod 6 :=
  3 + (T p n - p 0) + ((1 - (n : ZMod 6)) ^ (n % 2 + 1) - p n) + n * (3 - p 1)

lemma reflT (n : ℕ) : ∑ k ∈ range n, (n.choose k : ZMod 6) * p (n - k) = T p n - p 0 := by
  have h := Finset.sum_range_reflect (fun j => (n.choose j : ZMod 6) * p j) (n + 1)
  simp only [T]
  rw [← h, Finset.sum_range_succ]
  simp only [show n + 1 - 1 - n = 0 by omega, Nat.choose_zero_right, Nat.cast_one, one_mul,
    add_sub_cancel_right]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  rw [show n + 1 - 1 - k = n - k by omega, Nat.choose_symm (by omega)]

lemma formula (n : ℕ) (hn : 2 ≤ n) : ((a n : ℤ) : ZMod 6) = Φ n := by
  unfold a Φ
  push_cast
  rw [qq (n ^ 2) (Nat.one_le_pow _ _ (by omega))]
  have hs : ∀ k ∈ range n, (n.choose k : ZMod 6) * 3 ^ (k * (k + 1)) *
      (3 ^ k - ((n - k : ℕ) : ZMod 6)) ^ (n - k - 1) =
      (n.choose k : ZMod 6) * p (n - k) +
      ((if k = 0 then (1 - (n : ZMod 6)) ^ (n % 2 + 1) - p n else 0) +
        (if k = n - 1 then (n : ZMod 6) * (3 - p 1) else 0)) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, zero_mul, pow_zero, Nat.sub_zero,
        if_true, show (0 = n - 1) = False by simp; omega, if_false, add_zero]
      rw [pr _ (n - 1) (by omega), show (n - 1 + 1) % 2 = n % 2 by omega]
      ring
    · rcases eq_or_ne k (n - 1) with h1 | h1
      · subst h1
        rw [show n - (n - 1) = 1 by omega, Nat.sub_self, pow_zero, mul_one,
          qq _ (Nat.one_le_iff_ne_zero.mpr (by positivity)), Nat.choose_symm_of_eq_add (show n = (n - 1) + 1 by omega),
          Nat.choose_one_right]
        simp only [show n - 1 ≠ 0 by omega, if_false, if_true, zero_add]
        ring
      · simp only [show k ≠ 0 by omega, h1, if_false, add_zero]
        rw [qq _ (Nat.one_le_iff_ne_zero.mpr (by positivity)), qq _ h0, p,
          pr _ (n - k - 1) (by omega), show (n - k - 1 + 1) % 2 = (n - k) % 2 by omega]
        ring
  rw [Finset.sum_congr rfl hs, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq', reflT]
  simp only [Finset.mem_range, show 0 < n by omega, show n - 1 < n by omega, if_true]
  ring

lemma Φp (n : ℕ) : Φ (n + 9) = Φ (n + 3) := by
  unfold Φ
  rw [period p hp n, show n + 9 = (n + 3) + 6 by ring, hp, show (n + 3 + 6) % 2 = (n + 3) % 2 by omega]
  push_cast
  rw [show (6 : ZMod 6) = 0 by decide, add_zero]

lemma Φr : ∀ n, 6 ≤ n → Φ n = Φ (n % 6 + 6)
  | n, h => by
    rcases Nat.lt_or_ge n 12 with h1 | h1
    · rw [show n % 6 + 6 = n by omega]
    · have := Φp (n - 9)
      rw [show n - 9 + 9 = n by omega, show n - 9 + 3 = n - 6 by omega] at this
      rw [this, Φr (n - 6) (by omega), show (n - 6) % 6 = n % 6 by omega]

end P386656

theorem OMA.solution : type_of% @OMA.S_oeis_a386656.main := by
  intro n hn
  apply (ZMod.intCast_eq_intCast_iff _ _ 6).mp
  rw [P386656.formula n (by omega), P386656.Φr n hn]
  have ht : targetMod6 n = targetMod6 (n % 6 + 6) := by
    unfold targetMod6; rw [show (n % 6 + 6) % 6 = n % 6 by omega]
  rw [ht]
  have hr : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize n % 6 = r at hr ⊢
  interval_cases r <;> decide
