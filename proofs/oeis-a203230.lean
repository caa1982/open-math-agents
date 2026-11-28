import OMAStatements.S_oeis_a203230
import Mathlib

open OMA.S_oeis_a203230
open PowerSeries

namespace P203230

theorem esymm_cons (y : ℤ) (s : Multiset ℤ) (k : ℕ) :
    (y ::ₘ s).esymm (k + 1) = y * s.esymm k + s.esymm (k + 1) := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_def, Multiset.prod_cons, Multiset.sum_map_mul_left]
  ring

theorem esymm_big (s : Multiset ℤ) (k : ℕ) (h : Multiset.card s < k) : s.esymm k = 0 := by
  simp [Multiset.esymm, Multiset.powersetCard_eq_empty k h]

noncomputable def P (n : ℕ) : ℤ := ((Multiset.range n).map x).esymm n

theorem estep (n : ℕ) (hn : 1 ≤ n) : a (n + 1) = x n * a n + P n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  unfold a P
  rw [Multiset.range_succ, Multiset.map_cons, show k + 1 + 1 - 1 = k + 1 by omega,
    show k + 1 - 1 = k by omega, esymm_cons]

theorem pstep (n : ℕ) : P (n + 1) = x n * P n := by
  unfold P
  rw [Multiset.range_succ, Multiset.map_cons, esymm_cons,
    esymm_big _ (n + 1) (by simp)]
  ring

theorem rec (m : ℕ) (hm : 1 ≤ m) : a (m + 4) = 6 * a (m + 2) - 9 * a m := by
  have hr : m % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : m % 2 = 0 ∨ m % 2 = 1) with hr0 | hr1
  · -- r = 0
    have x0 : x (m) = 1 := by simp only [x, show (m) % 2 = 0 by omega]; norm_num
    have h0 := estep (m) (by omega)
    have q0 := pstep (m)
    have E1 : a (m + 1) = 1 * a m + 1 * P m := by rw [h0, x0]; ring
    have Q1 : P (m + 1) = 1 * P m := by rw [q0, x0]
    have x1 : x (m + 1) = 3 := by simp only [x, show (m + 1) % 2 = 1 by omega]; norm_num
    have h1 := estep (m + 1) (by omega)
    have q1 := pstep (m + 1)
    have E2 : a (m + 2) = 3 * a m + 4 * P m := by rw [show m + 2 = m + 1 + 1 by omega, h1, x1]; linear_combination 3 * E1 + Q1
    have Q2 : P (m + 2) = 3 * P m := by rw [show m + 2 = m + 1 + 1 by omega, q1, x1]; linear_combination 3 * Q1
    have x2 : x (m + 2) = 1 := by simp only [x, show (m + 2) % 2 = 0 by omega]; norm_num
    have h2 := estep (m + 2) (by omega)
    have q2 := pstep (m + 2)
    have E3 : a (m + 3) = 3 * a m + 7 * P m := by rw [show m + 3 = m + 2 + 1 by omega, h2, x2]; linear_combination 1 * E2 + Q2
    have Q3 : P (m + 3) = 3 * P m := by rw [show m + 3 = m + 2 + 1 by omega, q2, x2]; linear_combination 1 * Q2
    have x3 : x (m + 3) = 3 := by simp only [x, show (m + 3) % 2 = 1 by omega]; norm_num
    have h3 := estep (m + 3) (by omega)
    have q3 := pstep (m + 3)
    have E4 : a (m + 4) = 9 * a m + 24 * P m := by rw [show m + 4 = m + 3 + 1 by omega, h3, x3]; linear_combination 3 * E3 + Q3
    have Q4 : P (m + 4) = 9 * P m := by rw [show m + 4 = m + 3 + 1 by omega, q3, x3]; linear_combination 3 * Q3
    linear_combination E4 - 6 * E2
  · -- r = 1
    have x0 : x (m) = 3 := by simp only [x, show (m) % 2 = 1 by omega]; norm_num
    have h0 := estep (m) (by omega)
    have q0 := pstep (m)
    have E1 : a (m + 1) = 3 * a m + 1 * P m := by rw [h0, x0]; ring
    have Q1 : P (m + 1) = 3 * P m := by rw [q0, x0]
    have x1 : x (m + 1) = 1 := by simp only [x, show (m + 1) % 2 = 0 by omega]; norm_num
    have h1 := estep (m + 1) (by omega)
    have q1 := pstep (m + 1)
    have E2 : a (m + 2) = 3 * a m + 4 * P m := by rw [show m + 2 = m + 1 + 1 by omega, h1, x1]; linear_combination 1 * E1 + Q1
    have Q2 : P (m + 2) = 3 * P m := by rw [show m + 2 = m + 1 + 1 by omega, q1, x1]; linear_combination 1 * Q1
    have x2 : x (m + 2) = 3 := by simp only [x, show (m + 2) % 2 = 1 by omega]; norm_num
    have h2 := estep (m + 2) (by omega)
    have q2 := pstep (m + 2)
    have E3 : a (m + 3) = 9 * a m + 15 * P m := by rw [show m + 3 = m + 2 + 1 by omega, h2, x2]; linear_combination 3 * E2 + Q2
    have Q3 : P (m + 3) = 9 * P m := by rw [show m + 3 = m + 2 + 1 by omega, q2, x2]; linear_combination 3 * Q2
    have x3 : x (m + 3) = 1 := by simp only [x, show (m + 3) % 2 = 0 by omega]; norm_num
    have h3 := estep (m + 3) (by omega)
    have q3 := pstep (m + 3)
    have E4 : a (m + 4) = 9 * a m + 24 * P m := by rw [show m + 4 = m + 3 + 1 by omega, h3, x3]; linear_combination 1 * E3 + Q3
    have Q4 : P (m + 4) = 9 * P m := by rw [show m + 4 = m + 3 + 1 by omega, q3, x3]; linear_combination 1 * Q3
    linear_combination E4 - 6 * E2

theorem a0 : a 0 = 1 := by simp [a, Multiset.esymm, Multiset.powersetCard_zero_left]
theorem a1 : a 1 = 1 := by simp [a, Multiset.esymm, Multiset.powersetCard_zero_left]
theorem P1 : P 1 = x 0 := by simp [P, Multiset.esymm, Multiset.powersetCard_one]

end P203230

theorem OMA.solution : type_of% @OMA.S_oeis_a203230.main := by
  have hrec : ∀ n : ℕ, 5 ≤ n → a n = 6 * a (n - 2) - 9 * a (n - 4) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 2 = m + 2 by omega, show m + 4 - 4 = m by omega]
    exact P203230.rec m (by omega)
  refine ⟨hrec, ?_⟩
  have v0 : a 0 = 1 := P203230.a0
  have v1 : a 1 = 1 := P203230.a1
  have p1 : P203230.P 1 = 1 := by rw [P203230.P1]; simp [x]
  have p2 : P203230.P 2 = 3 := by rw [P203230.pstep 1, p1]; simp [x]
  have v2 : a 2 = 4 := by rw [P203230.estep 1 (by norm_num), v1, p1]; simp [x]
  have p3 : P203230.P 3 = 3 := by rw [P203230.pstep 2, p2]; simp [x]
  have v3 : a 3 = 7 := by rw [P203230.estep 2 (by norm_num), v2, p2]; simp [x]
  have p4 : P203230.P 4 = 9 := by rw [P203230.pstep 3, p3]; simp [x]
  have v4 : a 4 = 24 := by rw [P203230.estep 3 (by norm_num), v3, p3]; simp [x]
  have hp : ((-1 + 3 * X ^ 2) ^ 2 : PowerSeries ℤ) = 1 - C 6 * X ^ 2 + C 9 * X ^ 4 := by
    simp only [map_ofNat]; ring
  have hq : ∀ F : PowerSeries ℤ, F * (1 - C 6 * X ^ 2 + C 9 * X ^ 4) =
      F - C 6 * (F * X ^ 2) + C 9 * (F * X ^ 4) := fun F => by ring
  have hr : (X + 4 * X ^ 2 + X ^ 3 : PowerSeries ℤ) = X + C 4 * X ^ 2 + X ^ 3 := by
    simp only [map_ofNat]
  rw [hp, hq, hr]
  clear hp hq hr
  ext n
  simp only [map_sub, map_add, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_C_mul_X_pow,
    coeff_X_pow, coeff_X, coeff_C]
  rcases Nat.lt_or_ge n 5 with hn | hn
  · interval_cases n <;> simp [v0, v1, v2, v3, v4]
  · have h := hrec n (by omega)
    simp (disch := omega) only [if_pos, if_neg, Nat.sub_eq_zero_iff_le]
    simp only [add_zero, zero_add, neg_zero]
    linarith
