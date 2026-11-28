import OMAStatements.S_oeis_a203235
import Mathlib

open OMA.S_oeis_a203235
open PowerSeries

namespace P203235

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

theorem rec (m : ℕ) (hm : 1 ≤ m) : a (m + 8) = 6 * a (m + 4) - 9 * a m := by
  have hr : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3) with hr0 | hr1 | hr2 | hr3
  · -- r = 0
    have x0 : x (m) = 1 := by simp only [x, show (m) % 4 = 0 by omega]; norm_num
    have h0 := estep (m) (by omega)
    have q0 := pstep (m)
    have E1 : a (m + 1) = 1 * a m + 1 * P m := by rw [h0, x0]; ring
    have Q1 : P (m + 1) = 1 * P m := by rw [q0, x0]
    have x1 : x (m + 1) = 1 := by simp only [x, show (m + 1) % 4 = 1 by omega]; norm_num
    have h1 := estep (m + 1) (by omega)
    have q1 := pstep (m + 1)
    have E2 : a (m + 2) = 1 * a m + 2 * P m := by rw [show m + 2 = m + 1 + 1 by omega, h1, x1]; linear_combination 1 * E1 + Q1
    have Q2 : P (m + 2) = 1 * P m := by rw [show m + 2 = m + 1 + 1 by omega, q1, x1]; linear_combination 1 * Q1
    have x2 : x (m + 2) = 1 := by simp only [x, show (m + 2) % 4 = 2 by omega]; norm_num
    have h2 := estep (m + 2) (by omega)
    have q2 := pstep (m + 2)
    have E3 : a (m + 3) = 1 * a m + 3 * P m := by rw [show m + 3 = m + 2 + 1 by omega, h2, x2]; linear_combination 1 * E2 + Q2
    have Q3 : P (m + 3) = 1 * P m := by rw [show m + 3 = m + 2 + 1 by omega, q2, x2]; linear_combination 1 * Q2
    have x3 : x (m + 3) = 3 := by simp only [x, show (m + 3) % 4 = 3 by omega]; norm_num
    have h3 := estep (m + 3) (by omega)
    have q3 := pstep (m + 3)
    have E4 : a (m + 4) = 3 * a m + 10 * P m := by rw [show m + 4 = m + 3 + 1 by omega, h3, x3]; linear_combination 3 * E3 + Q3
    have Q4 : P (m + 4) = 3 * P m := by rw [show m + 4 = m + 3 + 1 by omega, q3, x3]; linear_combination 3 * Q3
    have x4 : x (m + 4) = 1 := by simp only [x, show (m + 4) % 4 = 0 by omega]; norm_num
    have h4 := estep (m + 4) (by omega)
    have q4 := pstep (m + 4)
    have E5 : a (m + 5) = 3 * a m + 13 * P m := by rw [show m + 5 = m + 4 + 1 by omega, h4, x4]; linear_combination 1 * E4 + Q4
    have Q5 : P (m + 5) = 3 * P m := by rw [show m + 5 = m + 4 + 1 by omega, q4, x4]; linear_combination 1 * Q4
    have x5 : x (m + 5) = 1 := by simp only [x, show (m + 5) % 4 = 1 by omega]; norm_num
    have h5 := estep (m + 5) (by omega)
    have q5 := pstep (m + 5)
    have E6 : a (m + 6) = 3 * a m + 16 * P m := by rw [show m + 6 = m + 5 + 1 by omega, h5, x5]; linear_combination 1 * E5 + Q5
    have Q6 : P (m + 6) = 3 * P m := by rw [show m + 6 = m + 5 + 1 by omega, q5, x5]; linear_combination 1 * Q5
    have x6 : x (m + 6) = 1 := by simp only [x, show (m + 6) % 4 = 2 by omega]; norm_num
    have h6 := estep (m + 6) (by omega)
    have q6 := pstep (m + 6)
    have E7 : a (m + 7) = 3 * a m + 19 * P m := by rw [show m + 7 = m + 6 + 1 by omega, h6, x6]; linear_combination 1 * E6 + Q6
    have Q7 : P (m + 7) = 3 * P m := by rw [show m + 7 = m + 6 + 1 by omega, q6, x6]; linear_combination 1 * Q6
    have x7 : x (m + 7) = 3 := by simp only [x, show (m + 7) % 4 = 3 by omega]; norm_num
    have h7 := estep (m + 7) (by omega)
    have q7 := pstep (m + 7)
    have E8 : a (m + 8) = 9 * a m + 60 * P m := by rw [show m + 8 = m + 7 + 1 by omega, h7, x7]; linear_combination 3 * E7 + Q7
    have Q8 : P (m + 8) = 9 * P m := by rw [show m + 8 = m + 7 + 1 by omega, q7, x7]; linear_combination 3 * Q7
    linear_combination E8 - 6 * E4
  · -- r = 1
    have x0 : x (m) = 1 := by simp only [x, show (m) % 4 = 1 by omega]; norm_num
    have h0 := estep (m) (by omega)
    have q0 := pstep (m)
    have E1 : a (m + 1) = 1 * a m + 1 * P m := by rw [h0, x0]; ring
    have Q1 : P (m + 1) = 1 * P m := by rw [q0, x0]
    have x1 : x (m + 1) = 1 := by simp only [x, show (m + 1) % 4 = 2 by omega]; norm_num
    have h1 := estep (m + 1) (by omega)
    have q1 := pstep (m + 1)
    have E2 : a (m + 2) = 1 * a m + 2 * P m := by rw [show m + 2 = m + 1 + 1 by omega, h1, x1]; linear_combination 1 * E1 + Q1
    have Q2 : P (m + 2) = 1 * P m := by rw [show m + 2 = m + 1 + 1 by omega, q1, x1]; linear_combination 1 * Q1
    have x2 : x (m + 2) = 3 := by simp only [x, show (m + 2) % 4 = 3 by omega]; norm_num
    have h2 := estep (m + 2) (by omega)
    have q2 := pstep (m + 2)
    have E3 : a (m + 3) = 3 * a m + 7 * P m := by rw [show m + 3 = m + 2 + 1 by omega, h2, x2]; linear_combination 3 * E2 + Q2
    have Q3 : P (m + 3) = 3 * P m := by rw [show m + 3 = m + 2 + 1 by omega, q2, x2]; linear_combination 3 * Q2
    have x3 : x (m + 3) = 1 := by simp only [x, show (m + 3) % 4 = 0 by omega]; norm_num
    have h3 := estep (m + 3) (by omega)
    have q3 := pstep (m + 3)
    have E4 : a (m + 4) = 3 * a m + 10 * P m := by rw [show m + 4 = m + 3 + 1 by omega, h3, x3]; linear_combination 1 * E3 + Q3
    have Q4 : P (m + 4) = 3 * P m := by rw [show m + 4 = m + 3 + 1 by omega, q3, x3]; linear_combination 1 * Q3
    have x4 : x (m + 4) = 1 := by simp only [x, show (m + 4) % 4 = 1 by omega]; norm_num
    have h4 := estep (m + 4) (by omega)
    have q4 := pstep (m + 4)
    have E5 : a (m + 5) = 3 * a m + 13 * P m := by rw [show m + 5 = m + 4 + 1 by omega, h4, x4]; linear_combination 1 * E4 + Q4
    have Q5 : P (m + 5) = 3 * P m := by rw [show m + 5 = m + 4 + 1 by omega, q4, x4]; linear_combination 1 * Q4
    have x5 : x (m + 5) = 1 := by simp only [x, show (m + 5) % 4 = 2 by omega]; norm_num
    have h5 := estep (m + 5) (by omega)
    have q5 := pstep (m + 5)
    have E6 : a (m + 6) = 3 * a m + 16 * P m := by rw [show m + 6 = m + 5 + 1 by omega, h5, x5]; linear_combination 1 * E5 + Q5
    have Q6 : P (m + 6) = 3 * P m := by rw [show m + 6 = m + 5 + 1 by omega, q5, x5]; linear_combination 1 * Q5
    have x6 : x (m + 6) = 3 := by simp only [x, show (m + 6) % 4 = 3 by omega]; norm_num
    have h6 := estep (m + 6) (by omega)
    have q6 := pstep (m + 6)
    have E7 : a (m + 7) = 9 * a m + 51 * P m := by rw [show m + 7 = m + 6 + 1 by omega, h6, x6]; linear_combination 3 * E6 + Q6
    have Q7 : P (m + 7) = 9 * P m := by rw [show m + 7 = m + 6 + 1 by omega, q6, x6]; linear_combination 3 * Q6
    have x7 : x (m + 7) = 1 := by simp only [x, show (m + 7) % 4 = 0 by omega]; norm_num
    have h7 := estep (m + 7) (by omega)
    have q7 := pstep (m + 7)
    have E8 : a (m + 8) = 9 * a m + 60 * P m := by rw [show m + 8 = m + 7 + 1 by omega, h7, x7]; linear_combination 1 * E7 + Q7
    have Q8 : P (m + 8) = 9 * P m := by rw [show m + 8 = m + 7 + 1 by omega, q7, x7]; linear_combination 1 * Q7
    linear_combination E8 - 6 * E4
  · -- r = 2
    have x0 : x (m) = 1 := by simp only [x, show (m) % 4 = 2 by omega]; norm_num
    have h0 := estep (m) (by omega)
    have q0 := pstep (m)
    have E1 : a (m + 1) = 1 * a m + 1 * P m := by rw [h0, x0]; ring
    have Q1 : P (m + 1) = 1 * P m := by rw [q0, x0]
    have x1 : x (m + 1) = 3 := by simp only [x, show (m + 1) % 4 = 3 by omega]; norm_num
    have h1 := estep (m + 1) (by omega)
    have q1 := pstep (m + 1)
    have E2 : a (m + 2) = 3 * a m + 4 * P m := by rw [show m + 2 = m + 1 + 1 by omega, h1, x1]; linear_combination 3 * E1 + Q1
    have Q2 : P (m + 2) = 3 * P m := by rw [show m + 2 = m + 1 + 1 by omega, q1, x1]; linear_combination 3 * Q1
    have x2 : x (m + 2) = 1 := by simp only [x, show (m + 2) % 4 = 0 by omega]; norm_num
    have h2 := estep (m + 2) (by omega)
    have q2 := pstep (m + 2)
    have E3 : a (m + 3) = 3 * a m + 7 * P m := by rw [show m + 3 = m + 2 + 1 by omega, h2, x2]; linear_combination 1 * E2 + Q2
    have Q3 : P (m + 3) = 3 * P m := by rw [show m + 3 = m + 2 + 1 by omega, q2, x2]; linear_combination 1 * Q2
    have x3 : x (m + 3) = 1 := by simp only [x, show (m + 3) % 4 = 1 by omega]; norm_num
    have h3 := estep (m + 3) (by omega)
    have q3 := pstep (m + 3)
    have E4 : a (m + 4) = 3 * a m + 10 * P m := by rw [show m + 4 = m + 3 + 1 by omega, h3, x3]; linear_combination 1 * E3 + Q3
    have Q4 : P (m + 4) = 3 * P m := by rw [show m + 4 = m + 3 + 1 by omega, q3, x3]; linear_combination 1 * Q3
    have x4 : x (m + 4) = 1 := by simp only [x, show (m + 4) % 4 = 2 by omega]; norm_num
    have h4 := estep (m + 4) (by omega)
    have q4 := pstep (m + 4)
    have E5 : a (m + 5) = 3 * a m + 13 * P m := by rw [show m + 5 = m + 4 + 1 by omega, h4, x4]; linear_combination 1 * E4 + Q4
    have Q5 : P (m + 5) = 3 * P m := by rw [show m + 5 = m + 4 + 1 by omega, q4, x4]; linear_combination 1 * Q4
    have x5 : x (m + 5) = 3 := by simp only [x, show (m + 5) % 4 = 3 by omega]; norm_num
    have h5 := estep (m + 5) (by omega)
    have q5 := pstep (m + 5)
    have E6 : a (m + 6) = 9 * a m + 42 * P m := by rw [show m + 6 = m + 5 + 1 by omega, h5, x5]; linear_combination 3 * E5 + Q5
    have Q6 : P (m + 6) = 9 * P m := by rw [show m + 6 = m + 5 + 1 by omega, q5, x5]; linear_combination 3 * Q5
    have x6 : x (m + 6) = 1 := by simp only [x, show (m + 6) % 4 = 0 by omega]; norm_num
    have h6 := estep (m + 6) (by omega)
    have q6 := pstep (m + 6)
    have E7 : a (m + 7) = 9 * a m + 51 * P m := by rw [show m + 7 = m + 6 + 1 by omega, h6, x6]; linear_combination 1 * E6 + Q6
    have Q7 : P (m + 7) = 9 * P m := by rw [show m + 7 = m + 6 + 1 by omega, q6, x6]; linear_combination 1 * Q6
    have x7 : x (m + 7) = 1 := by simp only [x, show (m + 7) % 4 = 1 by omega]; norm_num
    have h7 := estep (m + 7) (by omega)
    have q7 := pstep (m + 7)
    have E8 : a (m + 8) = 9 * a m + 60 * P m := by rw [show m + 8 = m + 7 + 1 by omega, h7, x7]; linear_combination 1 * E7 + Q7
    have Q8 : P (m + 8) = 9 * P m := by rw [show m + 8 = m + 7 + 1 by omega, q7, x7]; linear_combination 1 * Q7
    linear_combination E8 - 6 * E4
  · -- r = 3
    have x0 : x (m) = 3 := by simp only [x, show (m) % 4 = 3 by omega]; norm_num
    have h0 := estep (m) (by omega)
    have q0 := pstep (m)
    have E1 : a (m + 1) = 3 * a m + 1 * P m := by rw [h0, x0]; ring
    have Q1 : P (m + 1) = 3 * P m := by rw [q0, x0]
    have x1 : x (m + 1) = 1 := by simp only [x, show (m + 1) % 4 = 0 by omega]; norm_num
    have h1 := estep (m + 1) (by omega)
    have q1 := pstep (m + 1)
    have E2 : a (m + 2) = 3 * a m + 4 * P m := by rw [show m + 2 = m + 1 + 1 by omega, h1, x1]; linear_combination 1 * E1 + Q1
    have Q2 : P (m + 2) = 3 * P m := by rw [show m + 2 = m + 1 + 1 by omega, q1, x1]; linear_combination 1 * Q1
    have x2 : x (m + 2) = 1 := by simp only [x, show (m + 2) % 4 = 1 by omega]; norm_num
    have h2 := estep (m + 2) (by omega)
    have q2 := pstep (m + 2)
    have E3 : a (m + 3) = 3 * a m + 7 * P m := by rw [show m + 3 = m + 2 + 1 by omega, h2, x2]; linear_combination 1 * E2 + Q2
    have Q3 : P (m + 3) = 3 * P m := by rw [show m + 3 = m + 2 + 1 by omega, q2, x2]; linear_combination 1 * Q2
    have x3 : x (m + 3) = 1 := by simp only [x, show (m + 3) % 4 = 2 by omega]; norm_num
    have h3 := estep (m + 3) (by omega)
    have q3 := pstep (m + 3)
    have E4 : a (m + 4) = 3 * a m + 10 * P m := by rw [show m + 4 = m + 3 + 1 by omega, h3, x3]; linear_combination 1 * E3 + Q3
    have Q4 : P (m + 4) = 3 * P m := by rw [show m + 4 = m + 3 + 1 by omega, q3, x3]; linear_combination 1 * Q3
    have x4 : x (m + 4) = 3 := by simp only [x, show (m + 4) % 4 = 3 by omega]; norm_num
    have h4 := estep (m + 4) (by omega)
    have q4 := pstep (m + 4)
    have E5 : a (m + 5) = 9 * a m + 33 * P m := by rw [show m + 5 = m + 4 + 1 by omega, h4, x4]; linear_combination 3 * E4 + Q4
    have Q5 : P (m + 5) = 9 * P m := by rw [show m + 5 = m + 4 + 1 by omega, q4, x4]; linear_combination 3 * Q4
    have x5 : x (m + 5) = 1 := by simp only [x, show (m + 5) % 4 = 0 by omega]; norm_num
    have h5 := estep (m + 5) (by omega)
    have q5 := pstep (m + 5)
    have E6 : a (m + 6) = 9 * a m + 42 * P m := by rw [show m + 6 = m + 5 + 1 by omega, h5, x5]; linear_combination 1 * E5 + Q5
    have Q6 : P (m + 6) = 9 * P m := by rw [show m + 6 = m + 5 + 1 by omega, q5, x5]; linear_combination 1 * Q5
    have x6 : x (m + 6) = 1 := by simp only [x, show (m + 6) % 4 = 1 by omega]; norm_num
    have h6 := estep (m + 6) (by omega)
    have q6 := pstep (m + 6)
    have E7 : a (m + 7) = 9 * a m + 51 * P m := by rw [show m + 7 = m + 6 + 1 by omega, h6, x6]; linear_combination 1 * E6 + Q6
    have Q7 : P (m + 7) = 9 * P m := by rw [show m + 7 = m + 6 + 1 by omega, q6, x6]; linear_combination 1 * Q6
    have x7 : x (m + 7) = 1 := by simp only [x, show (m + 7) % 4 = 2 by omega]; norm_num
    have h7 := estep (m + 7) (by omega)
    have q7 := pstep (m + 7)
    have E8 : a (m + 8) = 9 * a m + 60 * P m := by rw [show m + 8 = m + 7 + 1 by omega, h7, x7]; linear_combination 1 * E7 + Q7
    have Q8 : P (m + 8) = 9 * P m := by rw [show m + 8 = m + 7 + 1 by omega, q7, x7]; linear_combination 1 * Q7
    linear_combination E8 - 6 * E4

theorem a0 : a 0 = 1 := by simp [a, Multiset.esymm, Multiset.powersetCard_zero_left]
theorem a1 : a 1 = 1 := by simp [a, Multiset.esymm, Multiset.powersetCard_zero_left]
theorem P1 : P 1 = x 0 := by simp [P, Multiset.esymm, Multiset.powersetCard_one]

end P203235

theorem OMA.solution : type_of% @OMA.S_oeis_a203235.main := by
  have hrec : ∀ n : ℕ, 9 ≤ n → a n = 6 * a (n - 4) - 9 * a (n - 8) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    rw [show m + 8 - 4 = m + 4 by omega, show m + 8 - 8 = m by omega]
    exact P203235.rec m (by omega)
  refine ⟨hrec, ?_⟩
  have v0 : a 0 = 1 := P203235.a0
  have v1 : a 1 = 1 := P203235.a1
  have p1 : P203235.P 1 = 1 := by rw [P203235.P1]; simp [x]
  have p2 : P203235.P 2 = 1 := by rw [P203235.pstep 1, p1]; simp [x]
  have v2 : a 2 = 2 := by rw [P203235.estep 1 (by norm_num), v1, p1]; simp [x]
  have p3 : P203235.P 3 = 1 := by rw [P203235.pstep 2, p2]; simp [x]
  have v3 : a 3 = 3 := by rw [P203235.estep 2 (by norm_num), v2, p2]; simp [x]
  have p4 : P203235.P 4 = 3 := by rw [P203235.pstep 3, p3]; simp [x]
  have v4 : a 4 = 10 := by rw [P203235.estep 3 (by norm_num), v3, p3]; simp [x]
  have p5 : P203235.P 5 = 3 := by rw [P203235.pstep 4, p4]; simp [x]
  have v5 : a 5 = 13 := by rw [P203235.estep 4 (by norm_num), v4, p4]; simp [x]
  have p6 : P203235.P 6 = 3 := by rw [P203235.pstep 5, p5]; simp [x]
  have v6 : a 6 = 16 := by rw [P203235.estep 5 (by norm_num), v5, p5]; simp [x]
  have p7 : P203235.P 7 = 3 := by rw [P203235.pstep 6, p6]; simp [x]
  have v7 : a 7 = 19 := by rw [P203235.estep 6 (by norm_num), v6, p6]; simp [x]
  have p8 : P203235.P 8 = 9 := by rw [P203235.pstep 7, p7]; simp [x]
  have v8 : a 8 = 60 := by rw [P203235.estep 7 (by norm_num), v7, p7]; simp [x]
  have hp : ((-1 + 3 * X ^ 4) ^ 2 : PowerSeries ℤ) = 1 - C 6 * X ^ 4 + C 9 * X ^ 8 := by
    simp only [map_ofNat]; ring
  have hq : ∀ F : PowerSeries ℤ, F * (1 - C 6 * X ^ 4 + C 9 * X ^ 8) =
      F - C 6 * (F * X ^ 4) + C 9 * (F * X ^ 8) := fun F => by ring
  have hr : (X + 2 * X ^ 2 + 3 * X ^ 3 + 10 * X ^ 4 + 7 * X ^ 5 + 4 * X ^ 6 + X ^ 7 : PowerSeries ℤ) = X + C 2 * X ^ 2 + C 3 * X ^ 3 + C 10 * X ^ 4 + C 7 * X ^ 5 + C 4 * X ^ 6 + X ^ 7 := by
    simp only [map_ofNat]
  rw [hp, hq, hr]
  clear hp hq hr
  ext n
  simp only [map_sub, map_add, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_C_mul_X_pow,
    coeff_X_pow, coeff_X, coeff_C]
  rcases Nat.lt_or_ge n 9 with hn | hn
  · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, v8]
  · have h := hrec n (by omega)
    simp (disch := omega) only [if_pos, if_neg, Nat.sub_eq_zero_iff_le]
    simp only [add_zero, zero_add, neg_zero]
    linarith
