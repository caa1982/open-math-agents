import OMAStatements.S_oeis_a203166
import Mathlib

open OMA.S_oeis_a203166
open PowerSeries

namespace P203166

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

theorem rec (m : ℕ) (hm : 1 ≤ m) : a (m + 10) = 240 * a (m + 5) - 14400 * a m := by
  have hr : m % 5 < 5 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4) with hr0 | hr1 | hr2 | hr3 | hr4
  · -- r = 0
    have x0 : x (m) = 1 := by simp only [x, show (m) % 5 = 0 by omega]; norm_num
    have h0 := estep (m) (by omega)
    have q0 := pstep (m)
    have E1 : a (m + 1) = 1 * a m + 1 * P m := by rw [h0, x0]; ring
    have Q1 : P (m + 1) = 1 * P m := by rw [q0, x0]
    have x1 : x (m + 1) = 2 := by simp only [x, show (m + 1) % 5 = 1 by omega]; norm_num
    have h1 := estep (m + 1) (by omega)
    have q1 := pstep (m + 1)
    have E2 : a (m + 2) = 2 * a m + 3 * P m := by rw [show m + 2 = m + 1 + 1 by omega, h1, x1]; linear_combination 2 * E1 + Q1
    have Q2 : P (m + 2) = 2 * P m := by rw [show m + 2 = m + 1 + 1 by omega, q1, x1]; linear_combination 2 * Q1
    have x2 : x (m + 2) = 3 := by simp only [x, show (m + 2) % 5 = 2 by omega]; norm_num
    have h2 := estep (m + 2) (by omega)
    have q2 := pstep (m + 2)
    have E3 : a (m + 3) = 6 * a m + 11 * P m := by rw [show m + 3 = m + 2 + 1 by omega, h2, x2]; linear_combination 3 * E2 + Q2
    have Q3 : P (m + 3) = 6 * P m := by rw [show m + 3 = m + 2 + 1 by omega, q2, x2]; linear_combination 3 * Q2
    have x3 : x (m + 3) = 4 := by simp only [x, show (m + 3) % 5 = 3 by omega]; norm_num
    have h3 := estep (m + 3) (by omega)
    have q3 := pstep (m + 3)
    have E4 : a (m + 4) = 24 * a m + 50 * P m := by rw [show m + 4 = m + 3 + 1 by omega, h3, x3]; linear_combination 4 * E3 + Q3
    have Q4 : P (m + 4) = 24 * P m := by rw [show m + 4 = m + 3 + 1 by omega, q3, x3]; linear_combination 4 * Q3
    have x4 : x (m + 4) = 5 := by simp only [x, show (m + 4) % 5 = 4 by omega]; norm_num
    have h4 := estep (m + 4) (by omega)
    have q4 := pstep (m + 4)
    have E5 : a (m + 5) = 120 * a m + 274 * P m := by rw [show m + 5 = m + 4 + 1 by omega, h4, x4]; linear_combination 5 * E4 + Q4
    have Q5 : P (m + 5) = 120 * P m := by rw [show m + 5 = m + 4 + 1 by omega, q4, x4]; linear_combination 5 * Q4
    have x5 : x (m + 5) = 1 := by simp only [x, show (m + 5) % 5 = 0 by omega]; norm_num
    have h5 := estep (m + 5) (by omega)
    have q5 := pstep (m + 5)
    have E6 : a (m + 6) = 120 * a m + 394 * P m := by rw [show m + 6 = m + 5 + 1 by omega, h5, x5]; linear_combination 1 * E5 + Q5
    have Q6 : P (m + 6) = 120 * P m := by rw [show m + 6 = m + 5 + 1 by omega, q5, x5]; linear_combination 1 * Q5
    have x6 : x (m + 6) = 2 := by simp only [x, show (m + 6) % 5 = 1 by omega]; norm_num
    have h6 := estep (m + 6) (by omega)
    have q6 := pstep (m + 6)
    have E7 : a (m + 7) = 240 * a m + 908 * P m := by rw [show m + 7 = m + 6 + 1 by omega, h6, x6]; linear_combination 2 * E6 + Q6
    have Q7 : P (m + 7) = 240 * P m := by rw [show m + 7 = m + 6 + 1 by omega, q6, x6]; linear_combination 2 * Q6
    have x7 : x (m + 7) = 3 := by simp only [x, show (m + 7) % 5 = 2 by omega]; norm_num
    have h7 := estep (m + 7) (by omega)
    have q7 := pstep (m + 7)
    have E8 : a (m + 8) = 720 * a m + 2964 * P m := by rw [show m + 8 = m + 7 + 1 by omega, h7, x7]; linear_combination 3 * E7 + Q7
    have Q8 : P (m + 8) = 720 * P m := by rw [show m + 8 = m + 7 + 1 by omega, q7, x7]; linear_combination 3 * Q7
    have x8 : x (m + 8) = 4 := by simp only [x, show (m + 8) % 5 = 3 by omega]; norm_num
    have h8 := estep (m + 8) (by omega)
    have q8 := pstep (m + 8)
    have E9 : a (m + 9) = 2880 * a m + 12576 * P m := by rw [show m + 9 = m + 8 + 1 by omega, h8, x8]; linear_combination 4 * E8 + Q8
    have Q9 : P (m + 9) = 2880 * P m := by rw [show m + 9 = m + 8 + 1 by omega, q8, x8]; linear_combination 4 * Q8
    have x9 : x (m + 9) = 5 := by simp only [x, show (m + 9) % 5 = 4 by omega]; norm_num
    have h9 := estep (m + 9) (by omega)
    have q9 := pstep (m + 9)
    have E10 : a (m + 10) = 14400 * a m + 65760 * P m := by rw [show m + 10 = m + 9 + 1 by omega, h9, x9]; linear_combination 5 * E9 + Q9
    have Q10 : P (m + 10) = 14400 * P m := by rw [show m + 10 = m + 9 + 1 by omega, q9, x9]; linear_combination 5 * Q9
    linear_combination E10 - 240 * E5
  · -- r = 1
    have x0 : x (m) = 2 := by simp only [x, show (m) % 5 = 1 by omega]; norm_num
    have h0 := estep (m) (by omega)
    have q0 := pstep (m)
    have E1 : a (m + 1) = 2 * a m + 1 * P m := by rw [h0, x0]; ring
    have Q1 : P (m + 1) = 2 * P m := by rw [q0, x0]
    have x1 : x (m + 1) = 3 := by simp only [x, show (m + 1) % 5 = 2 by omega]; norm_num
    have h1 := estep (m + 1) (by omega)
    have q1 := pstep (m + 1)
    have E2 : a (m + 2) = 6 * a m + 5 * P m := by rw [show m + 2 = m + 1 + 1 by omega, h1, x1]; linear_combination 3 * E1 + Q1
    have Q2 : P (m + 2) = 6 * P m := by rw [show m + 2 = m + 1 + 1 by omega, q1, x1]; linear_combination 3 * Q1
    have x2 : x (m + 2) = 4 := by simp only [x, show (m + 2) % 5 = 3 by omega]; norm_num
    have h2 := estep (m + 2) (by omega)
    have q2 := pstep (m + 2)
    have E3 : a (m + 3) = 24 * a m + 26 * P m := by rw [show m + 3 = m + 2 + 1 by omega, h2, x2]; linear_combination 4 * E2 + Q2
    have Q3 : P (m + 3) = 24 * P m := by rw [show m + 3 = m + 2 + 1 by omega, q2, x2]; linear_combination 4 * Q2
    have x3 : x (m + 3) = 5 := by simp only [x, show (m + 3) % 5 = 4 by omega]; norm_num
    have h3 := estep (m + 3) (by omega)
    have q3 := pstep (m + 3)
    have E4 : a (m + 4) = 120 * a m + 154 * P m := by rw [show m + 4 = m + 3 + 1 by omega, h3, x3]; linear_combination 5 * E3 + Q3
    have Q4 : P (m + 4) = 120 * P m := by rw [show m + 4 = m + 3 + 1 by omega, q3, x3]; linear_combination 5 * Q3
    have x4 : x (m + 4) = 1 := by simp only [x, show (m + 4) % 5 = 0 by omega]; norm_num
    have h4 := estep (m + 4) (by omega)
    have q4 := pstep (m + 4)
    have E5 : a (m + 5) = 120 * a m + 274 * P m := by rw [show m + 5 = m + 4 + 1 by omega, h4, x4]; linear_combination 1 * E4 + Q4
    have Q5 : P (m + 5) = 120 * P m := by rw [show m + 5 = m + 4 + 1 by omega, q4, x4]; linear_combination 1 * Q4
    have x5 : x (m + 5) = 2 := by simp only [x, show (m + 5) % 5 = 1 by omega]; norm_num
    have h5 := estep (m + 5) (by omega)
    have q5 := pstep (m + 5)
    have E6 : a (m + 6) = 240 * a m + 668 * P m := by rw [show m + 6 = m + 5 + 1 by omega, h5, x5]; linear_combination 2 * E5 + Q5
    have Q6 : P (m + 6) = 240 * P m := by rw [show m + 6 = m + 5 + 1 by omega, q5, x5]; linear_combination 2 * Q5
    have x6 : x (m + 6) = 3 := by simp only [x, show (m + 6) % 5 = 2 by omega]; norm_num
    have h6 := estep (m + 6) (by omega)
    have q6 := pstep (m + 6)
    have E7 : a (m + 7) = 720 * a m + 2244 * P m := by rw [show m + 7 = m + 6 + 1 by omega, h6, x6]; linear_combination 3 * E6 + Q6
    have Q7 : P (m + 7) = 720 * P m := by rw [show m + 7 = m + 6 + 1 by omega, q6, x6]; linear_combination 3 * Q6
    have x7 : x (m + 7) = 4 := by simp only [x, show (m + 7) % 5 = 3 by omega]; norm_num
    have h7 := estep (m + 7) (by omega)
    have q7 := pstep (m + 7)
    have E8 : a (m + 8) = 2880 * a m + 9696 * P m := by rw [show m + 8 = m + 7 + 1 by omega, h7, x7]; linear_combination 4 * E7 + Q7
    have Q8 : P (m + 8) = 2880 * P m := by rw [show m + 8 = m + 7 + 1 by omega, q7, x7]; linear_combination 4 * Q7
    have x8 : x (m + 8) = 5 := by simp only [x, show (m + 8) % 5 = 4 by omega]; norm_num
    have h8 := estep (m + 8) (by omega)
    have q8 := pstep (m + 8)
    have E9 : a (m + 9) = 14400 * a m + 51360 * P m := by rw [show m + 9 = m + 8 + 1 by omega, h8, x8]; linear_combination 5 * E8 + Q8
    have Q9 : P (m + 9) = 14400 * P m := by rw [show m + 9 = m + 8 + 1 by omega, q8, x8]; linear_combination 5 * Q8
    have x9 : x (m + 9) = 1 := by simp only [x, show (m + 9) % 5 = 0 by omega]; norm_num
    have h9 := estep (m + 9) (by omega)
    have q9 := pstep (m + 9)
    have E10 : a (m + 10) = 14400 * a m + 65760 * P m := by rw [show m + 10 = m + 9 + 1 by omega, h9, x9]; linear_combination 1 * E9 + Q9
    have Q10 : P (m + 10) = 14400 * P m := by rw [show m + 10 = m + 9 + 1 by omega, q9, x9]; linear_combination 1 * Q9
    linear_combination E10 - 240 * E5
  · -- r = 2
    have x0 : x (m) = 3 := by simp only [x, show (m) % 5 = 2 by omega]; norm_num
    have h0 := estep (m) (by omega)
    have q0 := pstep (m)
    have E1 : a (m + 1) = 3 * a m + 1 * P m := by rw [h0, x0]; ring
    have Q1 : P (m + 1) = 3 * P m := by rw [q0, x0]
    have x1 : x (m + 1) = 4 := by simp only [x, show (m + 1) % 5 = 3 by omega]; norm_num
    have h1 := estep (m + 1) (by omega)
    have q1 := pstep (m + 1)
    have E2 : a (m + 2) = 12 * a m + 7 * P m := by rw [show m + 2 = m + 1 + 1 by omega, h1, x1]; linear_combination 4 * E1 + Q1
    have Q2 : P (m + 2) = 12 * P m := by rw [show m + 2 = m + 1 + 1 by omega, q1, x1]; linear_combination 4 * Q1
    have x2 : x (m + 2) = 5 := by simp only [x, show (m + 2) % 5 = 4 by omega]; norm_num
    have h2 := estep (m + 2) (by omega)
    have q2 := pstep (m + 2)
    have E3 : a (m + 3) = 60 * a m + 47 * P m := by rw [show m + 3 = m + 2 + 1 by omega, h2, x2]; linear_combination 5 * E2 + Q2
    have Q3 : P (m + 3) = 60 * P m := by rw [show m + 3 = m + 2 + 1 by omega, q2, x2]; linear_combination 5 * Q2
    have x3 : x (m + 3) = 1 := by simp only [x, show (m + 3) % 5 = 0 by omega]; norm_num
    have h3 := estep (m + 3) (by omega)
    have q3 := pstep (m + 3)
    have E4 : a (m + 4) = 60 * a m + 107 * P m := by rw [show m + 4 = m + 3 + 1 by omega, h3, x3]; linear_combination 1 * E3 + Q3
    have Q4 : P (m + 4) = 60 * P m := by rw [show m + 4 = m + 3 + 1 by omega, q3, x3]; linear_combination 1 * Q3
    have x4 : x (m + 4) = 2 := by simp only [x, show (m + 4) % 5 = 1 by omega]; norm_num
    have h4 := estep (m + 4) (by omega)
    have q4 := pstep (m + 4)
    have E5 : a (m + 5) = 120 * a m + 274 * P m := by rw [show m + 5 = m + 4 + 1 by omega, h4, x4]; linear_combination 2 * E4 + Q4
    have Q5 : P (m + 5) = 120 * P m := by rw [show m + 5 = m + 4 + 1 by omega, q4, x4]; linear_combination 2 * Q4
    have x5 : x (m + 5) = 3 := by simp only [x, show (m + 5) % 5 = 2 by omega]; norm_num
    have h5 := estep (m + 5) (by omega)
    have q5 := pstep (m + 5)
    have E6 : a (m + 6) = 360 * a m + 942 * P m := by rw [show m + 6 = m + 5 + 1 by omega, h5, x5]; linear_combination 3 * E5 + Q5
    have Q6 : P (m + 6) = 360 * P m := by rw [show m + 6 = m + 5 + 1 by omega, q5, x5]; linear_combination 3 * Q5
    have x6 : x (m + 6) = 4 := by simp only [x, show (m + 6) % 5 = 3 by omega]; norm_num
    have h6 := estep (m + 6) (by omega)
    have q6 := pstep (m + 6)
    have E7 : a (m + 7) = 1440 * a m + 4128 * P m := by rw [show m + 7 = m + 6 + 1 by omega, h6, x6]; linear_combination 4 * E6 + Q6
    have Q7 : P (m + 7) = 1440 * P m := by rw [show m + 7 = m + 6 + 1 by omega, q6, x6]; linear_combination 4 * Q6
    have x7 : x (m + 7) = 5 := by simp only [x, show (m + 7) % 5 = 4 by omega]; norm_num
    have h7 := estep (m + 7) (by omega)
    have q7 := pstep (m + 7)
    have E8 : a (m + 8) = 7200 * a m + 22080 * P m := by rw [show m + 8 = m + 7 + 1 by omega, h7, x7]; linear_combination 5 * E7 + Q7
    have Q8 : P (m + 8) = 7200 * P m := by rw [show m + 8 = m + 7 + 1 by omega, q7, x7]; linear_combination 5 * Q7
    have x8 : x (m + 8) = 1 := by simp only [x, show (m + 8) % 5 = 0 by omega]; norm_num
    have h8 := estep (m + 8) (by omega)
    have q8 := pstep (m + 8)
    have E9 : a (m + 9) = 7200 * a m + 29280 * P m := by rw [show m + 9 = m + 8 + 1 by omega, h8, x8]; linear_combination 1 * E8 + Q8
    have Q9 : P (m + 9) = 7200 * P m := by rw [show m + 9 = m + 8 + 1 by omega, q8, x8]; linear_combination 1 * Q8
    have x9 : x (m + 9) = 2 := by simp only [x, show (m + 9) % 5 = 1 by omega]; norm_num
    have h9 := estep (m + 9) (by omega)
    have q9 := pstep (m + 9)
    have E10 : a (m + 10) = 14400 * a m + 65760 * P m := by rw [show m + 10 = m + 9 + 1 by omega, h9, x9]; linear_combination 2 * E9 + Q9
    have Q10 : P (m + 10) = 14400 * P m := by rw [show m + 10 = m + 9 + 1 by omega, q9, x9]; linear_combination 2 * Q9
    linear_combination E10 - 240 * E5
  · -- r = 3
    have x0 : x (m) = 4 := by simp only [x, show (m) % 5 = 3 by omega]; norm_num
    have h0 := estep (m) (by omega)
    have q0 := pstep (m)
    have E1 : a (m + 1) = 4 * a m + 1 * P m := by rw [h0, x0]; ring
    have Q1 : P (m + 1) = 4 * P m := by rw [q0, x0]
    have x1 : x (m + 1) = 5 := by simp only [x, show (m + 1) % 5 = 4 by omega]; norm_num
    have h1 := estep (m + 1) (by omega)
    have q1 := pstep (m + 1)
    have E2 : a (m + 2) = 20 * a m + 9 * P m := by rw [show m + 2 = m + 1 + 1 by omega, h1, x1]; linear_combination 5 * E1 + Q1
    have Q2 : P (m + 2) = 20 * P m := by rw [show m + 2 = m + 1 + 1 by omega, q1, x1]; linear_combination 5 * Q1
    have x2 : x (m + 2) = 1 := by simp only [x, show (m + 2) % 5 = 0 by omega]; norm_num
    have h2 := estep (m + 2) (by omega)
    have q2 := pstep (m + 2)
    have E3 : a (m + 3) = 20 * a m + 29 * P m := by rw [show m + 3 = m + 2 + 1 by omega, h2, x2]; linear_combination 1 * E2 + Q2
    have Q3 : P (m + 3) = 20 * P m := by rw [show m + 3 = m + 2 + 1 by omega, q2, x2]; linear_combination 1 * Q2
    have x3 : x (m + 3) = 2 := by simp only [x, show (m + 3) % 5 = 1 by omega]; norm_num
    have h3 := estep (m + 3) (by omega)
    have q3 := pstep (m + 3)
    have E4 : a (m + 4) = 40 * a m + 78 * P m := by rw [show m + 4 = m + 3 + 1 by omega, h3, x3]; linear_combination 2 * E3 + Q3
    have Q4 : P (m + 4) = 40 * P m := by rw [show m + 4 = m + 3 + 1 by omega, q3, x3]; linear_combination 2 * Q3
    have x4 : x (m + 4) = 3 := by simp only [x, show (m + 4) % 5 = 2 by omega]; norm_num
    have h4 := estep (m + 4) (by omega)
    have q4 := pstep (m + 4)
    have E5 : a (m + 5) = 120 * a m + 274 * P m := by rw [show m + 5 = m + 4 + 1 by omega, h4, x4]; linear_combination 3 * E4 + Q4
    have Q5 : P (m + 5) = 120 * P m := by rw [show m + 5 = m + 4 + 1 by omega, q4, x4]; linear_combination 3 * Q4
    have x5 : x (m + 5) = 4 := by simp only [x, show (m + 5) % 5 = 3 by omega]; norm_num
    have h5 := estep (m + 5) (by omega)
    have q5 := pstep (m + 5)
    have E6 : a (m + 6) = 480 * a m + 1216 * P m := by rw [show m + 6 = m + 5 + 1 by omega, h5, x5]; linear_combination 4 * E5 + Q5
    have Q6 : P (m + 6) = 480 * P m := by rw [show m + 6 = m + 5 + 1 by omega, q5, x5]; linear_combination 4 * Q5
    have x6 : x (m + 6) = 5 := by simp only [x, show (m + 6) % 5 = 4 by omega]; norm_num
    have h6 := estep (m + 6) (by omega)
    have q6 := pstep (m + 6)
    have E7 : a (m + 7) = 2400 * a m + 6560 * P m := by rw [show m + 7 = m + 6 + 1 by omega, h6, x6]; linear_combination 5 * E6 + Q6
    have Q7 : P (m + 7) = 2400 * P m := by rw [show m + 7 = m + 6 + 1 by omega, q6, x6]; linear_combination 5 * Q6
    have x7 : x (m + 7) = 1 := by simp only [x, show (m + 7) % 5 = 0 by omega]; norm_num
    have h7 := estep (m + 7) (by omega)
    have q7 := pstep (m + 7)
    have E8 : a (m + 8) = 2400 * a m + 8960 * P m := by rw [show m + 8 = m + 7 + 1 by omega, h7, x7]; linear_combination 1 * E7 + Q7
    have Q8 : P (m + 8) = 2400 * P m := by rw [show m + 8 = m + 7 + 1 by omega, q7, x7]; linear_combination 1 * Q7
    have x8 : x (m + 8) = 2 := by simp only [x, show (m + 8) % 5 = 1 by omega]; norm_num
    have h8 := estep (m + 8) (by omega)
    have q8 := pstep (m + 8)
    have E9 : a (m + 9) = 4800 * a m + 20320 * P m := by rw [show m + 9 = m + 8 + 1 by omega, h8, x8]; linear_combination 2 * E8 + Q8
    have Q9 : P (m + 9) = 4800 * P m := by rw [show m + 9 = m + 8 + 1 by omega, q8, x8]; linear_combination 2 * Q8
    have x9 : x (m + 9) = 3 := by simp only [x, show (m + 9) % 5 = 2 by omega]; norm_num
    have h9 := estep (m + 9) (by omega)
    have q9 := pstep (m + 9)
    have E10 : a (m + 10) = 14400 * a m + 65760 * P m := by rw [show m + 10 = m + 9 + 1 by omega, h9, x9]; linear_combination 3 * E9 + Q9
    have Q10 : P (m + 10) = 14400 * P m := by rw [show m + 10 = m + 9 + 1 by omega, q9, x9]; linear_combination 3 * Q9
    linear_combination E10 - 240 * E5
  · -- r = 4
    have x0 : x (m) = 5 := by simp only [x, show (m) % 5 = 4 by omega]; norm_num
    have h0 := estep (m) (by omega)
    have q0 := pstep (m)
    have E1 : a (m + 1) = 5 * a m + 1 * P m := by rw [h0, x0]; ring
    have Q1 : P (m + 1) = 5 * P m := by rw [q0, x0]
    have x1 : x (m + 1) = 1 := by simp only [x, show (m + 1) % 5 = 0 by omega]; norm_num
    have h1 := estep (m + 1) (by omega)
    have q1 := pstep (m + 1)
    have E2 : a (m + 2) = 5 * a m + 6 * P m := by rw [show m + 2 = m + 1 + 1 by omega, h1, x1]; linear_combination 1 * E1 + Q1
    have Q2 : P (m + 2) = 5 * P m := by rw [show m + 2 = m + 1 + 1 by omega, q1, x1]; linear_combination 1 * Q1
    have x2 : x (m + 2) = 2 := by simp only [x, show (m + 2) % 5 = 1 by omega]; norm_num
    have h2 := estep (m + 2) (by omega)
    have q2 := pstep (m + 2)
    have E3 : a (m + 3) = 10 * a m + 17 * P m := by rw [show m + 3 = m + 2 + 1 by omega, h2, x2]; linear_combination 2 * E2 + Q2
    have Q3 : P (m + 3) = 10 * P m := by rw [show m + 3 = m + 2 + 1 by omega, q2, x2]; linear_combination 2 * Q2
    have x3 : x (m + 3) = 3 := by simp only [x, show (m + 3) % 5 = 2 by omega]; norm_num
    have h3 := estep (m + 3) (by omega)
    have q3 := pstep (m + 3)
    have E4 : a (m + 4) = 30 * a m + 61 * P m := by rw [show m + 4 = m + 3 + 1 by omega, h3, x3]; linear_combination 3 * E3 + Q3
    have Q4 : P (m + 4) = 30 * P m := by rw [show m + 4 = m + 3 + 1 by omega, q3, x3]; linear_combination 3 * Q3
    have x4 : x (m + 4) = 4 := by simp only [x, show (m + 4) % 5 = 3 by omega]; norm_num
    have h4 := estep (m + 4) (by omega)
    have q4 := pstep (m + 4)
    have E5 : a (m + 5) = 120 * a m + 274 * P m := by rw [show m + 5 = m + 4 + 1 by omega, h4, x4]; linear_combination 4 * E4 + Q4
    have Q5 : P (m + 5) = 120 * P m := by rw [show m + 5 = m + 4 + 1 by omega, q4, x4]; linear_combination 4 * Q4
    have x5 : x (m + 5) = 5 := by simp only [x, show (m + 5) % 5 = 4 by omega]; norm_num
    have h5 := estep (m + 5) (by omega)
    have q5 := pstep (m + 5)
    have E6 : a (m + 6) = 600 * a m + 1490 * P m := by rw [show m + 6 = m + 5 + 1 by omega, h5, x5]; linear_combination 5 * E5 + Q5
    have Q6 : P (m + 6) = 600 * P m := by rw [show m + 6 = m + 5 + 1 by omega, q5, x5]; linear_combination 5 * Q5
    have x6 : x (m + 6) = 1 := by simp only [x, show (m + 6) % 5 = 0 by omega]; norm_num
    have h6 := estep (m + 6) (by omega)
    have q6 := pstep (m + 6)
    have E7 : a (m + 7) = 600 * a m + 2090 * P m := by rw [show m + 7 = m + 6 + 1 by omega, h6, x6]; linear_combination 1 * E6 + Q6
    have Q7 : P (m + 7) = 600 * P m := by rw [show m + 7 = m + 6 + 1 by omega, q6, x6]; linear_combination 1 * Q6
    have x7 : x (m + 7) = 2 := by simp only [x, show (m + 7) % 5 = 1 by omega]; norm_num
    have h7 := estep (m + 7) (by omega)
    have q7 := pstep (m + 7)
    have E8 : a (m + 8) = 1200 * a m + 4780 * P m := by rw [show m + 8 = m + 7 + 1 by omega, h7, x7]; linear_combination 2 * E7 + Q7
    have Q8 : P (m + 8) = 1200 * P m := by rw [show m + 8 = m + 7 + 1 by omega, q7, x7]; linear_combination 2 * Q7
    have x8 : x (m + 8) = 3 := by simp only [x, show (m + 8) % 5 = 2 by omega]; norm_num
    have h8 := estep (m + 8) (by omega)
    have q8 := pstep (m + 8)
    have E9 : a (m + 9) = 3600 * a m + 15540 * P m := by rw [show m + 9 = m + 8 + 1 by omega, h8, x8]; linear_combination 3 * E8 + Q8
    have Q9 : P (m + 9) = 3600 * P m := by rw [show m + 9 = m + 8 + 1 by omega, q8, x8]; linear_combination 3 * Q8
    have x9 : x (m + 9) = 4 := by simp only [x, show (m + 9) % 5 = 3 by omega]; norm_num
    have h9 := estep (m + 9) (by omega)
    have q9 := pstep (m + 9)
    have E10 : a (m + 10) = 14400 * a m + 65760 * P m := by rw [show m + 10 = m + 9 + 1 by omega, h9, x9]; linear_combination 4 * E9 + Q9
    have Q10 : P (m + 10) = 14400 * P m := by rw [show m + 10 = m + 9 + 1 by omega, q9, x9]; linear_combination 4 * Q9
    linear_combination E10 - 240 * E5

theorem a0 : a 0 = 1 := by simp [a, Multiset.esymm, Multiset.powersetCard_zero_left]
theorem a1 : a 1 = 1 := by simp [a, Multiset.esymm, Multiset.powersetCard_zero_left]
theorem P1 : P 1 = x 0 := by simp [P, Multiset.esymm, Multiset.powersetCard_one]

end P203166

theorem OMA.solution : type_of% @OMA.S_oeis_a203166.main := by
  have hrec : ∀ n : ℕ, 11 ≤ n → a n = 240 * a (n - 5) - 14400 * a (n - 10) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
    rw [show m + 10 - 5 = m + 5 by omega, show m + 10 - 10 = m by omega]
    exact P203166.rec m (by omega)
  refine ⟨hrec, ?_⟩
  have v0 : a 0 = 1 := P203166.a0
  have v1 : a 1 = 1 := P203166.a1
  have p1 : P203166.P 1 = 1 := by rw [P203166.P1]; simp [x]
  have p2 : P203166.P 2 = 2 := by rw [P203166.pstep 1, p1]; simp [x]
  have v2 : a 2 = 3 := by rw [P203166.estep 1 (by norm_num), v1, p1]; simp [x]
  have p3 : P203166.P 3 = 6 := by rw [P203166.pstep 2, p2]; simp [x]
  have v3 : a 3 = 11 := by rw [P203166.estep 2 (by norm_num), v2, p2]; simp [x]
  have p4 : P203166.P 4 = 24 := by rw [P203166.pstep 3, p3]; simp [x]
  have v4 : a 4 = 50 := by rw [P203166.estep 3 (by norm_num), v3, p3]; simp [x]
  have p5 : P203166.P 5 = 120 := by rw [P203166.pstep 4, p4]; simp [x]
  have v5 : a 5 = 274 := by rw [P203166.estep 4 (by norm_num), v4, p4]; simp [x]
  have p6 : P203166.P 6 = 120 := by rw [P203166.pstep 5, p5]; simp [x]
  have v6 : a 6 = 394 := by rw [P203166.estep 5 (by norm_num), v5, p5]; simp [x]
  have p7 : P203166.P 7 = 240 := by rw [P203166.pstep 6, p6]; simp [x]
  have v7 : a 7 = 908 := by rw [P203166.estep 6 (by norm_num), v6, p6]; simp [x]
  have p8 : P203166.P 8 = 720 := by rw [P203166.pstep 7, p7]; simp [x]
  have v8 : a 8 = 2964 := by rw [P203166.estep 7 (by norm_num), v7, p7]; simp [x]
  have p9 : P203166.P 9 = 2880 := by rw [P203166.pstep 8, p8]; simp [x]
  have v9 : a 9 = 12576 := by rw [P203166.estep 8 (by norm_num), v8, p8]; simp [x]
  have p10 : P203166.P 10 = 14400 := by rw [P203166.pstep 9, p9]; simp [x]
  have v10 : a 10 = 65760 := by rw [P203166.estep 9 (by norm_num), v9, p9]; simp [x]
  have hp : ((-1 + 120 * X ^ 5) ^ 2 : PowerSeries ℤ) = 1 - C 240 * X ^ 5 + C 14400 * X ^ 10 := by
    simp only [map_ofNat]; ring
  have hq : ∀ F : PowerSeries ℤ, F * (1 - C 240 * X ^ 5 + C 14400 * X ^ 10) =
      F - C 240 * (F * X ^ 5) + C 14400 * (F * X ^ 10) := fun F => by ring
  have hr : (X + 3 * X ^ 2 + 11 * X ^ 3 + 50 * X ^ 4 + 274 * X ^ 5 + 154 * X ^ 6 + 188 * X ^ 7 + 324 * X ^ 8 + 576 * X ^ 9 : PowerSeries ℤ) = X + C 3 * X ^ 2 + C 11 * X ^ 3 + C 50 * X ^ 4 + C 274 * X ^ 5 + C 154 * X ^ 6 + C 188 * X ^ 7 + C 324 * X ^ 8 + C 576 * X ^ 9 := by
    simp only [map_ofNat]
  rw [hp, hq, hr]
  clear hp hq hr
  ext n
  simp only [map_sub, map_add, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_C_mul_X_pow,
    coeff_X_pow, coeff_X, coeff_C]
  rcases Nat.lt_or_ge n 11 with hn | hn
  · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
  · have h := hrec n (by omega)
    simp (disch := omega) only [if_pos, if_neg, Nat.sub_eq_zero_iff_le]
    simp only [add_zero, zero_add, neg_zero]
    linarith
