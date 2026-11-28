import OMAStatements.S_oeis_a126396
import Mathlib

open OMA.S_oeis_a126396

namespace W126396

theorem sumK (f : Fin 9 → ℕ) : ∑ x, f x = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_eight]
  rfl

theorem a_sum (n : ℕ) : a n = ∑ f : Fin n → Fin 9, if (∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → close (f i) (f j)) then 1 else 0 := by
  rw [a, Finset.card_filter]

theorem sum_cons {n : ℕ} (F : (Fin (n + 1) → Fin 9) → ℕ) :
    ∑ f, F f = ∑ x : Fin 9, ∑ g : Fin n → Fin 9, F (Fin.cons x g) := by
  rw [← (Fin.consEquiv (fun _ => Fin 9)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem V_cc {n : ℕ} (x y : Fin 9) (h : Fin n → Fin 9) :
    (∀ i j : Fin (n + 2), (j : ℕ) = (i : ℕ) + 1 → close ((Fin.cons x (Fin.cons y h : Fin (n + 1) → Fin 9) : Fin (n + 2) → Fin 9) i) ((Fin.cons x (Fin.cons y h : Fin (n + 1) → Fin 9) : Fin (n + 2) → Fin 9) j)) ↔
      close x y ∧ (∀ i j : Fin (n + 1), (j : ℕ) = (i : ℕ) + 1 → close ((Fin.cons y h : Fin (n + 1) → Fin 9) i) ((Fin.cons y h : Fin (n + 1) → Fin 9) j)) := by
  constructor
  · intro H
    refine ⟨?_, fun i j hij => ?_⟩
    · have := H 0 1 (by simp)
      simpa using this
    · have := H i.succ j.succ (by simp [hij])
      simpa using this
  · rintro ⟨hxy, H⟩ i j hij
    induction i using Fin.cases with
    | zero =>
      have hj : j = 1 := Fin.ext (by simp at hij; simp [hij])
      subst hj
      simpa using hxy
    | succ i =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        have := H i j (by simp at hij; omega)
        simpa using this

def G (n : ℕ) (x : Fin 9) : ℕ :=
  ∑ g : Fin n → Fin 9, if (∀ i j : Fin (n + 1), (j : ℕ) = (i : ℕ) + 1 → close ((Fin.cons x g : Fin (n + 1) → Fin 9) i) ((Fin.cons x g : Fin (n + 1) → Fin 9) j)) then 1 else 0

theorem a_succ (n : ℕ) : a (n + 1) = ∑ x, G n x := by
  rw [a_sum, sum_cons]; rfl

theorem G_succ (n : ℕ) (x : Fin 9) : G (n + 1) x = ∑ y, if close x y then G n y else 0 := by
  rw [G, sum_cons]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [V_cc]
  split_ifs with hxy
  · simp [hxy, G]
  · simp [hxy]

theorem a0 : a 0 = 1 := by
  rw [a_sum, Fintype.sum_unique]
  simp

theorem G0 (x : Fin 9) : G 0 x = 1 := by
  rw [G, Fintype.sum_unique]
  simp

theorem Gs (n : ℕ) :
    G (n + 1) 0 = G n 0 + G n 1 + G n 2 ∧
    G (n + 1) 1 = G n 0 + G n 1 + G n 2 + G n 3 ∧
    G (n + 1) 2 = G n 0 + G n 1 + G n 2 + G n 3 + G n 4 ∧
    G (n + 1) 3 = G n 1 + G n 2 + G n 3 + G n 4 + G n 5 ∧
    G (n + 1) 4 = G n 2 + G n 3 + G n 4 + G n 5 + G n 6 ∧
    G (n + 1) 5 = G n 3 + G n 4 + G n 5 + G n 6 + G n 7 ∧
    G (n + 1) 6 = G n 4 + G n 5 + G n 6 + G n 7 + G n 8 ∧
    G (n + 1) 7 = G n 5 + G n 6 + G n 7 + G n 8 ∧
    G (n + 1) 8 = G n 6 + G n 7 + G n 8 := by
  simp only [G_succ, sumK]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [close]

theorem L0 : G 0 0 = 1 ∧ G 0 1 = 1 ∧ G 0 2 = 1 ∧ G 0 3 = 1 ∧ G 0 4 = 1 ∧ G 0 5 = 1 ∧ G 0 6 = 1 ∧ G 0 7 = 1 ∧ G 0 8 = 1 := by
  refine ⟨G0 _, G0 _, G0 _, G0 _, G0 _, G0 _, G0 _, G0 _, G0 _⟩

theorem L1 : G 1 0 = 3 ∧ G 1 1 = 4 ∧ G 1 2 = 5 ∧ G 1 3 = 5 ∧ G 1 4 = 5 ∧ G 1 5 = 5 ∧ G 1 6 = 5 ∧ G 1 7 = 4 ∧ G 1 8 = 3 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := Gs 0
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8⟩ := L0
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem L2 : G 2 0 = 12 ∧ G 2 1 = 17 ∧ G 2 2 = 22 ∧ G 2 3 = 24 ∧ G 2 4 = 25 ∧ G 2 5 = 24 ∧ G 2 6 = 22 ∧ G 2 7 = 17 ∧ G 2 8 = 12 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := Gs 1
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8⟩ := L1
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem L3 : G 3 0 = 51 ∧ G 3 1 = 75 ∧ G 3 2 = 100 ∧ G 3 3 = 112 ∧ G 3 4 = 117 ∧ G 3 5 = 112 ∧ G 3 6 = 100 ∧ G 3 7 = 75 ∧ G 3 8 = 51 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := Gs 2
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8⟩ := L2
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem L4 : G 4 0 = 226 ∧ G 4 1 = 338 ∧ G 4 2 = 455 ∧ G 4 3 = 516 ∧ G 4 4 = 541 ∧ G 4 5 = 516 ∧ G 4 6 = 455 ∧ G 4 7 = 338 ∧ G 4 8 = 226 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := Gs 3
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8⟩ := L3
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem L5 : G 5 0 = 1019 ∧ G 5 1 = 1535 ∧ G 5 2 = 2076 ∧ G 5 3 = 2366 ∧ G 5 4 = 2483 ∧ G 5 5 = 2366 ∧ G 5 6 = 2076 ∧ G 5 7 = 1535 ∧ G 5 8 = 1019 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := Gs 4
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8⟩ := L4
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem L6 : G 6 0 = 4630 ∧ G 6 1 = 6996 ∧ G 6 2 = 9479 ∧ G 6 3 = 10826 ∧ G 6 4 = 11367 ∧ G 6 5 = 10826 ∧ G 6 6 = 9479 ∧ G 6 7 = 6996 ∧ G 6 8 = 4630 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := Gs 5
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8⟩ := L5
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem A1 : a 1 = 9 := by
  rw [a_succ, sumK]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8⟩ := L0
  linarith

theorem A2 : a 2 = 39 := by
  rw [a_succ, sumK]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8⟩ := L1
  linarith

theorem A3 : a 3 = 175 := by
  rw [a_succ, sumK]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8⟩ := L2
  linarith

theorem A4 : a 4 = 793 := by
  rw [a_succ, sumK]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8⟩ := L3
  linarith

theorem A5 : a 5 = 3611 := by
  rw [a_succ, sumK]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8⟩ := L4
  linarith

theorem A6 : a 6 = 16475 := by
  rw [a_succ, sumK]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8⟩ := L5
  linarith

theorem A7 : a 7 = 75229 := by
  rw [a_succ, sumK]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8⟩ := L6
  linarith

theorem arec (m : ℕ) : (a (m + 6) : ℤ) = 6 * (a (m + 5) : ℤ) - 5 * (a (m + 4) : ℤ) - 8 * (a (m + 3) : ℤ) + 4 * (a (m + 2) : ℤ) + 2 * (a (m + 1) : ℤ) := by
  have h0 := a_succ (m + 0)
  rw [sumK] at h0
  have h1 := a_succ (m + 1)
  rw [sumK] at h1
  have h2 := a_succ (m + 2)
  rw [sumK] at h2
  have h3 := a_succ (m + 3)
  rw [sumK] at h3
  have h4 := a_succ (m + 4)
  rw [sumK] at h4
  have h5 := a_succ (m + 5)
  rw [sumK] at h5
  obtain ⟨E0_0, E0_1, E0_2, E0_3, E0_4, E0_5, E0_6, E0_7, E0_8⟩ := Gs (m + 0)
  obtain ⟨E1_0, E1_1, E1_2, E1_3, E1_4, E1_5, E1_6, E1_7, E1_8⟩ := Gs (m + 1)
  obtain ⟨E2_0, E2_1, E2_2, E2_3, E2_4, E2_5, E2_6, E2_7, E2_8⟩ := Gs (m + 2)
  obtain ⟨E3_0, E3_1, E3_2, E3_3, E3_4, E3_5, E3_6, E3_7, E3_8⟩ := Gs (m + 3)
  obtain ⟨E4_0, E4_1, E4_2, E4_3, E4_4, E4_5, E4_6, E4_7, E4_8⟩ := Gs (m + 4)
  simp only [show ∀ t : ℕ, m + t + 1 = m + (t + 1) from fun t => rfl, Nat.add_zero] at *
  rw [h0, h1, h2, h3, h4, h5]
  push_cast
  linarith

end W126396

open W126396 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a126396.main := by
  have hrec : ∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 6 * (a (n - 1) : ℤ) - 5 * (a (n - 2) : ℤ) - 8 * (a (n - 3) : ℤ) + 4 * (a (n - 4) : ℤ) + 2 * (a (n - 5) : ℤ) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [arec m]
    simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega]
  refine ⟨?_, ?_⟩
  · have hp : (1 - 6 * X + 5 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4 - 2 * X ^ 5 : PowerSeries ℚ) = 1 - PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (5 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (8 : ℚ) * PowerSeries.X ^ 3 - PowerSeries.C (4 : ℚ) * PowerSeries.X ^ 4 - PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 5 := by
      (try simp only [map_ofNat, map_one, one_mul, pow_one]) <;> ring
    have hr : (1 + 3 * X - 10 * X ^ 2 - 6 * X ^ 3 + 6 * X ^ 4 + 2 * X ^ 5 : PowerSeries ℚ) = 1 + PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (10 : ℚ) * PowerSeries.X ^ 2 - PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 5 := by
      (try simp only [map_ofNat, map_one, one_mul, pow_one]) <;> ring
    have hq : ∀ F : PowerSeries ℚ, F * (1 - PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (5 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (8 : ℚ) * PowerSeries.X ^ 3 - PowerSeries.C (4 : ℚ) * PowerSeries.X ^ 4 - PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 5) = F - PowerSeries.C (6 : ℚ) * (F * PowerSeries.X ^ 1) + PowerSeries.C (5 : ℚ) * (F * PowerSeries.X ^ 2) + PowerSeries.C (8 : ℚ) * (F * PowerSeries.X ^ 3) - PowerSeries.C (4 : ℚ) * (F * PowerSeries.X ^ 4) - PowerSeries.C (2 : ℚ) * (F * PowerSeries.X ^ 5) := fun F => by ring
    rw [hp, hr, hq]
    ext n
    simp only [map_sub, map_add, map_neg, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_C_mul,
      PowerSeries.coeff_mk, PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
    rcases Nat.lt_or_ge n 8 with hn | hn
    · interval_cases n <;> simp [a0, W126396.A1, W126396.A2, W126396.A3, W126396.A4, W126396.A5, W126396.A6, W126396.A7] <;> norm_num
    · have h := hrec n (by omega)
      have h' : (a n : ℚ) = 6 * (a (n - 1) : ℚ) - 5 * (a (n - 2) : ℚ) - 8 * (a (n - 3) : ℚ) + 4 * (a (n - 4) : ℚ) + 2 * (a (n - 5) : ℚ) := by exact_mod_cast h
      simp (disch := omega) only [if_pos, if_neg, PowerSeries.coeff_C]
      linarith
  · intro n hn
    rcases Nat.lt_or_ge n 6 with h | h
    · interval_cases n <;> simp [a0, W126396.A1, W126396.A2, W126396.A3, W126396.A4, W126396.A5, W126396.A6, W126396.A7]
    · have := hrec n h
      linarith
