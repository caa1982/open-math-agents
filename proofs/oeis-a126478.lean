import OMAStatements.S_oeis_a126478
import Mathlib

open OMA.S_oeis_a126478

namespace W126478

theorem sumK (f : Fin 10 → ℕ) : ∑ x, f x = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_eight]; rfl

theorem sum_cons {n : ℕ} (F : (Fin (n + 1) → Fin 10) → ℕ) :
    ∑ f, F f = ∑ x : Fin 10, ∑ g : Fin n → Fin 10, F (Fin.cons x g) := by
  rw [← (Fin.consEquiv (fun _ => Fin 10)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem V_cc {n : ℕ} (x y : Fin 10) (h : Fin n → Fin 10) :
    (∀ i j : Fin (n + 2), (j : ℕ) = (i : ℕ) + 1 → close ((Fin.cons x (Fin.cons y h : Fin (n + 1) → Fin 10) : Fin (n + 2) → Fin 10) i) ((Fin.cons x (Fin.cons y h : Fin (n + 1) → Fin 10) : Fin (n + 2) → Fin 10) j)) ↔
      close x y ∧ (∀ i j : Fin (n + 1), (j : ℕ) = (i : ℕ) + 1 → close ((Fin.cons y h : Fin (n + 1) → Fin 10) i) ((Fin.cons y h : Fin (n + 1) → Fin 10) j)) := by
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

def G (n : ℕ) (x : Fin 10) : ℕ :=
  ∑ g : Fin n → Fin 10, if (∀ i j : Fin (n + 1), (j : ℕ) = (i : ℕ) + 1 → close ((Fin.cons x g : Fin (n + 1) → Fin 10) i) ((Fin.cons x g : Fin (n + 1) → Fin 10) j)) then 1 else 0

theorem a_succ (n : ℕ) : a (n + 1) = ∑ x, G n x := by
  rw [a, Finset.card_filter, sum_cons]; rfl

theorem G_succ (n : ℕ) (x : Fin 10) : G (n + 1) x = ∑ y, if close x y then G n y else 0 := by
  rw [G, sum_cons]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [V_cc]
  split_ifs with hxy
  · simp [hxy, G]
  · simp [hxy]

theorem G0 (x : Fin 10) : G 0 x = 1 := by
  rw [G, Fintype.sum_unique]
  simp

theorem A0 : a 0 = 1 := by
  rw [a, Finset.card_filter, Fintype.sum_unique]
  simp

theorem Gs (n : ℕ) :
    G (n + 1) 0 = G n 0 + G n 1 + G n 2 + G n 3 ∧
    G (n + 1) 1 = G n 0 + G n 1 + G n 2 + G n 3 + G n 4 ∧
    G (n + 1) 2 = G n 0 + G n 1 + G n 2 + G n 3 + G n 4 + G n 5 ∧
    G (n + 1) 3 = G n 0 + G n 1 + G n 2 + G n 3 + G n 4 + G n 5 + G n 6 ∧
    G (n + 1) 4 = G n 1 + G n 2 + G n 3 + G n 4 + G n 5 + G n 6 + G n 7 ∧
    G (n + 1) 5 = G n 2 + G n 3 + G n 4 + G n 5 + G n 6 + G n 7 + G n 8 ∧
    G (n + 1) 6 = G n 3 + G n 4 + G n 5 + G n 6 + G n 7 + G n 8 + G n 9 ∧
    G (n + 1) 7 = G n 4 + G n 5 + G n 6 + G n 7 + G n 8 + G n 9 ∧
    G (n + 1) 8 = G n 5 + G n 6 + G n 7 + G n 8 + G n 9 ∧
    G (n + 1) 9 = G n 6 + G n 7 + G n 8 + G n 9 := by
  simp only [G_succ, sumK]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [close]

theorem L0 : G 0 0 = 1 ∧ G 0 1 = 1 ∧ G 0 2 = 1 ∧ G 0 3 = 1 ∧ G 0 4 = 1 ∧ G 0 5 = 1 ∧ G 0 6 = 1 ∧ G 0 7 = 1 ∧ G 0 8 = 1 ∧ G 0 9 = 1 := ⟨G0 _, G0 _, G0 _, G0 _, G0 _, G0 _, G0 _, G0 _, G0 _, G0 _⟩

theorem L1 : G 1 0 = 4 ∧ G 1 1 = 5 ∧ G 1 2 = 6 ∧ G 1 3 = 7 ∧ G 1 4 = 7 ∧ G 1 5 = 7 ∧ G 1 6 = 7 ∧ G 1 7 = 6 ∧ G 1 8 = 5 ∧ G 1 9 = 4 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := Gs 0
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := L0
  refine ⟨by rw [e0]; simp only [f0, f1, f2, f3], by rw [e1]; simp only [f0, f1, f2, f3, f4], by rw [e2]; simp only [f0, f1, f2, f3, f4, f5], by rw [e3]; simp only [f0, f1, f2, f3, f4, f5, f6], by rw [e4]; simp only [f1, f2, f3, f4, f5, f6, f7], by rw [e5]; simp only [f2, f3, f4, f5, f6, f7, f8], by rw [e6]; simp only [f3, f4, f5, f6, f7, f8, f9], by rw [e7]; simp only [f4, f5, f6, f7, f8, f9], by rw [e8]; simp only [f5, f6, f7, f8, f9], by rw [e9]; simp only [f6, f7, f8, f9]⟩

theorem L2 : G 2 0 = 22 ∧ G 2 1 = 29 ∧ G 2 2 = 36 ∧ G 2 3 = 43 ∧ G 2 4 = 45 ∧ G 2 5 = 45 ∧ G 2 6 = 43 ∧ G 2 7 = 36 ∧ G 2 8 = 29 ∧ G 2 9 = 22 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := Gs 1
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := L1
  refine ⟨by rw [e0]; simp only [f0, f1, f2, f3], by rw [e1]; simp only [f0, f1, f2, f3, f4], by rw [e2]; simp only [f0, f1, f2, f3, f4, f5], by rw [e3]; simp only [f0, f1, f2, f3, f4, f5, f6], by rw [e4]; simp only [f1, f2, f3, f4, f5, f6, f7], by rw [e5]; simp only [f2, f3, f4, f5, f6, f7, f8], by rw [e6]; simp only [f3, f4, f5, f6, f7, f8, f9], by rw [e7]; simp only [f4, f5, f6, f7, f8, f9], by rw [e8]; simp only [f5, f6, f7, f8, f9], by rw [e9]; simp only [f6, f7, f8, f9]⟩

theorem L3 : G 3 0 = 130 ∧ G 3 1 = 175 ∧ G 3 2 = 220 ∧ G 3 3 = 263 ∧ G 3 4 = 277 ∧ G 3 5 = 277 ∧ G 3 6 = 263 ∧ G 3 7 = 220 ∧ G 3 8 = 175 ∧ G 3 9 = 130 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := Gs 2
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := L2
  refine ⟨by rw [e0]; simp only [f0, f1, f2, f3], by rw [e1]; simp only [f0, f1, f2, f3, f4], by rw [e2]; simp only [f0, f1, f2, f3, f4, f5], by rw [e3]; simp only [f0, f1, f2, f3, f4, f5, f6], by rw [e4]; simp only [f1, f2, f3, f4, f5, f6, f7], by rw [e5]; simp only [f2, f3, f4, f5, f6, f7, f8], by rw [e6]; simp only [f3, f4, f5, f6, f7, f8, f9], by rw [e7]; simp only [f4, f5, f6, f7, f8, f9], by rw [e8]; simp only [f5, f6, f7, f8, f9], by rw [e9]; simp only [f6, f7, f8, f9]⟩

theorem L4 : G 4 0 = 788 ∧ G 4 1 = 1065 ∧ G 4 2 = 1342 ∧ G 4 3 = 1605 ∧ G 4 4 = 1695 ∧ G 4 5 = 1695 ∧ G 4 6 = 1605 ∧ G 4 7 = 1342 ∧ G 4 8 = 1065 ∧ G 4 9 = 788 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := Gs 3
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := L3
  refine ⟨by rw [e0]; simp only [f0, f1, f2, f3], by rw [e1]; simp only [f0, f1, f2, f3, f4], by rw [e2]; simp only [f0, f1, f2, f3, f4, f5], by rw [e3]; simp only [f0, f1, f2, f3, f4, f5, f6], by rw [e4]; simp only [f1, f2, f3, f4, f5, f6, f7], by rw [e5]; simp only [f2, f3, f4, f5, f6, f7, f8], by rw [e6]; simp only [f3, f4, f5, f6, f7, f8, f9], by rw [e7]; simp only [f4, f5, f6, f7, f8, f9], by rw [e8]; simp only [f5, f6, f7, f8, f9], by rw [e9]; simp only [f6, f7, f8, f9]⟩

theorem L5 : G 5 0 = 4800 ∧ G 5 1 = 6495 ∧ G 5 2 = 8190 ∧ G 5 3 = 9795 ∧ G 5 4 = 10349 ∧ G 5 5 = 10349 ∧ G 5 6 = 9795 ∧ G 5 7 = 8190 ∧ G 5 8 = 6495 ∧ G 5 9 = 4800 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := Gs 4
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := L4
  refine ⟨by rw [e0]; simp only [f0, f1, f2, f3], by rw [e1]; simp only [f0, f1, f2, f3, f4], by rw [e2]; simp only [f0, f1, f2, f3, f4, f5], by rw [e3]; simp only [f0, f1, f2, f3, f4, f5, f6], by rw [e4]; simp only [f1, f2, f3, f4, f5, f6, f7], by rw [e5]; simp only [f2, f3, f4, f5, f6, f7, f8], by rw [e6]; simp only [f3, f4, f5, f6, f7, f8, f9], by rw [e7]; simp only [f4, f5, f6, f7, f8, f9], by rw [e8]; simp only [f5, f6, f7, f8, f9], by rw [e9]; simp only [f6, f7, f8, f9]⟩

theorem A1 : a 1 = 10 := by
  rw [a_succ, sumK]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := L0
  simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9]

theorem A2 : a 2 = 58 := by
  rw [a_succ, sumK]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := L1
  simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9]

theorem A3 : a 3 = 350 := by
  rw [a_succ, sumK]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := L2
  simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9]

theorem A4 : a 4 = 2130 := by
  rw [a_succ, sumK]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := L3
  simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9]

theorem A5 : a 5 = 12990 := by
  rw [a_succ, sumK]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := L4
  simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9]

theorem A6 : a 6 = 79258 := by
  rw [a_succ, sumK]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := L5
  simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9]

set_option maxHeartbeats 0 in
theorem arec (m : ℕ) : (a (m + 5) : ℤ) = 7 * (a (m + 4) : ℤ) - 4 * (a (m + 3) : ℤ) - 10 * (a (m + 2) : ℤ) + 6 * (a (m + 1) : ℤ) := by
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
  obtain ⟨E0_0, E0_1, E0_2, E0_3, E0_4, E0_5, E0_6, E0_7, E0_8, E0_9⟩ := Gs (m + 0)
  obtain ⟨E1_0, E1_1, E1_2, E1_3, E1_4, E1_5, E1_6, E1_7, E1_8, E1_9⟩ := Gs (m + 1)
  obtain ⟨E2_0, E2_1, E2_2, E2_3, E2_4, E2_5, E2_6, E2_7, E2_8, E2_9⟩ := Gs (m + 2)
  obtain ⟨E3_0, E3_1, E3_2, E3_3, E3_4, E3_5, E3_6, E3_7, E3_8, E3_9⟩ := Gs (m + 3)
  simp only [show ∀ t : ℕ, m + t + 1 = m + (t + 1) from fun t => rfl, Nat.add_zero] at *
  simp only [h0, h1, h2, h3, h4]
  zify at *
  push_cast
  linear_combination (2 : ℤ) * E0_0 + (2 : ℤ) * E0_1 + (2 : ℤ) * E0_2 + (2 : ℤ) * E0_7 + (2 : ℤ) * E0_8 + (2 : ℤ) * E0_9 + (-2 : ℤ) * E1_0 + (-2 : ℤ) * E1_1 + (-2 : ℤ) * E1_2 + (-2 : ℤ) * E1_3 + (-2 : ℤ) * E1_6 + (-2 : ℤ) * E1_7 + (-2 : ℤ) * E1_8 + (-2 : ℤ) * E1_9 + (-3 : ℤ) * E2_0 + (-2 : ℤ) * E2_1 + (-1 : ℤ) * E2_2 + (-1 : ℤ) * E2_7 + (-2 : ℤ) * E2_8 + (-3 : ℤ) * E2_9 + (1 : ℤ) * E3_0 + (1 : ℤ) * E3_1 + (1 : ℤ) * E3_2 + (1 : ℤ) * E3_3 + (1 : ℤ) * E3_4 + (1 : ℤ) * E3_5 + (1 : ℤ) * E3_6 + (1 : ℤ) * E3_7 + (1 : ℤ) * E3_8 + (1 : ℤ) * E3_9

end W126478

open W126478 PowerSeries in
set_option maxHeartbeats 0 in
theorem OMA.solution : type_of% @OMA.S_oeis_a126478.main := by
  have hrec : ∀ n : ℕ, 5 ≤ n → (a n : ℤ) = 7 * (a (n - 1) : ℤ) - 4 * (a (n - 2) : ℤ) - 10 * (a (n - 3) : ℤ) + 6 * (a (n - 4) : ℤ) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    rw [arec m]
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
  have hrecQ : ∀ n : ℕ, 5 ≤ n → (a n : ℚ) = 7 * (a (n - 1) : ℚ) - 4 * (a (n - 2) : ℚ) - 10 * (a (n - 3) : ℚ) + 6 * (a (n - 4) : ℚ) := by
    intro n hn; exact_mod_cast hrec n hn
  refine ⟨?_, ?_⟩
  · have hp : ((1 - 7 * X + 4 * X ^ 2 + 10 * X ^ 3 - 6 * X ^ 4) : PowerSeries ℚ) = 1 - PowerSeries.C (7 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (4 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (10 : ℚ) * PowerSeries.X ^ 3 - PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 4 := by
      (try simp only [map_ofNat, map_one, one_mul, pow_one]) <;> ring
    have hr : (1 + 3 * X - 8 * X ^ 2 - 6 * X ^ 3 + 6 * X ^ 4 : PowerSeries ℚ) = 1 + PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (8 : ℚ) * PowerSeries.X ^ 2 - PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 4 := by
      (try simp only [map_ofNat, map_one, one_mul, pow_one]) <;> ring
    have hq : ∀ F : PowerSeries ℚ, F * (1 - PowerSeries.C (7 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (4 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (10 : ℚ) * PowerSeries.X ^ 3 - PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 4) = F - PowerSeries.C (7 : ℚ) * (F * PowerSeries.X ^ 1) + PowerSeries.C (4 : ℚ) * (F * PowerSeries.X ^ 2) + PowerSeries.C (10 : ℚ) * (F * PowerSeries.X ^ 3) - PowerSeries.C (6 : ℚ) * (F * PowerSeries.X ^ 4) := fun F => by ring
    rw [hp, hr, hq]
    ext n
    simp only [map_sub, map_add, map_neg, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_C_mul,
      PowerSeries.coeff_mk, PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
    rcases Nat.lt_or_ge n 7 with hn | hn
    · interval_cases n <;> simp [W126478.A0, W126478.A1, W126478.A2, W126478.A3, W126478.A4, W126478.A5, W126478.A6] <;> norm_num
    · have h' := hrecQ n (by omega)
      simp (disch := omega) only [if_pos, if_neg, PowerSeries.coeff_C]
      linarith
  · intro n hn
    rcases Nat.lt_or_ge n 5 with h | h
    · interval_cases n <;> simp [W126478.A0, W126478.A1, W126478.A2, W126478.A3, W126478.A4, W126478.A5, W126478.A6]
    · have := hrec n h
      linarith
