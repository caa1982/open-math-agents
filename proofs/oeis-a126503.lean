import OMAStatements.S_oeis_a126503
import Mathlib

open OMA.S_oeis_a126503

namespace W126503

theorem iv (n : ℕ) (w : Fin n → Fin 8) : isValid n w ↔ (∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → adjOk (w i) (w j)) := by
  constructor
  · intro h i j hij
    obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    simp only at hij
    subst hij
    exact h ⟨i, by omega⟩
  · intro h i
    exact h _ _ rfl

theorem adj_iff (x y : Fin 8) : adjOk x y ↔ (x : ℕ) ≤ (y : ℕ) + 4 ∧ (y : ℕ) ≤ (x : ℕ) + 4 := by
  unfold adjOk
  omega

theorem a_sum (n : ℕ) : a n = ∑ f : Fin n → Fin 8, if (∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → adjOk (f i) (f j)) then 1 else 0 := by
  rw [a, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro f _
  by_cases h : isValid n f
  · rw [if_pos h, if_pos ((iv n f).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((iv n f).mpr h'))]

theorem sum_cons {n : ℕ} (F : (Fin (n + 1) → Fin 8) → ℕ) :
    ∑ f, F f = ∑ x : Fin 8, ∑ g : Fin n → Fin 8, F (Fin.cons x g) := by
  rw [← (Fin.consEquiv (fun _ => Fin 8)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem V_cc {n : ℕ} (x y : Fin 8) (h : Fin n → Fin 8) :
    (∀ i j : Fin (n + 2), (j : ℕ) = (i : ℕ) + 1 → adjOk ((Fin.cons x (Fin.cons y h : Fin (n + 1) → Fin 8) : Fin (n + 2) → Fin 8) i) ((Fin.cons x (Fin.cons y h : Fin (n + 1) → Fin 8) : Fin (n + 2) → Fin 8) j)) ↔
      adjOk x y ∧ (∀ i j : Fin (n + 1), (j : ℕ) = (i : ℕ) + 1 → adjOk ((Fin.cons y h : Fin (n + 1) → Fin 8) i) ((Fin.cons y h : Fin (n + 1) → Fin 8) j)) := by
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

def G (n : ℕ) (x : Fin 8) : ℕ :=
  ∑ g : Fin n → Fin 8, if (∀ i j : Fin (n + 1), (j : ℕ) = (i : ℕ) + 1 → adjOk ((Fin.cons x g : Fin (n + 1) → Fin 8) i) ((Fin.cons x g : Fin (n + 1) → Fin 8) j)) then 1 else 0

theorem a_succ (n : ℕ) : a (n + 1) = ∑ x, G n x := by
  rw [a_sum, sum_cons]; rfl

theorem G_succ (n : ℕ) (x : Fin 8) : G (n + 1) x = ∑ y, if adjOk x y then G n y else 0 := by
  rw [G, sum_cons]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [V_cc]
  split_ifs with hxy
  · simp [hxy, G]
  · simp [hxy]

theorem a0 : a 0 = 1 := by
  rw [a_sum, Fintype.sum_unique]
  simp

theorem G0 (x : Fin 8) : G 0 x = 1 := by
  rw [G, Fintype.sum_unique]
  simp

theorem Gs (n : ℕ) :
    G (n + 1) 0 = G n 0 + G n 1 + G n 2 + G n 3 + G n 4 ∧
    G (n + 1) 1 = G n 0 + G n 1 + G n 2 + G n 3 + G n 4 + G n 5 ∧
    G (n + 1) 2 = G n 0 + G n 1 + G n 2 + G n 3 + G n 4 + G n 5 + G n 6 ∧
    G (n + 1) 3 = G n 0 + G n 1 + G n 2 + G n 3 + G n 4 + G n 5 + G n 6 + G n 7 ∧
    G (n + 1) 4 = G n 0 + G n 1 + G n 2 + G n 3 + G n 4 + G n 5 + G n 6 + G n 7 ∧
    G (n + 1) 5 = G n 1 + G n 2 + G n 3 + G n 4 + G n 5 + G n 6 + G n 7 ∧
    G (n + 1) 6 = G n 2 + G n 3 + G n 4 + G n 5 + G n 6 + G n 7 ∧
    G (n + 1) 7 = G n 3 + G n 4 + G n 5 + G n 6 + G n 7 := by
  simp only [G_succ, Fin.sum_univ_eight]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [adj_iff]

theorem L0 : G 0 0 = 1 ∧ G 0 1 = 1 ∧ G 0 2 = 1 ∧ G 0 3 = 1 ∧ G 0 4 = 1 ∧ G 0 5 = 1 ∧ G 0 6 = 1 ∧ G 0 7 = 1 := by
  refine ⟨G0 _, G0 _, G0 _, G0 _, G0 _, G0 _, G0 _, G0 _⟩

theorem L1 : G 1 0 = 5 ∧ G 1 1 = 6 ∧ G 1 2 = 7 ∧ G 1 3 = 8 ∧ G 1 4 = 8 ∧ G 1 5 = 7 ∧ G 1 6 = 6 ∧ G 1 7 = 5 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := Gs 0
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := L0
  refine ⟨by rw [e0]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e1]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e2]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e3]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e4]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e5]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e6]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e7]; simp only [f0, f1, f2, f3, f4, f5, f6, f7]⟩

theorem L2 : G 2 0 = 34 ∧ G 2 1 = 41 ∧ G 2 2 = 47 ∧ G 2 3 = 52 ∧ G 2 4 = 52 ∧ G 2 5 = 47 ∧ G 2 6 = 41 ∧ G 2 7 = 34 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := Gs 1
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := L1
  refine ⟨by rw [e0]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e1]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e2]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e3]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e4]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e5]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e6]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e7]; simp only [f0, f1, f2, f3, f4, f5, f6, f7]⟩

theorem L3 : G 3 0 = 226 ∧ G 3 1 = 273 ∧ G 3 2 = 314 ∧ G 3 3 = 348 ∧ G 3 4 = 348 ∧ G 3 5 = 314 ∧ G 3 6 = 273 ∧ G 3 7 = 226 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := Gs 2
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := L2
  refine ⟨by rw [e0]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e1]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e2]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e3]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e4]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e5]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e6]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e7]; simp only [f0, f1, f2, f3, f4, f5, f6, f7]⟩

theorem L4 : G 4 0 = 1509 ∧ G 4 1 = 1823 ∧ G 4 2 = 2096 ∧ G 4 3 = 2322 ∧ G 4 4 = 2322 ∧ G 4 5 = 2096 ∧ G 4 6 = 1823 ∧ G 4 7 = 1509 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := Gs 3
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := L3
  refine ⟨by rw [e0]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e1]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e2]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e3]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e4]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e5]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e6]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e7]; simp only [f0, f1, f2, f3, f4, f5, f6, f7]⟩

theorem L5 : G 5 0 = 10072 ∧ G 5 1 = 12168 ∧ G 5 2 = 13991 ∧ G 5 3 = 15500 ∧ G 5 4 = 15500 ∧ G 5 5 = 13991 ∧ G 5 6 = 12168 ∧ G 5 7 = 10072 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := Gs 4
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := L4
  refine ⟨by rw [e0]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e1]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e2]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e3]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e4]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e5]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e6]; simp only [f0, f1, f2, f3, f4, f5, f6, f7], by rw [e7]; simp only [f0, f1, f2, f3, f4, f5, f6, f7]⟩

theorem A1 : a 1 = 8 := by
  rw [a_succ, Fin.sum_univ_eight]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := L0
  simp only [f0, f1, f2, f3, f4, f5, f6, f7]

theorem A2 : a 2 = 52 := by
  rw [a_succ, Fin.sum_univ_eight]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := L1
  simp only [f0, f1, f2, f3, f4, f5, f6, f7]

theorem A3 : a 3 = 348 := by
  rw [a_succ, Fin.sum_univ_eight]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := L2
  simp only [f0, f1, f2, f3, f4, f5, f6, f7]

theorem A4 : a 4 = 2322 := by
  rw [a_succ, Fin.sum_univ_eight]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := L3
  simp only [f0, f1, f2, f3, f4, f5, f6, f7]

theorem A5 : a 5 = 15500 := by
  rw [a_succ, Fin.sum_univ_eight]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := L4
  simp only [f0, f1, f2, f3, f4, f5, f6, f7]

theorem A6 : a 6 = 103462 := by
  rw [a_succ, Fin.sum_univ_eight]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := L5
  simp only [f0, f1, f2, f3, f4, f5, f6, f7]

theorem arec (m : ℕ) : (a (m + 5) : ℤ) = 6 * (a (m + 4) : ℤ) + 5 * (a (m + 3) : ℤ) - 3 * (a (m + 2) : ℤ) - 2 * (a (m + 1) : ℤ) := by
  have h0 := a_succ (m + 0)
  rw [Fin.sum_univ_eight] at h0
  have h1 := a_succ (m + 1)
  rw [Fin.sum_univ_eight] at h1
  have h2 := a_succ (m + 2)
  rw [Fin.sum_univ_eight] at h2
  have h3 := a_succ (m + 3)
  rw [Fin.sum_univ_eight] at h3
  have h4 := a_succ (m + 4)
  rw [Fin.sum_univ_eight] at h4
  obtain ⟨E0_0, E0_1, E0_2, E0_3, E0_4, E0_5, E0_6, E0_7⟩ := Gs (m + 0)
  obtain ⟨E1_0, E1_1, E1_2, E1_3, E1_4, E1_5, E1_6, E1_7⟩ := Gs (m + 1)
  obtain ⟨E2_0, E2_1, E2_2, E2_3, E2_4, E2_5, E2_6, E2_7⟩ := Gs (m + 2)
  obtain ⟨E3_0, E3_1, E3_2, E3_3, E3_4, E3_5, E3_6, E3_7⟩ := Gs (m + 3)
  simp only [show ∀ t : ℕ, m + t + 1 = m + (t + 1) from fun t => rfl, Nat.add_zero] at *
  rw [h0, h1, h2, h3, h4]
  zify at *
  push_cast
  linear_combination (-1 : ℤ) * E0_3 + (-1 : ℤ) * E0_4 + (-1 : ℤ) * E1_0 + (-1 : ℤ) * E1_3 + (-1 : ℤ) * E1_4 + (-1 : ℤ) * E1_7 + (-1 : ℤ) * E2_0 + (1 : ℤ) * E2_2 + (2 : ℤ) * E2_3 + (2 : ℤ) * E2_4 + (1 : ℤ) * E2_5 + (-1 : ℤ) * E2_7 + (1 : ℤ) * E3_0 + (1 : ℤ) * E3_1 + (1 : ℤ) * E3_2 + (1 : ℤ) * E3_3 + (1 : ℤ) * E3_4 + (1 : ℤ) * E3_5 + (1 : ℤ) * E3_6 + (1 : ℤ) * E3_7

end W126503

open W126503 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a126503.main := by
  have hrec : ∀ n : ℕ, 5 ≤ n → (a n : ℤ) = 6 * (a (n - 1) : ℤ) + 5 * (a (n - 2) : ℤ) - 3 * (a (n - 3) : ℤ) - 2 * (a (n - 4) : ℤ) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    rw [arec m]
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
  refine ⟨?_, ?_⟩
  · have hp : (1 - 6 * X - 5 * X ^ 2 + 3 * X ^ 3 + 2 * X ^ 4 : PowerSeries ℚ) = 1 - PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (5 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 4 := by
      (try simp only [map_ofNat, map_one, one_mul, pow_one]) <;> ring
    have hr : (1 + 2 * X - X ^ 2 - X ^ 3 : PowerSeries ℚ) = 1 + PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.X ^ 2 - PowerSeries.X ^ 3 := by
      (try simp only [map_ofNat, map_one, one_mul, pow_one]) <;> ring
    have hq : ∀ F : PowerSeries ℚ, F * (1 - PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (5 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 4) = F - PowerSeries.C (6 : ℚ) * (F * PowerSeries.X ^ 1) - PowerSeries.C (5 : ℚ) * (F * PowerSeries.X ^ 2) + PowerSeries.C (3 : ℚ) * (F * PowerSeries.X ^ 3) + PowerSeries.C (2 : ℚ) * (F * PowerSeries.X ^ 4) := fun F => by ring
    rw [hp, hr, hq]
    ext n
    simp only [map_sub, map_add, map_neg, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_C_mul,
      PowerSeries.coeff_mk, PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
    rcases Nat.lt_or_ge n 7 with hn | hn
    · interval_cases n <;> simp [a0, W126503.A1, W126503.A2, W126503.A3, W126503.A4, W126503.A5, W126503.A6] <;> norm_num
    · have h := hrec n (by omega)
      have h' : (a n : ℚ) = 6 * (a (n - 1) : ℚ) + 5 * (a (n - 2) : ℚ) - 3 * (a (n - 3) : ℚ) - 2 * (a (n - 4) : ℚ) := by exact_mod_cast h
      simp (disch := omega) only [if_pos, if_neg, PowerSeries.coeff_C]
      linarith
  · intro n hn
    rcases Nat.lt_or_ge n 5 with h | h
    · interval_cases n <;> simp [a0, W126503.A1, W126503.A2, W126503.A3, W126503.A4, W126503.A5, W126503.A6]
    · have := hrec n h
      linarith
