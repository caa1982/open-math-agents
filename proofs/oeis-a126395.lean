import OMAStatements.S_oeis_a126395
import Mathlib

open OMA.S_oeis_a126395

namespace W126395

theorem a_sum (n : ℕ) : a n = ∑ f : Fin n → Fin 8, if (∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → close (f i) (f j)) then 1 else 0 := by
  rw [a, Finset.card_filter]

theorem sum_cons {n : ℕ} (F : (Fin (n + 1) → Fin 8) → ℕ) :
    ∑ f, F f = ∑ x : Fin 8, ∑ g : Fin n → Fin 8, F (Fin.cons x g) := by
  rw [← (Fin.consEquiv (fun _ => Fin 8)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem V_cc {n : ℕ} (x y : Fin 8) (h : Fin n → Fin 8) :
    (∀ i j : Fin (n + 2), (j : ℕ) = (i : ℕ) + 1 → close ((Fin.cons x (Fin.cons y h : Fin (n + 1) → Fin 8) : Fin (n + 2) → Fin 8) i) ((Fin.cons x (Fin.cons y h : Fin (n + 1) → Fin 8) : Fin (n + 2) → Fin 8) j)) ↔
      close x y ∧ (∀ i j : Fin (n + 1), (j : ℕ) = (i : ℕ) + 1 → close ((Fin.cons y h : Fin (n + 1) → Fin 8) i) ((Fin.cons y h : Fin (n + 1) → Fin 8) j)) := by
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
  ∑ g : Fin n → Fin 8, if (∀ i j : Fin (n + 1), (j : ℕ) = (i : ℕ) + 1 → close ((Fin.cons x g : Fin (n + 1) → Fin 8) i) ((Fin.cons x g : Fin (n + 1) → Fin 8) j)) then 1 else 0

theorem a_succ (n : ℕ) : a (n + 1) = ∑ x, G n x := by
  rw [a_sum, sum_cons]; rfl

theorem G_succ (n : ℕ) (x : Fin 8) : G (n + 1) x = ∑ y, if close x y then G n y else 0 := by
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
    G (n + 1) 0 = G n 0 + G n 1 + G n 2 ∧
    G (n + 1) 1 = G n 0 + G n 1 + G n 2 + G n 3 ∧
    G (n + 1) 2 = G n 0 + G n 1 + G n 2 + G n 3 + G n 4 ∧
    G (n + 1) 3 = G n 1 + G n 2 + G n 3 + G n 4 + G n 5 ∧
    G (n + 1) 4 = G n 2 + G n 3 + G n 4 + G n 5 + G n 6 ∧
    G (n + 1) 5 = G n 3 + G n 4 + G n 5 + G n 6 + G n 7 ∧
    G (n + 1) 6 = G n 4 + G n 5 + G n 6 + G n 7 ∧
    G (n + 1) 7 = G n 5 + G n 6 + G n 7 := by
  simp only [G_succ, Fin.sum_univ_eight]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [close]

theorem L0 : G 0 0 = 1 ∧ G 0 1 = 1 ∧ G 0 2 = 1 ∧ G 0 3 = 1 ∧ G 0 4 = 1 ∧ G 0 5 = 1 ∧ G 0 6 = 1 ∧ G 0 7 = 1 := by
  refine ⟨G0 _, G0 _, G0 _, G0 _, G0 _, G0 _, G0 _, G0 _⟩

theorem L1 : G 1 0 = 3 ∧ G 1 1 = 4 ∧ G 1 2 = 5 ∧ G 1 3 = 5 ∧ G 1 4 = 5 ∧ G 1 5 = 5 ∧ G 1 6 = 4 ∧ G 1 7 = 3 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := Gs 0
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := L0
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem L2 : G 2 0 = 12 ∧ G 2 1 = 17 ∧ G 2 2 = 22 ∧ G 2 3 = 24 ∧ G 2 4 = 24 ∧ G 2 5 = 22 ∧ G 2 6 = 17 ∧ G 2 7 = 12 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := Gs 1
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := L1
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem L3 : G 3 0 = 51 ∧ G 3 1 = 75 ∧ G 3 2 = 99 ∧ G 3 3 = 109 ∧ G 3 4 = 109 ∧ G 3 5 = 99 ∧ G 3 6 = 75 ∧ G 3 7 = 51 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := Gs 2
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := L2
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem L4 : G 4 0 = 225 ∧ G 4 1 = 334 ∧ G 4 2 = 443 ∧ G 4 3 = 491 ∧ G 4 4 = 491 ∧ G 4 5 = 443 ∧ G 4 6 = 334 ∧ G 4 7 = 225 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := Gs 3
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := L3
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem A1 : a 1 = 8 := by
  rw [a_succ, Fin.sum_univ_eight]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := L0
  linarith

theorem A2 : a 2 = 34 := by
  rw [a_succ, Fin.sum_univ_eight]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := L1
  linarith

theorem A3 : a 3 = 150 := by
  rw [a_succ, Fin.sum_univ_eight]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := L2
  linarith

theorem A4 : a 4 = 668 := by
  rw [a_succ, Fin.sum_univ_eight]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := L3
  linarith

theorem A5 : a 5 = 2986 := by
  rw [a_succ, Fin.sum_univ_eight]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := L4
  linarith

theorem arec (m : ℕ) : (a (m + 4) : ℤ) = 5 * (a (m + 3) : ℤ) - (a (m + 2) : ℤ) - 6 * (a (m + 1) : ℤ) := by
  have h0 := a_succ (m + 0)
  rw [Fin.sum_univ_eight] at h0
  have h1 := a_succ (m + 1)
  rw [Fin.sum_univ_eight] at h1
  have h2 := a_succ (m + 2)
  rw [Fin.sum_univ_eight] at h2
  have h3 := a_succ (m + 3)
  rw [Fin.sum_univ_eight] at h3
  obtain ⟨E0_0, E0_1, E0_2, E0_3, E0_4, E0_5, E0_6, E0_7⟩ := Gs (m + 0)
  obtain ⟨E1_0, E1_1, E1_2, E1_3, E1_4, E1_5, E1_6, E1_7⟩ := Gs (m + 1)
  obtain ⟨E2_0, E2_1, E2_2, E2_3, E2_4, E2_5, E2_6, E2_7⟩ := Gs (m + 2)
  simp only [show ∀ t : ℕ, m + t + 1 = m + (t + 1) from fun t => rfl, Nat.add_zero] at *
  rw [h0, h1, h2, h3]
  push_cast
  linarith

end W126395

open W126395 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a126395.main := by
  have hrec : ∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 5 * (a (n - 1) : ℤ) - (a (n - 2) : ℤ) - 6 * (a (n - 3) : ℤ) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [arec m]
    simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega]
  refine ⟨?_, ?_⟩
  · have hp : (1 - 5 * X + X ^ 2 + 6 * X ^ 3 : PowerSeries ℚ) = 1 - PowerSeries.C (5 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.X ^ 2 + PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 3 := by
      (try simp only [map_ofNat, map_one, one_mul, pow_one]) <;> ring
    have hr : (1 + 3 * X - 5 * X ^ 2 - 6 * X ^ 3 : PowerSeries ℚ) = 1 + PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (5 : ℚ) * PowerSeries.X ^ 2 - PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 3 := by
      (try simp only [map_ofNat, map_one, one_mul, pow_one]) <;> ring
    have hq : ∀ F : PowerSeries ℚ, F * (1 - PowerSeries.C (5 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.X ^ 2 + PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 3) = F - PowerSeries.C (5 : ℚ) * (F * PowerSeries.X ^ 1) + (F * PowerSeries.X ^ 2) + PowerSeries.C (6 : ℚ) * (F * PowerSeries.X ^ 3) := fun F => by ring
    rw [hp, hr, hq]
    ext n
    simp only [map_sub, map_add, map_neg, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_C_mul,
      PowerSeries.coeff_mk, PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
    rcases Nat.lt_or_ge n 6 with hn | hn
    · interval_cases n <;> simp [a0, W126395.A1, W126395.A2, W126395.A3, W126395.A4, W126395.A5] <;> norm_num
    · have h := hrec n (by omega)
      have h' : (a n : ℚ) = 5 * (a (n - 1) : ℚ) - (a (n - 2) : ℚ) - 6 * (a (n - 3) : ℚ) := by exact_mod_cast h
      simp (disch := omega) only [if_pos, if_neg, PowerSeries.coeff_C]
      linarith
  · intro n hn
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n <;> simp [a0, W126395.A1, W126395.A2, W126395.A3, W126395.A4, W126395.A5]
    · have := hrec n h
      linarith
