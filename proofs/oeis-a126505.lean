import OMAStatements.S_oeis_a126505
import Mathlib

open OMA.S_oeis_a126505

namespace W126505

theorem sumK (f : Fin 10 → ℕ) : ∑ x, f x = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_eight]
  rfl

theorem iv (n : ℕ) (w : Fin n → Fin 10) : isValid n w ↔ (∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → adjOk (w i) (w j)) := by
  constructor
  · intro h i j hij
    obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    simp only at hij
    subst hij
    exact h ⟨i, by omega⟩
  · intro h i
    exact h _ _ rfl

theorem adj_iff (x y : Fin 10) : adjOk x y ↔ (x : ℕ) ≤ (y : ℕ) + 4 ∧ (y : ℕ) ≤ (x : ℕ) + 4 := by
  unfold adjOk
  omega

theorem a_sum (n : ℕ) : a n = ∑ f : Fin n → Fin 10, if (∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → adjOk (f i) (f j)) then 1 else 0 := by
  rw [a, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro f _
  by_cases h : isValid n f
  · rw [if_pos h, if_pos ((iv n f).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((iv n f).mpr h'))]

theorem sum_cons {n : ℕ} (F : (Fin (n + 1) → Fin 10) → ℕ) :
    ∑ f, F f = ∑ x : Fin 10, ∑ g : Fin n → Fin 10, F (Fin.cons x g) := by
  rw [← (Fin.consEquiv (fun _ => Fin 10)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem V_cc {n : ℕ} (x y : Fin 10) (h : Fin n → Fin 10) :
    (∀ i j : Fin (n + 2), (j : ℕ) = (i : ℕ) + 1 → adjOk ((Fin.cons x (Fin.cons y h : Fin (n + 1) → Fin 10) : Fin (n + 2) → Fin 10) i) ((Fin.cons x (Fin.cons y h : Fin (n + 1) → Fin 10) : Fin (n + 2) → Fin 10) j)) ↔
      adjOk x y ∧ (∀ i j : Fin (n + 1), (j : ℕ) = (i : ℕ) + 1 → adjOk ((Fin.cons y h : Fin (n + 1) → Fin 10) i) ((Fin.cons y h : Fin (n + 1) → Fin 10) j)) := by
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
  ∑ g : Fin n → Fin 10, if (∀ i j : Fin (n + 1), (j : ℕ) = (i : ℕ) + 1 → adjOk ((Fin.cons x g : Fin (n + 1) → Fin 10) i) ((Fin.cons x g : Fin (n + 1) → Fin 10) j)) then 1 else 0

theorem a_succ (n : ℕ) : a (n + 1) = ∑ x, G n x := by
  rw [a_sum, sum_cons]; rfl

theorem G_succ (n : ℕ) (x : Fin 10) : G (n + 1) x = ∑ y, if adjOk x y then G n y else 0 := by
  rw [G, sum_cons]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [V_cc]
  split_ifs with hxy
  · simp [hxy, G]
  · simp [hxy]

theorem a0 : a 0 = 1 := by
  rw [a_sum, Fintype.sum_unique]
  simp

theorem G0 (x : Fin 10) : G 0 x = 1 := by
  rw [G, Fintype.sum_unique]
  simp

theorem Gs (n : ℕ) :
    G (n + 1) 0 = G n 0 + G n 1 + G n 2 + G n 3 + G n 4 ∧
    G (n + 1) 1 = G n 0 + G n 1 + G n 2 + G n 3 + G n 4 + G n 5 ∧
    G (n + 1) 2 = G n 0 + G n 1 + G n 2 + G n 3 + G n 4 + G n 5 + G n 6 ∧
    G (n + 1) 3 = G n 0 + G n 1 + G n 2 + G n 3 + G n 4 + G n 5 + G n 6 + G n 7 ∧
    G (n + 1) 4 = G n 0 + G n 1 + G n 2 + G n 3 + G n 4 + G n 5 + G n 6 + G n 7 + G n 8 ∧
    G (n + 1) 5 = G n 1 + G n 2 + G n 3 + G n 4 + G n 5 + G n 6 + G n 7 + G n 8 + G n 9 ∧
    G (n + 1) 6 = G n 2 + G n 3 + G n 4 + G n 5 + G n 6 + G n 7 + G n 8 + G n 9 ∧
    G (n + 1) 7 = G n 3 + G n 4 + G n 5 + G n 6 + G n 7 + G n 8 + G n 9 ∧
    G (n + 1) 8 = G n 4 + G n 5 + G n 6 + G n 7 + G n 8 + G n 9 ∧
    G (n + 1) 9 = G n 5 + G n 6 + G n 7 + G n 8 + G n 9 := by
  simp only [G_succ, sumK]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [adj_iff]

theorem L0 : G 0 0 = 1 ∧ G 0 1 = 1 ∧ G 0 2 = 1 ∧ G 0 3 = 1 ∧ G 0 4 = 1 ∧ G 0 5 = 1 ∧ G 0 6 = 1 ∧ G 0 7 = 1 ∧ G 0 8 = 1 ∧ G 0 9 = 1 := by
  refine ⟨G0 _, G0 _, G0 _, G0 _, G0 _, G0 _, G0 _, G0 _, G0 _, G0 _⟩

theorem L1 : G 1 0 = 5 ∧ G 1 1 = 6 ∧ G 1 2 = 7 ∧ G 1 3 = 8 ∧ G 1 4 = 9 ∧ G 1 5 = 9 ∧ G 1 6 = 8 ∧ G 1 7 = 7 ∧ G 1 8 = 6 ∧ G 1 9 = 5 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := Gs 0
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := L0
  refine ⟨by rw [e0]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e1]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e2]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e3]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e4]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e5]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e6]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e7]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e8]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e9]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9]⟩

theorem L2 : G 2 0 = 35 ∧ G 2 1 = 44 ∧ G 2 2 = 52 ∧ G 2 3 = 59 ∧ G 2 4 = 65 ∧ G 2 5 = 65 ∧ G 2 6 = 59 ∧ G 2 7 = 52 ∧ G 2 8 = 44 ∧ G 2 9 = 35 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := Gs 1
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := L1
  refine ⟨by rw [e0]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e1]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e2]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e3]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e4]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e5]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e6]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e7]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e8]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e9]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9]⟩

theorem L3 : G 3 0 = 255 ∧ G 3 1 = 320 ∧ G 3 2 = 379 ∧ G 3 3 = 431 ∧ G 3 4 = 475 ∧ G 3 5 = 475 ∧ G 3 6 = 431 ∧ G 3 7 = 379 ∧ G 3 8 = 320 ∧ G 3 9 = 255 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := Gs 2
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := L2
  refine ⟨by rw [e0]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e1]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e2]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e3]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e4]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e5]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e6]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e7]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e8]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e9]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9]⟩

theorem L4 : G 4 0 = 1860 ∧ G 4 1 = 2335 ∧ G 4 2 = 2766 ∧ G 4 3 = 3145 ∧ G 4 4 = 3465 ∧ G 4 5 = 3465 ∧ G 4 6 = 3145 ∧ G 4 7 = 2766 ∧ G 4 8 = 2335 ∧ G 4 9 = 1860 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := Gs 3
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := L3
  refine ⟨by rw [e0]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e1]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e2]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e3]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e4]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e5]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e6]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e7]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e8]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e9]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9]⟩

theorem L5 : G 5 0 = 13571 ∧ G 5 1 = 17036 ∧ G 5 2 = 20181 ∧ G 5 3 = 22947 ∧ G 5 4 = 25282 ∧ G 5 5 = 25282 ∧ G 5 6 = 22947 ∧ G 5 7 = 20181 ∧ G 5 8 = 17036 ∧ G 5 9 = 13571 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := Gs 4
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := L4
  refine ⟨by rw [e0]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e1]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e2]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e3]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e4]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e5]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e6]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e7]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e8]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e9]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9]⟩

theorem L6 : G 6 0 = 99017 ∧ G 6 1 = 124299 ∧ G 6 2 = 147246 ∧ G 6 3 = 167427 ∧ G 6 4 = 184463 ∧ G 6 5 = 184463 ∧ G 6 6 = 167427 ∧ G 6 7 = 147246 ∧ G 6 8 = 124299 ∧ G 6 9 = 99017 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := Gs 5
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := L5
  refine ⟨by rw [e0]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e1]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e2]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e3]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e4]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e5]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e6]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e7]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e8]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9], by rw [e9]; simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9]⟩

theorem A1 : a 1 = 10 := by
  rw [a_succ, sumK]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := L0
  simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9]

theorem A2 : a 2 = 70 := by
  rw [a_succ, sumK]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := L1
  simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9]

theorem A3 : a 3 = 510 := by
  rw [a_succ, sumK]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := L2
  simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9]

theorem A4 : a 4 = 3720 := by
  rw [a_succ, sumK]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := L3
  simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9]

theorem A5 : a 5 = 27142 := by
  rw [a_succ, sumK]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := L4
  simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9]

theorem A6 : a 6 = 198034 := by
  rw [a_succ, sumK]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := L5
  simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9]

theorem A7 : a 7 = 1444904 := by
  rw [a_succ, sumK]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := L6
  simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9]

theorem arec (m : ℕ) : (a (m + 6) : ℤ) = 7 * (a (m + 5) : ℤ) + 3 * (a (m + 4) : ℤ) - 6 * (a (m + 3) : ℤ) - (a (m + 2) : ℤ) + (a (m + 1) : ℤ) := by
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
  obtain ⟨E0_0, E0_1, E0_2, E0_3, E0_4, E0_5, E0_6, E0_7, E0_8, E0_9⟩ := Gs (m + 0)
  obtain ⟨E1_0, E1_1, E1_2, E1_3, E1_4, E1_5, E1_6, E1_7, E1_8, E1_9⟩ := Gs (m + 1)
  obtain ⟨E2_0, E2_1, E2_2, E2_3, E2_4, E2_5, E2_6, E2_7, E2_8, E2_9⟩ := Gs (m + 2)
  obtain ⟨E3_0, E3_1, E3_2, E3_3, E3_4, E3_5, E3_6, E3_7, E3_8, E3_9⟩ := Gs (m + 3)
  obtain ⟨E4_0, E4_1, E4_2, E4_3, E4_4, E4_5, E4_6, E4_7, E4_8, E4_9⟩ := Gs (m + 4)
  simp only [show ∀ t : ℕ, m + t + 1 = m + (t + 1) from fun t => rfl, Nat.add_zero] at *
  rw [h0, h1, h2, h3, h4, h5]
  zify at *
  push_cast
  linear_combination (1 : ℤ) * E0_0 + (1 : ℤ) * E0_9 + (1 : ℤ) * E1_0 + (-1 : ℤ) * E1_4 + (-1 : ℤ) * E1_5 + (1 : ℤ) * E1_9 + (-3 : ℤ) * E2_0 + (-1 : ℤ) * E2_1 + (-1 : ℤ) * E2_4 + (-1 : ℤ) * E2_5 + (-1 : ℤ) * E2_8 + (-3 : ℤ) * E2_9 + (-2 : ℤ) * E3_0 + (-1 : ℤ) * E3_1 + (1 : ℤ) * E3_3 + (2 : ℤ) * E3_4 + (2 : ℤ) * E3_5 + (1 : ℤ) * E3_6 + (-1 : ℤ) * E3_8 + (-2 : ℤ) * E3_9 + (1 : ℤ) * E4_0 + (1 : ℤ) * E4_1 + (1 : ℤ) * E4_2 + (1 : ℤ) * E4_3 + (1 : ℤ) * E4_4 + (1 : ℤ) * E4_5 + (1 : ℤ) * E4_6 + (1 : ℤ) * E4_7 + (1 : ℤ) * E4_8 + (1 : ℤ) * E4_9

end W126505

open W126505 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a126505.main := by
  have hrec : ∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 7 * (a (n - 1) : ℤ) + 3 * (a (n - 2) : ℤ) - 6 * (a (n - 3) : ℤ) - (a (n - 4) : ℤ) + (a (n - 5) : ℤ) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [arec m]
    simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega]
  refine ⟨?_, ?_⟩
  · have hp : (1 - 7 * X - 3 * X ^ 2 + 6 * X ^ 3 + X ^ 4 - X ^ 5 : PowerSeries ℚ) = 1 - PowerSeries.C (7 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.X ^ 4 - PowerSeries.X ^ 5 := by
      (try simp only [map_ofNat, map_one, one_mul, pow_one]) <;> ring
    have hr : (1 + 3 * X - 3 * X ^ 2 - 4 * X ^ 3 + X ^ 4 + X ^ 5 : PowerSeries ℚ) = 1 + PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 2 - PowerSeries.C (4 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.X ^ 4 + PowerSeries.X ^ 5 := by
      (try simp only [map_ofNat, map_one, one_mul, pow_one]) <;> ring
    have hq : ∀ F : PowerSeries ℚ, F * (1 - PowerSeries.C (7 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.X ^ 4 - PowerSeries.X ^ 5) = F - PowerSeries.C (7 : ℚ) * (F * PowerSeries.X ^ 1) - PowerSeries.C (3 : ℚ) * (F * PowerSeries.X ^ 2) + PowerSeries.C (6 : ℚ) * (F * PowerSeries.X ^ 3) + (F * PowerSeries.X ^ 4) - (F * PowerSeries.X ^ 5) := fun F => by ring
    rw [hp, hr, hq]
    ext n
    simp only [map_sub, map_add, map_neg, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_C_mul,
      PowerSeries.coeff_mk, PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
    rcases Nat.lt_or_ge n 8 with hn | hn
    · interval_cases n <;> simp [a0, W126505.A1, W126505.A2, W126505.A3, W126505.A4, W126505.A5, W126505.A6, W126505.A7] <;> norm_num
    · have h := hrec n (by omega)
      have h' : (a n : ℚ) = 7 * (a (n - 1) : ℚ) + 3 * (a (n - 2) : ℚ) - 6 * (a (n - 3) : ℚ) - (a (n - 4) : ℚ) + (a (n - 5) : ℚ) := by exact_mod_cast h
      simp (disch := omega) only [if_pos, if_neg, PowerSeries.coeff_C]
      linarith
  · intro n hn
    rcases Nat.lt_or_ge n 6 with h | h
    · interval_cases n <;> simp [a0, W126505.A1, W126505.A2, W126505.A3, W126505.A4, W126505.A5, W126505.A6, W126505.A7]
    · have := hrec n h
      linarith
