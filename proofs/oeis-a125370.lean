import OMAStatements.S_oeis_a125370
import Mathlib

open OMA.S_oeis_a125370

namespace C125370

theorem sumK (f : Fin 7 → ℕ) : ∑ x, f x = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  rw [Fin.sum_univ_seven]

theorem adj_iff (x y : Fin 7) : adjOk x y ↔ (x : ℕ) ≤ (y : ℕ) + 5 ∧ (y : ℕ) ≤ (x : ℕ) + 5 := by
  unfold adjOk
  omega

theorem cyc (m : ℕ) (w : Fin (m + 1) → Fin 7) :
    isValid (m + 1) w ↔ (∀ i j : Fin (m + 1), (j : ℕ) = (i : ℕ) + 1 → adjOk (w i) (w j)) ∧ adjOk (w (Fin.last m)) (w 0) := by
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, ?_⟩
    · have := h i
      have e : (⟨(i.val + 1) % (m + 1), Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩ : Fin (m + 1)) = j :=
        Fin.ext (by simp only; rw [← hij]; exact Nat.mod_eq_of_lt (by omega))
      rwa [e] at this
    · have := h (Fin.last m)
      have e : (⟨((Fin.last m).val + 1) % (m + 1), Nat.mod_lt _ (Nat.zero_lt_of_lt (Fin.last m).isLt)⟩ :
          Fin (m + 1)) = 0 := Fin.ext (by simp)
      rwa [e] at this
  · rintro ⟨hl, hw⟩ i
    by_cases hi : i.val < m
    · have e : (⟨(i.val + 1) % (m + 1), Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩ : Fin (m + 1)) =
          ⟨i.val + 1, by omega⟩ := Fin.ext (by simp only; exact Nat.mod_eq_of_lt (by omega))
      rw [e]
      exact hl i _ rfl
    · have hil : i = Fin.last m := Fin.ext (by simp; omega)
      subst hil
      have e : (⟨((Fin.last m).val + 1) % (m + 1), Nat.mod_lt _ (Nat.zero_lt_of_lt (Fin.last m).isLt)⟩ :
          Fin (m + 1)) = 0 := Fin.ext (by simp)
      rw [e]
      exact hw

theorem sum_cons {n : ℕ} (F : (Fin (n + 1) → Fin 7) → ℕ) :
    ∑ f, F f = ∑ x : Fin 7, ∑ g : Fin n → Fin 7, F (Fin.cons x g) := by
  rw [← (Fin.consEquiv (fun _ => Fin 7)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem V_cc {n : ℕ} (x y : Fin 7) (h : Fin n → Fin 7) :
    (∀ i j : Fin (n + 2), (j : ℕ) = (i : ℕ) + 1 → adjOk ((Fin.cons x (Fin.cons y h : Fin (n + 1) → Fin 7) : Fin (n + 2) → Fin 7) i) ((Fin.cons x (Fin.cons y h : Fin (n + 1) → Fin 7) : Fin (n + 2) → Fin 7) j)) ↔
      adjOk x y ∧ (∀ i j : Fin (n + 1), (j : ℕ) = (i : ℕ) + 1 → adjOk ((Fin.cons y h : Fin (n + 1) → Fin 7) i) ((Fin.cons y h : Fin (n + 1) → Fin 7) j)) := by
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

def H (m : ℕ) (x y : Fin 7) : ℕ :=
  ∑ g : Fin m → Fin 7, if (∀ i j : Fin (m + 1), (j : ℕ) = (i : ℕ) + 1 → adjOk ((Fin.cons x g : Fin (m + 1) → Fin 7) i) ((Fin.cons x g : Fin (m + 1) → Fin 7) j)) ∧
    (Fin.cons x g : Fin (m + 1) → Fin 7) (Fin.last m) = y then 1 else 0

theorem a_succ (m : ℕ) : a (m + 1) = ∑ x : Fin 7, ∑ y : Fin 7, if adjOk y x then H m x y else 0 := by
  rw [a, Finset.card_filter, sum_cons]
  apply Finset.sum_congr rfl
  intro x _
  have hy : ∀ y : Fin 7, (if adjOk y x then H m x y else 0) = ∑ g : Fin m → Fin 7,
      if ((∀ i j : Fin (m + 1), (j : ℕ) = (i : ℕ) + 1 → adjOk ((Fin.cons x g : Fin (m + 1) → Fin 7) i) ((Fin.cons x g : Fin (m + 1) → Fin 7) j)) ∧
        (Fin.cons x g : Fin (m + 1) → Fin 7) (Fin.last m) = y) ∧ adjOk y x then 1 else 0 := by
    intro y
    unfold H
    by_cases h : adjOk y x
    · simp only [h, if_true, and_true]
    · simp [h]
  rw [Finset.sum_congr rfl (fun y _ => hy y), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  simp only [cyc, Fin.cons_zero]
  by_cases hv : (∀ i j : Fin (m + 1), (j : ℕ) = (i : ℕ) + 1 → adjOk ((Fin.cons x g : Fin (m + 1) → Fin 7) i) ((Fin.cons x g : Fin (m + 1) → Fin 7) j))
  · simp only [eq_true hv, true_and]
    rw [Finset.sum_eq_single ((Fin.cons x g : Fin (m + 1) → Fin 7) (Fin.last m))]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · simp [eq_false hv]

theorem last_cc {m : ℕ} (x z : Fin 7) (h : Fin m → Fin 7) :
    (Fin.cons x (Fin.cons z h : Fin (m + 1) → Fin 7) : Fin (m + 2) → Fin 7) (Fin.last (m + 1)) =
      (Fin.cons z h : Fin (m + 1) → Fin 7) (Fin.last m) := by
  rw [← Fin.succ_last, Fin.cons_succ]

theorem H_succ (m : ℕ) (x y : Fin 7) : H (m + 1) x y = ∑ z, if adjOk x z then H m z y else 0 := by
  rw [H, sum_cons]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [V_cc, last_cc]
  by_cases hxz : adjOk x z
  · simp only [hxz, true_and, if_true]; rfl
  · simp [hxz]

theorem H0 (x y : Fin 7) : H 0 x y = if x = y then 1 else 0 := by
  rw [H, Fintype.sum_unique]
  by_cases h : x = y <;> simp [h]

theorem Hs (m : ℕ) :
    H (m + 1) 0 0 = H m 0 0 + H m 1 0 + H m 2 0 + H m 3 0 + H m 4 0 + H m 5 0 ∧
    H (m + 1) 0 1 = H m 0 1 + H m 1 1 + H m 2 1 + H m 3 1 + H m 4 1 + H m 5 1 ∧
    H (m + 1) 0 2 = H m 0 2 + H m 1 2 + H m 2 2 + H m 3 2 + H m 4 2 + H m 5 2 ∧
    H (m + 1) 0 3 = H m 0 3 + H m 1 3 + H m 2 3 + H m 3 3 + H m 4 3 + H m 5 3 ∧
    H (m + 1) 0 4 = H m 0 4 + H m 1 4 + H m 2 4 + H m 3 4 + H m 4 4 + H m 5 4 ∧
    H (m + 1) 0 5 = H m 0 5 + H m 1 5 + H m 2 5 + H m 3 5 + H m 4 5 + H m 5 5 ∧
    H (m + 1) 0 6 = H m 0 6 + H m 1 6 + H m 2 6 + H m 3 6 + H m 4 6 + H m 5 6 ∧
    H (m + 1) 1 0 = H m 0 0 + H m 1 0 + H m 2 0 + H m 3 0 + H m 4 0 + H m 5 0 + H m 6 0 ∧
    H (m + 1) 1 1 = H m 0 1 + H m 1 1 + H m 2 1 + H m 3 1 + H m 4 1 + H m 5 1 + H m 6 1 ∧
    H (m + 1) 1 2 = H m 0 2 + H m 1 2 + H m 2 2 + H m 3 2 + H m 4 2 + H m 5 2 + H m 6 2 ∧
    H (m + 1) 1 3 = H m 0 3 + H m 1 3 + H m 2 3 + H m 3 3 + H m 4 3 + H m 5 3 + H m 6 3 ∧
    H (m + 1) 1 4 = H m 0 4 + H m 1 4 + H m 2 4 + H m 3 4 + H m 4 4 + H m 5 4 + H m 6 4 ∧
    H (m + 1) 1 5 = H m 0 5 + H m 1 5 + H m 2 5 + H m 3 5 + H m 4 5 + H m 5 5 + H m 6 5 ∧
    H (m + 1) 1 6 = H m 0 6 + H m 1 6 + H m 2 6 + H m 3 6 + H m 4 6 + H m 5 6 + H m 6 6 ∧
    H (m + 1) 2 0 = H m 0 0 + H m 1 0 + H m 2 0 + H m 3 0 + H m 4 0 + H m 5 0 + H m 6 0 ∧
    H (m + 1) 2 1 = H m 0 1 + H m 1 1 + H m 2 1 + H m 3 1 + H m 4 1 + H m 5 1 + H m 6 1 ∧
    H (m + 1) 2 2 = H m 0 2 + H m 1 2 + H m 2 2 + H m 3 2 + H m 4 2 + H m 5 2 + H m 6 2 ∧
    H (m + 1) 2 3 = H m 0 3 + H m 1 3 + H m 2 3 + H m 3 3 + H m 4 3 + H m 5 3 + H m 6 3 ∧
    H (m + 1) 2 4 = H m 0 4 + H m 1 4 + H m 2 4 + H m 3 4 + H m 4 4 + H m 5 4 + H m 6 4 ∧
    H (m + 1) 2 5 = H m 0 5 + H m 1 5 + H m 2 5 + H m 3 5 + H m 4 5 + H m 5 5 + H m 6 5 ∧
    H (m + 1) 2 6 = H m 0 6 + H m 1 6 + H m 2 6 + H m 3 6 + H m 4 6 + H m 5 6 + H m 6 6 ∧
    H (m + 1) 3 0 = H m 0 0 + H m 1 0 + H m 2 0 + H m 3 0 + H m 4 0 + H m 5 0 + H m 6 0 ∧
    H (m + 1) 3 1 = H m 0 1 + H m 1 1 + H m 2 1 + H m 3 1 + H m 4 1 + H m 5 1 + H m 6 1 ∧
    H (m + 1) 3 2 = H m 0 2 + H m 1 2 + H m 2 2 + H m 3 2 + H m 4 2 + H m 5 2 + H m 6 2 ∧
    H (m + 1) 3 3 = H m 0 3 + H m 1 3 + H m 2 3 + H m 3 3 + H m 4 3 + H m 5 3 + H m 6 3 ∧
    H (m + 1) 3 4 = H m 0 4 + H m 1 4 + H m 2 4 + H m 3 4 + H m 4 4 + H m 5 4 + H m 6 4 ∧
    H (m + 1) 3 5 = H m 0 5 + H m 1 5 + H m 2 5 + H m 3 5 + H m 4 5 + H m 5 5 + H m 6 5 ∧
    H (m + 1) 3 6 = H m 0 6 + H m 1 6 + H m 2 6 + H m 3 6 + H m 4 6 + H m 5 6 + H m 6 6 ∧
    H (m + 1) 4 0 = H m 0 0 + H m 1 0 + H m 2 0 + H m 3 0 + H m 4 0 + H m 5 0 + H m 6 0 ∧
    H (m + 1) 4 1 = H m 0 1 + H m 1 1 + H m 2 1 + H m 3 1 + H m 4 1 + H m 5 1 + H m 6 1 ∧
    H (m + 1) 4 2 = H m 0 2 + H m 1 2 + H m 2 2 + H m 3 2 + H m 4 2 + H m 5 2 + H m 6 2 ∧
    H (m + 1) 4 3 = H m 0 3 + H m 1 3 + H m 2 3 + H m 3 3 + H m 4 3 + H m 5 3 + H m 6 3 ∧
    H (m + 1) 4 4 = H m 0 4 + H m 1 4 + H m 2 4 + H m 3 4 + H m 4 4 + H m 5 4 + H m 6 4 ∧
    H (m + 1) 4 5 = H m 0 5 + H m 1 5 + H m 2 5 + H m 3 5 + H m 4 5 + H m 5 5 + H m 6 5 ∧
    H (m + 1) 4 6 = H m 0 6 + H m 1 6 + H m 2 6 + H m 3 6 + H m 4 6 + H m 5 6 + H m 6 6 ∧
    H (m + 1) 5 0 = H m 0 0 + H m 1 0 + H m 2 0 + H m 3 0 + H m 4 0 + H m 5 0 + H m 6 0 ∧
    H (m + 1) 5 1 = H m 0 1 + H m 1 1 + H m 2 1 + H m 3 1 + H m 4 1 + H m 5 1 + H m 6 1 ∧
    H (m + 1) 5 2 = H m 0 2 + H m 1 2 + H m 2 2 + H m 3 2 + H m 4 2 + H m 5 2 + H m 6 2 ∧
    H (m + 1) 5 3 = H m 0 3 + H m 1 3 + H m 2 3 + H m 3 3 + H m 4 3 + H m 5 3 + H m 6 3 ∧
    H (m + 1) 5 4 = H m 0 4 + H m 1 4 + H m 2 4 + H m 3 4 + H m 4 4 + H m 5 4 + H m 6 4 ∧
    H (m + 1) 5 5 = H m 0 5 + H m 1 5 + H m 2 5 + H m 3 5 + H m 4 5 + H m 5 5 + H m 6 5 ∧
    H (m + 1) 5 6 = H m 0 6 + H m 1 6 + H m 2 6 + H m 3 6 + H m 4 6 + H m 5 6 + H m 6 6 ∧
    H (m + 1) 6 0 = H m 1 0 + H m 2 0 + H m 3 0 + H m 4 0 + H m 5 0 + H m 6 0 ∧
    H (m + 1) 6 1 = H m 1 1 + H m 2 1 + H m 3 1 + H m 4 1 + H m 5 1 + H m 6 1 ∧
    H (m + 1) 6 2 = H m 1 2 + H m 2 2 + H m 3 2 + H m 4 2 + H m 5 2 + H m 6 2 ∧
    H (m + 1) 6 3 = H m 1 3 + H m 2 3 + H m 3 3 + H m 4 3 + H m 5 3 + H m 6 3 ∧
    H (m + 1) 6 4 = H m 1 4 + H m 2 4 + H m 3 4 + H m 4 4 + H m 5 4 + H m 6 4 ∧
    H (m + 1) 6 5 = H m 1 5 + H m 2 5 + H m 3 5 + H m 4 5 + H m 5 5 + H m 6 5 ∧
    H (m + 1) 6 6 = H m 1 6 + H m 2 6 + H m 3 6 + H m 4 6 + H m 5 6 + H m 6 6 := by
  simp only [H_succ, sumK]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [adj_iff]

theorem L0 : H 0 0 0 = 1 ∧ H 0 0 1 = 0 ∧ H 0 0 2 = 0 ∧ H 0 0 3 = 0 ∧ H 0 0 4 = 0 ∧ H 0 0 5 = 0 ∧ H 0 0 6 = 0 ∧ H 0 1 0 = 0 ∧ H 0 1 1 = 1 ∧ H 0 1 2 = 0 ∧ H 0 1 3 = 0 ∧ H 0 1 4 = 0 ∧ H 0 1 5 = 0 ∧ H 0 1 6 = 0 ∧ H 0 2 0 = 0 ∧ H 0 2 1 = 0 ∧ H 0 2 2 = 1 ∧ H 0 2 3 = 0 ∧ H 0 2 4 = 0 ∧ H 0 2 5 = 0 ∧ H 0 2 6 = 0 ∧ H 0 3 0 = 0 ∧ H 0 3 1 = 0 ∧ H 0 3 2 = 0 ∧ H 0 3 3 = 1 ∧ H 0 3 4 = 0 ∧ H 0 3 5 = 0 ∧ H 0 3 6 = 0 ∧ H 0 4 0 = 0 ∧ H 0 4 1 = 0 ∧ H 0 4 2 = 0 ∧ H 0 4 3 = 0 ∧ H 0 4 4 = 1 ∧ H 0 4 5 = 0 ∧ H 0 4 6 = 0 ∧ H 0 5 0 = 0 ∧ H 0 5 1 = 0 ∧ H 0 5 2 = 0 ∧ H 0 5 3 = 0 ∧ H 0 5 4 = 0 ∧ H 0 5 5 = 1 ∧ H 0 5 6 = 0 ∧ H 0 6 0 = 0 ∧ H 0 6 1 = 0 ∧ H 0 6 2 = 0 ∧ H 0 6 3 = 0 ∧ H 0 6 4 = 0 ∧ H 0 6 5 = 0 ∧ H 0 6 6 = 1 := by
  simp only [H0]
  decide

theorem L1 : H 1 0 0 = 1 ∧ H 1 0 1 = 1 ∧ H 1 0 2 = 1 ∧ H 1 0 3 = 1 ∧ H 1 0 4 = 1 ∧ H 1 0 5 = 1 ∧ H 1 0 6 = 0 ∧ H 1 1 0 = 1 ∧ H 1 1 1 = 1 ∧ H 1 1 2 = 1 ∧ H 1 1 3 = 1 ∧ H 1 1 4 = 1 ∧ H 1 1 5 = 1 ∧ H 1 1 6 = 1 ∧ H 1 2 0 = 1 ∧ H 1 2 1 = 1 ∧ H 1 2 2 = 1 ∧ H 1 2 3 = 1 ∧ H 1 2 4 = 1 ∧ H 1 2 5 = 1 ∧ H 1 2 6 = 1 ∧ H 1 3 0 = 1 ∧ H 1 3 1 = 1 ∧ H 1 3 2 = 1 ∧ H 1 3 3 = 1 ∧ H 1 3 4 = 1 ∧ H 1 3 5 = 1 ∧ H 1 3 6 = 1 ∧ H 1 4 0 = 1 ∧ H 1 4 1 = 1 ∧ H 1 4 2 = 1 ∧ H 1 4 3 = 1 ∧ H 1 4 4 = 1 ∧ H 1 4 5 = 1 ∧ H 1 4 6 = 1 ∧ H 1 5 0 = 1 ∧ H 1 5 1 = 1 ∧ H 1 5 2 = 1 ∧ H 1 5 3 = 1 ∧ H 1 5 4 = 1 ∧ H 1 5 5 = 1 ∧ H 1 5 6 = 1 ∧ H 1 6 0 = 0 ∧ H 1 6 1 = 1 ∧ H 1 6 2 = 1 ∧ H 1 6 3 = 1 ∧ H 1 6 4 = 1 ∧ H 1 6 5 = 1 ∧ H 1 6 6 = 1 := by
  obtain ⟨e0_0, e0_1, e0_2, e0_3, e0_4, e0_5, e0_6, e1_0, e1_1, e1_2, e1_3, e1_4, e1_5, e1_6, e2_0, e2_1, e2_2, e2_3, e2_4, e2_5, e2_6, e3_0, e3_1, e3_2, e3_3, e3_4, e3_5, e3_6, e4_0, e4_1, e4_2, e4_3, e4_4, e4_5, e4_6, e5_0, e5_1, e5_2, e5_3, e5_4, e5_5, e5_6, e6_0, e6_1, e6_2, e6_3, e6_4, e6_5, e6_6⟩ := Hs 0
  obtain ⟨f0_0, f0_1, f0_2, f0_3, f0_4, f0_5, f0_6, f1_0, f1_1, f1_2, f1_3, f1_4, f1_5, f1_6, f2_0, f2_1, f2_2, f2_3, f2_4, f2_5, f2_6, f3_0, f3_1, f3_2, f3_3, f3_4, f3_5, f3_6, f4_0, f4_1, f4_2, f4_3, f4_4, f4_5, f4_6, f5_0, f5_1, f5_2, f5_3, f5_4, f5_5, f5_6, f6_0, f6_1, f6_2, f6_3, f6_4, f6_5, f6_6⟩ := L0
  refine ⟨by rw [e0_0]; simp only [f0_0, f1_0, f2_0, f3_0, f4_0, f5_0], by rw [e0_1]; simp only [f0_1, f1_1, f2_1, f3_1, f4_1, f5_1], by rw [e0_2]; simp only [f0_2, f1_2, f2_2, f3_2, f4_2, f5_2], by rw [e0_3]; simp only [f0_3, f1_3, f2_3, f3_3, f4_3, f5_3], by rw [e0_4]; simp only [f0_4, f1_4, f2_4, f3_4, f4_4, f5_4], by rw [e0_5]; simp only [f0_5, f1_5, f2_5, f3_5, f4_5, f5_5], by rw [e0_6]; simp only [f0_6, f1_6, f2_6, f3_6, f4_6, f5_6], by rw [e1_0]; simp only [f0_0, f1_0, f2_0, f3_0, f4_0, f5_0, f6_0], by rw [e1_1]; simp only [f0_1, f1_1, f2_1, f3_1, f4_1, f5_1, f6_1], by rw [e1_2]; simp only [f0_2, f1_2, f2_2, f3_2, f4_2, f5_2, f6_2], by rw [e1_3]; simp only [f0_3, f1_3, f2_3, f3_3, f4_3, f5_3, f6_3], by rw [e1_4]; simp only [f0_4, f1_4, f2_4, f3_4, f4_4, f5_4, f6_4], by rw [e1_5]; simp only [f0_5, f1_5, f2_5, f3_5, f4_5, f5_5, f6_5], by rw [e1_6]; simp only [f0_6, f1_6, f2_6, f3_6, f4_6, f5_6, f6_6], by rw [e2_0]; simp only [f0_0, f1_0, f2_0, f3_0, f4_0, f5_0, f6_0], by rw [e2_1]; simp only [f0_1, f1_1, f2_1, f3_1, f4_1, f5_1, f6_1], by rw [e2_2]; simp only [f0_2, f1_2, f2_2, f3_2, f4_2, f5_2, f6_2], by rw [e2_3]; simp only [f0_3, f1_3, f2_3, f3_3, f4_3, f5_3, f6_3], by rw [e2_4]; simp only [f0_4, f1_4, f2_4, f3_4, f4_4, f5_4, f6_4], by rw [e2_5]; simp only [f0_5, f1_5, f2_5, f3_5, f4_5, f5_5, f6_5], by rw [e2_6]; simp only [f0_6, f1_6, f2_6, f3_6, f4_6, f5_6, f6_6], by rw [e3_0]; simp only [f0_0, f1_0, f2_0, f3_0, f4_0, f5_0, f6_0], by rw [e3_1]; simp only [f0_1, f1_1, f2_1, f3_1, f4_1, f5_1, f6_1], by rw [e3_2]; simp only [f0_2, f1_2, f2_2, f3_2, f4_2, f5_2, f6_2], by rw [e3_3]; simp only [f0_3, f1_3, f2_3, f3_3, f4_3, f5_3, f6_3], by rw [e3_4]; simp only [f0_4, f1_4, f2_4, f3_4, f4_4, f5_4, f6_4], by rw [e3_5]; simp only [f0_5, f1_5, f2_5, f3_5, f4_5, f5_5, f6_5], by rw [e3_6]; simp only [f0_6, f1_6, f2_6, f3_6, f4_6, f5_6, f6_6], by rw [e4_0]; simp only [f0_0, f1_0, f2_0, f3_0, f4_0, f5_0, f6_0], by rw [e4_1]; simp only [f0_1, f1_1, f2_1, f3_1, f4_1, f5_1, f6_1], by rw [e4_2]; simp only [f0_2, f1_2, f2_2, f3_2, f4_2, f5_2, f6_2], by rw [e4_3]; simp only [f0_3, f1_3, f2_3, f3_3, f4_3, f5_3, f6_3], by rw [e4_4]; simp only [f0_4, f1_4, f2_4, f3_4, f4_4, f5_4, f6_4], by rw [e4_5]; simp only [f0_5, f1_5, f2_5, f3_5, f4_5, f5_5, f6_5], by rw [e4_6]; simp only [f0_6, f1_6, f2_6, f3_6, f4_6, f5_6, f6_6], by rw [e5_0]; simp only [f0_0, f1_0, f2_0, f3_0, f4_0, f5_0, f6_0], by rw [e5_1]; simp only [f0_1, f1_1, f2_1, f3_1, f4_1, f5_1, f6_1], by rw [e5_2]; simp only [f0_2, f1_2, f2_2, f3_2, f4_2, f5_2, f6_2], by rw [e5_3]; simp only [f0_3, f1_3, f2_3, f3_3, f4_3, f5_3, f6_3], by rw [e5_4]; simp only [f0_4, f1_4, f2_4, f3_4, f4_4, f5_4, f6_4], by rw [e5_5]; simp only [f0_5, f1_5, f2_5, f3_5, f4_5, f5_5, f6_5], by rw [e5_6]; simp only [f0_6, f1_6, f2_6, f3_6, f4_6, f5_6, f6_6], by rw [e6_0]; simp only [f1_0, f2_0, f3_0, f4_0, f5_0, f6_0], by rw [e6_1]; simp only [f1_1, f2_1, f3_1, f4_1, f5_1, f6_1], by rw [e6_2]; simp only [f1_2, f2_2, f3_2, f4_2, f5_2, f6_2], by rw [e6_3]; simp only [f1_3, f2_3, f3_3, f4_3, f5_3, f6_3], by rw [e6_4]; simp only [f1_4, f2_4, f3_4, f4_4, f5_4, f6_4], by rw [e6_5]; simp only [f1_5, f2_5, f3_5, f4_5, f5_5, f6_5], by rw [e6_6]; simp only [f1_6, f2_6, f3_6, f4_6, f5_6, f6_6]⟩

theorem L2 : H 2 0 0 = 6 ∧ H 2 0 1 = 6 ∧ H 2 0 2 = 6 ∧ H 2 0 3 = 6 ∧ H 2 0 4 = 6 ∧ H 2 0 5 = 6 ∧ H 2 0 6 = 5 ∧ H 2 1 0 = 6 ∧ H 2 1 1 = 7 ∧ H 2 1 2 = 7 ∧ H 2 1 3 = 7 ∧ H 2 1 4 = 7 ∧ H 2 1 5 = 7 ∧ H 2 1 6 = 6 ∧ H 2 2 0 = 6 ∧ H 2 2 1 = 7 ∧ H 2 2 2 = 7 ∧ H 2 2 3 = 7 ∧ H 2 2 4 = 7 ∧ H 2 2 5 = 7 ∧ H 2 2 6 = 6 ∧ H 2 3 0 = 6 ∧ H 2 3 1 = 7 ∧ H 2 3 2 = 7 ∧ H 2 3 3 = 7 ∧ H 2 3 4 = 7 ∧ H 2 3 5 = 7 ∧ H 2 3 6 = 6 ∧ H 2 4 0 = 6 ∧ H 2 4 1 = 7 ∧ H 2 4 2 = 7 ∧ H 2 4 3 = 7 ∧ H 2 4 4 = 7 ∧ H 2 4 5 = 7 ∧ H 2 4 6 = 6 ∧ H 2 5 0 = 6 ∧ H 2 5 1 = 7 ∧ H 2 5 2 = 7 ∧ H 2 5 3 = 7 ∧ H 2 5 4 = 7 ∧ H 2 5 5 = 7 ∧ H 2 5 6 = 6 ∧ H 2 6 0 = 5 ∧ H 2 6 1 = 6 ∧ H 2 6 2 = 6 ∧ H 2 6 3 = 6 ∧ H 2 6 4 = 6 ∧ H 2 6 5 = 6 ∧ H 2 6 6 = 6 := by
  obtain ⟨e0_0, e0_1, e0_2, e0_3, e0_4, e0_5, e0_6, e1_0, e1_1, e1_2, e1_3, e1_4, e1_5, e1_6, e2_0, e2_1, e2_2, e2_3, e2_4, e2_5, e2_6, e3_0, e3_1, e3_2, e3_3, e3_4, e3_5, e3_6, e4_0, e4_1, e4_2, e4_3, e4_4, e4_5, e4_6, e5_0, e5_1, e5_2, e5_3, e5_4, e5_5, e5_6, e6_0, e6_1, e6_2, e6_3, e6_4, e6_5, e6_6⟩ := Hs 1
  obtain ⟨f0_0, f0_1, f0_2, f0_3, f0_4, f0_5, f0_6, f1_0, f1_1, f1_2, f1_3, f1_4, f1_5, f1_6, f2_0, f2_1, f2_2, f2_3, f2_4, f2_5, f2_6, f3_0, f3_1, f3_2, f3_3, f3_4, f3_5, f3_6, f4_0, f4_1, f4_2, f4_3, f4_4, f4_5, f4_6, f5_0, f5_1, f5_2, f5_3, f5_4, f5_5, f5_6, f6_0, f6_1, f6_2, f6_3, f6_4, f6_5, f6_6⟩ := L1
  refine ⟨by rw [e0_0]; simp only [f0_0, f1_0, f2_0, f3_0, f4_0, f5_0], by rw [e0_1]; simp only [f0_1, f1_1, f2_1, f3_1, f4_1, f5_1], by rw [e0_2]; simp only [f0_2, f1_2, f2_2, f3_2, f4_2, f5_2], by rw [e0_3]; simp only [f0_3, f1_3, f2_3, f3_3, f4_3, f5_3], by rw [e0_4]; simp only [f0_4, f1_4, f2_4, f3_4, f4_4, f5_4], by rw [e0_5]; simp only [f0_5, f1_5, f2_5, f3_5, f4_5, f5_5], by rw [e0_6]; simp only [f0_6, f1_6, f2_6, f3_6, f4_6, f5_6], by rw [e1_0]; simp only [f0_0, f1_0, f2_0, f3_0, f4_0, f5_0, f6_0], by rw [e1_1]; simp only [f0_1, f1_1, f2_1, f3_1, f4_1, f5_1, f6_1], by rw [e1_2]; simp only [f0_2, f1_2, f2_2, f3_2, f4_2, f5_2, f6_2], by rw [e1_3]; simp only [f0_3, f1_3, f2_3, f3_3, f4_3, f5_3, f6_3], by rw [e1_4]; simp only [f0_4, f1_4, f2_4, f3_4, f4_4, f5_4, f6_4], by rw [e1_5]; simp only [f0_5, f1_5, f2_5, f3_5, f4_5, f5_5, f6_5], by rw [e1_6]; simp only [f0_6, f1_6, f2_6, f3_6, f4_6, f5_6, f6_6], by rw [e2_0]; simp only [f0_0, f1_0, f2_0, f3_0, f4_0, f5_0, f6_0], by rw [e2_1]; simp only [f0_1, f1_1, f2_1, f3_1, f4_1, f5_1, f6_1], by rw [e2_2]; simp only [f0_2, f1_2, f2_2, f3_2, f4_2, f5_2, f6_2], by rw [e2_3]; simp only [f0_3, f1_3, f2_3, f3_3, f4_3, f5_3, f6_3], by rw [e2_4]; simp only [f0_4, f1_4, f2_4, f3_4, f4_4, f5_4, f6_4], by rw [e2_5]; simp only [f0_5, f1_5, f2_5, f3_5, f4_5, f5_5, f6_5], by rw [e2_6]; simp only [f0_6, f1_6, f2_6, f3_6, f4_6, f5_6, f6_6], by rw [e3_0]; simp only [f0_0, f1_0, f2_0, f3_0, f4_0, f5_0, f6_0], by rw [e3_1]; simp only [f0_1, f1_1, f2_1, f3_1, f4_1, f5_1, f6_1], by rw [e3_2]; simp only [f0_2, f1_2, f2_2, f3_2, f4_2, f5_2, f6_2], by rw [e3_3]; simp only [f0_3, f1_3, f2_3, f3_3, f4_3, f5_3, f6_3], by rw [e3_4]; simp only [f0_4, f1_4, f2_4, f3_4, f4_4, f5_4, f6_4], by rw [e3_5]; simp only [f0_5, f1_5, f2_5, f3_5, f4_5, f5_5, f6_5], by rw [e3_6]; simp only [f0_6, f1_6, f2_6, f3_6, f4_6, f5_6, f6_6], by rw [e4_0]; simp only [f0_0, f1_0, f2_0, f3_0, f4_0, f5_0, f6_0], by rw [e4_1]; simp only [f0_1, f1_1, f2_1, f3_1, f4_1, f5_1, f6_1], by rw [e4_2]; simp only [f0_2, f1_2, f2_2, f3_2, f4_2, f5_2, f6_2], by rw [e4_3]; simp only [f0_3, f1_3, f2_3, f3_3, f4_3, f5_3, f6_3], by rw [e4_4]; simp only [f0_4, f1_4, f2_4, f3_4, f4_4, f5_4, f6_4], by rw [e4_5]; simp only [f0_5, f1_5, f2_5, f3_5, f4_5, f5_5, f6_5], by rw [e4_6]; simp only [f0_6, f1_6, f2_6, f3_6, f4_6, f5_6, f6_6], by rw [e5_0]; simp only [f0_0, f1_0, f2_0, f3_0, f4_0, f5_0, f6_0], by rw [e5_1]; simp only [f0_1, f1_1, f2_1, f3_1, f4_1, f5_1, f6_1], by rw [e5_2]; simp only [f0_2, f1_2, f2_2, f3_2, f4_2, f5_2, f6_2], by rw [e5_3]; simp only [f0_3, f1_3, f2_3, f3_3, f4_3, f5_3, f6_3], by rw [e5_4]; simp only [f0_4, f1_4, f2_4, f3_4, f4_4, f5_4, f6_4], by rw [e5_5]; simp only [f0_5, f1_5, f2_5, f3_5, f4_5, f5_5, f6_5], by rw [e5_6]; simp only [f0_6, f1_6, f2_6, f3_6, f4_6, f5_6, f6_6], by rw [e6_0]; simp only [f1_0, f2_0, f3_0, f4_0, f5_0, f6_0], by rw [e6_1]; simp only [f1_1, f2_1, f3_1, f4_1, f5_1, f6_1], by rw [e6_2]; simp only [f1_2, f2_2, f3_2, f4_2, f5_2, f6_2], by rw [e6_3]; simp only [f1_3, f2_3, f3_3, f4_3, f5_3, f6_3], by rw [e6_4]; simp only [f1_4, f2_4, f3_4, f4_4, f5_4, f6_4], by rw [e6_5]; simp only [f1_5, f2_5, f3_5, f4_5, f5_5, f6_5], by rw [e6_6]; simp only [f1_6, f2_6, f3_6, f4_6, f5_6, f6_6]⟩

theorem L3 : H 3 0 0 = 36 ∧ H 3 0 1 = 41 ∧ H 3 0 2 = 41 ∧ H 3 0 3 = 41 ∧ H 3 0 4 = 41 ∧ H 3 0 5 = 41 ∧ H 3 0 6 = 35 ∧ H 3 1 0 = 41 ∧ H 3 1 1 = 47 ∧ H 3 1 2 = 47 ∧ H 3 1 3 = 47 ∧ H 3 1 4 = 47 ∧ H 3 1 5 = 47 ∧ H 3 1 6 = 41 ∧ H 3 2 0 = 41 ∧ H 3 2 1 = 47 ∧ H 3 2 2 = 47 ∧ H 3 2 3 = 47 ∧ H 3 2 4 = 47 ∧ H 3 2 5 = 47 ∧ H 3 2 6 = 41 ∧ H 3 3 0 = 41 ∧ H 3 3 1 = 47 ∧ H 3 3 2 = 47 ∧ H 3 3 3 = 47 ∧ H 3 3 4 = 47 ∧ H 3 3 5 = 47 ∧ H 3 3 6 = 41 ∧ H 3 4 0 = 41 ∧ H 3 4 1 = 47 ∧ H 3 4 2 = 47 ∧ H 3 4 3 = 47 ∧ H 3 4 4 = 47 ∧ H 3 4 5 = 47 ∧ H 3 4 6 = 41 ∧ H 3 5 0 = 41 ∧ H 3 5 1 = 47 ∧ H 3 5 2 = 47 ∧ H 3 5 3 = 47 ∧ H 3 5 4 = 47 ∧ H 3 5 5 = 47 ∧ H 3 5 6 = 41 ∧ H 3 6 0 = 35 ∧ H 3 6 1 = 41 ∧ H 3 6 2 = 41 ∧ H 3 6 3 = 41 ∧ H 3 6 4 = 41 ∧ H 3 6 5 = 41 ∧ H 3 6 6 = 36 := by
  obtain ⟨e0_0, e0_1, e0_2, e0_3, e0_4, e0_5, e0_6, e1_0, e1_1, e1_2, e1_3, e1_4, e1_5, e1_6, e2_0, e2_1, e2_2, e2_3, e2_4, e2_5, e2_6, e3_0, e3_1, e3_2, e3_3, e3_4, e3_5, e3_6, e4_0, e4_1, e4_2, e4_3, e4_4, e4_5, e4_6, e5_0, e5_1, e5_2, e5_3, e5_4, e5_5, e5_6, e6_0, e6_1, e6_2, e6_3, e6_4, e6_5, e6_6⟩ := Hs 2
  obtain ⟨f0_0, f0_1, f0_2, f0_3, f0_4, f0_5, f0_6, f1_0, f1_1, f1_2, f1_3, f1_4, f1_5, f1_6, f2_0, f2_1, f2_2, f2_3, f2_4, f2_5, f2_6, f3_0, f3_1, f3_2, f3_3, f3_4, f3_5, f3_6, f4_0, f4_1, f4_2, f4_3, f4_4, f4_5, f4_6, f5_0, f5_1, f5_2, f5_3, f5_4, f5_5, f5_6, f6_0, f6_1, f6_2, f6_3, f6_4, f6_5, f6_6⟩ := L2
  refine ⟨by rw [e0_0]; simp only [f0_0, f1_0, f2_0, f3_0, f4_0, f5_0], by rw [e0_1]; simp only [f0_1, f1_1, f2_1, f3_1, f4_1, f5_1], by rw [e0_2]; simp only [f0_2, f1_2, f2_2, f3_2, f4_2, f5_2], by rw [e0_3]; simp only [f0_3, f1_3, f2_3, f3_3, f4_3, f5_3], by rw [e0_4]; simp only [f0_4, f1_4, f2_4, f3_4, f4_4, f5_4], by rw [e0_5]; simp only [f0_5, f1_5, f2_5, f3_5, f4_5, f5_5], by rw [e0_6]; simp only [f0_6, f1_6, f2_6, f3_6, f4_6, f5_6], by rw [e1_0]; simp only [f0_0, f1_0, f2_0, f3_0, f4_0, f5_0, f6_0], by rw [e1_1]; simp only [f0_1, f1_1, f2_1, f3_1, f4_1, f5_1, f6_1], by rw [e1_2]; simp only [f0_2, f1_2, f2_2, f3_2, f4_2, f5_2, f6_2], by rw [e1_3]; simp only [f0_3, f1_3, f2_3, f3_3, f4_3, f5_3, f6_3], by rw [e1_4]; simp only [f0_4, f1_4, f2_4, f3_4, f4_4, f5_4, f6_4], by rw [e1_5]; simp only [f0_5, f1_5, f2_5, f3_5, f4_5, f5_5, f6_5], by rw [e1_6]; simp only [f0_6, f1_6, f2_6, f3_6, f4_6, f5_6, f6_6], by rw [e2_0]; simp only [f0_0, f1_0, f2_0, f3_0, f4_0, f5_0, f6_0], by rw [e2_1]; simp only [f0_1, f1_1, f2_1, f3_1, f4_1, f5_1, f6_1], by rw [e2_2]; simp only [f0_2, f1_2, f2_2, f3_2, f4_2, f5_2, f6_2], by rw [e2_3]; simp only [f0_3, f1_3, f2_3, f3_3, f4_3, f5_3, f6_3], by rw [e2_4]; simp only [f0_4, f1_4, f2_4, f3_4, f4_4, f5_4, f6_4], by rw [e2_5]; simp only [f0_5, f1_5, f2_5, f3_5, f4_5, f5_5, f6_5], by rw [e2_6]; simp only [f0_6, f1_6, f2_6, f3_6, f4_6, f5_6, f6_6], by rw [e3_0]; simp only [f0_0, f1_0, f2_0, f3_0, f4_0, f5_0, f6_0], by rw [e3_1]; simp only [f0_1, f1_1, f2_1, f3_1, f4_1, f5_1, f6_1], by rw [e3_2]; simp only [f0_2, f1_2, f2_2, f3_2, f4_2, f5_2, f6_2], by rw [e3_3]; simp only [f0_3, f1_3, f2_3, f3_3, f4_3, f5_3, f6_3], by rw [e3_4]; simp only [f0_4, f1_4, f2_4, f3_4, f4_4, f5_4, f6_4], by rw [e3_5]; simp only [f0_5, f1_5, f2_5, f3_5, f4_5, f5_5, f6_5], by rw [e3_6]; simp only [f0_6, f1_6, f2_6, f3_6, f4_6, f5_6, f6_6], by rw [e4_0]; simp only [f0_0, f1_0, f2_0, f3_0, f4_0, f5_0, f6_0], by rw [e4_1]; simp only [f0_1, f1_1, f2_1, f3_1, f4_1, f5_1, f6_1], by rw [e4_2]; simp only [f0_2, f1_2, f2_2, f3_2, f4_2, f5_2, f6_2], by rw [e4_3]; simp only [f0_3, f1_3, f2_3, f3_3, f4_3, f5_3, f6_3], by rw [e4_4]; simp only [f0_4, f1_4, f2_4, f3_4, f4_4, f5_4, f6_4], by rw [e4_5]; simp only [f0_5, f1_5, f2_5, f3_5, f4_5, f5_5, f6_5], by rw [e4_6]; simp only [f0_6, f1_6, f2_6, f3_6, f4_6, f5_6, f6_6], by rw [e5_0]; simp only [f0_0, f1_0, f2_0, f3_0, f4_0, f5_0, f6_0], by rw [e5_1]; simp only [f0_1, f1_1, f2_1, f3_1, f4_1, f5_1, f6_1], by rw [e5_2]; simp only [f0_2, f1_2, f2_2, f3_2, f4_2, f5_2, f6_2], by rw [e5_3]; simp only [f0_3, f1_3, f2_3, f3_3, f4_3, f5_3, f6_3], by rw [e5_4]; simp only [f0_4, f1_4, f2_4, f3_4, f4_4, f5_4, f6_4], by rw [e5_5]; simp only [f0_5, f1_5, f2_5, f3_5, f4_5, f5_5, f6_5], by rw [e5_6]; simp only [f0_6, f1_6, f2_6, f3_6, f4_6, f5_6, f6_6], by rw [e6_0]; simp only [f1_0, f2_0, f3_0, f4_0, f5_0, f6_0], by rw [e6_1]; simp only [f1_1, f2_1, f3_1, f4_1, f5_1, f6_1], by rw [e6_2]; simp only [f1_2, f2_2, f3_2, f4_2, f5_2, f6_2], by rw [e6_3]; simp only [f1_3, f2_3, f3_3, f4_3, f5_3, f6_3], by rw [e6_4]; simp only [f1_4, f2_4, f3_4, f4_4, f5_4, f6_4], by rw [e6_5]; simp only [f1_5, f2_5, f3_5, f4_5, f5_5, f6_5], by rw [e6_6]; simp only [f1_6, f2_6, f3_6, f4_6, f5_6, f6_6]⟩

theorem L4 : H 4 0 0 = 241 ∧ H 4 0 1 = 276 ∧ H 4 0 2 = 276 ∧ H 4 0 3 = 276 ∧ H 4 0 4 = 276 ∧ H 4 0 5 = 276 ∧ H 4 0 6 = 240 ∧ H 4 1 0 = 276 ∧ H 4 1 1 = 317 ∧ H 4 1 2 = 317 ∧ H 4 1 3 = 317 ∧ H 4 1 4 = 317 ∧ H 4 1 5 = 317 ∧ H 4 1 6 = 276 ∧ H 4 2 0 = 276 ∧ H 4 2 1 = 317 ∧ H 4 2 2 = 317 ∧ H 4 2 3 = 317 ∧ H 4 2 4 = 317 ∧ H 4 2 5 = 317 ∧ H 4 2 6 = 276 ∧ H 4 3 0 = 276 ∧ H 4 3 1 = 317 ∧ H 4 3 2 = 317 ∧ H 4 3 3 = 317 ∧ H 4 3 4 = 317 ∧ H 4 3 5 = 317 ∧ H 4 3 6 = 276 ∧ H 4 4 0 = 276 ∧ H 4 4 1 = 317 ∧ H 4 4 2 = 317 ∧ H 4 4 3 = 317 ∧ H 4 4 4 = 317 ∧ H 4 4 5 = 317 ∧ H 4 4 6 = 276 ∧ H 4 5 0 = 276 ∧ H 4 5 1 = 317 ∧ H 4 5 2 = 317 ∧ H 4 5 3 = 317 ∧ H 4 5 4 = 317 ∧ H 4 5 5 = 317 ∧ H 4 5 6 = 276 ∧ H 4 6 0 = 240 ∧ H 4 6 1 = 276 ∧ H 4 6 2 = 276 ∧ H 4 6 3 = 276 ∧ H 4 6 4 = 276 ∧ H 4 6 5 = 276 ∧ H 4 6 6 = 241 := by
  obtain ⟨e0_0, e0_1, e0_2, e0_3, e0_4, e0_5, e0_6, e1_0, e1_1, e1_2, e1_3, e1_4, e1_5, e1_6, e2_0, e2_1, e2_2, e2_3, e2_4, e2_5, e2_6, e3_0, e3_1, e3_2, e3_3, e3_4, e3_5, e3_6, e4_0, e4_1, e4_2, e4_3, e4_4, e4_5, e4_6, e5_0, e5_1, e5_2, e5_3, e5_4, e5_5, e5_6, e6_0, e6_1, e6_2, e6_3, e6_4, e6_5, e6_6⟩ := Hs 3
  obtain ⟨f0_0, f0_1, f0_2, f0_3, f0_4, f0_5, f0_6, f1_0, f1_1, f1_2, f1_3, f1_4, f1_5, f1_6, f2_0, f2_1, f2_2, f2_3, f2_4, f2_5, f2_6, f3_0, f3_1, f3_2, f3_3, f3_4, f3_5, f3_6, f4_0, f4_1, f4_2, f4_3, f4_4, f4_5, f4_6, f5_0, f5_1, f5_2, f5_3, f5_4, f5_5, f5_6, f6_0, f6_1, f6_2, f6_3, f6_4, f6_5, f6_6⟩ := L3
  refine ⟨by rw [e0_0]; simp only [f0_0, f1_0, f2_0, f3_0, f4_0, f5_0], by rw [e0_1]; simp only [f0_1, f1_1, f2_1, f3_1, f4_1, f5_1], by rw [e0_2]; simp only [f0_2, f1_2, f2_2, f3_2, f4_2, f5_2], by rw [e0_3]; simp only [f0_3, f1_3, f2_3, f3_3, f4_3, f5_3], by rw [e0_4]; simp only [f0_4, f1_4, f2_4, f3_4, f4_4, f5_4], by rw [e0_5]; simp only [f0_5, f1_5, f2_5, f3_5, f4_5, f5_5], by rw [e0_6]; simp only [f0_6, f1_6, f2_6, f3_6, f4_6, f5_6], by rw [e1_0]; simp only [f0_0, f1_0, f2_0, f3_0, f4_0, f5_0, f6_0], by rw [e1_1]; simp only [f0_1, f1_1, f2_1, f3_1, f4_1, f5_1, f6_1], by rw [e1_2]; simp only [f0_2, f1_2, f2_2, f3_2, f4_2, f5_2, f6_2], by rw [e1_3]; simp only [f0_3, f1_3, f2_3, f3_3, f4_3, f5_3, f6_3], by rw [e1_4]; simp only [f0_4, f1_4, f2_4, f3_4, f4_4, f5_4, f6_4], by rw [e1_5]; simp only [f0_5, f1_5, f2_5, f3_5, f4_5, f5_5, f6_5], by rw [e1_6]; simp only [f0_6, f1_6, f2_6, f3_6, f4_6, f5_6, f6_6], by rw [e2_0]; simp only [f0_0, f1_0, f2_0, f3_0, f4_0, f5_0, f6_0], by rw [e2_1]; simp only [f0_1, f1_1, f2_1, f3_1, f4_1, f5_1, f6_1], by rw [e2_2]; simp only [f0_2, f1_2, f2_2, f3_2, f4_2, f5_2, f6_2], by rw [e2_3]; simp only [f0_3, f1_3, f2_3, f3_3, f4_3, f5_3, f6_3], by rw [e2_4]; simp only [f0_4, f1_4, f2_4, f3_4, f4_4, f5_4, f6_4], by rw [e2_5]; simp only [f0_5, f1_5, f2_5, f3_5, f4_5, f5_5, f6_5], by rw [e2_6]; simp only [f0_6, f1_6, f2_6, f3_6, f4_6, f5_6, f6_6], by rw [e3_0]; simp only [f0_0, f1_0, f2_0, f3_0, f4_0, f5_0, f6_0], by rw [e3_1]; simp only [f0_1, f1_1, f2_1, f3_1, f4_1, f5_1, f6_1], by rw [e3_2]; simp only [f0_2, f1_2, f2_2, f3_2, f4_2, f5_2, f6_2], by rw [e3_3]; simp only [f0_3, f1_3, f2_3, f3_3, f4_3, f5_3, f6_3], by rw [e3_4]; simp only [f0_4, f1_4, f2_4, f3_4, f4_4, f5_4, f6_4], by rw [e3_5]; simp only [f0_5, f1_5, f2_5, f3_5, f4_5, f5_5, f6_5], by rw [e3_6]; simp only [f0_6, f1_6, f2_6, f3_6, f4_6, f5_6, f6_6], by rw [e4_0]; simp only [f0_0, f1_0, f2_0, f3_0, f4_0, f5_0, f6_0], by rw [e4_1]; simp only [f0_1, f1_1, f2_1, f3_1, f4_1, f5_1, f6_1], by rw [e4_2]; simp only [f0_2, f1_2, f2_2, f3_2, f4_2, f5_2, f6_2], by rw [e4_3]; simp only [f0_3, f1_3, f2_3, f3_3, f4_3, f5_3, f6_3], by rw [e4_4]; simp only [f0_4, f1_4, f2_4, f3_4, f4_4, f5_4, f6_4], by rw [e4_5]; simp only [f0_5, f1_5, f2_5, f3_5, f4_5, f5_5, f6_5], by rw [e4_6]; simp only [f0_6, f1_6, f2_6, f3_6, f4_6, f5_6, f6_6], by rw [e5_0]; simp only [f0_0, f1_0, f2_0, f3_0, f4_0, f5_0, f6_0], by rw [e5_1]; simp only [f0_1, f1_1, f2_1, f3_1, f4_1, f5_1, f6_1], by rw [e5_2]; simp only [f0_2, f1_2, f2_2, f3_2, f4_2, f5_2, f6_2], by rw [e5_3]; simp only [f0_3, f1_3, f2_3, f3_3, f4_3, f5_3, f6_3], by rw [e5_4]; simp only [f0_4, f1_4, f2_4, f3_4, f4_4, f5_4, f6_4], by rw [e5_5]; simp only [f0_5, f1_5, f2_5, f3_5, f4_5, f5_5, f6_5], by rw [e5_6]; simp only [f0_6, f1_6, f2_6, f3_6, f4_6, f5_6, f6_6], by rw [e6_0]; simp only [f1_0, f2_0, f3_0, f4_0, f5_0, f6_0], by rw [e6_1]; simp only [f1_1, f2_1, f3_1, f4_1, f5_1, f6_1], by rw [e6_2]; simp only [f1_2, f2_2, f3_2, f4_2, f5_2, f6_2], by rw [e6_3]; simp only [f1_3, f2_3, f3_3, f4_3, f5_3, f6_3], by rw [e6_4]; simp only [f1_4, f2_4, f3_4, f4_4, f5_4, f6_4], by rw [e6_5]; simp only [f1_5, f2_5, f3_5, f4_5, f5_5, f6_5], by rw [e6_6]; simp only [f1_6, f2_6, f3_6, f4_6, f5_6, f6_6]⟩

theorem A0 : a 0 = 1 := by decide

theorem A1 : a 1 = 7 := by
  rw [a_succ]
  simp only [sumK, adj_iff]
  obtain ⟨f0_0, f0_1, f0_2, f0_3, f0_4, f0_5, f0_6, f1_0, f1_1, f1_2, f1_3, f1_4, f1_5, f1_6, f2_0, f2_1, f2_2, f2_3, f2_4, f2_5, f2_6, f3_0, f3_1, f3_2, f3_3, f3_4, f3_5, f3_6, f4_0, f4_1, f4_2, f4_3, f4_4, f4_5, f4_6, f5_0, f5_1, f5_2, f5_3, f5_4, f5_5, f5_6, f6_0, f6_1, f6_2, f6_3, f6_4, f6_5, f6_6⟩ := L0
  simp only [f0_0, f0_1, f0_2, f0_3, f0_4, f0_5, f0_6, f1_0, f1_1, f1_2, f1_3, f1_4, f1_5, f1_6, f2_0, f2_1, f2_2, f2_3, f2_4, f2_5, f2_6, f3_0, f3_1, f3_2, f3_3, f3_4, f3_5, f3_6, f4_0, f4_1, f4_2, f4_3, f4_4, f4_5, f4_6, f5_0, f5_1, f5_2, f5_3, f5_4, f5_5, f5_6, f6_0, f6_1, f6_2, f6_3, f6_4, f6_5, f6_6]
  decide

theorem A2 : a 2 = 47 := by
  rw [a_succ]
  simp only [sumK, adj_iff]
  obtain ⟨f0_0, f0_1, f0_2, f0_3, f0_4, f0_5, f0_6, f1_0, f1_1, f1_2, f1_3, f1_4, f1_5, f1_6, f2_0, f2_1, f2_2, f2_3, f2_4, f2_5, f2_6, f3_0, f3_1, f3_2, f3_3, f3_4, f3_5, f3_6, f4_0, f4_1, f4_2, f4_3, f4_4, f4_5, f4_6, f5_0, f5_1, f5_2, f5_3, f5_4, f5_5, f5_6, f6_0, f6_1, f6_2, f6_3, f6_4, f6_5, f6_6⟩ := L1
  simp only [f0_0, f0_1, f0_2, f0_3, f0_4, f0_5, f0_6, f1_0, f1_1, f1_2, f1_3, f1_4, f1_5, f1_6, f2_0, f2_1, f2_2, f2_3, f2_4, f2_5, f2_6, f3_0, f3_1, f3_2, f3_3, f3_4, f3_5, f3_6, f4_0, f4_1, f4_2, f4_3, f4_4, f4_5, f4_6, f5_0, f5_1, f5_2, f5_3, f5_4, f5_5, f5_6, f6_0, f6_1, f6_2, f6_3, f6_4, f6_5, f6_6]
  decide

theorem A3 : a 3 = 307 := by
  rw [a_succ]
  simp only [sumK, adj_iff]
  obtain ⟨f0_0, f0_1, f0_2, f0_3, f0_4, f0_5, f0_6, f1_0, f1_1, f1_2, f1_3, f1_4, f1_5, f1_6, f2_0, f2_1, f2_2, f2_3, f2_4, f2_5, f2_6, f3_0, f3_1, f3_2, f3_3, f3_4, f3_5, f3_6, f4_0, f4_1, f4_2, f4_3, f4_4, f4_5, f4_6, f5_0, f5_1, f5_2, f5_3, f5_4, f5_5, f5_6, f6_0, f6_1, f6_2, f6_3, f6_4, f6_5, f6_6⟩ := L2
  simp only [f0_0, f0_1, f0_2, f0_3, f0_4, f0_5, f0_6, f1_0, f1_1, f1_2, f1_3, f1_4, f1_5, f1_6, f2_0, f2_1, f2_2, f2_3, f2_4, f2_5, f2_6, f3_0, f3_1, f3_2, f3_3, f3_4, f3_5, f3_6, f4_0, f4_1, f4_2, f4_3, f4_4, f4_5, f4_6, f5_0, f5_1, f5_2, f5_3, f5_4, f5_5, f5_6, f6_0, f6_1, f6_2, f6_3, f6_4, f6_5, f6_6]
  decide

theorem A4 : a 4 = 2067 := by
  rw [a_succ]
  simp only [sumK, adj_iff]
  obtain ⟨f0_0, f0_1, f0_2, f0_3, f0_4, f0_5, f0_6, f1_0, f1_1, f1_2, f1_3, f1_4, f1_5, f1_6, f2_0, f2_1, f2_2, f2_3, f2_4, f2_5, f2_6, f3_0, f3_1, f3_2, f3_3, f3_4, f3_5, f3_6, f4_0, f4_1, f4_2, f4_3, f4_4, f4_5, f4_6, f5_0, f5_1, f5_2, f5_3, f5_4, f5_5, f5_6, f6_0, f6_1, f6_2, f6_3, f6_4, f6_5, f6_6⟩ := L3
  simp only [f0_0, f0_1, f0_2, f0_3, f0_4, f0_5, f0_6, f1_0, f1_1, f1_2, f1_3, f1_4, f1_5, f1_6, f2_0, f2_1, f2_2, f2_3, f2_4, f2_5, f2_6, f3_0, f3_1, f3_2, f3_3, f3_4, f3_5, f3_6, f4_0, f4_1, f4_2, f4_3, f4_4, f4_5, f4_6, f5_0, f5_1, f5_2, f5_3, f5_4, f5_5, f5_6, f6_0, f6_1, f6_2, f6_3, f6_4, f6_5, f6_6]
  decide

theorem A5 : a 5 = 13927 := by
  rw [a_succ]
  simp only [sumK, adj_iff]
  obtain ⟨f0_0, f0_1, f0_2, f0_3, f0_4, f0_5, f0_6, f1_0, f1_1, f1_2, f1_3, f1_4, f1_5, f1_6, f2_0, f2_1, f2_2, f2_3, f2_4, f2_5, f2_6, f3_0, f3_1, f3_2, f3_3, f3_4, f3_5, f3_6, f4_0, f4_1, f4_2, f4_3, f4_4, f4_5, f4_6, f5_0, f5_1, f5_2, f5_3, f5_4, f5_5, f5_6, f6_0, f6_1, f6_2, f6_3, f6_4, f6_5, f6_6⟩ := L4
  simp only [f0_0, f0_1, f0_2, f0_3, f0_4, f0_5, f0_6, f1_0, f1_1, f1_2, f1_3, f1_4, f1_5, f1_6, f2_0, f2_1, f2_2, f2_3, f2_4, f2_5, f2_6, f3_0, f3_1, f3_2, f3_3, f3_4, f3_5, f3_6, f4_0, f4_1, f4_2, f4_3, f4_4, f4_5, f4_6, f5_0, f5_1, f5_2, f5_3, f5_4, f5_5, f5_6, f6_0, f6_1, f6_2, f6_3, f6_4, f6_5, f6_6]
  decide

theorem aH (m : ℕ) : a (m + 1) = H m 0 0 + H m 0 1 + H m 0 2 + H m 0 3 + H m 0 4 + H m 0 5 + H m 1 0 + H m 1 1 + H m 1 2 + H m 1 3 + H m 1 4 + H m 1 5 + H m 1 6 + H m 2 0 + H m 2 1 + H m 2 2 + H m 2 3 + H m 2 4 + H m 2 5 + H m 2 6 + H m 3 0 + H m 3 1 + H m 3 2 + H m 3 3 + H m 3 4 + H m 3 5 + H m 3 6 + H m 4 0 + H m 4 1 + H m 4 2 + H m 4 3 + H m 4 4 + H m 4 5 + H m 4 6 + H m 5 0 + H m 5 1 + H m 5 2 + H m 5 3 + H m 5 4 + H m 5 5 + H m 5 6 + H m 6 1 + H m 6 2 + H m 6 3 + H m 6 4 + H m 6 5 + H m 6 6 := by
  rw [a_succ]
  simp only [sumK]
  simp [adj_iff]
  ring

set_option maxHeartbeats 0 in
theorem arec (m : ℕ) : (a (m + 4) : ℤ) = 7 * (a (m + 3) : ℤ) - (a (m + 2) : ℤ) - 5 * (a (m + 1) : ℤ) := by
  have h0 := aH (m + 0)
  have h1 := aH (m + 1)
  have h2 := aH (m + 2)
  have h3 := aH (m + 3)
  obtain ⟨E0_0_0, E0_0_1, E0_0_2, E0_0_3, E0_0_4, E0_0_5, E0_0_6, E0_1_0, E0_1_1, E0_1_2, E0_1_3, E0_1_4, E0_1_5, E0_1_6, E0_2_0, E0_2_1, E0_2_2, E0_2_3, E0_2_4, E0_2_5, E0_2_6, E0_3_0, E0_3_1, E0_3_2, E0_3_3, E0_3_4, E0_3_5, E0_3_6, E0_4_0, E0_4_1, E0_4_2, E0_4_3, E0_4_4, E0_4_5, E0_4_6, E0_5_0, E0_5_1, E0_5_2, E0_5_3, E0_5_4, E0_5_5, E0_5_6, E0_6_0, E0_6_1, E0_6_2, E0_6_3, E0_6_4, E0_6_5, E0_6_6⟩ := Hs (m + 0)
  obtain ⟨E1_0_0, E1_0_1, E1_0_2, E1_0_3, E1_0_4, E1_0_5, E1_0_6, E1_1_0, E1_1_1, E1_1_2, E1_1_3, E1_1_4, E1_1_5, E1_1_6, E1_2_0, E1_2_1, E1_2_2, E1_2_3, E1_2_4, E1_2_5, E1_2_6, E1_3_0, E1_3_1, E1_3_2, E1_3_3, E1_3_4, E1_3_5, E1_3_6, E1_4_0, E1_4_1, E1_4_2, E1_4_3, E1_4_4, E1_4_5, E1_4_6, E1_5_0, E1_5_1, E1_5_2, E1_5_3, E1_5_4, E1_5_5, E1_5_6, E1_6_0, E1_6_1, E1_6_2, E1_6_3, E1_6_4, E1_6_5, E1_6_6⟩ := Hs (m + 1)
  obtain ⟨E2_0_0, E2_0_1, E2_0_2, E2_0_3, E2_0_4, E2_0_5, E2_0_6, E2_1_0, E2_1_1, E2_1_2, E2_1_3, E2_1_4, E2_1_5, E2_1_6, E2_2_0, E2_2_1, E2_2_2, E2_2_3, E2_2_4, E2_2_5, E2_2_6, E2_3_0, E2_3_1, E2_3_2, E2_3_3, E2_3_4, E2_3_5, E2_3_6, E2_4_0, E2_4_1, E2_4_2, E2_4_3, E2_4_4, E2_4_5, E2_4_6, E2_5_0, E2_5_1, E2_5_2, E2_5_3, E2_5_4, E2_5_5, E2_5_6, E2_6_0, E2_6_1, E2_6_2, E2_6_3, E2_6_4, E2_6_5, E2_6_6⟩ := Hs (m + 2)
  simp only [show ∀ t : ℕ, m + t + 1 = m + (t + 1) from fun t => rfl, Nat.add_zero] at *
  simp only [h0, h1, h2, h3]
  zify at *
  push_cast
  linear_combination (-5 : ℤ) * E0_0_0 + (-1 : ℤ) * E0_1_1 + (-1 : ℤ) * E0_1_2 + (-1 : ℤ) * E0_1_3 + (-1 : ℤ) * E0_1_4 + (-1 : ℤ) * E0_1_5 + (-1 : ℤ) * E0_2_1 + (-1 : ℤ) * E0_2_2 + (-1 : ℤ) * E0_2_3 + (-1 : ℤ) * E0_2_4 + (-1 : ℤ) * E0_2_5 + (-1 : ℤ) * E0_3_1 + (-1 : ℤ) * E0_3_2 + (-1 : ℤ) * E0_3_3 + (-1 : ℤ) * E0_3_4 + (-1 : ℤ) * E0_3_5 + (-1 : ℤ) * E0_4_1 + (-1 : ℤ) * E0_4_2 + (-1 : ℤ) * E0_4_3 + (-1 : ℤ) * E0_4_4 + (-1 : ℤ) * E0_4_5 + (-1 : ℤ) * E0_5_1 + (-1 : ℤ) * E0_5_2 + (-1 : ℤ) * E0_5_3 + (-1 : ℤ) * E0_5_4 + (-1 : ℤ) * E0_5_5 + (-5 : ℤ) * E0_6_6 + (-1 : ℤ) * E1_0_0 + (-1 : ℤ) * E1_0_1 + (-1 : ℤ) * E1_0_2 + (-1 : ℤ) * E1_0_3 + (-1 : ℤ) * E1_0_4 + (-1 : ℤ) * E1_0_5 + (5 : ℤ) * E1_0_6 + (-1 : ℤ) * E1_1_0 + (-1 : ℤ) * E1_1_6 + (-1 : ℤ) * E1_2_0 + (-1 : ℤ) * E1_2_6 + (-1 : ℤ) * E1_3_0 + (-1 : ℤ) * E1_3_6 + (-1 : ℤ) * E1_4_0 + (-1 : ℤ) * E1_4_6 + (-1 : ℤ) * E1_5_0 + (-1 : ℤ) * E1_5_6 + (5 : ℤ) * E1_6_0 + (-1 : ℤ) * E1_6_1 + (-1 : ℤ) * E1_6_2 + (-1 : ℤ) * E1_6_3 + (-1 : ℤ) * E1_6_4 + (-1 : ℤ) * E1_6_5 + (-1 : ℤ) * E1_6_6 + (1 : ℤ) * E2_0_0 + (1 : ℤ) * E2_0_1 + (1 : ℤ) * E2_0_2 + (1 : ℤ) * E2_0_3 + (1 : ℤ) * E2_0_4 + (1 : ℤ) * E2_0_5 + (1 : ℤ) * E2_1_0 + (1 : ℤ) * E2_1_1 + (1 : ℤ) * E2_1_2 + (1 : ℤ) * E2_1_3 + (1 : ℤ) * E2_1_4 + (1 : ℤ) * E2_1_5 + (1 : ℤ) * E2_1_6 + (1 : ℤ) * E2_2_0 + (1 : ℤ) * E2_2_1 + (1 : ℤ) * E2_2_2 + (1 : ℤ) * E2_2_3 + (1 : ℤ) * E2_2_4 + (1 : ℤ) * E2_2_5 + (1 : ℤ) * E2_2_6 + (1 : ℤ) * E2_3_0 + (1 : ℤ) * E2_3_1 + (1 : ℤ) * E2_3_2 + (1 : ℤ) * E2_3_3 + (1 : ℤ) * E2_3_4 + (1 : ℤ) * E2_3_5 + (1 : ℤ) * E2_3_6 + (1 : ℤ) * E2_4_0 + (1 : ℤ) * E2_4_1 + (1 : ℤ) * E2_4_2 + (1 : ℤ) * E2_4_3 + (1 : ℤ) * E2_4_4 + (1 : ℤ) * E2_4_5 + (1 : ℤ) * E2_4_6 + (1 : ℤ) * E2_5_0 + (1 : ℤ) * E2_5_1 + (1 : ℤ) * E2_5_2 + (1 : ℤ) * E2_5_3 + (1 : ℤ) * E2_5_4 + (1 : ℤ) * E2_5_5 + (1 : ℤ) * E2_5_6 + (1 : ℤ) * E2_6_1 + (1 : ℤ) * E2_6_2 + (1 : ℤ) * E2_6_3 + (1 : ℤ) * E2_6_4 + (1 : ℤ) * E2_6_5 + (1 : ℤ) * E2_6_6

end C125370

open C125370 PowerSeries in
set_option maxHeartbeats 0 in
theorem OMA.solution : type_of% @OMA.S_oeis_a125370.main := by
  have hrec : ∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 7 * (a (n - 1) : ℤ) - (a (n - 2) : ℤ) - 5 * (a (n - 3) : ℤ) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [arec m]
    simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega]
  have hrecQ : ∀ n : ℕ, 4 ≤ n → (a n : ℚ) = 7 * (a (n - 1) : ℚ) - (a (n - 2) : ℚ) - 5 * (a (n - 3) : ℚ) := by
    intro n hn; exact_mod_cast hrec n hn
  refine ⟨?_, ?_, ?_⟩
  · have hp : (((1 - X) * (1 - 6 * X - 5 * X ^ 2)) : PowerSeries ℚ) = 1 - PowerSeries.C (7 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.X ^ 2 + PowerSeries.C (5 : ℚ) * PowerSeries.X ^ 3 := by
      (try simp only [map_ofNat, map_one, one_mul, pow_one]) <;> ring
    have hr : (1 - X ^ 2 - 10 * X ^ 3 : PowerSeries ℚ) = 1 - PowerSeries.X ^ 2 - PowerSeries.C (10 : ℚ) * PowerSeries.X ^ 3 := by
      (try simp only [map_ofNat, map_one, one_mul, pow_one]) <;> ring
    have hq : ∀ F : PowerSeries ℚ, F * (1 - PowerSeries.C (7 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.X ^ 2 + PowerSeries.C (5 : ℚ) * PowerSeries.X ^ 3) = F - PowerSeries.C (7 : ℚ) * (F * PowerSeries.X ^ 1) + (F * PowerSeries.X ^ 2) + PowerSeries.C (5 : ℚ) * (F * PowerSeries.X ^ 3) := fun F => by ring
    rw [hp, hr, hq]
    ext n
    simp only [map_sub, map_add, map_neg, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_C_mul,
      PowerSeries.coeff_mk, PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
    rcases Nat.lt_or_ge n 6 with hn | hn
    · interval_cases n <;> simp [C125370.A0, C125370.A1, C125370.A2, C125370.A3, C125370.A4, C125370.A5] <;> norm_num
    · have h' := hrecQ n (by omega)
      simp (disch := omega) only [if_pos, if_neg, PowerSeries.coeff_C]
      linarith
  · have hs : Real.sqrt 14 ^ 2 = 14 := Real.sq_sqrt (by norm_num)
    have q1 : (3 - Real.sqrt 14) ^ 2 = (6 : ℝ) * (3 - Real.sqrt 14) + (5 : ℝ) := by linear_combination (1 : ℝ) * hs
    have q2 : (3 + Real.sqrt 14) ^ 2 = (6 : ℝ) * (3 + Real.sqrt 14) + (5 : ℝ) := by linear_combination (1 : ℝ) * hs
    have hsum : (3 - Real.sqrt 14) + (3 + Real.sqrt 14) = (6 : ℝ) := by ring
    generalize (3 - Real.sqrt 14) = x1 at q1 hsum ⊢
    generalize (3 + Real.sqrt 14) = x2 at q2 hsum ⊢
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      rcases (by omega : n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n) with rfl | rfl | rfl | h4
      · rw [C125370.A1]; push_cast; linear_combination (-1 : ℝ) * hsum
      · rw [C125370.A2]; push_cast; linear_combination (-1 : ℝ) * (q1 + q2 + (6 : ℝ) * hsum)
      · rw [C125370.A3]; push_cast
        linear_combination (-1 : ℝ) * ((x1 + (6 : ℝ)) * q1 + (x2 + (6 : ℝ)) * q2 + (41 : ℝ) * hsum)
      · have r := hrec n h4
        have r' : (a n : ℝ) = 7 * (a (n - 1) : ℝ) - (a (n - 2) : ℝ) - 5 * (a (n - 3) : ℝ) := by exact_mod_cast r
        rw [r', ih (n - 1) (by omega) (by omega), ih (n - 2) (by omega) (by omega),
          ih (n - 3) (by omega) (by omega)]
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
        rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega, show k + 3 - 3 = k by omega]
        linear_combination (-1 : ℝ) * ((x1 ^ k * (x1 - 1)) * q1 + (x2 ^ k * (x2 - 1)) * q2)
  · intro n hn
    have := hrec n hn
    linarith
