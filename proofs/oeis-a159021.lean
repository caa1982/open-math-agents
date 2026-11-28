import OMAStatements.S_oeis_a159021
import Mathlib

open OMA.S_oeis_a159021

namespace OMA.P_oeis_a159021

def Q (M x : ℕ) : Prop :=
  x = M * M ∨ x = M * M + M ∨ x = M * M + 2 * M ∨
    ∃ i j, i + j = M ∧ 1 ≤ i ∧ 1 ≤ j ∧ (x = (M + i) * (M + i) + j ∨ x = (M + i) * (M + i) + 2 * M)

def P (x : ℕ) : Prop :=
  x = 19 ∨ x = 23 ∨ x = 27 ∨ x = 32 ∨ x = 37 ∨ x = 43 ∨ ∃ k, Q (7 * 2 ^ k) x

theorem sq (n a : ℕ) (h : a ≤ n + n) : Nat.sqrt (n * n + a) = n := Nat.sqrt_add_eq n h

theorem stepQ' (M x : ℕ) (hM7 : 7 ≤ M) (hx : Q M x) :
    Q M (x + Nat.sqrt x) ∨ x + Nat.sqrt x = (2 * M) * (2 * M) := by
  rcases hx with rfl | rfl | rfl | ⟨i, j, hij, hi, hj, rfl | rfl⟩
  · left; refine Or.inr (Or.inl ?_)
    rw [Nat.sqrt_eq]
  · left; refine Or.inr (Or.inr (Or.inl ?_))
    rw [sq M M (by omega)]; ring
  · left; refine Or.inr (Or.inr (Or.inr ⟨1, M - 1, by omega, le_rfl, by omega, Or.inl ?_⟩))
    rw [sq M (2 * M) (by omega)]
    obtain ⟨t, rfl⟩ : ∃ t, M = t + 1 := ⟨M - 1, by omega⟩
    rw [show t + 1 - 1 = t by omega]; ring
  · left; refine Or.inr (Or.inr (Or.inr ⟨i, j, hij, hi, hj, Or.inr ?_⟩))
    rw [sq (M + i) j (by omega)]
    subst hij; ring
  · rw [sq (M + i) (2 * M) (by omega)]
    rcases Nat.lt_or_ge j 2 with hj1 | hj2
    · right
      obtain rfl : j = 1 := by omega
      subst hij; ring
    · left; refine Or.inr (Or.inr (Or.inr ⟨i + 1, j - 1, by omega, by omega, by omega, Or.inl ?_⟩))
      obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
      subst hij
      rw [show t + 1 - 1 = t by omega]; ring

theorem stepQ (k x : ℕ) (hx : Q (7 * 2 ^ k) x) : ∃ k', Q (7 * 2 ^ k') (x + Nat.sqrt x) := by
  have hM7 : 7 ≤ 7 * 2 ^ k := by
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  rcases stepQ' _ x hM7 hx with h | h
  · exact ⟨k, h⟩
  · refine ⟨k + 1, Or.inl ?_⟩
    rw [h, pow_succ]; ring

theorem stepP (x : ℕ) (hx : P x) : P (x + Nat.sqrt x) := by
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | ⟨k, hk⟩
  · right; left; rw [show (19 : ℕ) = 4 * 4 + 3 from rfl, sq 4 3 (by norm_num)]
  · right; right; left; rw [show (23 : ℕ) = 4 * 4 + 7 from rfl, sq 4 7 (by norm_num)]
  · right; right; right; left; rw [show (27 : ℕ) = 5 * 5 + 2 from rfl, sq 5 2 (by norm_num)]
  · right; right; right; right; left; rw [show (32 : ℕ) = 5 * 5 + 7 from rfl, sq 5 7 (by norm_num)]
  · right; right; right; right; right; left
    rw [show (37 : ℕ) = 6 * 6 + 1 from rfl, sq 6 1 (by norm_num)]
  · right; right; right; right; right; right
    refine ⟨0, Or.inl ?_⟩
    rw [show (43 : ℕ) = 6 * 6 + 7 from rfl, sq 6 7 (by norm_num)]
    norm_num
  · right; right; right; right; right; right
    exact stepQ k x hk

theorem allP (n : ℕ) : P (a n) := by
  induction n with
  | zero => left; rfl
  | succ n ih => exact stepP _ ih

theorem nsq (m x : ℕ) (h1 : m * m < x) (h2 : x < (m + 1) * (m + 1)) : ¬ IsSquare x := by
  rintro ⟨r, hr⟩
  exact Nat.not_exists_sq h1 h2 ⟨r, hr.symm⟩

end OMA.P_oeis_a159021

open OMA.P_oeis_a159021 in
theorem OMA.solution : type_of% @OMA.S_oeis_a159021.main := by
  intro n hsq
  have hP := allP n
  generalize a n = x at hP hsq ⊢
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | ⟨k, hk⟩
  · exact absurd hsq (nsq 4 19 (by norm_num) (by norm_num))
  · exact absurd hsq (nsq 4 23 (by norm_num) (by norm_num))
  · exact absurd hsq (nsq 5 27 (by norm_num) (by norm_num))
  · exact absurd hsq (nsq 5 32 (by norm_num) (by norm_num))
  · exact absurd hsq (nsq 6 37 (by norm_num) (by norm_num))
  · exact absurd hsq (nsq 6 43 (by norm_num) (by norm_num))
  · have hM7 : 7 ≤ 7 * 2 ^ k := by
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega
    generalize hM : 7 * 2 ^ k = M at hk hM7
    rcases hk with rfl | rfl | rfl | ⟨i, j, hij, hi, hj, rfl | rfl⟩
    · exact ⟨k, by rw [hM]; ring⟩
    · exact absurd hsq (nsq M _ (by nlinarith) (by nlinarith))
    · exact absurd hsq (nsq M _ (by nlinarith) (by nlinarith))
    · exact absurd hsq (nsq (M + i) _ (by nlinarith) (by nlinarith))
    · exact absurd hsq (nsq (M + i) _ (by nlinarith) (by nlinarith))
