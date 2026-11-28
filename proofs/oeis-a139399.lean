import OMAStatements.S_oeis_a139399
import Mathlib

open OMA.S_oeis_a139399

namespace P139399

theorem pre1 (x : ℕ) (h : f x = 1) : x = 2 := by
  unfold f at h; split_ifs at h <;> omega

theorem pre2 (x : ℕ) (h : f x = 2) : x = 4 := by
  unfold f at h; split_ifs at h <;> omega

end P139399

theorem OMA.solution : type_of% @OMA.S_oeis_a139399.main := by
  intro n hn hk
  have hK : f^[A006577 n] n = 1 := Nat.sInf_mem hk
  set K := A006577 n with hKdef
  have hK1 : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · rw [h] at hK; simp at hK; omega
    · exact h
  have hx : f^[K - 1] n = 2 := by
    apply P139399.pre1
    rw [← Function.iterate_succ_apply' f, show (K - 1).succ = K by omega, hK]
  have hK2 : 2 ≤ K := by
    by_contra hc
    rw [show K - 1 = 0 by omega] at hx; simp at hx; omega
  have hy : f^[K - 2] n = 4 := by
    apply P139399.pre2
    rw [← Function.iterate_succ_apply' f, show (K - 2).succ = K - 1 by omega, hx]
  have hne : ∃ k, f^[k] n = 1 ∨ f^[k] n = 2 ∨ f^[k] n = 4 := ⟨K - 2, Or.inr (Or.inr hy)⟩
  have hJ := Nat.sInf_mem hne
  have hJle : a n ≤ K - 2 := Nat.sInf_le (Or.inr (Or.inr hy))
  change f^[a n] n = 1 ∨ f^[a n] n = 2 ∨ f^[a n] n = 4 at hJ
  have hmin : ∀ m, f^[m] n = 1 → K ≤ m := fun m hm => Nat.sInf_le hm
  rcases hJ with h1 | h2 | h4
  · have := hmin _ h1; omega
  · have : f^[a n + 1] n = 1 := by rw [Function.iterate_succ_apply', h2]; rfl
    have := hmin _ this; omega
  · have : f^[a n + 2] n = 1 := by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h4]; rfl
    have := hmin _ this
    omega
