import OMAStatements.S_oeis_a237275
import Mathlib

open OMA.S_oeis_a237275

theorem OMA.solution : type_of% @OMA.S_oeis_a237275.main := by
  have key : ∀ n w : ℕ, w ∈ {k : ℕ | 0 < k ∧ 1 < k % 10 ∧ (k % 10) ^ n ∣ k} →
      (∀ k : ℕ, 0 < k → 1 < k % 10 → (k % 10) ^ n ∣ k → k ≤ w → k % 10 = 2) → a n % 10 = 2 := by
    intro n w hw hb
    have hm := Nat.sInf_mem ⟨w, hw⟩
    have hle : a n ≤ w := Nat.sInf_le hw
    exact hb _ hm.1 hm.2.1 hm.2.2 hle
  have p2 : ∀ n : ℕ, 2 ^ (n + 1) % 10 = if n % 4 = 0 then 2 else if n % 4 = 1 then 4
      else if n % 4 = 2 then 8 else 6 := by
    intro n
    induction n with
    | zero => norm_num
    | succ k ih =>
      rw [pow_succ, Nat.mul_mod, ih]
      have : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
      have e : (k + 1) % 4 = (k % 4 + 1) % 4 := by omega
      rw [e]
      generalize k % 4 = t at this ⊢
      interval_cases t <;> norm_num
  have p3 : ∀ n : ℕ, 5 * 2 ^ (n + 4) < 3 ^ (n + 4) := by
    intro n
    induction n with
    | zero => norm_num
    | succ k ih =>
      have e1 : 3 ^ (k + 1 + 4) = 3 * 3 ^ (k + 4) := by ring
      have e2 : 2 ^ (k + 1 + 4) = 2 * 2 ^ (k + 4) := by ring
      omega
  intro n
  rcases n with _ | _ | _ | _ | n
  · apply key 0 2 (by norm_num)
    intro k h0 h1 h2 hk
    interval_cases k <;> first | decide | (revert h1 h2; decide)
  · apply key 1 2 (by norm_num)
    intro k h0 h1 h2 hk
    interval_cases k <;> first | decide | (revert h1 h2; decide)
  · apply key 2 12 (by norm_num)
    intro k h0 h1 h2 hk
    interval_cases k <;> first | decide | (revert h1 h2; decide)
  · apply key 3 32 (by norm_num)
    intro k h0 h1 h2 hk
    interval_cases k <;> first | decide | (revert h1 h2; decide)
  · have hw : ∃ j : ℕ, 1 ≤ j ∧ j ≤ 5 ∧ (2 ^ (n + 4) * j) % 10 = 2 := by
      have e := p2 (n + 3)
      have : (n + 3) % 4 < 4 := Nat.mod_lt _ (by norm_num)
      rw [show n + 3 + 1 = n + 4 by ring] at e
      generalize (n + 3) % 4 = t at this e
      interval_cases t <;> simp at e
      · exact ⟨1, by norm_num, by norm_num, by rw [Nat.mul_mod, e]⟩
      · exact ⟨3, by norm_num, by norm_num, by rw [Nat.mul_mod, e]⟩
      · exact ⟨4, by norm_num, by norm_num, by rw [Nat.mul_mod, e]⟩
      · exact ⟨2, by norm_num, by norm_num, by rw [Nat.mul_mod, e]⟩
    obtain ⟨j, hj1, hj5, hjm⟩ := hw
    apply key (n + 4) (2 ^ (n + 4) * j)
    · refine ⟨by positivity, by omega, ?_⟩
      rw [hjm]
      exact dvd_mul_right _ _
    · intro k h0 h1 h2 hk
      by_contra hne
      have hd : 3 ≤ k % 10 := by omega
      have e1 : 3 ^ (n + 4) ≤ (k % 10) ^ (n + 4) := Nat.pow_le_pow_left hd _
      have e2 : (k % 10) ^ (n + 4) ≤ k := Nat.le_of_dvd h0 h2
      have e3 : 2 ^ (n + 4) * j ≤ 2 ^ (n + 4) * 5 := Nat.mul_le_mul_left _ hj5
      have := p3 n
      omega
