import OMAStatements.S_oeis_a193229
import Mathlib

open OMA.S_oeis_a193229

namespace P193229

lemma succ_eq (n k : ℕ) : a193229 (n + 1) k =
    ∑ i ∈ Finset.range (n + 1), if k ≤ i + 1 then (i + 1) * a193229 n i else 0 := by
  rw [a193229]

lemma zero_gt : ∀ n k, n < k → a193229 n k = 0
  | 0, k + 1, _ => by simp [a193229]
  | n + 1, k, h => by
    rw [succ_eq]
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [if_neg (by omega)]

lemma rec0 (n : ℕ) : a193229 (n + 1) 0 = a193229 (n + 1) 1 := by
  rw [succ_eq, succ_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [if_pos (by omega), if_pos (by omega)]

lemma rec1 (n k : ℕ) : a193229 (n + 1) (k + 1) = a193229 (n + 1) (k + 2) + (k + 1) * a193229 n k := by
  rcases Nat.lt_or_ge n k with h | h
  · rw [zero_gt n k h, zero_gt (n + 1) (k + 1) (by omega), zero_gt (n + 1) (k + 2) (by omega)]
    simp
  rw [succ_eq, succ_eq]
  have hs : ∀ i ∈ Finset.range (n + 1), (if k + 1 ≤ i + 1 then (i + 1) * a193229 n i else 0) =
      (if k + 2 ≤ i + 1 then (i + 1) * a193229 n i else 0) +
        (if k = i then (i + 1) * a193229 n i else 0) := by
    intro i _
    by_cases h1 : k = i
    · subst h1; simp
    · by_cases h2 : k + 2 ≤ i + 1
      · rw [if_pos (by omega), if_pos h2, if_neg h1]; simp
      · rw [if_neg (by omega), if_neg h2, if_neg h1]
  rw [Finset.sum_congr rfl hs, Finset.sum_add_distrib, Finset.sum_ite_eq]
  rw [if_pos (by simp only [Finset.mem_range]; omega)]

lemma diag : ∀ k, a193229 k k = k.factorial
  | 0 => by simp [a193229]
  | k + 1 => by
    rw [rec1, zero_gt (k + 1) (k + 2) (by omega), diag k, Nat.factorial_succ]; ring

lemma key : ∀ m k, 2 ^ m * m.factorial * a193229 (k + m) k = (k + 2 * m).factorial
  | 0, k => by simp [diag]
  | m + 1, 0 => by
    have h1 := key m 1
    rw [show 1 + m = m + 1 by omega] at h1
    rw [show 0 + (m + 1) = m + 1 by omega, rec0, show 0 + 2 * (m + 1) = (1 + 2 * m) + 1 by omega,
      Nat.factorial_succ (1 + 2 * m), ← h1, Nat.factorial_succ m, pow_succ]
    ring
  | m + 1, j + 1 => by
    have h1 := key m (j + 2)
    have h2 := key (m + 1) j
    rw [show j + 1 + (m + 1) = (j + m + 1) + 1 by omega, rec1,
      show j + m + 1 + 1 = (j + 2) + m by omega]
    rw [show j + (m + 1) = j + m + 1 by omega] at h2
    rw [show j + 1 + 2 * (m + 1) = (j + 2 * m + 2) + 1 by omega, Nat.factorial_succ (j + 2 * m + 2)]
    rw [show j + 2 + 2 * m = j + 2 * m + 2 by omega] at h1
    rw [show j + 2 * (m + 1) = j + 2 * m + 2 by omega] at h2
    have e : 2 ^ (m + 1) * (m + 1).factorial * (a193229 (j + 2 + m) (j + 2) + (j + 1) * a193229 (j + m + 1) j)
        = 2 * (m + 1) * (2 ^ m * m.factorial * a193229 (j + 2 + m) (j + 2)) +
          (j + 1) * (2 ^ (m + 1) * (m + 1).factorial * a193229 (j + m + 1) j) := by
      rw [Nat.factorial_succ, pow_succ]; ring
    rw [e, h1, h2]; ring

end P193229

theorem OMA.solution : type_of% @OMA.S_oeis_a193229.main := by
  intro n k hk
  obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
  rw [show k + m - k = m by omega, show 2 * (k + m) - k = k + 2 * m by omega]
  exact P193229.key m k
