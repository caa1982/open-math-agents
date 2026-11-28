import OMAStatements.S_oeis_a088023
import Mathlib

open OMA.S_oeis_a088023

namespace P088023

theorem len : ∀ k, (block k).length = 2 ^ k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp [block, step, ih, pow_succ]; ring

def g (k i : ℕ) : ℕ := (block k).getD i 0

theorem pre (k i : ℕ) (hi : i < 2 ^ k) : g (k + 1) i = g k i := by
  simp only [g, block, step]
  rw [List.getD_append _ _ _ _ (by rw [len]; exact hi)]

theorem sec (k j : ℕ) (hj : j < 2 ^ k) : g (k + 1) (2 ^ k + j) = g k (2 ^ k - 1 - j) + j + 1 := by
  simp only [g, block, step]
  rw [List.getD_append_right _ _ _ _ (by rw [len]; omega), len, show 2 ^ k + j - 2 ^ k = j by omega]
  rw [List.getD_eq_getElem _ _ (by simp [len]; exact hj), List.getD_eq_getElem _ _ (by rw [len]; omega)]
  simp [List.getElem_reverse, len]
  try ring_nf
  try (congr 2; omega)

theorem mono : ∀ k i, i + 1 < 2 ^ k → g k i ≤ g k (i + 1) ∧ g k (i + 1) ≤ g k i + 1 := by
  intro k
  induction k with
  | zero => intro i hi; simp at hi
  | succ k ih =>
    intro i hi
    have hp : 0 < 2 ^ k := by positivity
    rcases Nat.lt_or_ge (i + 1) (2 ^ k) with h1 | h1
    · rw [pre k i (by omega), pre k (i + 1) h1]; exact ih i h1
    · rcases Nat.eq_or_lt_of_le h1 with h2 | h2
      · -- i = 2^k - 1
        rw [pre k i (by omega), show i + 1 = 2 ^ k + 0 by omega, sec k 0 hp]
        rw [show 2 ^ k - 1 - 0 = i by omega]
        omega
      · obtain ⟨j, rfl⟩ : ∃ j, i = 2 ^ k + j := ⟨i - 2 ^ k, by omega⟩
        have hj : j + 1 < 2 ^ k := by rw [pow_succ] at hi; omega
        rw [sec k j (by omega), show 2 ^ k + j + 1 = 2 ^ k + (j + 1) by ring, sec k (j + 1) hj]
        have := ih (2 ^ k - 1 - (j + 1)) (by omega)
        rw [show 2 ^ k - 1 - (j + 1) + 1 = 2 ^ k - 1 - j by omega] at this
        omega

theorem stable (k k' i : ℕ) (hk : k ≤ k') (hi : i < 2 ^ k) : g k' i = g k i := by
  induction k', hk using Nat.le_induction with
  | base => rfl
  | succ k' hk ih =>
    rw [pre k' i (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hk)), ih]

theorem ltlog (n : ℕ) (hn : 1 ≤ n) : n - 1 < 2 ^ (Nat.log2 n + 1) := by
  have := Nat.lt_log2_self (n := n)
  omega

end P088023

theorem OMA.solution : type_of% @OMA.S_oeis_a088023.main := by
  intro n hn
  have h1 : a n = P088023.g (Nat.log2 n + 1) (n - 1) := by simp [a, hn, P088023.g]
  have h2 : a (n + 1) = P088023.g (Nat.log2 (n + 1) + 1) n := by simp [a, P088023.g]
  have hle : Nat.log2 n ≤ Nat.log2 (n + 1) := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]; exact Nat.log_mono_right (by omega)
  rw [h1, h2, ← P088023.stable (Nat.log2 n + 1) (Nat.log2 (n + 1) + 1) (n - 1) (by omega) (P088023.ltlog n hn)]
  have hn' := P088023.ltlog (n + 1) (by omega)
  have := P088023.mono (Nat.log2 (n + 1) + 1) (n - 1) (by omega)
  rw [show n - 1 + 1 = n by omega] at this
  exact this.1
