import OMAStatements.S_oeis_a348482
import Mathlib

open OMA.S_oeis_a348482

open Polynomial

private def G (j : ℕ) : ℚ := ∑ i ∈ Finset.range j, (i.factorial : ℚ)

private lemma G_succ (j : ℕ) : G (j + 1) = G j + (j.factorial : ℚ) := by
  simp [G, Finset.sum_range_succ]

private lemma TG (n k : ℕ) (hk : k ≤ n + 1) : T n k = (G (n + 1) - G k) / (k.factorial : ℚ) := by
  unfold T G
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sub _ hk]

private lemma T0 (n k : ℕ) (hk : n < k) : T n k = 0 := by
  unfold T
  rw [Finset.Icc_eq_empty (by omega)]
  simp

private lemma coeffp (n k : ℕ) : (p n).coeff k = T n k := by
  unfold p
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · simp at h; rw [T0 n k (by omega)]

private lemma part1 (N n : ℕ) : ∑ k ∈ Finset.range n, (G N - G k) / ((k.factorial : ℚ) * ((k : ℚ) + 2)) =
    G N * (1 - 1 / ((n + 1).factorial : ℚ)) - 1 + G (n + 1) / ((n + 1).factorial : ℚ) := by
  induction n with
  | zero => simp [G]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, G_succ (n + 1), G_succ n]
    rw [Nat.factorial_succ (n + 1), Nat.factorial_succ n]
    push_cast
    have : (n.factorial : ℚ) ≠ 0 := by positivity
    have : ((n : ℚ) + 1) ≠ 0 := by positivity
    have : ((n : ℚ) + 2) ≠ 0 := by positivity
    have : ((n : ℚ) + 1 + 1) ≠ 0 := by positivity
    field_simp
    ring

private noncomputable def sm (n : ℕ) : ℚ[X] := ∑ j ∈ Finset.range (n + 1), (X : ℚ[X]) ^ j

private lemma pa (n : ℕ) : p n - derivative (p n) = sm n := by
  ext k
  rw [coeff_sub, coeff_derivative, coeffp, coeffp]
  unfold sm
  rw [finsetSum_coeff]
  simp only [coeff_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · simp at h
    rw [TG n k (by omega), TG n (k + 1) (by omega), G_succ k, Nat.factorial_succ]
    push_cast
    have : (k.factorial : ℚ) ≠ 0 := by positivity
    have : ((k : ℚ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  · simp at h
    rw [T0 n k (by omega), T0 n (k + 1) (by omega)]
    ring

private lemma Z (f : ℚ[X]) (h : f - derivative f = 0) : f = 0 := by
  by_contra hf
  have hc : f.coeff f.natDegree ≠ 0 := by
    rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hf
  have h2 : (f - derivative f).coeff f.natDegree = f.coeff f.natDegree := by
    rw [coeff_sub, coeff_derivative, coeff_eq_zero_of_natDegree_lt (show f.natDegree < f.natDegree + 1 by omega)]
    ring
  rw [h, coeff_zero] at h2
  exact hc h2.symm

private lemma degp (m : ℕ) : (p m).natDegree ≤ m := by
  unfold p
  apply natDegree_sum_le_of_forall_le
  intro k hk
  simp at hk
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

private lemma tel (m : ℕ) (q : ℚ[X]) :
    ∑ i ∈ Finset.Icc 1 m, ((derivative)^[i] q - (derivative)^[i + 1] q) =
      derivative q - (derivative)^[m + 1] q := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

private lemma partc (m : ℕ) : p (m + 1) = (X + 1) * p m + 1 +
    ∑ i ∈ Finset.Icc 1 m, (derivative)^[i] (p m) := by
  have hz : (derivative)^[m + 1] (p m) = 0 := iterate_derivative_eq_zero (by have := degp m; omega)
  have hd : derivative (∑ i ∈ Finset.Icc 1 m, (derivative)^[i] (p m)) =
      ∑ i ∈ Finset.Icc 1 m, (derivative)^[i + 1] (p m) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Function.iterate_succ_apply']
  have ht := tel m (p m)
  rw [Finset.sum_sub_distrib, hz, sub_zero] at ht
  have hs : sm (m + 1) = X * sm m + 1 := by
    unfold sm
    rw [Finset.sum_range_succ' _ (m + 1), Finset.mul_sum]
    simp [pow_succ, mul_comm]
  apply eq_of_sub_eq_zero
  apply Z
  have e1 := pa (m + 1)
  have e2 := pa m
  rw [derivative_sub, derivative_add, derivative_add, derivative_mul, hd, derivative_one,
    derivative_add, derivative_X, derivative_one]
  linear_combination e1 - X * e2 + hs - ht

private lemma part3 (n : ℕ) : (p n).eval (-1) = (A173184 n : ℚ) := by
  have hE : ∀ n, (p n).eval (-1) = ∑ k ∈ Finset.range (n + 1), T n k * (-1) ^ k := by
    intro n
    unfold p
    rw [eval_finsetSum]
    simp
  induction n with
  | zero => rw [hE]; simp [T, A173184]
  | succ n ih =>
    rw [hE] at ih ⊢
    have hd := numDerangements_sum (n + 1)
    have hD : ((numDerangements (n + 1) : ℕ) : ℚ) =
        ∑ k ∈ Finset.range (n + 1 + 1), ((n + 1).factorial : ℚ) / (k.factorial : ℚ) * (-1) ^ k := by
      have := congrArg (fun z : ℤ => (z : ℚ)) hd
      push_cast at this
      rw [this]
      apply Finset.sum_congr rfl
      intro k hk
      simp at hk
      have hf := Nat.factorial_mul_ascFactorial k (n + 1 - k)
      rw [show k + (n + 1 - k) = n + 1 by omega] at hf
      have hf' : ((k + 1).ascFactorial (n + 1 - k) : ℚ) = ((n + 1).factorial : ℚ) / (k.factorial : ℚ) := by
        have : (k.factorial : ℚ) ≠ 0 := by positivity
        rw [eq_div_iff this, ← hf]; push_cast; ring
      rw [hf']; ring
    have hT : ∀ k ∈ Finset.range (n + 1 + 1), T (n + 1) k * (-1) ^ k =
        T n k * (-1) ^ k + ((n + 1).factorial : ℚ) / (k.factorial : ℚ) * (-1) ^ k := by
      intro k hk
      simp at hk
      rw [TG (n + 1) k (by omega), TG n k (by omega), G_succ (n + 1)]
      ring
    rw [Finset.sum_congr rfl hT, Finset.sum_add_distrib, ← hD, Finset.sum_range_succ (fun k => T n k * (-1) ^ k),
      T0 n (n + 1) (by omega), ih]
    unfold A173184
    rw [Finset.sum_range_succ _ (n + 1)]
    push_cast; ring

theorem OMA.solution : type_of% @OMA.S_oeis_a348482.main := by
  refine ⟨fun n hn => ⟨?_, ?_⟩, fun n hn => ?_, part3⟩
  · rw [TG n 1 (by omega), TG n 0 (by omega)]
    simp [G]
  · rw [TG n 0 (by omega)]
    have h := part1 (n + 1) n
    rw [show (∑ k ∈ Finset.range n, T n k / ((k : ℚ) + 2)) =
        ∑ k ∈ Finset.range n, (G (n + 1) - G k) / ((k.factorial : ℚ) * ((k : ℚ) + 2)) from
      Finset.sum_congr rfl (fun k hk => by
        simp at hk; rw [TG n k (by omega), div_div])]
    rw [h]
    have : ((n + 1).factorial : ℚ) ≠ 0 := by positivity
    simp [G]
    field_simp
    ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [show m + 1 - 1 = m by omega]
    exact partc m
