import OMAStatements.S_mo_130121
import Mathlib

open OMA.S_mo_130121

lemma mo130121_corner (v : Fin 8 → Bool) :
    sqDist v (fun _ => (1 : ℝ) / 8) =
      1 / 8 + 3 / 4 * ((Finset.univ.filter (fun i => v i = true)).card : ℝ) := by
  unfold sqDist
  have h : ∀ i, ((if v i then (1 : ℝ) else 0) - 1 / 8) ^ 2 =
      1 / 64 + 3 / 4 * (if v i = true then (1 : ℝ) else 0) := by
    intro i; cases v i <;> norm_num
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole]
  simp
  norm_num

lemma mo130121_half (v : Fin 8 → Bool) (hv : sqDist v (halfCenter 8 3) ≤ 7 / 8) :
    ∀ i : Fin 8, 3 ≤ (i : ℕ) → v i = false := by
  intro i hi
  by_contra hne
  have hvi : v i = true := by simpa using hne
  have hle : ((if v i then (1 : ℝ) else 0) - halfCenter 8 3 i) ^ 2 ≤ sqDist v (halfCenter 8 3) := by
    unfold sqDist
    exact Finset.single_le_sum (f := fun j => ((if v j then (1 : ℝ) else 0) - halfCenter 8 3 j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hc : halfCenter 8 3 i = 0 := by
    unfold halfCenter; simp; omega
  rw [hvi, hc] at hle
  norm_num at hle
  linarith

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_130121.main) := by
  intro h
  set R : ℝ := Real.sqrt (7 / 8) with hR
  have hR2 : R ^ 2 = 7 / 8 := by rw [hR, Real.sq_sqrt]; norm_num
  have hRpos : 0 < R := by rw [hR]; positivity
  have hfl : ⌊4 * R ^ 2⌋₊ = 3 := by
    rw [hR2, Nat.floor_eq_iff (by norm_num)]; norm_num
  have h1 := h 8 R hRpos (by rw [hR2]; norm_num) (fun _ => 1 / 8)
  rw [hfl] at h1
  have hlow : 9 ≤ covered 8 (fun _ => (1 : ℝ) / 8) R := by
    have hsub : Finset.univ.filter (fun v : Fin 8 → Bool =>
        (Finset.univ.filter (fun i => v i = true)).card ≤ 1) ⊆
        Finset.univ.filter (fun v : Fin 8 → Bool => sqDist v (fun _ => (1 : ℝ) / 8) ≤ R ^ 2) := by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      rw [mo130121_corner, hR2]
      have : ((Finset.univ.filter (fun i => v i = true)).card : ℝ) ≤ 1 := by exact_mod_cast hv
      linarith
    have hcard : (Finset.univ.filter (fun v : Fin 8 → Bool =>
        (Finset.univ.filter (fun i => v i = true)).card ≤ 1)).card = 9 := by decide
    unfold covered
    rw [← hcard]
    exact Finset.card_le_card hsub
  have hup : covered 8 (halfCenter 8 3) R ≤ 8 := by
    have hsub : Finset.univ.filter (fun v : Fin 8 → Bool => sqDist v (halfCenter 8 3) ≤ R ^ 2) ⊆
        Finset.univ.filter (fun v : Fin 8 → Bool =>
          v 3 = false ∧ v 4 = false ∧ v 5 = false ∧ v 6 = false ∧ v 7 = false) := by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      rw [hR2] at hv
      have := mo130121_half v hv
      exact ⟨this 3 (by decide), this 4 (by decide), this 5 (by decide), this 6 (by decide),
        this 7 (by decide)⟩
    have hcard : (Finset.univ.filter (fun v : Fin 8 → Bool =>
          v 3 = false ∧ v 4 = false ∧ v 5 = false ∧ v 6 = false ∧ v 7 = false)).card = 8 := by
      decide
    unfold covered
    rw [← hcard]
    exact Finset.card_le_card hsub
  omega
