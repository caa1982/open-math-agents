import OMAStatements.S_oeis_a307985
import Mathlib

open OMA.S_oeis_a307985

namespace P307985

theorem mem_tri (n x y z : ℕ) : (x, y, z) ∈ triangles n ↔
    (1 ≤ x ∧ x ≤ n) ∧ (1 ≤ y ∧ y ≤ n) ∧ (1 ≤ z ∧ z ≤ n) ∧
      x + y + z = n ∧ x ≤ y ∧ y ≤ z ∧ z < x + y ∧ y ∣ n := by
  simp [triangles, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, and_assoc]

theorem y_eq (n x y z : ℕ) (h : (x, y, z) ∈ triangles n) : n = 3 * y := by
  rw [mem_tri] at h
  obtain ⟨⟨hx1, -⟩, ⟨hy1, -⟩, -, hs, hxy, hyz, hz, q, hq⟩ := h
  have h1 : 2 * y < n := by omega
  have h2 : n < 4 * y := by omega
  rcases Nat.lt_or_ge q 3 with h3 | h3
  · have : y * q ≤ y * 2 := Nat.mul_le_mul_left y (by omega)
    omega
  · rcases Nat.lt_or_ge q 4 with h4 | h4
    · have : q = 3 := by omega
      subst this; omega
    · have : y * 4 ≤ y * q := Nat.mul_le_mul_left y h4
      omega

theorem tri_eq (m : ℕ) : triangles (3 * m) =
    (Finset.Ioc (m / 2) m).image (fun x => (x, m, 2 * m - x)) := by
  ext ⟨x, y, z⟩
  constructor
  · intro h
    have hy := y_eq _ _ _ _ h
    have hym : y = m := by omega
    subst hym
    rw [mem_tri] at h
    obtain ⟨⟨hx1, -⟩, -, -, hs, hxy, hyz, hz, -⟩ := h
    simp only [Finset.mem_image, Finset.mem_Ioc, Prod.mk.injEq]
    refine ⟨x, ⟨by omega, hxy⟩, ?_⟩
    simp only [true_and]
    omega
  · intro h
    simp only [Finset.mem_image, Finset.mem_Ioc, Prod.mk.injEq] at h
    obtain ⟨w, ⟨h1, h2⟩, rfl, rfl, rfl⟩ := h
    rw [mem_tri]
    refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, h2, by omega,
      by omega, ⟨3, by ring⟩⟩

theorem closed (n : ℕ) : a n = if n % 3 = 0 then (n / 3 + 1) / 2 else 0 := by
  unfold a
  split_ifs with h
  · obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m := ⟨n / 3, by omega⟩
    rw [tri_eq, Finset.card_image_of_injective _ (fun x1 x2 h => by
      simp only [Prod.mk.injEq] at h; exact h.1), Nat.card_Ioc]
    omega
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    rintro ⟨x, y, z⟩ hm
    have := y_eq _ _ _ _ hm
    omega

end P307985

theorem OMA.solution : type_of% @OMA.S_oeis_a307985.main := by
  intro n hn
  simp only [P307985.closed]
  have h3 : (n - 3) % 3 = n % 3 := by omega
  have h6 : (n - 6) % 3 = n % 3 := by omega
  have h9 : (n - 9) % 3 = n % 3 := by omega
  rw [h3, h6, h9]
  split_ifs with h
  · have e : (n / 3 + 1) / 2 = ((n - 3) / 3 + 1) / 2 + ((n - 6) / 3 + 1) / 2 - ((n - 9) / 3 + 1) / 2 := by omega
    have e2 : ((n - 9) / 3 + 1) / 2 ≤ ((n - 3) / 3 + 1) / 2 + ((n - 6) / 3 + 1) / 2 := by omega
    rw [e]
    push_cast [e2]
    ring
  · simp
