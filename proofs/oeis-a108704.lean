import OMAStatements.S_oeis_a108704
import Mathlib

open OMA.S_oeis_a108704
open PowerSeries

namespace P108704

theorem nC (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : PowerSeries ℚ) = C (OfNat.ofNat n : ℚ) :=
  (map_ofNat C n).symm

theorem ode (S R F : PowerSeries ℚ) (hS : S ^ 2 = 1 - 2 * X) (hR : 2 * R = X ^ 2)
    (hF : F * S = (PowerSeries.exp ℚ).subst R) :
    (1 - 2 * X) * d⁄dX ℚ F = (1 + X - 2 * X ^ 2) * F := by
  have h2ne : (2 : PowerSeries ℚ) ≠ 0 := by
    intro h; have := congrArg constantCoeff h
    rw [show (2 : PowerSeries ℚ) = C 2 from (map_ofNat C 2).symm, constantCoeff_C, map_zero] at this
    norm_num at this
  have hR0 : constantCoeff R = 0 := by
    have h : constantCoeff (2 : ℚ⟦X⟧) * constantCoeff R = 0 := by
      rw [← map_mul, hR]; simp
    rw [show (2 : PowerSeries ℚ) = C 2 from (map_ofNat C 2).symm, constantCoeff_C] at h
    simpa using h
  have hs : HasSubst R := HasSubst.of_constantCoeff_zero' hR0
  have hRd : d⁄dX ℚ R = X := by
    have h := congrArg (d⁄dX ℚ) hR
    rw [nC, Derivation.leibniz, derivative_C, smul_zero, add_zero, smul_eq_mul, pow_two,
      Derivation.leibniz, derivative_X] at h
    apply mul_left_cancel₀ h2ne
    rw [← nC] at h
    linear_combination h
  have hW : d⁄dX ℚ ((PowerSeries.exp ℚ).subst R) = X * (PowerSeries.exp ℚ).subst R := by
    rw [derivative_subst hs, derivative_exp, hRd]; ring
  have h1 : d⁄dX ℚ F * S + F * d⁄dX ℚ S = X * (F * S) := by
    have h := congrArg (d⁄dX ℚ) hF
    rw [Derivation.leibniz, hW, ← hF, smul_eq_mul, smul_eq_mul] at h
    linear_combination h
  have h2 : 2 * S * d⁄dX ℚ S = -2 := by
    have h := congrArg (d⁄dX ℚ) hS
    have hd2 : d⁄dX ℚ (1 - 2 * X : PowerSeries ℚ) = -2 := by
      rw [map_sub, Derivation.map_one_eq_zero, nC, Derivation.leibniz, derivative_C, derivative_X]
      simp [nC]
    rw [hd2, pow_two, Derivation.leibniz] at h
    simp only [smul_eq_mul] at h
    linear_combination h
  have key : 2 * ((1 - 2 * X) * d⁄dX ℚ F - (1 + X - 2 * X ^ 2) * F) = 0 := by
    linear_combination 2 * S * h1 - 2 * (d⁄dX ℚ F - X * F) * hS - F * h2
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left h2ne)

end P108704

theorem OMA.solution : type_of% @OMA.S_oeis_a108704.main := by
  intro S R F hS hS0 hR hF n hn
  have e := congrArg (coeff (n - 1)) (P108704.ode S R F hS hR hF)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega, a]
  simp only [P108704.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, coeff_succ_X_mul, coeff_X, coeff_one, coeff_derivative] at e
  simp at e
  try rw [coeff_derivative] at e
  try rw [coeff_derivative] at e
  have f3 : ((k + 3).factorial : ℚ) = (k + 3) * (k + 2).factorial := by
    rw [show k + 3 = (k + 2) + 1 by omega, Nat.factorial_succ]; push_cast; ring
  have f2 : ((k + 2).factorial : ℚ) = (k + 2) * (k + 1).factorial := by
    rw [show k + 2 = (k + 1) + 1 by omega, Nat.factorial_succ]; push_cast; ring
  have f1 : ((k + 1).factorial : ℚ) = (k + 1) * k.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [f3, f2, f1]
  push_cast at e ⊢
  linear_combination ((k + 2) * (k + 1) * (k.factorial : ℚ)) * e
