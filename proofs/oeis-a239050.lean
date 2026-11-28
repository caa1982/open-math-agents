import OMAStatements.S_oeis_a239050
import Mathlib

open OMA.S_oeis_a239050
open ArithmeticFunction

namespace P239050

theorem s_succ (e : ℕ) : sigma 1 (3 ^ (e + 1)) = 3 * sigma 1 (3 ^ e) + 1 := by
  rw [sigma_apply_prime_pow Nat.prime_three, sigma_apply_prime_pow Nat.prime_three,
    Finset.sum_range_succ', Finset.mul_sum]
  simp only [mul_one, pow_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem s_ge (e : ℕ) (he : 1 ≤ e) : 2 ≤ sigma 1 (3 ^ e) := by
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
  rw [s_succ]
  have : 0 < sigma 1 (3 ^ f) := sigma_pos 1 _ (by positivity)
  omega

end P239050

theorem OMA.solution : type_of% @OMA.S_oeis_a239050.main := by
  intro n hn
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show n ≠ 0 by omega) 3 (by norm_num)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have h3m : Nat.Coprime 3 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm
  have hc : Nat.Coprime (3 ^ e) m := Nat.Coprime.pow_left _ h3m
  have hc' : Nat.Coprime (3 ^ (e + 1)) m := Nat.Coprime.pow_left _ h3m
  unfold a
  rw [show 3 * (3 ^ e * m) = 3 ^ (e + 1) * m by ring,
    isMultiplicative_sigma.map_mul_of_coprime hc, isMultiplicative_sigma.map_mul_of_coprime hc',
    P239050.s_succ]
  have hpos : 0 < sigma 1 m := sigma_pos 1 m (by omega)
  constructor
  · intro h
    have h' : sigma 1 (3 ^ e) * sigma 1 m = 1 * sigma 1 m := by nlinarith
    have h1 : sigma 1 (3 ^ e) = 1 := Nat.eq_of_mul_eq_mul_right hpos h'
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simpa using hm
    · have := P239050.s_ge e he; omega
  · intro h
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp
    · exfalso; apply h
      exact Dvd.dvd.mul_right (dvd_pow_self 3 (by omega)) m
