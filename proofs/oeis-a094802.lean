import OMAStatements.S_oeis_a094802
import Mathlib

open OMA.S_oeis_a094802

theorem OMA.solution : type_of% @OMA.S_oeis_a094802.main := by
  intro n hn
  have hbdd : BddAbove {p : ℕ | p ≤ n ∧ p.Prime} := ⟨n, fun x hx => hx.1⟩
  have hne : ({p : ℕ | p ≤ n ∧ p.Prime}).Nonempty := ⟨5, by omega, by norm_num⟩
  have hmem := Nat.sSup_mem hne hbdd
  have hmax : ∀ q : ℕ, q ≤ n → q.Prime → q ≤ largestPrimeLe n :=
    fun q h1 h2 => le_csSup hbdd ⟨h1, h2⟩
  set p := largestPrimeLe n with hpdef
  have hpp : p.Prime := hmem.2
  have hpn : p ≤ n := hmem.1
  have hp5 : 5 ≤ p := hmax 5 (by omega) (by norm_num)
  have h2p : n < 2 * p := by
    obtain ⟨q, hq, hq1, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) (by omega)
    have := hmax q (by omega) hq
    omega
  have hab : ∀ a b : ℕ, 0 < a → a < b → a * b ∣ b.factorial := by
    intro a b ha hab
    rw [← Nat.mul_factorial_pred (by omega : b ≠ 0), mul_comm a b]
    exact mul_dvd_mul_left b (Nat.dvd_factorial ha (by omega))
  have hin : ∀ m : ℕ, 1 ≤ m → m ≤ n → m ∣ p.factorial := by
    intro m hm1 hmn
    by_cases hmp : m ≤ p
    · exact Nat.dvd_factorial (by omega) hmp
    have hnp : ¬ m.Prime := fun h => hmp (hmax m hmn h)
    have hm2 : m ≠ 1 := by omega
    set a := m.minFac with hadef
    have ha : a.Prime := Nat.minFac_prime hm2
    have ha2 := ha.two_le
    have hsq : a ^ 2 ≤ m := Nat.minFac_sq_le_self (by omega) hnp
    obtain ⟨b, hb⟩ : a ∣ m := Nat.minFac_dvd m
    have hab' : a ≤ b := by nlinarith
    have hbp : b < p := by nlinarith
    rw [hb]
    rcases Nat.lt_or_eq_of_le hab' with h | h
    · exact (hab a b (by omega) h).trans (Nat.factorial_dvd_factorial hbp.le)
    · subst h
      have h2a : 2 * a ≤ p := by
        rcases (by omega : a = 2 ∨ a = 3 ∨ 4 ≤ a) with h | h | h
        · rw [h] at hb ⊢; omega
        · rw [h] at hb ⊢
          have := hmax 7 (by omega) (by norm_num)
          omega
        · nlinarith
      have e1 : a * a ∣ a * (2 * a) := mul_dvd_mul_left a (dvd_mul_left a 2)
      exact e1.trans ((hab a (2 * a) (by omega) (by omega)).trans (Nat.factorial_dvd_factorial h2a))
  have hS : p ∈ {k : ℕ | ∀ m : ℕ, 1 ≤ m → m ≤ n → m ∣ k.factorial} := hin
  have heq : a n = p := by
    apply le_antisymm (Nat.sInf_le hS)
    apply le_csInf ⟨p, hS⟩
    intro k hk
    exact (Nat.Prime.dvd_factorial hpp).mp (hk p hpp.one_lt.le hpn)
  rw [heq]
  exact ⟨hpp, rfl⟩
