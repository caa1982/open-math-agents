import OMAStatements.S_oeis_a005309
import Mathlib

open OMA.S_oeis_a005309
open PowerSeries

namespace P005309

def cv (a b : ℕ → ℤ) (n : ℕ) : ℤ := ∑ i ∈ Finset.range (n + 1), a i * b (n - i)

def lmul (a b : List ℤ) : List ℤ :=
  (List.range 8).map (fun n => cv (fun i => a.getD i 0) (fun i => b.getD i 0) n)

def Agree (F : PowerSeries ℤ) (a : List ℤ) : Prop := ∀ n < 8, coeff n F = a.getD n 0

theorem agree_mul {F G : PowerSeries ℤ} {a b : List ℤ} (hF : Agree F a) (hG : Agree G b) :
    Agree (F * G) (lmul a b) := by
  intro n hn
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i F * coeff j G)]
  simp only [lmul, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hn,
    Option.map_some, Option.getD_some, cv]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  rw [hF i (by omega), hG (n - i) (by omega)]
  simp only [List.getD_eq_getElem?_getD]

def lone : List ℤ := [1, 0, 0, 0, 0, 0, 0, 0]

theorem agree_one : Agree 1 lone := by
  intro n hn
  rw [coeff_one]
  interval_cases n <;> rfl

def lpow (a : List ℤ) : ℕ → List ℤ
  | 0 => lone
  | m + 1 => lmul (lpow a m) a

theorem agree_pow {F : PowerSeries ℤ} {a : List ℤ} (hF : Agree F a) : ∀ m, Agree (F ^ m) (lpow a m)
  | 0 => by rw [pow_zero]; exact agree_one
  | m + 1 => by rw [pow_succ]; exact agree_mul (agree_pow hF m) hF

def lf (k : ℕ) : List ℤ := (List.range 8).map (fun m => if m = 0 then 1 else if k ∣ m then 2 else 0)

theorem agree_f (k : ℕ) : Agree (fermionicFactor k) (lf k) := by
  intro n hn
  simp only [fermionicFactor, coeff_mk, lf, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hn, Option.map_some, Option.getD_some]

def lprod : ℕ → List ℤ
  | 0 => lone
  | m + 1 => lmul (lprod m) (lpow (lf (m + 1)) m)

theorem agree_prod : ∀ m, Agree (∏ k ∈ Finset.Icc 1 m, (fermionicFactor k) ^ (k - 1)) (lprod m)
  | 0 => by simp only [Finset.Icc_self, show Finset.Icc 1 0 = ∅ by rfl, Finset.prod_empty]; exact agree_one
  | m + 1 => by
    rw [Finset.prod_Icc_succ_top (by omega), show m + 1 - 1 = m by omega]
    exact agree_mul (agree_prod m) (agree_pow (agree_f (m + 1)) m)

theorem a9 (j : ℕ) (hj : j < 8) : A005309 j = (lprod j).getD j 0 := agree_prod j j hj

end P005309

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a005309.main) := by
  intro h
  have e := congrArg (coeff 7) h
  simp only [add_mul, neg_mul, one_mul, mul_assoc, map_add, map_neg, map_sub, coeff_succ_X_mul,
    pow_succ, pow_zero, coeff_mk, coeff_C_mul, coeff_one, coeff_X, coeff_C] at e
  simp only [P005309.a9 6 (by norm_num), P005309.a9 7 (by norm_num)] at e
  revert e
  decide
