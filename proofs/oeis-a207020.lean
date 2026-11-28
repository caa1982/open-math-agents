import OMAStatements.S_oeis_a207020
import Mathlib

open OMA.S_oeis_a207020
open PowerSeries

namespace P207020

def c (h : ℕ) (r : Row) : ℤ := ((tails h r).length : ℤ)

theorem cs (h : ℕ) (r : Row) : c (h + 1) r = ((below r).map (c h)).sum := by
  simp only [c, tails, List.length_flatMap, List.length_map]
  push_cast [Nat.cast_list_sum]
  simp [List.map_map, Function.comp_def]
  rfl

theorem lsum (l : List Row) (f g k m q : Row → ℤ)
    (hl : ∀ s ∈ l, f s = 4 * g s - 6 * k s + 4 * m s - q s) :
    (l.map f).sum = 4 * (l.map g).sum - 6 * (l.map k).sum + 4 * (l.map m).sum - (l.map q).sum := by
  induction l with
  | nil => simp
  | cons s l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [hl s (by simp), ih (fun x hx => hl x (by simp [hx]))]
    ring

set_option maxRecDepth 100000 in
theorem base : ∀ r : Row, c 5 r = 4 * c 4 r - 6 * c 3 r + 4 * c 2 r - c 1 r := by decide +kernel

theorem rec_all : ∀ h : ℕ, ∀ r : Row, c (h + 5) r = 4 * c (h + 4) r - 6 * c (h + 3) r + 4 * c (h + 2) r - c (h + 1) r := by
  intro h
  induction h with
  | zero => exact base
  | succ h ih =>
    intro r
    rw [show h + 1 + 5 = (h + 5) + 1 by omega, show h + 1 + 4 = (h + 4) + 1 by omega,
      show h + 1 + 3 = (h + 3) + 1 by omega, show h + 1 + 2 = (h + 2) + 1 by omega,
      show h + 1 + 1 = (h + 1) + 1 by omega, cs (h + 5), cs (h + 4), cs (h + 3), cs (h + 2), cs (h + 1)]
    exact lsum _ _ _ _ _ _ (fun s _ => ih s)

theorem rows_len : rows.length = 9 := by decide

theorem a_eq (h : ℕ) : a (h + 1) = 9 * c h 15 := by
  show ((grids h).length : ℤ) = _
  simp only [grids, List.length_flatMap, List.length_map, c]
  rw [List.map_const', List.sum_replicate, rows_len, smul_eq_mul, Nat.cast_mul]
  push_cast; ring

theorem rec15 (n : ℕ) : a (n + 5) = 4 * a (n + 4) - 6 * a (n + 3) + 4 * a (n + 2) - a (n + 1) := by
  rw [a_eq (n + 4), a_eq (n + 3), a_eq (n + 2), a_eq (n + 1), a_eq n]
  rcases n with _ | n
  · have : c 4 15 = 4 * c 3 15 - 6 * c 2 15 + 4 * c 1 15 - c 0 15 := by decide +kernel
    linear_combination 9 * this
  · have := rec_all n 15
    rw [show n + 1 + 4 = n + 5 by omega, show n + 1 + 3 = n + 4 by omega, show n + 1 + 2 = n + 3 by omega,
      show n + 1 + 1 = n + 2 by omega]
    linear_combination 9 * this

end P207020

theorem OMA.solution : type_of% @OMA.S_oeis_a207020.main := by
  refine ⟨?_, P207020.rec15⟩
  have hp : ((1 - X) ^ 4 : PowerSeries ℤ) = 1 - C 4 * X ^ 1 + C 6 * X ^ 2 - C 4 * X ^ 3 + X ^ 4 := by
    simp only [map_ofNat]; ring
  have hq : ∀ F : PowerSeries ℤ, F * (1 - C 4 * X ^ 1 + C 6 * X ^ 2 - C 4 * X ^ 3 + X ^ 4) =
      F - C 4 * (F * X ^ 1) + C 6 * (F * X ^ 2) - C 4 * (F * X ^ 3) + F * X ^ 4 := fun F => by ring
  have hr : (9 * X * (1 + 5 * X - 2 * X ^ 2) : PowerSeries ℤ) = C 9 * X ^ 1 + C 45 * X ^ 2 - C 18 * X ^ 3 := by
    simp only [map_ofNat]; ring
  rw [hp, hq, hr]
  clear hp hq hr
  ext n
  simp only [map_sub, map_add, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_C_mul_X_pow, coeff_C]
  rcases Nat.lt_or_ge n 5 with hn | hn
  · have v : a 0 = 0 ∧ a 1 = 9 ∧ a 2 = 81 ∧ a 3 = 252 ∧ a 4 = 558 := by decide +kernel
    obtain ⟨v0, v1, v2, v3, v4⟩ := v
    interval_cases n <;> simp [coeff_C, v0, v1, v2, v3, v4]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have h := P207020.rec15 m
    simp (disch := omega) only [if_pos, if_neg]
    rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
    linarith
