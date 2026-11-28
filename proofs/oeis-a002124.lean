import OMAStatements.S_oeis_a002124
import Mathlib

open OMA.S_oeis_a002124

namespace OMA.P_oeis_a002124

def ops : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def C : ℕ → ℕ → List (List ℕ)
  | 0, n => if n = 0 then [[]] else []
  | f + 1, n => if n = 0 then [[]] else
      (ops.filter (fun p => p ≤ n)).flatMap (fun p => (C f (n - p)).map (fun l => p :: l))

theorem ops_iff (p : ℕ) (hp : p ≤ 25) : p ∈ ops ↔ (Nat.Prime p ∧ p % 2 = 1) := by
  interval_cases p <;> simp [ops] <;> norm_num

theorem comp_zero (l : List ℕ) : IsOddPrimeComp 0 l ↔ l = [] := by
  constructor
  · rintro ⟨hs, hp⟩
    cases l with
    | nil => rfl
    | cons a t =>
      exfalso
      have := (hp a (by simp)).1.pos
      simp at hs
      omega
  · rintro rfl
    simp [IsOddPrimeComp]

theorem mem_C (f : ℕ) : ∀ n, n ≤ f → n ≤ 25 → ∀ l, (l ∈ C f n ↔ IsOddPrimeComp n l) := by
  induction f with
  | zero =>
    intro n hn _ l
    have : n = 0 := by omega
    subst this
    simp [C, comp_zero]
  | succ f ih =>
    intro n hn h25 l
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp [C, comp_zero]
    · simp only [C, Nat.pos_iff_ne_zero.mp hpos, if_false, List.mem_flatMap, List.mem_filter,
        List.mem_map, decide_eq_true_eq]
      constructor
      · rintro ⟨p, ⟨hp, hpn⟩, l', hl', rfl⟩
        have hpp := (ops_iff p (by omega)).1 hp
        have hpos' := hpp.1.pos
        rw [ih (n - p) (by omega) (by omega)] at hl'
        obtain ⟨hs, hall⟩ := hl'
        refine ⟨?_, ?_⟩
        · simp [hs]; omega
        · intro q hq
          simp at hq
          rcases hq with rfl | hq
          · exact hpp
          · exact hall q hq
      · rintro ⟨hs, hall⟩
        cases l with
        | nil => simp at hs; omega
        | cons p t =>
          have hpp := hall p (by simp)
          simp at hs
          have hpn : p ≤ n := by omega
          refine ⟨p, ⟨(ops_iff p (by omega)).2 hpp, hpn⟩, t, ?_, rfl⟩
          have hpos' := hpp.1.pos
          rw [ih (n - p) (by omega) (by omega)]
          refine ⟨by omega, fun q hq => hall q (by simp [hq])⟩

theorem A_eq (n : ℕ) (h : n ≤ 25) : A002124 n = (C 25 n).toFinset.card := by
  unfold A002124
  have : {l : List ℕ | IsOddPrimeComp n l} = ↑((C 25 n).toFinset) := by
    ext l
    simp [mem_C 25 n h h l]
  rw [this, Set.ncard_coe_finset]

theorem v16 : (C 25 16).toFinset.card = 14 := by decide +kernel
theorem v18 : (C 25 18).toFinset.card = 21 := by decide +kernel
theorem v19 : (C 25 19).toFinset.card = 28 := by decide +kernel
theorem v20 : (C 25 20).toFinset.card = 33 := by decide +kernel
theorem v22 : (C 25 22).toFinset.card = 58 := by decide +kernel
theorem v25 : (C 25 25).toFinset.card = 125 := by decide +kernel

end OMA.P_oeis_a002124

open OMA.P_oeis_a002124 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a002124.main) := by
  intro h
  have hR : -(PowerSeries.X - 1) * (PowerSeries.X + 1) * (PowerSeries.X ^ 2 + PowerSeries.X + 1) *
        (PowerSeries.X ^ 2 - PowerSeries.X + 1) = (1 - PowerSeries.X ^ 6 : PowerSeries ℤ) := by ring
  rw [hR] at h
  have h25 := congrArg (PowerSeries.coeff 25) h
  simp only [sub_mul, add_mul, one_mul, map_sub, map_add, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_mk, PowerSeries.coeff_one, PowerSeries.coeff_X_pow] at h25
  norm_num at h25
  rw [A_eq 25 (by norm_num), A_eq 22 (by norm_num), A_eq 20 (by norm_num), A_eq 19 (by norm_num),
    A_eq 18 (by norm_num), A_eq 16 (by norm_num), v16, v18, v19, v20, v22, v25] at h25
  norm_num at h25
