import OMAStatements.S_oeis_a144642
import Mathlib

open OMA.S_oeis_a144642

namespace P144642

def T (y : ℕ) : ℕ := y * (y + 1) / 2

theorem T_mono {a b : ℕ} (h : a ≤ b) : T a ≤ T b := by
  unfold T
  exact Nat.div_le_div_right (Nat.mul_le_mul h (by omega))

def srch (r : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if T ((lo + hi) / 2) ≤ r then srch r f ((lo + hi) / 2) hi else srch r f lo ((lo + hi) / 2)

def ok (r : ℕ) : Bool :=
  decide (T (srch r 13 0 4096) < r) && decide (r < T (srch r 13 0 4096 + 1))

theorem ok_sound (r : ℕ) (h : ok r = true) (y : ℕ) : T y ≠ r := by
  unfold ok at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  intro hy
  rcases Nat.lt_or_ge y (srch r 13 0 4096 + 1) with h1 | h1
  · have := T_mono (show y ≤ srch r 13 0 4096 by omega)
    omega
  · have := T_mono h1
    omega

def fibs : List ℕ := [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987, 1597,
  2584, 4181, 6765, 10946, 17711, 28657, 46368, 75025, 121393, 196418, 317811, 514229, 832040,
  1346269, 2178309, 3524578]

theorem fib_mem : ∀ m < 34, Nat.fib m ∈ fibs := by decide

def chk (a b : ℕ) : Bool :=
  (List.range' a b).all fun x => fibs.all fun f =>
    decide (3970902 < x ^ 2 + f) || ok (3970902 - x ^ 2 - f)

theorem c1 : chk 0 500 = true := by decide +kernel
theorem c2 : chk 500 500 = true := by decide +kernel
theorem c3 : chk 1000 500 = true := by decide +kernel
theorem c4 : chk 1500 493 = true := by decide +kernel

theorem chk_all (x : ℕ) (hx : x < 1993) (f : ℕ) (hf : f ∈ fibs) :
    3970902 < x ^ 2 + f ∨ ok (3970902 - x ^ 2 - f) = true := by
  have key : ∀ a b, chk a b = true → a ≤ x → x < a + b →
      3970902 < x ^ 2 + f ∨ ok (3970902 - x ^ 2 - f) = true := by
    intro a b h h1 h2
    unfold chk at h
    rw [List.all_eq_true] at h
    have := h x (List.mem_range'_1.mpr ⟨h1, h2⟩)
    rw [List.all_eq_true] at this
    have := this f hf
    simpa [Bool.or_eq_true, decide_eq_true_eq] using this
  by_cases h1 : x < 500
  · exact key 0 500 c1 (by omega) (by omega)
  by_cases h2 : x < 1000
  · exact key 500 500 c2 (by omega) (by omega)
  by_cases h3 : x < 1500
  · exact key 1000 500 c3 (by omega) (by omega)
  · exact key 1500 493 c4 (by omega) (by omega)

end P144642

open P144642 in
theorem OMA.solution : type_of% @OMA.S_oeis_a144642.main := by
  intro h
  obtain ⟨x, y, m, he⟩ := h 3970902 (by norm_num)
  have hm : m < 34 := by
    by_contra hc
    have h1 := Nat.fib_mono (show 34 ≤ m by omega)
    have h2 : Nat.fib 34 = 5702887 := by norm_num
    omega
  have hx : x < 1993 := by
    by_contra hc
    have : 1993 ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  rcases chk_all x hx (Nat.fib m) (fib_mem m hm) with h1 | h1
  · omega
  · exact ok_sound _ h1 y (by unfold T; omega)
