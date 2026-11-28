import OMAStatements.S_oeis_a316316
import Mathlib

open OMA.S_oeis_a316316

namespace P316316

def shift40 (w : Window) : Window := ⟨w.a + 40, w.b + 40, w.c + 40, w.d + 40, w.e + 40, w.f + 40⟩

theorem step_shift (w : Window) : step (shift40 w) = shift40 (step w) := by
  simp only [step, shift40, Window.mk.injEq]
  refine ⟨trivial, trivial, trivial, trivial, trivial, ?_⟩ <;> ring

theorem key : ∀ k, window (k + 12) = shift40 (window k) := by
  intro k
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show k + 1 + 12 = (k + 12) + 1 by omega, window, ih, window, step_shift]

end P316316

theorem OMA.solution : type_of% @OMA.S_oeis_a316316.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [show k + 1 + 12 = (k + 12) + 1 by omega, term, term, P316316.key]
  rfl
