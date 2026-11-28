import OMAStatements.S_oeis_a002062
import Mathlib

open OMA.S_oeis_a002062

theorem OMA.solution : type_of% @OMA.S_oeis_a002062.main := by
  have key : ∀ n : ℕ, lucas (n + 1) = Nat.fib (n + 2) + Nat.fib n ∧
      lucas (n + 2) = Nat.fib (n + 3) + Nat.fib (n + 1) := by
    intro n
    induction n with
    | zero => decide
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      show lucas (k + 2) + lucas (k + 1) = _
      rw [ih.1, ih.2, Nat.fib_add_two (n := k + 2), Nat.fib_add_two (n := k + 1),
        Nat.fib_add_two (n := k)]
      ring
  intro n
  have h := (key n).2
  have h3 : Nat.fib (n + 3) = Nat.fib (n + 2) + Nat.fib (n + 1) := by rw [Nat.fib_add_two (n := n + 1)]; ring
  simp only [A002062, A006355, A066982]
  rw [h]
  push_cast
  rw [h3]
  push_cast
  ring
