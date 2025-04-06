import Mathlib.Tactic

def is_limit (x : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |x n - l| < ε

example : is_limit (fun n => 2) 2 := by
  dsimp [is_limit]
  intro ε hε
  use 2
  intro n hn
  rw [show |_| < ε ↔ 0 < ε by simp]
  apply hε
