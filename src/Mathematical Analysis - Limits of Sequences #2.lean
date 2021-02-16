-- https://www.codewars.com/kata/5e9981da9dd96e001f3b7c0c/train/lean

import data.real.basic
open classical
attribute [instance] prop_decidable

/-
  Rigorous definition of a limit
  For a sequence x_n, we say that \lim_{n \to \infty} x_n = l if
    ∀ ε > 0, ∃ N, n ≥ N → |x_n - l| < ε
-/

def lim_to_inf (x : ℕ → ℝ) (l : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (x n - l) < ε

/-
-- Suppose |x_n - l| \leq y_n and \lim_{n\to\infty} y_n = 0.
-- Then \lim_{n\to\infty} x_n = l.
def SUBMISSION := ∀ (x y : ℕ → ℝ) l,
  (∀ n, abs (x n - l) ≤ y n) →
  lim_to_inf y 0 →
  lim_to_inf x l
notation `SUBMISSION` := SUBMISSION
-/

example (x : ℝ) : x ≤ abs x 
:= 
by exact le_abs_self x


theorem exercise_1p3 (x y : ℕ → ℝ) (l : ℝ)
  (h₁ : ∀ n, abs (x n - l) ≤ y n) (h₂ : lim_to_inf y 0) :
  lim_to_inf x l := 
begin 
  -- unfold lim_to_inf,
  show ∀ (ε : ℝ), ε > 0 → (∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → abs (x n - l) < ε),
  intros ε pos_ε, -- let ε be a real number such that ε > 0
  -- unfold lim_to_inf at h₂,
  specialize h₂ ε pos_ε, -- using h₂, ε, and pos_ε we get that ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → abs (y n - 0) < ε
  cases h₂ with n hn,
  use n,
  intros n_1 hn_1,
  specialize hn n_1 hn_1,
  specialize h₁ n_1,
  clear hn_1 n pos_ε,
  simp at hn,
  have : y n_1 ≤ abs (y n_1), 
  exact le_abs_self (y n_1),
  linarith,
end

