-- Uniqueness of limits in a metric space
-- https://www.codewars.com/kata/5ea1f341014f0c0001ec7c5e/train/lean

/-
This kata was designed by @JasonKY

Using the Lean maths library's definition of a metric space, we can define the notion of a sequence converging to a limit. Note: the arrow in the notation s ⟶ x can be typeset in VS Code with \hom or \h.

The challenge is to prove that a sequence of elements in a metric space has at most one limit.

Here is the contents of Preloaded.lean.
-/

import topology.metric_space.basic
import tactic 

def converges_to {X : Type*} [metric_space X] (s : ℕ → X) (x : X) :=
∀ (ε : ℝ) (hε : 0 < ε), ∃ N : ℕ, ∀ (n : ℕ) (hn : N ≤ n), dist x (s n) < ε

notation s ` ⟶ ` x := converges_to s x

#check archimedean

lemma archimedean' (ε : ℝ) : (0 ≤ ε ∧ ∀ n : ℕ, (ε * n) < 1) → ε = 0 := sorry  

lemma lem1 {ε N : ℝ} 
  (pos_ε : 0 ≤ ε)
  (pos_N : 0 < N)  
  (hε : ε < 2 * (1 / (2 * N) )) 

: ε * N < 1 := 
calc 
  ε * N <  2 * (1 / (2 * N) ) * N : by sorry 
    ... = (2 / (2 * N)) * N : sorry 
    ... = (1/N) * N : sorry 
    ... = 1 : by sorry 

theorem limit_unique {X : Type*} [metric_space X] {s : ℕ → X}
  (x₀ x₁ : X) (h₀ : s ⟶ x₀) (h₁ : s ⟶ x₁) :
x₀ = x₁ := 
begin 
unfold converges_to at h₀,
unfold converges_to at h₁,
suffices hx: (dist x₀ x₁) = 0, 
  by exact zero_eq_dist.mp (eq.symm hx),
apply archimedean',
split, 
  by simp only [dist_nonneg],
intros N,
set ε := 1/(2 * (N : ℝ)) with he,
have hε : ε > 0, by sorry,
specialize h₀ ε hε,
specialize h₁ ε hε,
cases h₀ with N₀ h₀,
cases h₁ with N₁ h₁,

let n:= max N₀ N₁,
specialize h₀ n,
specialize h₁ n,

have hN₀ : N₀ ≤ n, exact le_max_left N₀ N₁,
have hN₁ : N₁ ≤ n, exact le_max_right N₀ N₁,

have hd₀ := h₀ hN₀,
have hd₁ := h₁ hN₁,

have hd₀₁:= dist_triangle_right x₀ x₁ (s n),
have : dist x₀ x₁ < 2 * ε, by linarith,
clear h₀ h₁ hd₀ hd₁ hd₀₁ hN₀ hN₁ n,
rw he at this,

exact lem1 (@dist_nonneg X _inst_1 x₀ x₁) this,

-- specialize h₀ N₀,
-- have : N₀ ≤ N₀, by exact rfl.ge, 
-- have h₀' := h₀ this, 
-- clear h₀ this,

repeat {sorry,}
end

#check @dist_nonneg