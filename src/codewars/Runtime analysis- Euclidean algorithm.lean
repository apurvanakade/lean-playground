-- https://www.codewars.com/kata/5eb80c83eccaf80032feae69/train/lean

/-
def gcd : nat → nat → nat
| 0        y := y
| (succ x) y := have y % succ x < succ x, from mod_lt _ $ succ_pos _,
                gcd (y % succ x) (succ x)
-/

import data.nat.basic

open nat
open classical
attribute [instance] prop_decidable

def gcd_steps : ℕ → ℕ → ℕ
| 0        y := 0
| (succ x) y := have y % succ x < succ x, from mod_lt _ $ succ_pos _,
                1 + gcd_steps (y % succ x) (succ x)

def fib : ℕ → ℕ 
| 0 := 0 
| 1 := 1 
| (n + 2) := (fib n) + (fib (n + 1))

theorem euclid_not_constant : ∀ n, ∃ a b, gcd_steps a b = n := 
begin 
  intro n,
  use (fib n), 
  use (fib (n+1)),
  induction n with n hyp,
  unfold fib, refl,
  
  repeat {sorry,}
end 

example (n:ℕ) : n.succ = n + 1 := rfl