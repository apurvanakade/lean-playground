import data.nat.basic 

open tactic 
open tactic.interactive («have»)

example (a b : ℕ) (h : a = b) : b = a := eq.symm h

meta def my_symm : tactic unit := 
do 
  eq1 ← get_local `h,
  «have» none none ``(eq.symm %%eq1) 

example (a b : ℕ) (h : a = b) : b = a := 
begin 
  my_symm,
  exact this
end 

open interactive (parse)
open lean.parser (ident)

meta def tactic.interactive.my_symm' (eq1 : parse ident) : tactic unit := 
do 
  eq1 ← get_local eq1,
  «have» none none ``(eq.symm %%eq1)

example (a b : ℕ) (h : a = b) : b = a := 
begin 
  my_symm' h, 
  sorry,
end