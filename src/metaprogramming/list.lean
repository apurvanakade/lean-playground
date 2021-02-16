universe u 
variables a b c : Type u 

open tactic 
open interactive

/- 

List monad:

inductive list (T : Type u)
| nil : list
| cons (hd : T) (tl : list) : list


Given a function f: a → b, the following are two ways of defining the induced function list f : list a → list b. 
-/

-- def map (f : a → b) (l : list a)
-- : list b := 
-- match l with 
-- | [] := [] 
-- | (h :: t) := ((f h) :: map t)
-- end


def map' (f : a → b) : list a
→ list b 
| [] := [] 
| (h :: t) := ((f h) :: map' t)

def map'' (f : a → b) (α : list a)
: list b 
:= 
do x ← α,
  return (f x)


def map''' (f : a → b) (α : list a)
: list b 
:= 
α >>= (λ x, return (f x))


#check map' 
#check map'' 
#check map''' 

#check @return 

#check monad 

meta def list_local_ctx : tactic unit := 
do 
  ctx ← tactic.local_context,
  ctx.mmap' (λ str, infer_type str >>= tactic.trace)

example (a : ℕ) : a ≥ a := 
begin
  list_local_ctx,
  sorry,
end 
