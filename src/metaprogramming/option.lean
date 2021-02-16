universe u
variables a b c : Type u 

/- 
Option monad:

inductive option (α : Type u)
| none : option
| some (val : α) : option


option a is type which has two constructors 
some a and none.

Thus option a can be thought of as a "subtype" of a. 

Given a function f: a → b, we can define a function g: option a → option b which sends x : option a to (f x) if x is some a otherwise sends it to none. 

Following are the different ways of defining this function. 

The first method uses the inductive definition of option and the other three use monadic interpretation of option.
-/

def g  (α : option a) (f : a → b)
  : option b := 
match α with 
| (some x) := f x 
| none     := none 
end


def g'  (α : option a) (f : a → b)
  : option b := 
do x ← α,
  return (f x)

def g''  (α : option a) (f : a → b)
  : option b := 
bind α (λ x, f x)

def g'''  (α : option a) (f : a → b)
  : option b := 
α >>= (λ x, f x)

#check g 
#check g'
#check g'' 
#check g''' 