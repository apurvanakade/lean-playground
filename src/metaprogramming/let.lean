universe u 
variables a b c : Type u 

meta def trace_example : tactic unit := 
do 
  goal ← tactic.target,
  tactic.trace goal


meta def let_example : tactic unit := 
do 
  let message := "Hello world!",
  tactic.trace message


#check trace_example
#eval let_example