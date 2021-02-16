open tactic 

example (a b : Prop) : a → b → a ∧ b := 
by 
  do 
    intros,
    split,
    local_context >>= trace,
    target >>= trace,
    assumption,
    assumption

meta def find_pattern (e:expr) 
  : list expr → tactic expr 
| [] := fail "did not find matching pattern"
| (h :: t) := do 
                h_type ← infer_type h,
                do {unify e h_type,
                  return h}
                <|> 
                find_pattern t


meta def my_assumption : tactic unit := 
do 
  {
    local_ctx ← local_context,
    tar ← target, 
    pattern ← find_pattern tar local_ctx, 
    tactic.exact pattern
  } <|> failed



example (a b : Prop) : a → b → a ∧ b := 
by 
  do 
    intros,
    split,
    local_context >>= trace,
    target >>= trace,
    my_assumption,
    my_assumption