open tactic 

meta def do_nothing 
: tactic unit := 
skip

example (a : ℕ) : ℕ := 
begin 
  do_nothing, 
  assumption,
end 

-----------------------------------------------------


meta def test_if_equality : tactic unit :=
do { `(%%l = %%r) ← target,
      let message := "LHS = " ++ (to_string l) ++ ", RHS = " ++ (to_string r),
      tactic.trace message }
<|> fail "Goal is not an equality"

meta def test_if_lt : tactic unit :=
do { `(%%l < %%r) ← target,
      let message := "LHS = " ++ (to_string l) ++ ", RHS = " ++ (to_string r),
      tactic.trace message }
<|> fail "Goal is not an equality"


meta def test_if_le : tactic unit :=
do { `(%%l ≤ %%r) ← target,
      let message := "LHS = " ++ (to_string l) ++ ", RHS = " ++ (to_string r),
      tactic.trace message }
<|> fail "Goal is not an equality"

meta def test_if_gt : tactic unit :=
do { `(%%l > %%r) ← target,
      let message := "LHS = " ++ (to_string l) ++ ", RHS = " ++ (to_string r),
      tactic.trace message }
<|> fail "Goal is not an equality"


meta def test_if_ge : tactic unit :=
do { `(%%l ≥ %%r) ← target,
      let message := "LHS = " ++ (to_string l) ++ ", RHS = " ++ (to_string r),
      tactic.trace message }
<|> fail "Goal is not an equality"


meta def get_LHS_RHS : tactic unit :=
test_if_equality
<|> test_if_lt 
<|> test_if_le 
<|> test_if_gt 
<|> test_if_ge 
<|> fail "Goal does not have an LHS and RHS"

example (a : ℕ) : a ≥ a := 
begin
  get_LHS_RHS,
  sorry,
end 