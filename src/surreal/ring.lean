import set_theory.surreal 
-- set_option pp.notation false

#check surreal
#check pgame 

namespace pgame

-- theorem mul_left_moves : Π {x y : pgame}, (x * y).left_moves = x.1 :=

theorem zero_mul : ∀ (x : pgame), (0 * x).equiv 0 :=
begin
intros x,
split,
rw le_zero,
sorry,
rw zero_le,
sorry,
end

end pgame
