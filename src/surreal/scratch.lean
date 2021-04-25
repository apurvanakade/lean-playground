import set_theory.surreal 

open pgame

#check pgame.relabelling

local infix ` ~ ` := pgame.relabelling

example (x y z t : pgame) : x ∼ y → y ∼ z → z ∼ t → x ∼ t :=
begin
intros a b c,
calc x ∼ y : a
     ... ∼ z : b
     ... ∼ t : c
end


