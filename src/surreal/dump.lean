import set_theory.surreal
open pgame

-- `x*y` has exactly the same moves as `y*x`.
def mul_comm_relabelling' : Π (x y : pgame), relabelling (x * y) (y * x) :=
begin
  intros x y,
  fsplit,
  calc (x * y).left_moves
    ≃ x.left_moves × y.left_moves ⊕ x.right_moves × y.right_moves : @left_moves_mul x y
    ... ≃  y.left_moves × x.left_moves ⊕ x.right_moves × y.right_moves : by {refine equiv.sum_congr _ _, apply equiv.prod_comm, refl, }
    ... ≃  y.left_moves × x.left_moves ⊕ y.right_moves × x.right_moves : by {refine equiv.sum_congr _ _, refl, apply equiv.prod_comm }
    ... ≃ (y * x).left_moves : equiv.symm (@left_moves_mul y x), 
    
  calc (x * y).right_moves
    ≃ x.left_moves × y.right_moves ⊕ x.right_moves × y.left_moves : @right_moves_mul x y
    ... ≃ y.right_moves × x.left_moves ⊕ x.right_moves × y.left_moves : by { refine equiv.sum_congr _ _, apply equiv.prod_comm, refl}
    ... ≃ y.right_moves × x.left_moves ⊕ y.left_moves × x.right_moves : by {refine
equiv.sum_congr _ _, refl, apply equiv.prod_comm }
  ... ≃ y.left_moves × x.right_moves ⊕ y.right_moves × x.left_moves : by apply equiv.sum_comm
    ... ≃ (y * x).right_moves : equiv.symm (@right_moves_mul y x),

dsimp at *, 
rintro i,
fsplit, fsplit,
intros,

sorry,
 sorry,
end

-- def mul_one_relabelling' : Π (x : pgame), relabelling (x * 1) x
-- | (mk xl xr xL xR) :=
-- begin 
--   let x:= (mk xl xr xL xR),
--   refine ⟨_,_,_,_⟩,
--   have := (@left_moves_mul x 1),
--   --rw one_left_moves at *; rw one_right_moves at *,
--   dsimp[one_left_moves, one_right_moves] at *,
--   { 
--   calc 
--   (x * 1).left_moves ≃ x.left_moves × punit ⊕ x.right_moves × pempty : left_moves_mul
--   ... ≃ x.left_moves × punit ⊕ pempty : by refine equiv.sum_congr (equiv.cast rfl) (equiv.prod_pempty _)
--   ... ≃ x.left_moves × punit : equiv.sum_pempty (left_moves x × punit)
--   ... ≃ x.left_moves : equiv.prod_punit (left_moves x),
--   },
--   { 
--   calc 
--     (x * 1).right_moves ≃ x.left_moves × pempty ⊕ x.right_moves × punit : right_moves_mul
--     ... ≃ pempty ⊕ x.right_moves × punit : by refine equiv.sum_congr (equiv.prod_pempty _) (equiv.cast rfl)
--     ... ≃ x.right_moves × punit : equiv.pempty_sum (right_moves x × punit)
--     ... ≃ x.right_moves : equiv.prod_punit (right_moves x),
--   },
--   dsimp at *,
--   rintro (⟨i, ⟨⟩⟩ | ⟨i, ⟨⟩⟩),  
-- end
