import set_theory.game  

open pgame

namespace pgame

local infix ` ≈ ` := pgame.equiv

theorem equiv_of_mk_equiv {x y : pgame}
  (L : x.left_moves ≃ y.left_moves) (R : x.right_moves ≃ y.right_moves)
  (hl : ∀ (i : x.left_moves), x.move_left i ≈ y.move_left (L i))
  (hr : ∀ (j : y.right_moves), x.move_right (R.symm j) ≈ y.move_right j) : x ≈ y :=
sorry
  
theorem equiv_of_game_eq {x y : pgame}
  (L : x.left_moves ≃ y.left_moves) (R : x.right_moves ≃ y.right_moves)
  (hl : ∀ (i : x.left_moves), ⟦x.move_left i⟧ = ⟦y.move_left (L i)⟧)
  (hr : ∀ (j : y.right_moves), ⟦x.move_right (R.symm j)⟧ = ⟦y.move_right j⟧) :
  -- (hl : ∀ (i : x.left_moves), x.move_left i ≈ y.move_left (L i))
  -- (hr : ∀ (j : y.right_moves), x.move_right (R.symm j) ≈ y.move_right j) :
  x ≈ y := sorry
-- begin
--   fsplit; rw le_def,
--   { exact ⟨λ i, or.inl ⟨L i, (hl i).1⟩, λ j, or.inr ⟨R.symm j, (hr j).1⟩⟩ },
--   { fsplit; apply quotient.sound,
--     { intro i,
--       left,
--       specialize hl (L.symm i),
--       simp only [move_left_mk, equiv.apply_symm_apply] at hl,
--       use ⟨L.symm i, hl.2⟩ },
--     { intro j,
--       right,
--       specialize hr (R j),
--       simp only [move_right_mk, equiv.symm_apply_apply] at hr,
--       use ⟨R j, hr.2⟩ } }
-- end
#check add_congr

def mul (x y : pgame) : pgame :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  have y := mk yl yr yL yR,
  refine ⟨xl × yl ⊕ xr × yr, xl × yr ⊕ xr × yl, _, _⟩; rintro (⟨i, j⟩ | ⟨i, j⟩),
  { exact IHxl i y + IHyl j - IHxl i (yL j) },
  { exact IHxr i y + IHyr j - IHxr i (yR j) },
  { exact IHxl i y + IHyr j - IHxl i (yR j) },
  { exact IHxr i y + IHyl j - IHxr i (yL j) }
end

instance : has_mul pgame := ⟨mul⟩

theorem mul_congr {w x y z : pgame} (h₁ : w ≈ x) (h₂ : y ≈ z) : w * y ≈ x * z :=
begin
  refine equiv_of_mk_equiv _ _ _ _,

end 
end pgame
