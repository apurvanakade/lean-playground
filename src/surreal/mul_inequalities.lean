import set_theory.surreal
namespace pgame
universe u
open pgame

local infix ` ≈ ` := pgame.equiv

theorem sub_congr {w x y z : pgame} (h₁ : w ≈ x) (h₂ : y ≈ z) : w - y ≈ x - z :=
sorry

theorem mul_congr {w x y z : pgame} (h₁ : w ≈ x) (h₂ : y ≈ z) : w * y ≈ x * z :=
sorry

lemma sub_zero_equiv (x : pgame.{u}) : x - 0 ≈ x := sorry
#check lt_of_equiv_of_lt

-- theorem lt_of_lt_of_equiv {x y z} (h₁ : x < y) (h₂ : y ≈ z) : x < z := lt_of_lt_of_le h₁ h₂.1
-- theorem le_of_le_of_equiv {x y z} (h₁ : x ≤ y) (h₂ : y ≈ z) : x ≤ z := le_trans h₁ h₂.1
-- theorem lt_of_equiv_of_lt {x y z} (h₁ : x ≈ y) (h₂ : y < z) : x < z := lt_of_le_of_lt h₁.1 h₂
-- theorem le_of_equiv_of_le {x y z} (h₁ : x ≈ y) (h₂ : y ≤ z) : x ≤ z := le_trans h₁.1 h₂


#check @zero_le 
-- zero_le :
--   ∀ {x : pgame},
--     0 ≤ x ↔ 
-- ∀ (j : xR), ∃ (i : (xR j).left_moves), 0 ≤ (xR j).move_left i

#check @zero_lt
-- zero_lt :
--   ∀ {x : pgame},
--     0 < x ↔ 
-- ∃ (i : xL), ∀ (j : (xL i).right_moves), 0 < (xL i).move_right j

#check left_moves_add

def left_moves_add_add (x y z : pgame) : (x + y + z).left_moves ≃ x.left_moves ⊕ y.left_moves ⊕ z.left_moves :=
by { cases x, cases y, cases z, sorry }

def right_moves_add_add (x y z : pgame) : (x + y + z).right_moves ≃ x.right_moves ⊕ y.right_moves ⊕ z.right_moves :=
by { cases x, cases y, cases z, sorry }


theorem zero_le' {x : pgame} : 0 ≤ x ↔ 
  (∀ j : x.right_moves, 0 < x.move_right j) :=
begin
  rw le_def_lt,
  split,
  rintros ⟨hi,hj⟩ j,
  exact hj j,
  rintros hj,
  split,
  rintros ⟨⟩,
  exact hj,
end

theorem zero_lt' {x : pgame} : 0 < x ↔ 
  (∃ i : x.left_moves, 0 ≤ x.move_left i) :=
by {rw lt_def_le, dsimp, simp[forall_pempty] }

/-- An explicit description of the moves for Right in `x * y`. -/

lemma mk_mul_move_left_inl' {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_left (sum.inl (i,j))
  = (xL i - mk xl xr xL xR) * (mk yl yr yL yR - yL j) + mk xl xr xL xR * mk yl yr yL yR := 
sorry

lemma mul_move_left_inl' {x y : pgame} {i j} :
   (x * y).move_left ((@left_moves_mul x y).symm (sum.inl (i,j)))
   = (x.move_left i - x) * (y - y.move_left j) + x * y :=
sorry

lemma mk_mul_move_left_inr' {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_left (sum.inr (i,j))
  = (xR i - mk xl xr xL xR) * (mk yl yr yL yR - yR j) + mk xl xr xL xR * mk yl yr yL yR :=
sorry

lemma mul_move_left_inr' {x y : pgame} {i j} :
   (x * y).move_left ((@left_moves_mul x y).symm (sum.inr (i,j)))
   = (x.move_right i - x) * (y - y.move_right j) + x * y := 
sorry

lemma mk_mul_move_right_inl' {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_right (sum.inl (i,j))
  = (xL i - mk xl xr xL xR) * (mk yl yr yL yR - yR j) + mk xl xr xL xR * mk yl yr yL yR := 
sorry

lemma mul_move_right_inl' {x y : pgame} {i j} :
   (x * y).move_right ((@right_moves_mul x y).symm (sum.inr (i, j)))
   = (x.move_right i - x) * (y - y.move_left j) + x * y := 
sorry

@[simp] lemma mk_mul_move_right_inr' {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_right (sum.inr (i,j))
  = (xR i - mk xl xr xL xR) * (mk yl yr yL yR - yL j) + mk xl xr xL xR * mk yl yr yL yR := 
sorry

lemma mul_move_right_inr' {x y : pgame} {i j} :
   (x * y).move_right ((@right_moves_mul x y).symm (sum.inr (i,j)))
   = (x.move_right i - x) * (y - y.move_left j) + x * y := 
sorry

lemma aux {x : pgame} (ox : numeric x) : (0 ≤ x) → (0 ≈ x) ∨ (0 < x) :=
begin
  rintros,
  by_cases 0 ≈ x,
  left, exact h,

  unfold pgame.equiv at *,
  push_neg at h,
  right,
  rw lt_iff_le_not_le numeric_zero ox,
  split, assumption,
  intros ᾰ_1, solve_by_elim,

end  

def foo : Π {x y : pgame} (ox : numeric x) (oy : numeric y), ((0 < x) → (0 < y) → 0 < x * y) ∧ (x * y).numeric
| (mk xl xr xL xR) (mk yl yr yL yR) ox oy:=
begin 
  set x := mk xl xr xL xR,
  set y := mk yl yr yL yR,
  split,
  
  intros pos_x pos_y,
  
  cases  zero_lt'.1 pos_x with i hi, 
  dsimp at *,
  cases zero_lt'.1 pos_y with j hj, 
  dsimp at *,

  rw zero_lt',

  use sum.inl (i,j), 
  dsimp,

  cases aux (ox.2.1 i) hi with h₁ h₂,
  cases aux (oy.2.1 j) hj with h₃ h₄,
  { calc 0 ≤ 0 : by refl
       ... ≈ 0 + 0 : (add_zero_equiv 0).symm
       ... ≈ 0 + 0 - 0 : (sub_zero_equiv _).symm
       ... ≈ 0 * y + x * 0 - 0 * 0 : sub_congr (add_congr (zero_mul_equiv _).symm (mul_zero_equiv _).symm) (mul_zero_equiv _).symm 
       ... ≈ xL i * y + x * yL j - xL i * yL j : by {refine sub_congr (add_congr _ _) _; refine mul_congr _ _; simpa <|> refl } },
  { calc 0 ≤ mk xl xr xL xR * yL j : le_of_lt numeric_zero (foo ox (oy.2.1 j)).2 ((foo ox (oy.2.1 j)).1 pos_x h₄)
       ... ≈ 0 + mk xl xr xL xR * yL j : (zero_add_equiv _).symm
       ... ≈ 0 + mk xl xr xL xR * yL j - 0 : (sub_zero_equiv _).symm
       ... ≈ 0 * mk yl yr yL yR + mk xl xr xL xR * yL j - 0 * yL j : sub_congr (add_congr (zero_mul_equiv _).symm (equiv_refl _)) (zero_mul_equiv _).symm
       ... ≈ xL i * mk yl yr yL yR + mk xl xr xL xR * yL j - xL i * yL j : by {refine sub_congr (add_congr _ _) _; refine mul_congr _ _; simpa <|> refl } },

  sorry, -- most complex case
repeat {sorry},
end
using_well_founded { dec_tac := pgame_wf_tac }

#check @add_le_add_right

#check @mk_mul_move_left_inl




end pgame
/-- Definition of `x < y` on pre-games, in terms of `≤` -/
-- theorem lt_def_le {x y : pgame} : x < y ↔
--   (∃ i : y.left_moves, x ≤ y.move_left i) ∨
--   (∃ j : x.right_moves, x.move_right j ≤ y) :=
-- by { cases x, cases y, refl }
