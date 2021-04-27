import set_theory.surreal 
open pgame
namespace pgame

universe u

/-- An explicit description of the moves for Left in `x * y`. -/
def left_moves_mul {x y : pgame} : (x * y).left_moves 
  ≃ x.left_moves × y.left_moves ⊕ x.right_moves × y.right_moves :=
by { cases x, cases y, refl, }

/-- An explicit description of the moves for Right in `x * y`. -/
def right_moves_mul {x y : pgame} : (x * y).right_moves 
  ≃ x.left_moves × y.right_moves ⊕ x.right_moves × y.left_moves :=
by { cases x, cases y, refl, }

@[simp] lemma mk_mul_move_left_inl {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_left (sum.inl (i,j))
    = xL i * (mk yl yr yL yR) + (mk xl xr xL xR) * yL j - xL i * yL j
:= rfl

@[simp] lemma mul_move_left_inl {x y : pgame} {i j} :
   (x * y).move_left ((@left_moves_mul x y).symm (sum.inl (i,j)))
     = x.move_left i * y + x * y.move_left j - x.move_left i * y.move_left j
:= by {cases x, cases y, refl} 

@[simp] lemma mk_mul_move_left_inr {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_left (sum.inr (i,j))
    = xR i * (mk yl yr yL yR) + (mk xl xr xL xR) * yR j - xR i * yR j
:= rfl

@[simp] lemma mul_move_left_inr {x y : pgame} {i j} :
   (x * y).move_left ((@left_moves_mul x y).symm (sum.inr (i,j)))
     = x.move_right i * y + x * y.move_right j - x.move_right i * y.move_right j
:= by {cases x, cases y, refl}

@[simp] lemma mk_mul_move_right_inl {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_right (sum.inl (i,j))
    = xL i * (mk yl yr yL yR) + (mk xl xr xL xR) * yR j - xL i * yR j
:= rfl

@[simp] lemma mul_move_right_inl {x y : pgame} {i j} :
   (x * y).move_right ((@right_moves_mul x y).symm (sum.inr (i, j)))
     = x.move_right i * y + x * y.move_left j - x.move_right i * y.move_left j
:= by {cases x, cases y, refl} 

@[simp] lemma mk_mul_move_right_inr {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_right (sum.inr (i,j))
    = xR i * (mk yl yr yL yR) + (mk xl xr xL xR) * yL j - xR i * yL j
:= rfl

@[simp] lemma mul_move_right_inr {x y : pgame} {i j} :
   (x * y).move_right ((@right_moves_mul x y).symm (sum.inr (i,j)))
     = x.move_right i * y + x * y.move_left j - x.move_right i * y.move_left j
:= by {cases x, cases y, refl}

local infix ` ~ ` := relabelling

/-- `x * 0` has exactly the same moves as `0`. -/
theorem mul_zero_relabelling : Π (x : pgame), relabelling (x * 0) 0
| (mk xl xr xL xR) :=
⟨by fsplit; rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩),
 by fsplit; rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩), 
 by rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩),
 by rintro ⟨⟩⟩

/-- `x * 0` is equivalent to `0`. -/
lemma mul_zero_equiv (x : pgame) : (x * 0).equiv 0 :=
equiv_of_relabelling (mul_zero_relabelling x)
   
/-- `0 * x` has exactly the same moves as `0`. -/
theorem zero_mul_relabelling : Π (x : pgame), relabelling (0 * x) 0
| (mk xl xr xL xR) :=
⟨by fsplit; rintro (⟨⟨⟩, _⟩ | ⟨⟨⟩, _⟩),
 by fsplit; rintro (⟨⟨⟩, _⟩ | ⟨⟨⟩, _⟩),
 by rintro (⟨⟨⟩,_⟩ | ⟨⟨⟩,_⟩),
 by rintro ⟨⟩⟩ 

/-- `0 * x` is equivalent to `0`. -/
lemma zero_mul_equiv (x : pgame) : (0 * x).equiv 0 :=
equiv_of_relabelling (zero_mul_relabelling x)

theorem sub_congr_relabelling {w x y z : pgame} 
  (h₁ : w.relabelling x) (h₂ : y.relabelling z) : (w - y).relabelling (x - z) :=
  sorry

#check equiv.refl

def mul_one_relabelling : Π {x : pgame.{u}}, relabelling (x * 1) x
| (mk xl xr xL xR) :=
begin 
  refine ⟨_,_,_,_⟩,
  calc
     (mk xl xr xL xR * 1).left_moves
         ≃ xl × punit ⊕ xr × pempty : by refl
     ... ≃ xl × punit ⊕ pempty : equiv.sum_congr (equiv.refl _) (equiv.prod_pempty _)
     ... ≃ xl × punit : equiv.sum_pempty _
     ... ≃ xl : equiv.prod_punit _,

  calc
     (mk xl xr xL xR * 1).right_moves
         ≃ xl × pempty ⊕ xr × punit : by refl
     ... ≃ pempty ⊕ xr × punit : equiv.sum_congr (equiv.prod_pempty _) (equiv.refl _)
     ... ≃ xr × punit : equiv.pempty_sum _
     ... ≃ xr : equiv.prod_punit _,

  rintros (⟨i, ⟨⟩⟩|⟨i, ⟨⟩⟩),
  calc
    xL i * 1 + mk xl xr xL xR * 0 - xL i * 0
           ~ xL i * 1 + mk xl xr xL xR * 0 - 0 : sub_congr_relabelling (relabelling.refl _) (mul_zero_relabelling _)
       ... ~ xL i * 1 + mk xl xr xL xR * 0 + (-0) : by refl
       ... ~ xL i * 1 + (mk xl xr xL xR * 0 + 0) : sorry
       ... ~ xL i * 1 + mk xl xr xL xR * 0 : sorry
       ... ~ xL i * 1 + 0 : sorry
       ... ~ xL i * 1 : sorry
       ... ~ xL i : mul_one_relabelling,
  
  intro j,
  calc
    xR j * 1 + mk xl xr xL xR * 0 - xR j * 0
        ~ xR j * 1 + (mk xl xr xL xR * 0 - xR j * 0) : sorry
    ... ~ xR j * 1 + (mk xl xr xL xR * 0 - xR j * 0) : sorry
    ... ~ xR j * 1 + (mk xl xr xL xR - xR j) * 0 : sorry
    ... ~ xR j * 1 + 0 : sorry
    ... ~ xR j * 1 : by { refine add_zero_relabelling _ }
    ... ~ xR j : mul_one_relabelling,
end
using_well_founded { dec_tac := pgame_wf_tac }

example : ∀ (a b c : nat), a + b + c = a + ( b + c )
:=  add_assoc

end pgame

example (a b c : Type) : a × (b ⊕ c) ≃ (a × b) ⊕ (a × c) :=
equiv.prod_sum_distrib a b c

