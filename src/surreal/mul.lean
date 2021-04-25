import set_theory.surreal
open pgame
namespace pgame

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
  = (mk xl xr xL xR).move_left i * (mk yl yr yL yR)
    + (mk xl xr xL xR) * (mk yl yr yL yR).move_left j
    - (mk xl xr xL xR).move_left i * (mk yl yr yL yR).move_left j
:= rfl

@[simp] lemma mul_move_left_inl {x y : pgame} {i j} :
   (x * y).move_left ((@left_moves_mul x y).symm (sum.inl (i,j)))
   = x.move_left i * y + x * y.move_left j - x.move_left i * y.move_left j
:= by {cases x, cases y, refl} 

@[simp] lemma mk_mul_move_left_inr {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_left (sum.inr (i,j))
  = (mk xl xr xL xR).move_right i * (mk yl yr yL yR)
    + (mk xl xr xL xR) * (mk yl yr yL yR).move_right j
    - (mk xl xr xL xR).move_right i * (mk yl yr yL yR).move_right j
:= rfl

@[simp] lemma mul_move_left_inr {x y : pgame} {i j} :
   (x * y).move_left ((@left_moves_mul x y).symm (sum.inr (i,j)))
   = x.move_right i * y + x * y.move_right j - x.move_right i * y.move_right j
:= by {cases x, cases y, refl}

@[simp] lemma mk_mul_move_right_inl {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_right (sum.inl (i,j))
  = (mk xl xr xL xR).move_left i * (mk yl yr yL yR)
    + (mk xl xr xL xR) * (mk yl yr yL yR).move_right j
    - (mk xl xr xL xR).move_left i * (mk yl yr yL yR).move_right j
:= rfl

@[simp] lemma mul_move_right_inl {x y : pgame} {i j} :
   (x * y).move_right ((@right_moves_mul x y).symm (sum.inr (i, j)))
   = x.move_right i * y + x * y.move_left j - x.move_right i * y.move_left j
:= by {cases x, cases y, refl} 

@[simp] lemma mk_mul_move_right_inr {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_right (sum.inr (i,j))
  = (mk xl xr xL xR).move_right i * (mk yl yr yL yR)
    + (mk xl xr xL xR) * (mk yl yr yL yR).move_left j
    - (mk xl xr xL xR).move_right i * (mk yl yr yL yR).move_left j
:= rfl

@[simp] lemma mul_move_right_inr {x y : pgame} {i j} :
   (x * y).move_right ((@right_moves_mul x y).symm (sum.inr (i,j)))
   = x.move_right i * y + x * y.move_left j - x.move_right i * y.move_left j
:= by {cases x, cases y, refl}

/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
    then `w + y` has the same moves as `x + z`. -/
def add_congr_relabelling : ∀ {w x y z : pgame},
w.relabelling x → y.relabelling z → (w + y).relabelling (x + z)
| (mk wl wr wL wR) (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR)
  ⟨L_equiv₁, R_equiv₁, L_relabelling₁, R_relabelling₁⟩
  ⟨L_equiv₂, R_equiv₂, L_relabelling₂, R_relabelling₂⟩ :=
begin
  refine ⟨_,_,_,_⟩,
  { fsplit,
    { rintro (i|j),
      { exact sum.inl (L_equiv₁ i) },
      { exact sum.inr (L_equiv₂ j) }},
    { rintro (i|j),
      { exact sum.inl (L_equiv₁.symm i) },
      { exact sum.inr (L_equiv₂.symm j) }},
    { rintro (_|_); simp only [equiv.symm_apply_apply] },
    { rintro (_|_); simp only [equiv.apply_symm_apply] }},
  { fsplit,
    { rintro (i|j),
      { exact sum.inl (R_equiv₁ i) },
      { exact sum.inr (R_equiv₂ j) }},
    { rintro (i|j),
      { exact sum.inl (R_equiv₁.symm i) },
      { exact sum.inr (R_equiv₂.symm j) }},
    { rintro (_|_); simp only [equiv.symm_apply_apply] },
    { rintro (_|_); simp only [equiv.apply_symm_apply] }},
  { rintro (i|j), 
    { exact add_congr_relabelling 
        (L_relabelling₁ i) 
        (⟨L_equiv₂, R_equiv₂, L_relabelling₂, R_relabelling₂⟩) },
    { exact add_congr_relabelling 
        (⟨L_equiv₁, R_equiv₁, L_relabelling₁, R_relabelling₁⟩) 
        (L_relabelling₂ j) }},
        
  { rintro (i|j),
    { exact add_congr_relabelling 
        (R_relabelling₁ i) 
        (⟨L_equiv₂, R_equiv₂, L_relabelling₂, R_relabelling₂⟩) },
    { exact add_congr_relabelling 
        (⟨L_equiv₁, R_equiv₁, L_relabelling₁, R_relabelling₁⟩) 
        (R_relabelling₂ j) }},
end
using_well_founded { dec_tac := pgame_wf_tac }

/-- If `x` has the same moves as `y`, then `-x` has the sames moves as `-y`. -/
def neg_congr_relabelling : ∀ {x y : pgame}, x.relabelling y → (-x).relabelling (-y)
| (mk xl xr xL xR) (mk yl yr yL yR) ⟨L_equiv, R_equiv, L_relabelling, R_relabelling⟩ :=
  ⟨R_equiv, L_equiv,
    λ i, neg_congr_relabelling (by simpa using R_relabelling (R_equiv i)),
    λ i, neg_congr_relabelling (by simpa using L_relabelling (L_equiv.symm i))⟩

/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
then `w - y` has the same moves as `x - z`. -/
theorem sub_congr_relabelling {w x y z : pgame} 
  (h₁ : w.relabelling x) (h₂ : y.relabelling z) : (w - y).relabelling (x - z) :=
add_congr_relabelling h₁ (neg_congr_relabelling h₂)

/-- If `a` has the same moves as `x`, `b` has the same moves as `y`,
and `c` has the same moves as `z`, then `a + b - c` has the same moves as `y + x - z`. -/
lemma add_sub_comm {a b c x y z : pgame}
  (h₁ : a.relabelling x) (h₂ : b.relabelling y) (h₃ : c.relabelling z) :
  (a + b - c).relabelling (y + x - z) := 
sub_congr_relabelling
  (relabelling.trans
    (add_comm_relabelling a b)
    (add_congr_relabelling h₂ h₁)) h₃

/-- `x * y` has exactly the same moves as `y * x`. -/
theorem mul_comm_relabelling (x y : pgame) : (x * y).relabelling (y * x):=
begin
  induction x with xl xr xL xR I1 I2 generalizing y,
  induction y with yl yr yL yR J1 J2,

  refine ⟨_,_,_,_⟩,

  { fsplit; rintro (⟨i, j⟩ | ⟨i, j⟩); 
    exact sum.inl (j,i) <|> exact sum.inr (j,i) <|> refl },

  { fsplit; rintro (⟨i, j⟩ | ⟨i, j⟩); 
    exact sum.inl (j,i) <|> exact sum.inr (j,i) <|> refl },

  { rintro (⟨i, j⟩ | ⟨i, j⟩),
    { exact add_sub_comm (I1 i (mk yl yr yL yR)) (J1 j) (I1 i (yL j)) },
    { exact add_sub_comm (I2 i (mk yl yr yL yR)) (J2 j) (I2 i (yR j)) }},

  { rintro (⟨i, j⟩ | ⟨i, j⟩),
    { exact add_sub_comm (I2 j (mk yl yr yL yR)) (J1 i) (I2 j (yL i)) },
    { exact add_sub_comm (I1 j (mk yl yr yL yR)) (J2 i) (I1 j (yR i)) }}
end

/-- `x * y` is equivalent to `y * x`. -/
theorem mul_comm_equiv (x y : pgame) : (x * y).equiv (y * x) := 
equiv_of_relabelling (mul_comm_relabelling x y) 

/-- `x * 0` has exactly the same moves as `0`. -/
theorem mul_zero_relabelling : Π (x : pgame), relabelling (x * 0) 0
| (mk xl xr xL xR) :=
⟨by fsplit; rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩),
 by fsplit; rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩), 
 by rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩),
 by rintro ⟨⟩⟩

/-- `x * 0` is equivalent to `0`. -/
theorem mul_zero_equiv (x : pgame) : (x * 0).equiv 0 :=
equiv_of_relabelling (mul_zero_relabelling x)
   
/-- `0 * x` has exactly the same moves as `0`. -/
theorem zero_mul_relabelling : Π (x : pgame), relabelling (0 * x) 0
| (mk xl xr xL xR) :=
⟨by fsplit; rintro (⟨⟨⟩, _⟩ | ⟨⟨⟩, _⟩),
 by fsplit; rintro (⟨⟨⟩, _⟩ | ⟨⟨⟩, _⟩),
 by rintro (⟨⟨⟩,_⟩ | ⟨⟨⟩,_⟩),
 by rintro ⟨⟩⟩ 

/-- `0 * x` is equivalent to `0`. -/
theorem zero_mul_equiv (x : pgame) : (0 * x).equiv 0 :=
equiv_of_relabelling (zero_mul_relabelling x)

end pgame
