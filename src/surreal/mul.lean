import set_theory.surreal
import tactic
open pgame
namespace pgame

universe u

/-- An explicit description of the moves for Left in `x * y`. -/
def left_moves_mul {x y : pgame.{u}} : (x * y).left_moves 
  ≃ x.left_moves × y.left_moves ⊕ x.right_moves × y.right_moves :=
by { cases x, cases y, refl, }

/-- An explicit description of the moves for Right in `x * y`. -/
def right_moves_mul {x y : pgame.{u}} : (x * y).right_moves 
  ≃ x.left_moves × y.right_moves ⊕ x.right_moves × y.left_moves :=
by { cases x, cases y, refl, }

@[simp] lemma mk_mul_move_left_inl {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_left (sum.inl (i,j))
  = xL i * (mk yl yr yL yR) + (mk xl xr xL xR) * yL j - xL i * yL j
:= rfl

@[simp] lemma mul_move_left_inl {x y : pgame.{u}} {i j} :
   (x * y).move_left ((@left_moves_mul x y).symm (sum.inl (i,j)))
   = x.move_left i * y + x * y.move_left j - x.move_left i * y.move_left j
:= by {cases x, cases y, refl} 

@[simp] lemma mk_mul_move_left_inr {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_left (sum.inr (i,j))
  = xR i * (mk yl yr yL yR) + (mk xl xr xL xR) * yR j - xR i * yR j
:= rfl

@[simp] lemma mul_move_left_inr {x y : pgame.{u}} {i j} :
   (x * y).move_left ((@left_moves_mul x y).symm (sum.inr (i,j)))
   = x.move_right i * y + x * y.move_right j - x.move_right i * y.move_right j
:= by {cases x, cases y, refl}

@[simp] lemma mk_mul_move_right_inl {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_right (sum.inl (i,j))
  = xL i * (mk yl yr yL yR) + (mk xl xr xL xR) * yR j - xL i * yR j
:= rfl

@[simp] lemma mul_move_right_inl {x y : pgame.{u}} {i j} :
   (x * y).move_right ((@right_moves_mul x y).symm (sum.inr (i, j)))
   = x.move_right i * y + x * y.move_left j - x.move_right i * y.move_left j
:= by {cases x, cases y, refl} 

@[simp] lemma mk_mul_move_right_inr {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_right (sum.inr (i,j))
  = xR i * (mk yl yr yL yR) + (mk xl xr xL xR) * yL j - xR i * yL j
:= rfl

@[simp] lemma mul_move_right_inr {x y : pgame.{u}} {i j} :
   (x * y).move_right ((@right_moves_mul x y).symm (sum.inr (i,j)))
   = x.move_right i * y + x * y.move_left j - x.move_right i * y.move_left j
:= by {cases x, cases y, refl}

/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
then `w + y` has the same moves as `x + z`. -/
def add_congr_relabelling : ∀ {w x y z : pgame.{u}},
w.relabelling x → y.relabelling z → (w + y).relabelling (x + z)
| (mk wl wr wL wR) (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR)
  ⟨L_equiv₁, R_equiv₁, L_relabelling₁, R_relabelling₁⟩
  ⟨L_equiv₂, R_equiv₂, L_relabelling₂, R_relabelling₂⟩ :=
begin
  refine ⟨equiv.sum_congr L_equiv₁ L_equiv₂, equiv.sum_congr R_equiv₁ R_equiv₂,_,_⟩,
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
and `c` has the same moves as `z`, then `a + b - c` has the same moves as `x + y - z`. -/
lemma add_sub_relabelling {a b c x y z : pgame.{u}}
  (h₁ : a.relabelling x) (h₂ : b.relabelling y) (h₃ : c.relabelling z) :
  (a + b - c).relabelling (x + y - z) := 
sub_congr_relabelling (add_congr_relabelling h₁ h₂) h₃
  
/-- If `a` has the same moves as `x`, `b` has the same moves as `y`,
and `c` has the same moves as `z`, then `a + b - c` has the same moves as `y + x - z`. -/
lemma add_comm_sub_relabelling {a b c x y z : pgame.{u}}
  (h₁ : a.relabelling x) (h₂ : b.relabelling y) (h₃ : c.relabelling z) :
  (a + b - c).relabelling (y + x - z) := 
sub_congr_relabelling
  (relabelling.trans (add_comm_relabelling a b) (add_congr_relabelling h₂ h₁)) h₃

/-- `x * y` has exactly the same moves as `y * x`. -/
theorem mul_comm_relabelling (x y : pgame.{u}) : (x * y).relabelling (y * x):=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  let x := mk xl xr xL xR,
  let y := mk yl yr yL yR,
  refine ⟨equiv.sum_congr (equiv.prod_comm _ _) (equiv.prod_comm _ _), _ ,_,_⟩,
  calc 
   (x * y).right_moves
       ≃ xl × yr ⊕ xr × yl : by refl
   ... ≃ xr × yl ⊕ xl × yr : equiv.sum_comm _ _
   ... ≃ yl × xr ⊕ yr × xl : equiv.sum_congr (equiv.prod_comm _ _) (equiv.prod_comm _ _)
   ... ≃ (y * x).right_moves : by refl,
  { rintro (⟨i, j⟩ | ⟨i, j⟩),
    { exact add_comm_sub_relabelling (IHxl i y) (IHyl j) (IHxl i (yL j)) },
    { exact add_comm_sub_relabelling (IHxr i y) (IHyr j) (IHxr i (yR j)) }},
  { rintro (⟨i, j⟩ | ⟨i, j⟩),
    { exact add_comm_sub_relabelling (IHxr j y) (IHyl i) (IHxr j (yL i)) },
    { exact add_comm_sub_relabelling (IHxl j y) (IHyr i) (IHxl j (yR i)) }}
end

/-- `x * y` is equivalent to `y * x`. -/
theorem mul_comm_equiv (x y : pgame) : (x * y).equiv (y * x) := 
equiv_of_relabelling (mul_comm_relabelling x y) 

/-- `x * 0` has exactly the same moves as `0`. -/
theorem mul_zero_relabelling : Π (x : pgame), relabelling (x * 0) 0
| (mk xl xr xL xR) :=
⟨by fsplit; rintro (⟨_,⟨⟩⟩ | ⟨_,⟨⟩⟩),
 by fsplit; rintro (⟨_,⟨⟩⟩ | ⟨_,⟨⟩⟩), 
 by rintro (⟨_,⟨⟩⟩ | ⟨_,⟨⟩⟩),
 by rintro ⟨⟩⟩

/-- `x * 0` is equivalent to `0`. -/
theorem mul_zero_equiv (x : pgame) : (x * 0).equiv 0 :=
equiv_of_relabelling (mul_zero_relabelling x)
   
/-- `0 * x` has exactly the same moves as `0`. -/
theorem zero_mul_relabelling : Π (x : pgame), relabelling (0 * x) 0
| (mk xl xr xL xR) :=
⟨by fsplit; rintro (⟨⟨⟩,_⟩ | ⟨⟨⟩,_⟩),
 by fsplit; rintro (⟨⟨⟩,_⟩ | ⟨⟨⟩,_⟩),
 by rintro (⟨⟨⟩,_⟩ | ⟨⟨⟩,_⟩),
 by rintro ⟨⟩⟩ 

/-- `0 * x` is equivalent to `0`. -/
theorem zero_mul_equiv (x : pgame) : (0 * x).equiv 0 :=
equiv_of_relabelling (zero_mul_relabelling x)

#check add_assoc_relabelling

/-- `(x + y) + z` has exactly the same moves as `x + (y + z)`. -/
def mul_assoc_relabelling : Π (x y z : pgame.{u}), relabelling ((x * y) * z) (x * (y * z))
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) :=
begin
  -- refine ⟨equiv.prod_assoc _ _ _, equiv.prod_assoc _ _ _, _, _⟩,
    refine ⟨_,_,_,_⟩,
    fsplit,
    rintros (⟨(⟨i,j⟩|⟨i,j⟩),k⟩|⟨(⟨i,j⟩|⟨i,j⟩),k⟩),
    exact sum.inl (i, sum.inl (j, k)),
    exact sum.inr (i, sum.inr (j, k)),
    exact sum.inl (i, sum.inr (j, k)),
    exact sum.inr (i, sum.inl (j, k)),
    
    rintros (⟨i, (⟨j,k⟩|⟨j,k⟩)⟩|⟨i,(⟨j,k⟩|⟨j,k⟩)⟩),
    exact sum.inl (sum.inl (i,j), k),
    exact sum.inr (sum.inl (i, j), k),
    exact sum.inr (sum.inr (i, j), k),
    exact sum.inl (sum.inr (i, j), k),

  {tidy},
  {tidy},

  fsplit,
  
    rintros (⟨(⟨i,j⟩|⟨i,j⟩),k⟩|⟨(⟨i,j⟩|⟨i,j⟩),k⟩),
    exact sum.inl (i, sum.inl (j, k)),
    exact sum.inr (i, sum.inr (j, k)),
    exact sum.inl (i, sum.inr (j, k)),
    exact sum.inr (i, sum.inl (j, k)),
    
    rintros (⟨i, (⟨j,k⟩|⟨j,k⟩)⟩|⟨i,(⟨j,k⟩|⟨j,k⟩)⟩),
    exact sum.inl (sum.inl (i, j), k),
    exact sum.inr (sum.inl (i, j), k),
    exact sum.inr (sum.inr (i, j), k),
    exact sum.inl (sum.inr (i, j), k),

  {tidy},
  {tidy},

    rintros (⟨(⟨i,j⟩|⟨i,j⟩),k⟩|⟨(⟨i,j⟩|⟨i,j⟩),k⟩),
    
  dsimp,
   -- have := mul_assoc_relabelling (xL i) (yL j) (zL k),
     

    -- calc
    --   (xl × yl ⊕ xr × yr) × zl ⊕ (xl × yr ⊕ xr × yl) × zr
    --     ≃ xl × (yl × zl ⊕ yr × zr) ⊕ xr × (yl × zr ⊕ yr × zl) : sorry,
end
-- instance : ring surreal := { add := _,
--   add_assoc := _,
--   zero := _,
--   zero_add := _,
--   add_zero := _,
--   neg := _,
--   sub := _,
--   sub_eq_add_neg := _,
--   add_left_neg := _,
--   add_comm := _,
--   mul := _,
--   mul_assoc := _,
--   one := _,
--   one_mul := _,
--   mul_one := _,
--   left_distrib := _,
--   right_distrib := _ }

end pgame

