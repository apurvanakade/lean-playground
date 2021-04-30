import set_theory.surreal
open pgame
namespace pgame
universe u

/-- An explicit description of the moves for Left in `x * y`. -/
def left_moves_mul (x y : pgame) : (x * y).left_moves
  ≃ x.left_moves × y.left_moves ⊕ x.right_moves × y.right_moves :=
by { cases x, cases y, refl, }

/-- An explicit description of the moves for Right in `x * y`. -/
def right_moves_mul (x y : pgame) : (x * y).right_moves
  ≃ x.left_moves × y.right_moves ⊕ x.right_moves × y.left_moves :=
by { cases x, cases y, refl, }

@[simp] lemma mk_mul_move_left_inl {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_left (sum.inl (i, j))
  = xL i * (mk yl yr yL yR) + (mk xl xr xL xR) * yL j - xL i * yL j :=
 rfl

@[simp] lemma mul_move_left_inl {x y : pgame} {i j} :
   (x * y).move_left ((left_moves_mul x y).symm (sum.inl (i, j)))
   = x.move_left i * y + x * y.move_left j - x.move_left i * y.move_left j :=
by {cases x, cases y, refl}

@[simp] lemma mk_mul_move_left_inr {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_left (sum.inr (i, j))
  = xR i * (mk yl yr yL yR) + (mk xl xr xL xR) * yR j - xR i * yR j :=
rfl

@[simp] lemma mul_move_left_inr {x y : pgame} {i j} :
   (x * y).move_left ((left_moves_mul x y).symm (sum.inr (i, j)))
   = x.move_right i * y + x * y.move_right j - x.move_right i * y.move_right j :=
by {cases x, cases y, refl}

@[simp] lemma mk_mul_move_right_inl {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_right (sum.inl (i, j))
  = xL i * (mk yl yr yL yR) + (mk xl xr xL xR) * yR j - xL i * yR j :=
rfl

@[simp] lemma mul_move_right_inl {x y : pgame} {i j} :
   (x * y).move_right ((right_moves_mul x y).symm (sum.inl (i, j)))
   = x.move_left i * y + x * y.move_right j - x.move_left i * y.move_right j :=
by {cases x, cases y, refl}

@[simp] lemma mk_mul_move_right_inr {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_right (sum.inr (i,j))
  = xR i * (mk yl yr yL yR) + (mk xl xr xL xR) * yL j - xR i * yL j :=
rfl

@[simp] lemma mul_move_right_inr {x y : pgame} {i j} :
   (x * y).move_right ((right_moves_mul x y).symm (sum.inr (i, j)))
   = x.move_right i * y + x * y.move_left j - x.move_right i * y.move_left j :=
by {cases x, cases y, refl}

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
def sub_congr_relabelling {w x y z : pgame} 
  (h₁ : w.relabelling x) (h₂ : y.relabelling z) : (w - y).relabelling (x - z) :=
add_congr_relabelling h₁ (neg_congr_relabelling h₂)

/-- If `a` has the same moves as `x`, `b` has the same moves as `y`,
and `c` has the same moves as `z`, then `a + b - c` has the same moves as `x + y - z`.
This lemma is repeatedly used for simplifying multiplication of surreal numbers. -/
def add_sub_relabelling {a b c x y z : pgame}
  (h₁ : a.relabelling x) (h₂ : b.relabelling y) (h₃ : c.relabelling z) :
  (a + b - c).relabelling (x + y - z) :=
sub_congr_relabelling (add_congr_relabelling h₁ h₂) h₃

/-- If `a` has the same moves as `x`, `b` has the same moves as `y`,
and `c` has the same moves as `z`, then `a + b - c` has the same moves as `y + x - z`.
This lemma is repeatedly used for simplifying multiplication of surreal numbers. -/
def add_comm_sub_relabelling {a b c x y z : pgame}
  (h₁ : a.relabelling x) (h₂ : b.relabelling y) (h₃ : c.relabelling z) :
  (a + b - c).relabelling (y + x - z) :=
sub_congr_relabelling
  ((add_comm_relabelling a b).trans (add_congr_relabelling h₂ h₁)) h₃

def add_sub_congr {a b c x y z : pgame}
  (h₁ : a.equiv x) (h₂ : b.equiv y) (h₃ : c.equiv z) :
  (a + b - c).relabelling (x + y - z) :=
sorry
end pgame

#lint
