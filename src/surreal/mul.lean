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

#check @punit.rec
example (x y : Type) (a b : x) (f : x → y) : a = b → f a = f b :=
by {intros, exact congr_arg f ᾰ}

example
  (xl xr : Type)
  (xL : xl → pgame)
  (xR : xr → pgame)
  (i : xl) :
  ((mk xl xr xL xR * 1).move_left (sum.inl (i, punit.star))).relabelling
    (xL i) :=
begin
  sorry, 
end
  

def mul_one_relabelling : Π (x : pgame), relabelling (x * 1) x
| (mk xl xr xL xR) :=
begin 
  fsplit,
  fsplit, 
  rintro (⟨i, ⟨⟩⟩ | ⟨j, ⟨⟩⟩),
  dsimp, exact i,

  rintro i,
  exact sum.inl (i, punit.star), 
  
  rintros ⟨i, ⟨⟩⟩, 
  refl,

  rcases x with ⟨x, ⟨⟩⟩,
  intros x, refl,

  fsplit,
  rintro (⟨i, ⟨⟩⟩ | ⟨i, ⟨⟩⟩),
  exact i,

  exact λ i, sum.inr (i, punit.star),

  rintros (⟨i, ⟨⟩⟩| ⟨i, ⟨⟩⟩), 
  refl,

  dsimp,
  rintros x, refl,

  rintros (⟨i, ⟨⟩⟩|⟨i, ⟨⟩⟩),
  dsimp,
  /-

  
  -/
  
  extract_goal,
  sorry,
  rintros i, dsimp at i,
  dsimp,
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

local infix ` ~ ` := pgame.relabelling

theorem add_congr_relabelling {w x y z : pgame} 
  (h₁ : w ~ x) (h₂ : y ~ z) : w + y ~ x + z :=
begin 
  sorry,
end 
#check pgame.neg
theorem neg_congr_relabelling {x y : pgame} 
  (h₁ : x ~ y) : -x ~ -y :=
begin
  
  cases h₁ with _ _ hl hr hL hR,
  fsplit, 
  dsimp [has_neg.neg, neg] at *,
  exact hr,
  
  sorry,
end

theorem sub_congr_relabelling {w x y z : pgame} 
  (h₁ : w ~ x) (h₂ : y ~ z) : w - y ~ x - z :=
add_congr_relabelling h₁ (neg_congr_relabelling h₂)

lemma add_neg_comm {a b c x y z : pgame} : (a ~ x) → (b ~ y) → (c ~ z) → (a + b - c ~ y + x - z) := 
begin 
  intros h1 h2 h3,
  suffices : a + b ~ y + x, by exact sub_congr_relabelling this h3,
  calc 
    a + b 
        ~ a + y : add_congr_relabelling (relabelling.refl a) h2
    ... ~ x + y : add_congr_relabelling h1 (relabelling.refl y)
    ... ~ y + x : add_comm_relabelling x y
end

def mul_comm_relabelling' (x y : pgame) : relabelling (x * y) (y * x):=
begin
  induction x with xl xr xL xR I1 I2 generalizing y,
  induction y with yl yr yL yR J1 J2,

  let x := mk xl xr xL xR,
  let y := mk yl yr yL yR,

  refine ⟨_,_,_,_⟩,

  { fsplit; rintro (⟨i, j⟩ | ⟨i, j⟩); 
    exact sum.inl (j,i) <|> exact sum.inr (j,i) <|> refl },

  { fsplit; rintro (⟨i, j⟩ | ⟨i, j⟩); 
    exact sum.inl (j,i) <|> exact sum.inr (j,i) <|> refl },

  { rintro (⟨i, j⟩ | ⟨i, j⟩),
    { exact add_neg_comm (I1 i y) (J1 j) (I1 i (yL j)) },
    { exact add_neg_comm (I2 i y) (J2 j) (I2 i (yR j)) }},

  { rintro (⟨i, j⟩ | ⟨i, j⟩),
    { exact add_neg_comm (I2 j y) (J1 i) (I2 j (yL i)) },
    { exact add_neg_comm (I1 j y) (J2 i) (I1 j (yR i)) }}
end

-- `x*y` has exactly the same moves as `y*x`.
def mul_comm_relabelling : Π (x y : pgame), relabelling (x * y) (y * x) :=
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

/-- The product of `x = {xL | xR}` and `y = {yL | yR}` is
`{xL*y + x*yL - xL*yL, xR*y + x*yR - xR*yR | xL*y + x*yR - xL*yR, x*yL + xR*y - xR*yL }`. -/
-- def mul (x y : pgame) : pgame :=
-- begin
--   induction x with xl xr xL xR IHxl IHxr generalizing y,
--   induction y with yl yr yL yR IHyl IHyr,
--   have y := mk yl yr yL yR,
--   refine ⟨xl × yl ⊕ xr × yr, xl × yr ⊕ xr × yl, _, _⟩; rintro (⟨i, j⟩ | ⟨i, j⟩),
--   { exact IHxl i y + IHyl j - IHxl i (yL j) },
--   { exact IHxr i y + IHyr j - IHxr i (yR j) },
--   { exact IHxl i y + IHyr j - IHxl i (yR j) },
--   { exact IHxr i y + IHyl j - IHxr i (yL j) }
-- end
-- 

/-- `x+y` has exactly the same moves as `y+x`. -/
-- def add_comm_relabelling : Π (x y : pgame.{u}), relabelling (x + y) (y + x)
-- | (mk xl xr xL xR) (mk yl yr yL yR) :=
-- begin
--   refine ⟨equiv.sum_comm _ _, equiv.sum_comm _ _, _, _⟩;
--   rintros (_|_);
--   { simp [left_moves_add, right_moves_add], apply add_comm_relabelling }
-- end
-- using_well_founded { dec_tac := pgame_wf_tac }

-- theorem add_comm_le {x y : pgame} : x + y ≤ y + x :=
-- le_of_relabelling (add_comm_relabelling x y)

-- theorem add_comm_equiv {x y : pgame} : x + y ≈ y + x :=
-- equiv_of_relabelling (add_comm_relabelling x y)

-- /-- `(x + y) + z` has exactly the same moves as `x + (y + z)`. -/
-- def add_assoc_relabelling : Π (x y z : pgame.{u}), relabelling ((x + y) + z) (x + (y + z))
-- | (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) :=
-- begin
--   refine ⟨equiv.sum_assoc _ _ _, equiv.sum_assoc _ _ _, _, _⟩,
--   { rintro (⟨i|i⟩|i),
--     { apply add_assoc_relabelling, },
--     { change relabelling
--         (mk xl xr xL xR + yL i + mk zl zr zL zR) (mk xl xr xL xR + (yL i + mk zl zr zL zR)),
--       apply add_assoc_relabelling, },
--     { change relabelling
--         (mk xl xr xL xR + mk yl yr yL yR + zL i) (mk xl xr xL xR + (mk yl yr yL yR + zL i)),
--       apply add_assoc_relabelling, } },
--   { rintro (j|⟨j|j⟩),
--     { apply add_assoc_relabelling, },
--     { change relabelling
--         (mk xl xr xL xR + yR j + mk zl zr zL zR) (mk xl xr xL xR + (yR j + mk zl zr zL zR)),
--       apply add_assoc_relabelling, },
--     { change relabelling
--         (mk xl xr xL xR + mk yl yr yL yR + zR j) (mk xl xr xL xR + (mk yl yr yL yR + zR j)),
--       apply add_assoc_relabelling, } },
-- end
-- using_well_founded { dec_tac := pgame_wf_tac }

-- theorem add_assoc_equiv {x y z : pgame} : (x + y) + z ≈ x + (y + z) :=
-- equiv_of_relabelling (add_assoc_relabelling x y z)

-- theorem add_le_add_right : Π {x y z : pgame} (h : x ≤ y), x + z ≤ y + z
-- | (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) :=
-- begin
--   intros h,
--   rw le_def,
--   split,
--   { -- if Left plays first
--     intros i,
--     change xl ⊕ zl at i,
--     cases i,
--     { -- either they play in x
--       rw le_def at h,
--       cases h,
--       have t := h_left i,
--       rcases t with ⟨i', ih⟩ | ⟨j, jh⟩,
--       { left,
--         refine ⟨(left_moves_add _ _).inv_fun (sum.inl i'), _⟩,
--         exact add_le_add_right ih, },
--       { right,
--         refine ⟨(right_moves_add _ _).inv_fun (sum.inl j), _⟩,
--         convert add_le_add_right jh,
--         apply add_move_right_inl },
--       },
--     { -- or play in z
--       left,
--       refine ⟨(left_moves_add _ _).inv_fun (sum.inr i), _⟩,
--       exact add_le_add_right h, }, },
--   { -- if Right plays first
--     intros j,
--     change yr ⊕ zr at j,
--     cases j,
--     { -- either they play in y
--       rw le_def at h,
--       cases h,
--       have t := h_right j,
--       rcases t with ⟨i, ih⟩ | ⟨j', jh⟩,
--       { left,
--         refine ⟨(left_moves_add _ _).inv_fun (sum.inl i), _⟩,
--         convert add_le_add_right ih,
--         apply add_move_left_inl },
--       { right,
--         refine ⟨(right_moves_add _ _).inv_fun (sum.inl j'), _⟩,
--         exact add_le_add_right jh } },
--     { -- or play in z
--       right,
--       refine ⟨(right_moves_add _ _).inv_fun (sum.inr j), _⟩,
--       exact add_le_add_right h } }
-- end
-- using_well_founded { dec_tac := pgame_wf_tac }

-- theorem add_le_add_left {x y z : pgame} (h : y ≤ z) : x + y ≤ x + z :=
-- calc x + y ≤ y + x : add_comm_le
--      ... ≤ z + x : add_le_add_right h
--      ... ≤ x + z : add_comm_le

-- theorem add_congr {w x y z : pgame} (h₁ : w ≈ x) (h₂ : y ≈ z) : w + y ≈ x + z :=
-- ⟨calc w + y ≤ w + z : add_le_add_left h₂.1
--         ... ≤ x + z : add_le_add_right h₁.1,
--  calc x + z ≤ x + y : add_le_add_left h₂.2
--         ... ≤ w + y : add_le_add_right h₁.2⟩
