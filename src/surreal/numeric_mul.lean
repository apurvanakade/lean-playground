import set_theory.surreal

open pgame

universe u

local infix ` ≈ ` := pgame.equiv

#check numeric
-- def numeric : pgame → Prop
-- | ⟨l, r, L, R⟩ :=
--   (∀ i j, L i < R j) ∧ (∀ i, numeric (L i)) ∧ (∀ i, numeric (R i))

lemma numeric_aux (x : pgame) :
  (∀ i, x.move_left i < x ∧ numeric (x.move_left i)) ∧
  (∀ i, x < x.move_right i ∧ numeric (x.move_right i)) → x.numeric := sorry


#check @le_def_lt
-- ⊢ ∀ {x y : pgame},
--     x ≤ y ↔
--     ∀ (i : x.left_moves), x.move_left i < y ∧
--     ∀ (j : y.right_moves), x < y.move_right j

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

-- theorem le_def_lt {x y : pgame} : x ≤ y ↔
--   (∀ i : x.left_moves, x.move_left i < y) ∧
--   (∀ j : y.right_moves, x < y.move_right j) :=
-- by { cases x, cases y, refl }

theorem le_zero' {x : pgame} : x ≤ 0 ↔ 
  (∀ i : x.left_moves, x.move_left i < 0) :=
begin
  rw le_def_lt,
  split,
  rintros ⟨hi,hj⟩ i,
  exact hi i,
  rintros hj,
  split,
  exact hj,
  rintros ⟨⟩,
end

theorem zero_lt' {x : pgame} : 0 < x ↔ 
  (∃ i : x.left_moves, 0 ≤ x.move_left i) :=
by {rw lt_def_le, dsimp, simp[forall_pempty] }
-- (xL i < (mk xl xr xL xR)) ∧ ((mk xl xr xL xR) < xR j) ∧ numeric (xL i) ∧ numeric (xR j) → (mk xl xr xL xR).numeric := sorry

example ( a b : ℤ ) : (0 < a) → (0 < b) → (0 < a * b) :=
begin
  exact mul_pos,
end

theorem foo (x : pgame) (ox : numeric x) : ¬ (x ≈ 0) → (0 < x) ∨ (x < 0) := sorry

theorem numeric_mul_pos : Π {x y z w : pgame} (ox : numeric x) (oy : numeric y) (oz : numeric z) (ow : numeric w),
(0 < x → 0 < y → 0 < x * y) ∧
(w ≈ 0 → w * z ≈ 0)
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) (mk wl wr wL wR) ox oy oz ow :=
begin
  set x := mk xl xr xL xR with hx,
  set y := mk yl yr yL yR with hy,
  set w := mk wl wr wL wR with hw,
  split,
  intros pos_x pos_y,
  rw zero_lt',
  cases zero_lt'.1 pos_x with i hi,
  cases zero_lt'.1 pos_y with j hj,
  dsimp at *,
  use sum.inl (i,j),
  dsimp,
  rw ←hx at *,
  rw ←hy at *,
  by_cases h : xL i ≈ 0,
  sorry,
  cases foo (xL i) (ox.2.1 i) h,
  sorry,
  sorry,

  intro hw,
  split,
  rw le_zero',
  rintros (⟨i,j⟩|⟨i,j⟩),
  dsimp,
  rw ←hx at *, 
sorry,
dsimp,
sorry,
rw zero_le',
  rintros (⟨i,j⟩|⟨i,j⟩),
  dsimp,
  sorry,
  dsimp,
  sorry,

  
  

end

theorem numeric_mul_pos' : Π {x y : pgame} (ox : numeric x) (oy : numeric y) (oxy : numeric (x * y)) (neg_x : x < 0) (neg_y : y < 0), 0 < x * y := sorry

theorem numeric_mul_neg : Π {x y : pgame} (ox : numeric x) (oy : numeric y) (oxy : numeric (x * y)) (pos_x : 0 < x) (neg_y : y < 0), x * y < 0 := sorry

theorem numeric_sub : Π {x y : pgame} (ox : numeric x) (oy : numeric y), numeric (x - y)
| ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ ox oy := sorry


theorem numeric_mul : Π {x y z : pgame} (ox : x.numeric) (oy : y.numeric), 
((x * y).numeric ) ∧
((x ≈ y) → ⟦x * z⟧ = ⟦y * z⟧) ∧
(Π {a b A B : pgame} (oA : numeric A) (oB : numeric B) (oa : numeric a) (ob : numeric b), a < A → b < B → a * B + b * A < a * b + A * B )
| (mk xl xr xL xR) (mk yl yr yL yR) 
:=
begin
    set x := mk xl xr xL xR with hx,
    set y := mk yl yr yL yR with hy,
  split,
  {
    intros ox oy,
      fsplit,
      rintro (⟨i, j⟩ | ⟨i, j⟩) (⟨k, l⟩ | ⟨j_fst, j_snd⟩),
      {
        change xL i * y + x * yL j - xL i * yL j < xL k * y + x * yR l - xL k * yR l,
      }, sorry, sorry, sorry, sorry,
  },

  
end 
