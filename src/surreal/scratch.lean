import set_theory.surreal

namespace pgame 
open pgame

-- some lemmas first 
theorem numeric_sub {x y : pgame} (ox : numeric x) (oy : numeric y) : numeric (x - y) :=
numeric_add ox (numeric_neg oy)

theorem zero_le₁ {x : pgame} : 0 ≤ x ↔
  (∀ j : x.right_moves, 0 < x.move_right j) :=
by { rw le_def_lt, exact ⟨λ ⟨hl, hr⟩ j, hr j, λ hr, ⟨by rintro ⟨ ⟩, hr⟩⟩ }

theorem le_zero₁ {x : pgame} : x ≤ 0 ↔
  (∀ i : x.left_moves, x.move_left i < 0) :=
by { rw le_def_lt, exact ⟨λ ⟨hl, hr⟩ i, hl i, λ hl, ⟨hl, by rintro ⟨ ⟩⟩⟩ }

theorem zero_lt₁ {x : pgame} : 0 < x ↔
  (∃ i : x.left_moves, 0 ≤ x.move_left i) :=
by {rw lt_def_le, dsimp, simp[forall_pempty] }

theorem lt_zero₁ {x : pgame} : x < 0 ↔
  (∃ j : x.right_moves, x.move_right j ≤ 0) :=
by {rw lt_def_le, dsimp, simp[forall_pempty] }

-- missing trans rules for pgames
@[trans] theorem lt_of_lt_of_equiv' {x y z : pgame} (h₁ : x < y) (h₂ : y ≈ z) : x < z := lt_of_lt_of_le h₁ h₂.1
@[trans] theorem le_of_le_of_equiv' {x y z : pgame} (h₁ : x ≤ y) (h₂ : y ≈ z) : x ≤ z := le_trans h₁ h₂.1
@[trans] theorem lt_of_equiv_of_lt' {x y z : pgame} (h₁ : x ≈ y) (h₂ : y < z) : x < z := lt_of_le_of_lt h₁.1 h₂
@[trans] theorem le_of_equiv_of_le' {x y z : pgame} (h₁ : x ≈ y) (h₂ : y ≤ z) : x ≤ z := le_trans h₁.1 h₂

--problem will well-founded recursion :(

set_option trace.solve_by_elim true

theorem foobar : Π {x y : pgame},
(x.numeric → y.numeric → 0 < x → 0 < y → 0 < x * y) ∧
(x.numeric → y.numeric → 0 ≤ x → 0 ≤ y → 0 ≤ x * y)
| (mk xl xr xL xR) (mk yl yr yL yR) :=
begin
  let x := mk xl xr xL xR,
  let y := mk yl yr yL yR,
  split,
  { intros ox oy pos_x pos_y,
    have nonneg_x : 0 ≤ x, from le_of_lt numeric_zero ox pos_x,
    have nonneg_y : 0 ≤ y, from le_of_lt numeric_zero oy pos_y,
    obtain ⟨i, hi⟩ := zero_lt₁.1 pos_x,
    obtain ⟨j, hj⟩ := zero_lt₁.1 pos_y,
    rw zero_lt₁,
    use sum.inl (i, j),
    calc 0 ≤ yL j * (x - xL i)
           : foobar.2 (oy.2.1 j) (numeric_sub ox (ox.2.1 i))
            hj ((@le_iff_sub_nonneg (xL i) x).1 (le_of_lt (ox.2.1 i) ox (ox.move_left_lt i)))
       ... ≈ (x - xL i) * yL j
           : mul_comm_equiv _ _
       ... ≈ 0 + (x - xL i) * yL j
           : (zero_add_equiv _).symm
       ... ≤ xL i * y + (x - xL i) * yL j
           : add_le_add_right $ foobar.2 (ox.2.1 i) oy hi nonneg_y
       ... ≈ xL i * y + x * yL j - xL i * yL j
           : by { apply @quotient.exact pgame, simp, abel } },
  { intros ox oy nonneg_x nonneg_y,
    have hx' := zero_le₁.1 nonneg_x, dsimp at hx',
    have hy' := zero_le₁.1 nonneg_y, dsimp at hy',
    rw zero_le₁,
    rintros (⟨i, j⟩ | ⟨i, j⟩),
    { by_cases h : 0 ≤ xL i,
      { calc 0 ≤ xL i * y : foobar.2 (ox.2.1 i) oy h nonneg_y
      ... ≈ xL i * y + 0 : (add_zero_equiv _).symm
      ... < xL i * y + (x - xL i) * yR j
          : add_lt_add_left $ foobar.1 (numeric_sub ox (ox.2.1 i)) (oy.2.2 j)
                                (lt_iff_sub_pos.1 (ox.move_left_lt i)) (hy' j)
      ... ≈ xL i * y + x * yR j - xL i * yR j
          : by { apply @quotient.exact pgame, simp, abel } },
      { rw not_le at h,
        calc 0  ≤ x * yR j
                : foobar.2 ox (oy.2.2 j) nonneg_x (le_of_lt numeric_zero (oy.2.2 j) (hy' j))
          ... ≈ x * yR j + 0 : (add_zero_equiv _).symm
          ... < x * yR j + (-xL i) * (yR j - y)
                : by {refine add_lt_add_left (foobar.1 (numeric_neg (ox.2.1 i))
                                       (numeric_sub (oy.2.2 j) oy)
                                       _ _), 
                                       -- (lt_iff_sub_pos.1 h)
                                       -- (lt_iff_sub_pos.1 (oy.-- lt_move_right j)
                                       have : (0:pgame) = -(0:pgame), by simp, rw this,
                          rw ←lt_iff_neg_gt, exact h,
                          rw ←lt_iff_sub_pos, exact oy.lt_move_right j,
                                       }
          ... ≈ xL i * y + x * yR j - xL i * yR j
              : by { apply @quotient.exact pgame, simp, abel } } },
  {
    by_cases h : 0 ≤ yL j,
    {calc 0 < xR i * (y - yL j)
            : foobar.1 (ox.2.2 i) (numeric_sub oy (oy.2.1 j)) (hx' i) (lt_iff_sub_pos.1 (oy.move_left_lt j))
     ... ≈ 0 + xR i * (y - yL j) : (zero_add_equiv _).symm
     ... ≤ x * yL j + xR i * (y - yL j)
         : add_le_add_right $ foobar.2 ox (oy.2.1 j) nonneg_x h
     ... ≈ xR i * y + x * yL j - xR i * yL j : by { apply @quotient.exact pgame, simp, abel } },
    {rw not_le at h,
    calc 0
         < (xR i - x) * (-yL j)
         : by {refine foobar.1 (numeric_sub (ox.2.2 i) ox) (numeric_neg (oy.2.1 j))
           (lt_iff_sub_pos.1 (ox.lt_move_right i)) _,
           have : (0:pgame) = -(0:pgame), by simp, rw this,
           rw ←lt_iff_neg_gt, exact h }
      ... ≈ 0 + (xR i - x) * (-yL j)
          : (zero_add_equiv _).symm
      ... ≤ xR i * y + (xR i - x) * (-yL j)
          : add_le_add_right $ foobar.2 (ox.2.2 i) oy
                                  (le_of_lt numeric_zero (ox.2.2 i) (hx' i)) nonneg_y
      ... ≈ xR i * y + x * yL j - xR i * yL j : by { apply @quotient.exact pgame, simp, abel } } } },
end
using_well_founded { dec_tac := pgame_wf_tac }

end pgame
