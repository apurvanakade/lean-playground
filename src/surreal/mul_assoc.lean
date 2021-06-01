import set_theory.surreal tactic.ring
import set_theory.game

open pgame
namespace pgame
universe u

local infix ` ≈ ` := pgame.equiv

def sub_congr {w x y z : pgame} 
  (h₁ : w ≈ x) (h₂ : y ≈ z) : (w - y) ≈ (x - z) :=
sorry

meta def try_inl_inr : tactic unit :=
`[assumption]
    <|> (do `[apply sum.inr], try_inl_inr )
    <|> (do `[apply sum.inl], try_inl_inr )
    <|> (do `[apply prod.mk], try_inl_inr, try_inl_inr )


lemma equiv_of_mk_equiv {x y : pgame} (L : x.left_moves ≃ y.left_moves) (R : x.right_moves ≃ y.right_moves)
         (hl : ∀ (i : x.left_moves), (x.move_left i).equiv (y.move_left (L i)))
         (hr : ∀ (j : y.right_moves), (x.move_right (R.symm j)).equiv (y.move_right j)) :
       x.equiv y :=
sorry
 
/-- `(x + y) * z` is equivalent to `x * z + y * z.`-/
theorem right_distrib_equiv (x y z : pgame) : (x + y) * z ≈ x * z + y * z :=
sorry

theorem left_distrib_equiv : Π (x y z : pgame), (x * (y + z)).equiv (x * y + x * z)
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) :=
sorry

set_option trace.solve_by_elim true

lemma aux'' {a b c d x y z c' : pgame} :
  (a + b - c) * z + x * y * c' - (a + b - c) * d
  ≈ a * z + b * z - c * z + x * y * c' - a * d + b * d + c * d :=
sorry
      
lemma aux' {a b c x y z : pgame} :
a * (y * z) + x * (b * z) - a * (b * z) + x * (y * c) - a * (y * c) + x * (b * c) + a * (b * c)
  ≈ a * (y * z) + x * (b * z + y * c - b * c) - a * (b * z + y * c - b * c)
:= sorry


theorem eq_of_mk_eq {x y : pgame}
  (L : x.left_moves ≃ y.left_moves) (R : x.right_moves ≃ y.right_moves)
  (hl : ∀ (i : x.left_moves), ⟦x.move_left i⟧ = ⟦y.move_left (L i)⟧)
  (hr : ∀ (j : y.right_moves), ⟦x.move_right (R.symm j)⟧ = ⟦y.move_right j⟧) :
  ⟦x⟧ = ⟦y⟧ := sorry
  
theorem left_distrib : Π (x y z : pgame), ⟦x * (y + z)⟧ = ⟦x * y⟧ + ⟦x * z⟧
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) :=
begin
  let x := mk xl xr xL xR,
  let y := mk yl yr yL yR,
  let z := mk zl zr zL zR,
  refine eq_of_mk_eq _ _ _ _,
  { fsplit,
    { rintros (⟨_,(_|_)⟩|⟨_,(_|_)⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 5 } },
    { rintros ((⟨_,_⟩|⟨_,_⟩)|(⟨_,_⟩|⟨_,_⟩));
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 5 } },
    { rintros (⟨_,(_|_)⟩|⟨_,(_|_)⟩); refl },
    { rintros ((⟨_,_⟩|⟨_,_⟩)|(⟨_,_⟩|⟨_,_⟩)); refl } },
  { fsplit,
    { rintros (⟨_,(_|_)⟩|⟨_,(_|_)⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 5 } },
    { rintros ((⟨_,_⟩|⟨_,_⟩)|(⟨_,_⟩|⟨_,_⟩));
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 5 } },
    { rintros (⟨_,(_|_)⟩|⟨_,(_|_)⟩); refl },
    { rintros ((⟨_,_⟩|⟨_,_⟩)|(⟨_,_⟩|⟨_,_⟩)); refl } },
    { rintros (⟨i,(j|k)⟩|⟨i,(j|k)⟩),
      { change ⟦xL i * (y + z) + x * (yL j + z) - xL i * (yL j + z)⟧
                = ⟦xL i * y + x * yL j - xL i * yL j + x * z⟧,
        simp[left_distrib], abel },
      { change ⟦xL i * (y + z) + x * (y + zL k) - xL i * (y + zL k)⟧
              = ⟦x * y + (xL i * z + x * zL k - xL i * zL k)⟧,
        simp[left_distrib], abel },
      { change ⟦xR i * (y + z) + x * (yR j + z) - xR i * (yR j + z)⟧
              = ⟦xR i * y + x * yR j - xR i * yR j + x * z⟧,
        simp[left_distrib], abel },
      { change ⟦xR i * (y + z) + x * (y + zR k) - xR i * (y + zR k)⟧
              = ⟦x * y + (xR i * z + x * zR k - xR i * zR k)⟧,
        simp[left_distrib], abel } },
    { rintros ((⟨i,j⟩|⟨i,j⟩)|(⟨i,k⟩|⟨i,k⟩)),
      { change ⟦xL i * (y + z) + x * (yR j + z) - xL i * (yR j + z)⟧
              = ⟦xL i * y + x * yR j - xL i * yR j + x * z⟧,
        simp[left_distrib], abel },
      { change ⟦xR i * (y + z) + x * (yL j + z) - xR i * (yL j + z)⟧
              = ⟦xR i * y + x * yL j - xR i * yL j + x * z⟧,
        simp[left_distrib], abel },
      { change ⟦xL i * (y + z) + x * (y + zR k) - xL i * (y + zR k)⟧
              = ⟦x * y + (xL i * z + x * zR k - xL i * zR k)⟧,
        simp[left_distrib], abel },
      { change ⟦xR i * (y + z) + x * (y + zL k) - xR i * (y + zL k)⟧
              = ⟦x * y + (xR i * z + x * zL k - xR i * zL k)⟧,
        simp[left_distrib], abel } }
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem mul_zero : Π (x : pgame), ⟦x * 0⟧ = ⟦0⟧ := sorry
theorem mul_one : Π (x : pgame), ⟦x * 1⟧ = ⟦x⟧ 
| (mk xl xr xL xR) :=
begin
  let x := mk xl xr xL xR,
  refine eq_of_mk_eq _ _ _ _,
  { fsplit,
     rintros (⟨_, ⟨ ⟩⟩ | ⟨_, ⟨ ⟩⟩), assumption,
     rintros i,  exact sum.inl(i, punit.star),
     rintros (⟨_, ⟨ ⟩⟩ | ⟨_, ⟨ ⟩⟩), refl,
     rintros i, refl,
  },
  { fsplit,
    rintros (⟨_, ⟨ ⟩⟩ | ⟨_, ⟨ ⟩⟩), assumption,
    rintros i,  exact sum.inr(i, punit.star), 
    rintros (⟨_, ⟨ ⟩⟩ | ⟨_, ⟨ ⟩⟩), refl,
    rintros i, refl,
  },
  rintros (⟨i, ⟨ ⟩⟩ | ⟨i, ⟨ ⟩⟩),
  change ⟦xL i * 1 + x * 0 - xL i * 0⟧ = ⟦xL i⟧,
  simp [mul_zero, mul_one],

  rintros j,
  change ⟦xR j * 1 + x * 0 - xR j * 0⟧ = ⟦xR j⟧,
  simp [mul_zero, mul_one],
end

#check left_distrib
theorem mul_assoc_equiv : Π (x y z : pgame), ((x * y) * z).equiv (x * (y * z))
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) :=
begin
  let x := mk xl xr xL xR,
  let y := mk yl yr yL yR,
  let z := mk zl zr zL zR,
  refine equiv_of_mk_equiv _ _ _ _,
  { fsplit,
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩); try_inl_inr },
    { rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_,⟨_, _⟩ | ⟨_, _⟩⟩); try_inl_inr },
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_,_⟩ | ⟨_, _⟩,_⟩); refl },
    { rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_,⟨_, _⟩ | ⟨_, _⟩⟩); refl } },
  { fsplit,
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩,_⟩); try_inl_inr },
    { rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_,⟨_, _⟩ | ⟨_, _⟩⟩); try_inl_inr },
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_,_⟩ | ⟨_, _⟩,_⟩); refl },
    { rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩); refl } },
  { rintro (⟨⟨i, j⟩ | ⟨i, j⟩, k⟩ | ⟨⟨i, j⟩ | ⟨i, j⟩, k⟩),
    { calc 
        (xL i * y + x * yL j - xL i * yL j) * z + (x * y) * zL k
          - (xL i * y + x * yL j - xL i * yL j) * zL k 
            ≈ (xL i * y) * z + (x * yL j) * z - (xL i * yL j) * z + (x * y) * zL k
                  - (xL i * y) * zL k + (x * yL j) * zL k + (xL i * yL j) * zL k
            : aux''
        ... ≈ xL i * (y * z) + x * (yL j * z) - xL i * (yL j * z) + x * (y * zL k)
                 - xL i * (y * zL k) + x * (yL j * zL k) + xL i * (yL j * zL k)
            : by { repeat { apply add_congr <|> apply neg_congr }; apply mul_assoc_equiv }
        ... ≈ xL i * (y * z) + x * (yL j * z + y * zL k - yL j * zL k)
                 - xL i * (yL j * z + y * zL k - yL j * zL k)
            : aux' },
     
        

    repeat {sorry}, },
  repeat {sorry},
end 

end pgame









