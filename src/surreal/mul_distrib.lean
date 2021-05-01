import set_theory.surreal
import set_theory.game tactic.abel

open pgame
namespace pgame
universe u

meta def stupid_tactic : tactic unit :=
`[assumption]
    <|> (do `[apply sum.inr], stupid_tactic )
    <|> (do `[apply sum.inl], stupid_tactic )
    <|> (do `[apply prod.mk], stupid_tactic, stupid_tactic )

lemma foo {x y : pgame} (L : x.left_moves ≃ y.left_moves) (R : x.right_moves ≃ y.right_moves)
         (hl : ∀ (i : x.left_moves), (x.move_left i).equiv (y.move_left (L i)))
         (hr : ∀ (j : y.right_moves), (x.move_right (R.symm j)).equiv (y.move_right j)) :
       x.equiv y :=
begin
  fsplit,
  { rw le_def, exact ⟨ λ i, or.inl ⟨L i, (hl i).1⟩, λ j, or.inr ⟨R.symm j, (hr j).1⟩⟩ },
  { rw le_def,
    fsplit,
    { intro i,
      left, 
      specialize hl (L.symm i),
      simp only [move_left_mk, equiv.apply_symm_apply] at hl,
      use ⟨L.symm i, hl.2 ⟩},
    { intro j,
      right, 
      specialize hr (R j),
      simp only [move_right_mk, equiv.symm_apply_apply] at hr,
      use ⟨R j, hr.2⟩ }}
end

local infix ` ≈ ` := pgame.equiv

lemma aux {a b c d e : pgame} : (a + b) + (c + d) - (e + b) ≈ a + c - e + d :=
begin
  apply @quotient.exact pgame,
  change (⟦a⟧ + ⟦b⟧ + (⟦c⟧ + ⟦d⟧) - (⟦e⟧ + ⟦b⟧) : game) = ⟦a⟧ + ⟦c⟧ + -⟦e⟧ + ⟦d⟧,
  abel,
end

lemma aux' {a b c d e : pgame} : (b + a) + (d + c) - (b + e) ≈ d + (a + c - e) :=
begin
  apply @quotient.exact pgame,
  change (⟦b⟧ + ⟦a⟧ + (⟦d⟧ + ⟦c⟧) - (⟦b⟧ + ⟦e⟧) : game) = ⟦d⟧ + (⟦a⟧ + ⟦c⟧ + -⟦e⟧),
  abel,
end

theorem left_distrib_equiv : Π (x y z : pgame), (x * (y + z)).equiv (x * y + x * z)
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) :=
begin
  let x := mk xl xr xL xR,
  let y := mk yl yr yL yR,
  let z := mk zl zr zL zR,
  refine foo _ _ _ _,
  { fsplit,
    { rintros (⟨_,(_|_)⟩|⟨_,(_|_)⟩), repeat {stupid_tactic}},
    { rintros ((⟨_,_⟩|⟨_,_⟩)|(⟨_,_⟩|⟨_,_⟩)), repeat {stupid_tactic} },
    { rintros (⟨_,(_|_)⟩|⟨_,(_|_)⟩), repeat {refl} },
    { rintros ((⟨_,_⟩|⟨_,_⟩)|(⟨_,_⟩|⟨_,_⟩)), repeat {refl} }},
  { fsplit,
    { rintros (⟨_,(_|_)⟩|⟨_,(_|_)⟩), repeat {stupid_tactic} },
    { rintros ((⟨_,_⟩|⟨_,_⟩)|(⟨_,_⟩|⟨_,_⟩)), repeat {stupid_tactic} },
    { rintros (⟨_,(_|_)⟩|⟨_,(_|_)⟩), repeat {refl} },
    { rintros ((⟨_,_⟩|⟨_,_⟩)|(⟨_,_⟩|⟨_,_⟩)), repeat {refl} }},
  { rintros (⟨i,(j|k)⟩|⟨i,(j|k)⟩),
    { calc
        xL i * (y + z) + x * (yL j + z) - xL i * (yL j + z)
            ≈  (xL i * y + xL i * z) + (x * yL j + x * z) - (xL i * yL j + xL i * z)
            : by { refine add_congr (add_congr _ _) (neg_congr _); apply left_distrib_equiv }
        ... ≈ xL i * y + x * yL j - xL i * yL j + x * z : aux },
    { calc
        xL i * (y + z) + x * (y + zL k) - xL i * (y + zL k)
            ≈ (xL i * y + xL i * z) + (x * y + x * zL k) - (xL i * y + xL i * zL k)
            : by { refine add_congr (add_congr _ _) (neg_congr _); apply left_distrib_equiv }
        ... ≈  x * y + (xL i * z + x * zL k - xL i * zL k) : aux' },
    { calc
        xR i * (y + z) + x * (yR j + z) - xR i * (yR j + z)
            ≈  (xR i * y + xR i * z) + (x * yR j + x * z) - (xR i * yR j + xR i * z)
            : by { refine add_congr (add_congr _ _) (neg_congr _); apply left_distrib_equiv }
        ... ≈ xR i * y + x * yR j - xR i * yR j + x * z : aux },
    { calc
        xR i * (y + z) + x * (y + zR k) - xR i * (y + zR k)
            ≈ (xR i * y + xR i * z) + (x * y + x * zR k) - (xR i * y + xR i * zR k)
            : by { refine add_congr (add_congr _ _) (neg_congr _); apply left_distrib_equiv }
        ... ≈ x * y + (xR i * z + x * zR k - xR i * zR k) : aux' } },
  { rintros ((⟨i,j⟩|⟨i,j⟩)|(⟨i,k⟩|⟨i,k⟩)),
    { calc
        xL i * (y + z) + x * (yR j + z) - xL i * (yR j + z)
            ≈  (xL i * y + xL i * z) + (x * yR j + x * z) - (xL i * yR j + xL i * z)
            : by { refine add_congr (add_congr _ _) (neg_congr _); apply left_distrib_equiv }
        ... ≈ xL i * y + x * yR j - xL i * yR j + x * z : aux },
    { calc
        xR i * (y + z) + x * (yL j + z) - xR i * (yL j + z)
            ≈  (xR i * y + xR i * z) + (x * yL j + x * z) - (xR i * yL j + xR i * z)
            : by { refine add_congr (add_congr _ _) (neg_congr _); apply left_distrib_equiv }
        ... ≈ xR i * y + x * yL j - xR i * yL j + x * z : aux },
    { calc
        xL i * (y + z) + x * (y + zR k) - xL i * (y + zR k)
            ≈ (xL i * y + xL i * z) + (x * y + x * zR k) - (xL i * y + xL i * zR k)
            : by { refine add_congr (add_congr _ _) (neg_congr _); apply left_distrib_equiv }
        ... ≈  x * y + (xL i * z + x * zR k - xL i * zR k) : aux' },
    { calc
        xR i * (y + z) + x * (y + zL k) - xR i * (y + zL k)
            ≈ (xR i * y + xR i * z) + (x * y + x * zL k) - (xR i * y + xR i * zL k)
            : by { refine add_congr (add_congr _ _) (neg_congr _); apply left_distrib_equiv }
        ... ≈ x * y + (xR i * z + x * zL k - xR i * zL k) : aux' } }
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem right_distrib_equiv (x y z : pgame) : ((x + y) * z).equiv (x * z + y * z) :=
calc (x + y) * z ≈ z * (x + y) : mul_comm_equiv _ _
             ... ≈ z * x + z * y : left_distrib_equiv _ _ _
             ... ≈ (x * z + y * z) : add_congr (mul_comm_equiv _ _) (mul_comm_equiv _ _)

end pgame

