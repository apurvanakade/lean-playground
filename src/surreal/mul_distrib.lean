import surreal.mul_lemmas
import set_theory.surreal
import set_theory.pgame

open pgame
namespace pgame
universe u

meta def stupid_tactic : tactic unit :=
`[assumption]
    <|> (do `[apply sum.inr], stupid_tactic )
    <|> (do `[apply sum.inl], stupid_tactic )
    <|> (do `[apply prod.mk], stupid_tactic, stupid_tactic )

local infix ` ≈ ` := pgame.equiv

inductive weak_relabelling : pgame.{u} → pgame.{u} → Type (u+1)
| mk : Π {x y : pgame} (L : x.left_moves ≃ y.left_moves) (R : x.right_moves ≃ y.right_moves),
         (∀ (i : x.left_moves), (x.move_left i).equiv (y.move_left (L i))) →
         (∀ (j : y.right_moves), (x.move_right (R.symm j)).equiv (y.move_right j)) →
       weak_relabelling x y

theorem weak_relabelling.equiv {x y : pgame} (r : weak_relabelling x y) : x ≈ y :=
sorry

def left_distrib_relabelling : Π (x y z : pgame.{u}), (x * (y + z)).weak_relabelling (x * y + x * z)
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) :=
begin
  set x := mk xl xr xL xR with hx,
  set y := mk yl yr yL yR with hy,
  set z := mk zl zr zL zR with hz,
  refine ⟨_, _, _, _⟩,
  { fsplit,
    { rintros (⟨_,(_|_)⟩|⟨_,(_|_)⟩), repeat {stupid_tactic} },
    { rintros ((⟨_,_⟩|⟨_,_⟩)|(⟨_,_⟩|⟨_,_⟩)), repeat {stupid_tactic} },
    { rintros (⟨_,(_|_)⟩|⟨_,(_|_)⟩), repeat {refl} },
    { rintros ((⟨_,_⟩|⟨_,_⟩)|(⟨_,_⟩|⟨_,_⟩)), repeat {refl} }},
  { fsplit,
    { rintros (⟨_,(_|_)⟩|⟨_,(_|_)⟩), repeat {stupid_tactic} },
    { rintros ((⟨_,_⟩|⟨_,_⟩)|(⟨_,_⟩|⟨_,_⟩)), repeat {stupid_tactic} },
    { rintros (⟨_,(_|_)⟩|⟨_,(_|_)⟩), repeat {refl} },
    { rintros ((⟨_,_⟩|⟨_,_⟩)|(⟨_,_⟩|⟨_,_⟩)), repeat {refl} }},
  { rintros (⟨i,(j|k)⟩|⟨i,(j|k)⟩),
    dsimp,
    calc
      xL i * (y + z) + x * (yL j + z) - xL i * (yL j + z)
          ≈  (xL i * y + xL i * z) + (x * yL j + x * z) - (xL i * yL j + xL i * z) :
            by { refine equiv_of_relabelling (add_sub_congr _ _ _), repeat {exact (left_distrib_relabelling _ _ _).equiv} }
      ... ≈ xL i * y + x * yL j - xL i * yL j + x * z : sorry,

    calc
      xL i * (y + z) + x * (y + zL k) - xL i * (y + zL k)
        ≈  x * y + (xL i * z + x * zL k - xL i * zL k) : sorry,

    calc
      xR i * (y + z) + x * (yR j + z) - xR i * (yR j + z)
        ≈ xR i * y + x * yR j - xR i * yR j + x * z : sorry,
        
    calc
      xR i * (y + z) + x * (y + zR k) - xR i * (y + zR k)
        ≈ x * y + (xR i * z + x * zR k - xR i * zR k) : sorry,
    },
    {
      rintros ((⟨i,j⟩|⟨i,j⟩)|(⟨i,k⟩|⟨i,k⟩)),
      dsimp,
      calc
        xL i * (y + z) + x * (yR j + z) - xL i * (yR j + z)
          ≈ xL i * y + x * yR j - xL i * yR j + x * z : sorry,
            
      calc
        xR i * (y + z) + x * (yL j + z) - xR i * (yL j + z)
          ≈ xR i * y + x * yL j - xR i * yL j + x * z : sorry,

      calc
        xL i * (y + z) + x * (y + zR k) - xL i * (y + zR k)
          ≈  x * y + (xL i * z + x * zR k - xL i * zR k) : sorry,

      calc
        xR i * (y + z) + x * (y + zL k) - xR i * (y + zL k)
          ≈ x * y + (xR i * z + x * zL k - xR i * zL k) : sorry,
    },
end
using_well_founded { dec_tac := pgame_wf_tac }
end pgame

/-- The sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
-- def add (x y : pgame) : pgame :=
-- begin
--   induction x with xl xr xL xR IHxl IHxr generalizing y,
--   induction y with yl yr yL yR IHyl IHyr,
--   have y := mk yl yr yL yR,
--   refine ⟨xl ⊕ yl, xr ⊕ yr, sum.rec _ _, sum.rec _ _⟩,
--   { exact λ i, IHxl i y },
--   { exact λ i, IHyl i },
--   { exact λ i, IHxr i y },
--   { exact λ i, IHyr i }
-- 
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

