import set_theory.surreal

namespace pgame
open pgame 

@[trans] theorem lt_trans {x y z : pgame} : x < y → y < z → x < z :=
sorry

theorem numeric_sub : Π {x y : pgame} (ox : numeric x) (oy : numeric y), numeric (x - y) := sorry


def foobar : Π {x y : pgame} (ox : numeric x) (oy : numeric y), numeric (x * y) 
| (mk xl xr xL xR) (mk yl yr yL yR) ox oy:=
begin 
  let x := mk xl xr xL xR,
  let y := mk yl yr yL yR,
  refine ⟨_,_,_⟩,
  { 
  intros i j,
  suffices : ((x * y).move_left i < x * y) ∧ (x * y < (x * y).move_right j),
  apply pgame.lt_trans this.1 this.2,
  split, 
  rcases i with ⟨i₁,i₂⟩,
  rcases j with ⟨j₁,j₂⟩,
  repeat {sorry},
   },
   
  rintro (⟨i_fst, i_snd⟩ | ⟨i_fst, i_snd⟩),

  refine numeric_sub (numeric_add _ _) _,
  apply foobar (ox.2.1 i_fst) oy,
  apply foobar ox (oy.2.1 i_snd),
  apply foobar (ox.2.1 i_fst) (oy.2.1 i_snd),

  refine numeric_sub (numeric_add _ _) _,
  apply foobar (ox.2.2 i_fst) oy,
  apply foobar ox (oy.2.2 i_snd),
  apply foobar (ox.2.2 i_fst) (oy.2.2 i_snd),

  rintro (⟨i_fst, i_snd⟩ | ⟨i_fst, i_snd⟩),
  
  refine numeric_sub (numeric_add _ _) _,
  apply foobar (ox.2.1 i_fst) oy,
  apply foobar ox (oy.2.2 i_snd),
  apply foobar (ox.2.1 i_fst) (oy.2.2 i_snd),

  refine numeric_sub (numeric_add _ _) _,
  apply foobar (ox.2.2 i_fst) oy,
  apply foobar ox (oy.2.1 i_snd),
  apply foobar (ox.2.2 i_fst) (oy.2.1 i_snd),
end 
using_well_founded { dec_tac := pgame_wf_tac }


end pgame