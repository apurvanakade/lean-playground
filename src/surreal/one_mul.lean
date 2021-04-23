import set_theory.surreal 
open pgame
namespace pgame

theorem mul_one_relabelling (x : pgame) : relabelling (x * (1:pgame)) x :=
begin 
  induction x with xl xr xL xR IHxl IHxr,
refine ⟨_,_,_,_⟩,
 {fsplit,
  rintro (⟨a, ⟨⟩⟩ | ⟨a, ⟨⟩⟩),
  use a,  
  swap,
  rintros (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩), 
   dsimp at *, refl ,  
   intros x, refl,
  },

{
  fsplit,
  rintro (⟨a, ⟨⟩⟩ | ⟨a, ⟨⟩⟩),
  use a,
  intros a, swap,
  { intros x, cases x,
    {
      cases x, cases x_snd,
    },
    cases x,
    cases x_snd, dsimp at *, refl,
  },
  intros x, refl,
},
dsimp at *,
rintro (⟨a, ⟨⟩⟩ | ⟨a, ⟨⟩⟩),
fsplit; dsimp at *,
specialize IHxl a,
{ },
{ fsplit, rintro b,
},
repeat {sorry},
end 


end pgame












