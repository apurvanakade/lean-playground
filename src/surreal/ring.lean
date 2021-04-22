import set_theory.surreal 

namespace pgame


theorem mul_zero_relabelling : Π (x : pgame), relabelling (x * 0) 0
| (mk xl xr xL xR) :=
⟨by fsplit; rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩),
 by fsplit; rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩), 
 by rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩),
 by rintro ⟨⟩⟩
   
theorem zero_mul_relabelling : Π (x : pgame), relabelling (0 * x) 0
| (mk xl xr xL xR) :=
⟨by fsplit; rintro (⟨⟨⟩, _⟩ | ⟨⟨⟩, _⟩),
 by fsplit; rintro (⟨⟨⟩, _⟩ | ⟨⟨⟩, _⟩),
 by rintro (⟨⟨⟩,_⟩ | ⟨⟨⟩,_⟩),
 by rintro ⟨⟩⟩ 
 

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












