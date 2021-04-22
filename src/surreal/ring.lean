import set_theory.surreal 

namespace pgame

theorem mul_zero_relabelling : Π (x : pgame), relabelling (x * 0) 0
| (mk xl xr xL xR) :=
⟨ 
by fsplit; rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩),
by fsplit; rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩), 
by rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩),
by rintro ⟨⟩
⟩
   
theorem zero_mul_relabelling : Π (x : pgame), relabelling (0 * x) 0
| (mk xl xr xL xR) :=
⟨
by fsplit; rintro (⟨⟨⟩, _⟩ | ⟨⟨⟩, _⟩),
by fsplit; rintro (⟨⟨⟩, _⟩ | ⟨⟨⟩, _⟩),
by rintro (⟨⟨⟩,_⟩ | ⟨⟨⟩,_⟩),
by rintro ⟨⟩
⟩ 
   

theorem mul_one_relabelling : Π (x : pgame), relabelling (x * (1:pgame)) x
| (mk xl xr xL xR) :=
begin 
refine ⟨_,_,_,_⟩,
 
repeat {sorry},
end


end pgame












