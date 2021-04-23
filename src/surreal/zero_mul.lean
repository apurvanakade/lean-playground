import set_theory.surreal 
open pgame
namespace pgame


/-- `x * 0` has exactly the same moves as `0`. -/
theorem mul_zero_relabelling : Π (x : pgame), relabelling (x * 0) 0
| (mk xl xr xL xR) :=
⟨by fsplit; rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩),
 by fsplit; rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩), 
 by rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩),
 by rintro ⟨⟩⟩

/-- `x * 0` is equivalent to `0`. -/
lemma mul_zero_equiv (x : pgame) : (x * 0).equiv 0 :=
equiv_of_relabelling (mul_zero_relabelling x)
   
/-- `0 * x` has exactly the same moves as `0`. -/
theorem zero_mul_relabelling : Π (x : pgame), relabelling (0 * x) 0
| (mk xl xr xL xR) :=
⟨by fsplit; rintro (⟨⟨⟩, _⟩ | ⟨⟨⟩, _⟩),
 by fsplit; rintro (⟨⟨⟩, _⟩ | ⟨⟨⟩, _⟩),
 by rintro (⟨⟨⟩,_⟩ | ⟨⟨⟩,_⟩),
 by rintro ⟨⟩⟩ 
 

/-- `0 * x` is equivalent to `0`. -/
lemma zero_mul_equiv (x : pgame) : (0 * x).equiv 0 :=
equiv_of_relabelling (zero_mul_relabelling x)



end pgame












