import set_theory.surreal 

namespace pgame

def mul_zero_relabelling :
  Π (x : pgame), relabelling (x * 0) 0
  := by {rintros ⟨⟩, tidy}
   
def zero_mul_relabelling :
  Π (x : pgame), relabelling (0 * x) 0
  := by {rintros ⟨⟩, tidy}
   
end pgame













