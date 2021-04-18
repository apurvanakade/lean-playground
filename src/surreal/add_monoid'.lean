import set_theory.surreal
open surreal 
namespace surreal

section

-- otherwise the elaborator gets in our way
local attribute [elab_with_expected_type] quotient.ind

instance : add_monoid surreal :=
{ add := add,
  add_assoc := add_assoc,
  zero := 0,
  zero_add := quotient.ind $ λ a, quotient.sound $ pgame.zero_add_equiv _,
  add_zero := quotient.ind $ λ a, quotient.sound $ pgame.add_zero_equiv _ }

end

end surreal
