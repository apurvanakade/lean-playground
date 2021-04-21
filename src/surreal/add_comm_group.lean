import set_theory.surreal
-- set_option pp.notation false
namespace surreal

#check @pgame.add_comm_equiv

def neg : surreal → surreal :=
surreal.lift (λ x ox, ⟦⟨-x, pgame.numeric_neg ox⟩⟧) (λ _ _ _ _ a, quotient.sound (pgame.neg_congr a))

instance : add_comm_group surreal :=
{ add             := surreal.add,
  add_assoc       := surreal.add_assoc,
  zero            := 0,
  zero_add        := by { rintros ⟨x, ox⟩, exact quotient.sound (pgame.zero_add_equiv _) },
  add_zero        := by { rintros ⟨x, ox⟩, exact quotient.sound (pgame.add_zero_equiv _) }, 
  neg             := surreal.neg,
  sub             := λ a b, a + surreal.neg b,
  sub_eq_add_neg  := by try_refl_tac,
  add_left_neg    := by { rintros ⟨x, ox⟩, exact quotient.sound pgame.add_left_neg_equiv }, 
  add_comm        := by { rintros ⟨x, ox⟩ ⟨y, oy⟩, exact quotient.sound pgame.add_comm_equiv } }

end surreal


