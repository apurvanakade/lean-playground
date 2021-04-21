import set_theory.surreal
namespace surreal

def neg : surreal → surreal :=
surreal.lift (λ x ox, ⟦⟨-x, pgame.numeric_neg ox⟩⟧) (λ _ _ _ _ a, quotient.sound (pgame.neg_congr a))

instance : ordered_add_comm_group surreal :=
{ add               := surreal.add,
  add_assoc         := surreal.add_assoc,
  zero              := 0,
  zero_add          := by { rintros ⟨x, ox⟩, exact quotient.sound (pgame.zero_add_equiv _) },
  add_zero          := by { rintros ⟨x, ox⟩, exact quotient.sound (pgame.add_zero_equiv _) }, 
  neg               := surreal.neg, 
  sub               := λ x y, x + surreal.neg y,
  sub_eq_add_neg    := by try_refl_tac,
  add_left_neg      := by { rintros ⟨x, ox⟩, exact quotient.sound pgame.add_left_neg_equiv }, 
  add_comm          := by { rintros ⟨x, ox⟩ ⟨y, oy⟩, exact quotient.sound pgame.add_comm_equiv },
  le                := surreal.le,
  lt                := surreal.lt,
  le_refl           := by { rintros ⟨x, ox⟩, refl },
  le_trans          := by { rintros ⟨x, ox⟩ ⟨y, oy⟩ ⟨z, oz⟩, exact pgame.le_trans },
  lt_iff_le_not_le  := by { rintros ⟨x, ox⟩ ⟨y, oy⟩, exact pgame.lt_iff_le_not_le ox oy },
  le_antisymm       := by { rintros ⟨x, ox⟩ ⟨y, oy⟩ h₁ h₂, exact quotient.sound ⟨h₁, h₂⟩ },
  add_le_add_left   := by { rintros ⟨x, ox⟩ ⟨y, oy⟩ hx ⟨z, oz⟩, exact pgame.add_le_add_left hx } }

end surreal

