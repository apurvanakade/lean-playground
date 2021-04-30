import tactic

meta def stupid_tactic : tactic unit :=
`[assumption]
    <|> (do `[apply sum.inr], stupid_tactic )
    <|> (do `[apply sum.inl], stupid_tactic )
    <|> (do `[apply prod.mk], stupid_tactic, stupid_tactic )

example (xl yl zl xr yr zr : Type) :
  (xl × yl ⊕ xr × yr) × zl ⊕ (xl × yr ⊕ xr × yl) × zr
  ≃ xl × (yl × zl ⊕ yr × zr) ⊕ xr × (yl × zr ⊕ yr × zl) :=
{ to_fun    := by rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩); stupid_tactic,
  left_inv  := by rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩); refl,
  inv_fun   := by rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩); stupid_tactic,
  right_inv := by rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩); refl }

example (xl yl zl xr yr zr : Type) :
  (xl × yl ⊕ xr × yr) × zl ⊕ (xl × yr ⊕ xr × yl) × zr
  ≃ xl × (yl × zl ⊕ yr × zr) ⊕ xr × (yl × zr ⊕ yr × zl) :=
begin
fsplit,
  simp[equiv.sum_comm, equiv.prod_assoc, equiv.prod_sum_distrib, equiv.sum_prod_distrib],
end

example (xl yl zl xr yr zr : Prop) :
  (xl ∧ yl) ∧ zl ∨ (xl ∧ yr) ∧ zr
  = xl ∧ (yr ∧ zr) ∨ xr ∧ (yr ∧ zl) :=
begin
  tauto,
  
end

example (a b c x y z : Prop) :
  (a ∧ b) ∧ c → a ∧ (b ∧ c) :=
begin
  tauto,
  
end
