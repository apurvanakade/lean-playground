import set_theory.surreal
open pgame

theorem numeric_nat (n : ℕ) : numeric n :=
begin
  induction n with n hn,
  apply numeric_zero,
  apply numeric_add hn numeric_one,
end

theorem numeric_omega : numeric omega :=
⟨by rintros ⟨ ⟩ ⟨ ⟩, λ i, by simp [numeric_nat i.down] , by rintros ⟨ ⟩⟩

#check numeric_nat
#check numeric_omega
