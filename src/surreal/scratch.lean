import set_theory.surreal
import data.rat.basic
import data.nat.prime
import ring_theory.localization
import tactic

namespace surreal

def powers_half : ℕ → surreal := sorry

#reduce powers 2
-- λ (y : ℕ), ∃ (n : ℕ), npow_rec n 2 = y

def powers_two : submonoid ℤ :=
{ carrier  := powers 2,
  one_mem' := powers.one_mem,
  mul_mem' := λ _ _, powers.mul_mem }

@[simp] noncomputable def dyadic_mk' (m : ℤ) (n : ℕ) : surreal := m • powers_half n

noncomputable def dyadic_mk : ℤ × powers_two → surreal :=
λ ⟨m, a, ha⟩, dyadic_mk' m (classical.some ha)

def dyadic' : localization powers_two → surreal := sorry

noncomputable def dyadic : add_monoid_hom (localization powers_two) surreal := sorry

end surreal
