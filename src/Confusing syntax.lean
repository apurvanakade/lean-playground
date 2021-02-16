import data.nat.basic
import tactic

open classical
attribute [instance] prop_decidable

theorem exists_unique_le : ∃! n m : ℕ, m ≤ n :=
begin 
  unfold exists_unique,
  use 0,
  split, 
    use 0,
    split, refl,
    intro y,
    exact nat.le_zero_iff.mp,

    intro y,
    intro hy,
    cases hy with z hy,
    contrapose! hy,
    -- intros hz,
    -- by_cases z=y,
    have ht := nat.exists_eq_succ_of_ne_zero hy,
    cases ht with t ht,
    rw ht,
    intro hz,

    by_cases z=t + 1,

      rw h,
      use t,
      split, linarith, simp only [self_eq_add_right, ne.def, not_false_iff, one_ne_zero],

      use t+1,
      split, refl, simp only [ne.def], contrapose! h, symmetry, assumption,
end 
