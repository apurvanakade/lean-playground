import set_theory.surreal
open surreal 
namespace surreal
-- set_option pp.notation false

-- instance : add_semigroup surreal :=
-- { add_assoc := add_assoc,
--   ..(by apply_instance : has_add surreal) }

theorem zero_add : ∀ x : surreal, 0 + x = x :=
sorry

theorem add_zero : ∀ x : surreal, x + 0 = x :=
sorry

instance : add_monoid surreal := {
  add := add,
  add_assoc := add_assoc,
  zero := 0,
  zero_add := zero_add,
  add_zero := add_zero }


-- add_group, add_comm_semigroup, add_comm_group, ordered_add_comm_group,

-- def neg : surreal → surreal := sorry

-- theorem sub_eq_add_neg : (∀ x y : surreal) x + (neg y) = x
-- add_left_neg

-- instance : add_group surreal := {
--   add := add,
--   add_assoc := surreal.add_assoc,
--   zero := 0,
--   zero_add := surreal.zero_add,
--   add_zero := surreal.add_zero,
--   neg := neg,
--   sub := λ x y, x + (neg y),
--   sub_eq_add_neg := _,
--   add_left_neg := _ }
-- end surreal
