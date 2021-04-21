import set_theory.surreal
open surreal 
namespace surreal

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
end 
