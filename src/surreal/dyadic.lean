import data.rat.basic
import data.nat.prime
import ring_theory.localization
import tactic

namespace rat

def is_dyadic (q : ℚ) : Prop := ∃ (n : ℕ), q.denom = 2^n

theorem denom_dvd' (n : ℤ) (d : ℕ) : ((mk_nat n d).denom) ∣ d := by exact_mod_cast denom_dvd n d

theorem num_denom'' {a : ℚ} : mk_nat a.num a.denom = a := num_denom

lemma denom_pow_two_mul_denom_pow_two (m₁ m₂ : ℤ) (n₁ n₂ : ℕ) :
  ∃ k : ℕ, (mk_nat m₁ (2 ^ n₁) * mk_nat m₂ (2 ^ n₂)).denom = 2 ^ k :=
begin
  let x := rat.mk m₁ (2 ^ n₁ : ℕ),
  let y := rat.mk m₂ (2 ^ n₂ : ℕ),
  have : (x * y).denom ∣ 2 ^ (n₁ + n₂), by
  { calc (x * y).denom ∣ x.denom * y.denom : mul_denom_dvd _ _
                   ... ∣ 2 ^ n₁ * 2 ^ n₂ : mul_dvd_mul (denom_dvd' _ _) (denom_dvd' _ _)
                   ... = 2 ^ (n₁ + n₂) : (pow_add 2 n₁ n₂).symm },
  obtain ⟨k, -, hk⟩ := (nat.dvd_prime_pow nat.prime_two).1 this,
  exact ⟨k, hk⟩,
end

theorem dyadic.mul (x y : ℚ) : x.is_dyadic → y.is_dyadic → (x * y).is_dyadic :=
begin
  rintros ⟨nx, hnx⟩ ⟨ny, hny⟩,
  obtain ⟨k, hk⟩ := denom_pow_two_mul_denom_pow_two x.num y.num nx ny,
  use k,
  rwa [← hnx, ← hny, num_denom'', num_denom''] at hk,
end

lemma denom_pow_two_add_denom_pow_two (m₁ m₂ : ℤ) (n₁ n₂ : ℕ) :
  ∃ k : ℕ, (rat.mk_nat m₁ (2 ^ n₁) + rat.mk_nat m₂ (2 ^ n₂)).denom = 2 ^ k :=
begin
  let x := rat.mk m₁ (2 ^ n₁ : ℕ),
  let y := rat.mk m₂ (2 ^ n₂ : ℕ),
  have : (x + y).denom ∣ 2 ^ (n₁ + n₂), by
  { calc (x + y).denom ∣ x.denom * y.denom : add_denom_dvd _ _
                   ... ∣ 2 ^ n₁ * 2 ^ n₂ : mul_dvd_mul (denom_dvd' _ _) (denom_dvd' _ _)
                   ... = 2 ^ (n₁ + n₂) : (pow_add 2 n₁ n₂).symm },
  obtain ⟨k, -, hk⟩ := (nat.dvd_prime_pow nat.prime_two).1 this,
  exact ⟨k, hk⟩,
end

theorem dyadic.add (x y : ℚ) : x.is_dyadic → y.is_dyadic → (x + y).is_dyadic :=
begin
  rintros ⟨nx, hnx⟩ ⟨ny, hny⟩,
  obtain ⟨k, hk⟩ := denom_pow_two_add_denom_pow_two x.num y.num nx ny,
  use k,
  rwa [← hnx, ← hny, num_denom'', num_denom''] at hk,
end

theorem dyadic.neg (x : ℚ): x.is_dyadic → (-x).is_dyadic :=
λ ⟨n, hn⟩, ⟨n, by simp[hn]⟩

def dyadic : subring ℚ :=
{ carrier   := { x : ℚ | x.is_dyadic },
  one_mem'  := ⟨0, by norm_num⟩,
  mul_mem'  := dyadic.mul,
  zero_mem' := ⟨0, by norm_num⟩,
  add_mem'  := dyadic.add,
  neg_mem'  := dyadic.neg }
  
lemma aux (a b : rat.dyadic) : a = b ↔ a.val = b.val := by { simp only [set_like.coe_eq_coe, subtype.val_eq_coe], }

def a : localization_map.away_map 2 rat.dyadic :=
{ to_fun := λ n : ℤ, (n : rat.dyadic),
  map_one' := by norm_num,
  map_mul' := by norm_num,
  map_zero' := rfl,
  map_add' := by norm_num,
  map_units' :=
  begin
    rintro ⟨y, a, ha⟩,
    rw is_unit_iff_exists_inv,
    let b := rat.mk' 1 (2^a) (pow_pos zero_lt_two a) (nat.coprime_one_left (2 ^ a)),
    use [b, a],
    rw aux,
    simp only [subring.coe_mul, subring.coe_one, subring.coe_int_cast, subtype.coe_mk, subtype.val_eq_coe], 
    have : b = ((2 ^ a) : ℚ)⁻¹, by { rw eq_inv_iff, have := @rat.inv_def' b, simp at this, symmetry, assumption },
    rw this,
    rw ← ha,
    simp,
    refine rat.mul_inv_cancel _ _,
    apply ne_of_gt,
    simp only [zero_lt_bit0, pow_pos, zero_lt_one],
  end,
  surj' := by { rintro ⟨a, ⟨b, h⟩⟩, simp, use a.num,
          use 2 ^ b, use b, norm_cast, rw ← h, rw aux, simp, },
  eq_iff_exists' := by { intros x y, split, norm_cast, intro hxy, use 1, norm_num, exact hxy,
          rintro ⟨⟨c, d, e⟩, hc⟩,
           norm_cast, have : (c:ℤ) ≠ 0,
          by { clear hc x y, apply ne_of_gt, rw ← e, apply pow_pos, dec_trivial },
          exact mul_right_cancel' this hc,} }


end rat
