import data.rat.basic
import data.nat.prime
import ring_theory.localization
import tactic
import set_theory.surreal

namespace surreal

def dyadic_map : localization (@submonoid.powers ℤ _ 2) →+ surreal := sorry

end surreal

namespace rat

def is_dyadic (q : ℚ) : Prop := ∃ (n : ℕ), q.denom = 2^n

-- TODO: move this data.rat.basic
theorem denom_dvd' (n : ℤ) (d : ℕ) : ((mk_nat n d).denom) ∣ d := by exact_mod_cast denom_dvd n d

-- TODO: move this data.rat.basic
theorem num_denom'' {a : ℚ} : mk_nat a.num a.denom = a := num_denom

-- TODO: move this data.rat.basic
lemma denom_pow_prime_mul_denom_pow_prime (m₁ m₂ : ℤ) (n₁ n₂ : ℕ) {p : ℕ} (hp : p.prime) :
  ∃ k : ℕ, (mk_nat m₁ (p ^ n₁) * mk_nat m₂ (p ^ n₂)).denom = p ^ k :=
begin
  let x := mk m₁ (p ^ n₁ : ℕ),
  let y := mk m₂ (p ^ n₂ : ℕ),
  have : (x * y).denom ∣ p ^ (n₁ + n₂), by
  { calc (x * y).denom ∣ x.denom * y.denom : mul_denom_dvd _ _
                   ... ∣ p ^ n₁ * p ^ n₂   : mul_dvd_mul (denom_dvd' _ _) (denom_dvd' _ _)
                   ... = p ^ (n₁ + n₂)     : (pow_add p n₁ n₂).symm },
  obtain ⟨k, -, hk⟩ := (nat.dvd_prime_pow hp).1 this,
  exact ⟨k, hk⟩,
end

-- TODO: move this data.rat.basic
lemma denom_pow_prime_add_denom_pow_prime (m₁ m₂ : ℤ) (n₁ n₂ : ℕ) {p : ℕ} (hp : p.prime) :
  ∃ k : ℕ, (mk_nat m₁ (p ^ n₁) + mk_nat m₂ (p ^ n₂)).denom = p ^ k :=
begin
  let x := mk m₁ (p ^ n₁ : ℕ),
  let y := mk m₂ (p ^ n₂ : ℕ),
  have : (x + y).denom ∣ p ^ (n₁ + n₂), by
  { calc (x + y).denom ∣ x.denom * y.denom : add_denom_dvd _ _
                   ... ∣ p ^ n₁ * p ^ n₂   : mul_dvd_mul (denom_dvd' _ _) (denom_dvd' _ _)
                   ... = p ^ (n₁ + n₂)     : (pow_add p n₁ n₂).symm },
  obtain ⟨k, -, hk⟩ := (nat.dvd_prime_pow hp).1 this,
  exact ⟨k, hk⟩,
end

theorem dyadic.mul (x y : ℚ) : x.is_dyadic → y.is_dyadic → (x * y).is_dyadic :=
begin
  rintros ⟨nx, hnx⟩ ⟨ny, hny⟩,
  obtain ⟨k, hk⟩ := denom_pow_prime_mul_denom_pow_prime x.num y.num nx ny nat.prime_two,
  use k,
  rwa [← hnx, ← hny, num_denom'', num_denom''] at hk,
end

theorem dyadic.add (x y : ℚ) : x.is_dyadic → y.is_dyadic → (x + y).is_dyadic :=
begin
  rintros ⟨nx, hnx⟩ ⟨ny, hny⟩,
  obtain ⟨k, hk⟩ := denom_pow_prime_add_denom_pow_prime x.num y.num nx ny nat.prime_two,
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
  
lemma dyadic.coe_eq_iff (x y : dyadic) : x = y ↔ x.val = y.val :=
by { simp only [set_like.coe_eq_coe, subtype.val_eq_coe] }

def int.localization_away_two_dyadic : localization_map.away_map 2 dyadic :=
{ to_fun         := λ m : ℤ, (m : dyadic),
  map_one'       := by norm_num,
  map_mul'       := by norm_num,
  map_zero'      := rfl,
  map_add'       := by norm_num,
  map_units'     := begin
                      rintro ⟨_, a, h⟩,
                      rw is_unit_iff_exists_inv,
                      let b := mk' 1 (2 ^ a) (pow_pos zero_lt_two a) (nat.coprime_one_left (2 ^ a)),
                      use [b, a],
                      simp only [dyadic.coe_eq_iff, subring.coe_mul, subring.coe_one,
                                subring.coe_int_cast, subtype.coe_mk, subtype.val_eq_coe],
                      have : b = ((2 ^ a) : ℚ)⁻¹,
                        by { rw [eq_inv_iff, inv_def'],
                             simp only [nat.cast_bit0, int.cast_one, nat.cast_one,
                                        div_one, nat.cast_pow] },
                      rw [this, ← h],
                      simp only [int.cast_pow, int.cast_bit0, int.cast_one],
                      refine rat.mul_inv_cancel _ _,
                      apply ne_of_gt,
                      simp only [zero_lt_bit0, pow_pos, zero_lt_one],
                    end,
  surj'          := begin
                      rintro ⟨a, b, h⟩,
                      use [a.num, 2 ^ b, b],
                      simp [dyadic.coe_eq_iff],
                      norm_cast,
                      rw [← h, mul_denom_eq_num],
                    end,
  eq_iff_exists' := begin
                      intros x y,
                      norm_cast,
                      split,
                      { intro hxy,
                        use 1,
                        simpa only [mul_one, submonoid.coe_one] },
                      { rintro ⟨⟨c, _, hc⟩, hxy⟩,
                        have : (c:ℤ) ≠ 0,
                          by { apply ne_of_gt, rw ← hc, apply pow_pos, dec_trivial },
                        exact mul_right_cancel' this hxy },
                    end }

noncomputable def dyadic_to_surreal : dyadic →+ surreal :=
add_monoid_hom.comp surreal.dyadic_map
  (localization.ring_equiv_of_quotient int.localization_away_two_dyadic).symm

end rat
