import set_theory.surreal
import data.rat.basic
import data.nat.prime
import ring_theory.localization
import tactic


namespace pgame
open pgame

@[trans] theorem lt_of_lt_of_equiv' {x y z : pgame} (h₁ : x < y) (h₂ : y ≈ z) : x < z := lt_of_lt_of_le h₁ h₂.1
@[trans] theorem le_of_le_of_equiv' {x y z : pgame} (h₁ : x ≤ y) (h₂ : y ≈ z) : x ≤ z := le_trans h₁ h₂.1
@[trans] theorem lt_of_equiv_of_lt' {x y z : pgame} (h₁ : x ≈ y) (h₂ : y < z) : x < z := lt_of_le_of_lt h₁.1 h₂
@[trans] theorem le_of_equiv_of_le' {x y z : pgame} (h₁ : x ≈ y) (h₂ : y ≤ z) : x ≤ z := le_trans h₁.1 h₂

def half : pgame := ⟨punit, punit, 0, 1⟩

@[simp] lemma half_move_left : half.move_left punit.star = 0 := rfl
@[simp] lemma half_move_right : half.move_right punit.star = 1 := rfl

theorem numeric_half : numeric half :=
-- ⟨λ _ _, zero_lt_one,
--  λ _, numeric_zero,
--  λ _, numeric_one⟩
begin
  split,
  { rintros ⟨ ⟩ ⟨ ⟩,
    dsimp,
    rw zero_lt,
    use punit.star,
    rintro ⟨ ⟩ },
  split,
  { rintro ⟨ ⟩, exact numeric_zero },
  { rintro ⟨ ⟩, exact numeric_one }
end

theorem zero_lt_half : 0 < half :=
begin
  rw lt_def,
  left,
  use punit.star,
  split; rintro ⟨⟩,
end

theorem half_lt_one : half < 1 :=
begin
  rw lt_def,
  right,
  use punit.star,
  split; rintro ⟨⟩,
  dsimp,
  rw zero_lt,
  use punit.star,
  rintro ⟨ ⟩
--  exact zero_lt_one,
end

theorem add_half_half_equiv_one : half + half ≈ 1 :=
begin
  split; rw le_def,
  { split,
    { rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩),
      { right,
        use (sum.inr punit.star),
        calc ((half + half).move_left (sum.inl punit.star)).move_right (sum.inr punit.star)
            = (half.move_left punit.star + half).move_right (sum.inr punit.star) : by fsplit
        ... = (0 + half).move_right (sum.inr punit.star) : by fsplit
        ... ≈ 1 : zero_add_equiv 1
        ... ≤ 1 : le_refl 1 },
      { right,
        use (sum.inl punit.star),
        calc ((half + half).move_left (sum.inr punit.star)).move_right (sum.inl punit.star)
            = (half + half.move_left punit.star).move_right (sum.inl punit.star) : by fsplit
        ... = (half + 0).move_right (sum.inl punit.star) : by fsplit
        ... ≈ 1 : add_zero_equiv 1
        ... ≤ 1 : le_refl 1 } },
    { rintro ⟨⟩ } },
  { split,
    { rintro ⟨⟩,
      left,
      use (sum.inl punit.star),
      calc 0 ≤ half : le_of_lt numeric_zero numeric_half zero_lt_half
      ... ≈ 0 + half : (zero_add_equiv half).symm
      ... = (half + half).move_left (sum.inl punit.star) : by fsplit },
    { rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩),
      { left,
        use (sum.inr punit.star),
        calc 1 ≤ 1 : le_refl 1
           ... ≈ 1 + 0 : (add_zero_equiv 1).symm },
      { use (sum.inl punit.star),
        calc 1 ≤ 1 : le_refl 1
           ... ≈ 0 + 1 : (zero_add_equiv 1).symm } } }
end

def pow_half : ℕ → pgame
| 0       := mk punit pempty 0 pempty.elim
| (n + 1) := mk punit punit 0 (λ _, pow_half n)

@[simp] lemma pow_half_left_moves {n} : (pow_half n).left_moves = punit :=
by { cases n; refl }

@[simp] lemma pow_half_right_moves {n} : (pow_half (n + 1)).right_moves = punit :=
by { cases n; refl }

@[simp] lemma pow_half_move_left {n i} : (pow_half n).move_left i = 0 :=
by { cases n; cases i; refl }

lemma pow_half_move_left' (n) : ∃ i, (pow_half n).move_left i = 0 :=
by { cases n; use punit.star; refl }

lemma pow_half_move_right' (n) : ∃ i, (pow_half (n + 1)).move_right i = pow_half n :=
by { cases n; use punit.star; refl }

theorem numeric_pow_half {n} : (pow_half n).numeric :=
begin
  induction n with n hn,
  { exact numeric_one },
  { split,
    { rintro ⟨ ⟩ ⟨ ⟩,
      obtain ⟨i, hi⟩ := pow_half_move_left' n,
      dsimp,
      rw ← hi,
      exact hn.move_left_lt i },
    { exact ⟨λ _, numeric_zero, λ _, hn⟩ } }
end

theorem pow_half_lt {n : ℕ} : pow_half (n + 1) < pow_half n :=
begin
  obtain ⟨i, hi⟩ := pow_half_move_right' n,
  have := (@numeric_pow_half (n + 1)).lt_move_right i,
  rwa hi at this,
end

theorem zero_lt_pow_half {n : ℕ} : 0 < pow_half n :=
by { cases n; rw lt_def_le; use ⟨punit.star, le_refl 0⟩ }

theorem add_pow_half_pow_half {n} : pow_half (n + 1) + pow_half (n + 1) ≈ pow_half n :=
begin
  induction n with n hn,
  { exact add_half_half_equiv_one },
  split; rw le_def_lt,
  { split,
    { rintro (⟨⟨ ⟩⟩ | ⟨⟨ ⟩⟩),
      { calc 0 + pow_half (n.succ + 1) ≈ pow_half (n.succ + 1) : zero_add_equiv _
                                   ... < pow_half n.succ       : pow_half_lt },
      { calc pow_half (n.succ + 1) + 0 ≈ pow_half (n.succ + 1) : add_zero_equiv _
                                   ... < pow_half n.succ       : pow_half_lt } },
    { rintro ⟨⟩,
      change pow_half (n.succ + 1) + pow_half (n.succ + 1) < (pow_half n),
      rw lt_def_le,
      right,
      use sum.inl punit.star,
      calc pow_half (n.succ) + pow_half (n.succ + 1) ≤ pow_half (n.succ) + pow_half (n.succ) : add_le_add_left $ le_of_lt numeric_pow_half numeric_pow_half pow_half_lt
      ... ≈ pow_half n : hn } },
  split,
  { rintro ⟨⟩,
    calc 0 ≈ 0 + 0 : (add_zero_equiv _).symm
    ... ≤ pow_half (n.succ + 1) + 0 : by {refine add_le_add_right _, apply le_of_lt numeric_zero, apply numeric_pow_half, apply zero_lt_pow_half, }
    ... < pow_half (n.succ + 1) + pow_half (n.succ + 1) : add_lt_add_left zero_lt_pow_half },
  { rintro (⟨⟨ ⟩⟩ | ⟨⟨ ⟩⟩),
    { calc pow_half n.succ ≈ pow_half n.succ + 0 : (add_zero_equiv _).symm
                       ... < pow_half (n.succ) + pow_half (n.succ + 1) : add_lt_add_left zero_lt_pow_half },
    { calc pow_half n.succ ≈ 0 + pow_half n.succ : (zero_add_equiv _).symm
                       ... < pow_half (n.succ + 1) + pow_half (n.succ) : add_lt_add_right zero_lt_pow_half } }
end

end pgame

namespace surreal

-- def surreal_game : surreal →+ game :=
-- add_monoid_hom.mk' (surreal.lift (λ x ox, ⟦x⟧) (λ x y _ _ hxy,  @quotient.sound _ _ x y hxy))
--   $ by { rintros ⟨_, _⟩ ⟨_, _⟩, refl }

def half : surreal := ⟦⟨pgame.half, pgame.numeric_half⟩⟧

def pow_half (n : ℕ) : surreal := ⟦⟨pgame.pow_half n, pgame.numeric_pow_half⟩⟧

@[simp]
lemma pow_half_zero : pow_half 0 = 1 := rfl

@[simp]
lemma pow_half_one : pow_half 1 = half := rfl

lemma pow_half_succ (n : ℕ) : pow_half n = 2 • pow_half n.succ :=
sorry

theorem add_half_half_eq_one : half + half = 1 :=
quotient.sound pgame.add_half_half_equiv_one

lemma mem_powers_iff {α : Type*} [monoid α] (z x : α) :
  x ∈ submonoid.powers z ↔ ∃ n : ℕ, z ^ n = x := iff.rfl

def pow (n : ℕ) : @submonoid.powers ℤ _ 2 := ⟨2 ^ n, n, rfl⟩

noncomputable def log (p : @submonoid.powers ℤ _ 2) : ℕ :=
classical.some $ (mem_powers_iff 2 p.val).1 p.prop

lemma int.exists_nat_eq_of_nonneg {x : ℤ} (h : 0 ≤ x) : ∃ (y : ℕ), (y : ℤ) = x :=
begin
  cases x,
  { simp },
  { refine absurd h _,
    simp },
end

noncomputable instance : has_coe (@submonoid.powers ℤ _ 2) nat :=
⟨begin
   rintro ⟨a, ha⟩,
   have hha := classical.some_spec ha,
   have : 0 ≤ a, by
     {
       have := nat.one_le_two_pow (classical.some ha),
       rw ← hha,
       linarith,
     },
   exact classical.some (int.exists_nat_eq_of_nonneg this),
 end⟩

lemma int.pow_right_injective {x : ℤ} (h : 2 ≤ x) : function.injective (λ (n : ℕ), x ^ n) :=
begin
  intros n m hnm,
  obtain ⟨y, rfl⟩ : ∃ (y : ℕ), (y : ℤ) = x := int.exists_nat_eq_of_nonneg ((zero_le_two).trans h),
  have : 2 ≤ y,
  { rw ←int.coe_nat_le,
    simpa using h },
  apply nat.pow_right_injective this,
  simpa [←int.coe_nat_pow, int.coe_nat_inj'] using hnm
end

@[simp]
theorem log_pow_eq_self (n : ℕ) : log (pow n) = n :=
begin
  unfold log,
  generalize_proofs h,
  exact @int.pow_right_injective 2 rfl.ge (classical.some h) n (classical.some_spec h),
end

@[simp]
theorem pow_log_eq_self (n : @submonoid.powers ℤ _ 2) : pow (log n) = n :=
begin
  unfold pow, unfold log,
  rcases n with ⟨_, hn⟩,
  congr,
  exact classical.some_spec hn,
end

noncomputable def dyadic' (p : ℤ × @submonoid.powers ℤ _ 2) : surreal :=
p.fst • pow_half (log p.snd)

@[simp]
theorem mk_dyadic {p : ℤ × @submonoid.powers ℤ _ 2} :
  dyadic' (p.fst, pow p.snd) = p.fst • pow_half p.snd :=
begin
  unfold dyadic',
  congr,
  apply log_pow_eq_self,
end


-- lemma lem0 : dyadic' (1, pow 0) =  :=
-- begin
--   unfold dyadic',
--   simp,
--   rw ← add_half_half_eq_one,
--   abel,
-- end

-- lemma lem1 : dyadic' (2, pow 1) = 1 :=
-- begin
--   unfold dyadic',
--   simp,
--   rw ← add_half_half_eq_one,
--   abel,
-- end

-- set_option pp.notation false

lemma lem_n (n : ℕ) : dyadic' (2 ^ n, pow n) = 1 :=
begin
  unfold dyadic',
  induction n with n hn; simp at *,
  rw [← hn, pow_half_succ n],
  norm_cast,
  rw [smul_smul (2^n) 2 (pow_half n.succ)],
  congr,
  ring_nf,
end

example (a b : ℤ) : 0 < a → 0 ≤ b → 0 < a + b :=
by { library_search }

lemma anything (m : ℕ) (x : surreal) (hx : 0 < x) : 0 ≤ m • x :=
begin
  induction m with m hm,
  { simp only [le_refl, zero_smul] },
  { rw [succ_nsmul x m],
    apply add_nonneg (le_of_lt hx) hm }

end

lemma something (m : ℕ) (x : surreal) (hm : 0 < m) : 0 < x → 0 < m • x :=
begin
  intro hx,
  induction m with m hm,
  { exfalso, exact nat.lt_asymm hm hm },
  {
    rw [succ_nsmul x m],
    apply lt_add_of_pos_of_le hx (anything m x hx) }
end

-- lemma smul_cancel' (m : ℕ) (x : surreal) : x = 0 ∨ m = 0 ↔ m • x = 0 :=
-- begin
--   split, sorry,
--   { rintro hmx,
--     cases m with m,
--     sorry,
--     right,
--     rcases x with ⟨⟨xl, xr, xL, xR⟩, ox⟩,
--     sorry,
--   }
-- end

lemma smul_cancel (m : ℤ) (x y : surreal) (hm : m ≠ 0) : x = y ↔ m • x  = m • y :=
begin
  split; rintro hxy,
  { congr, exact hxy },
  {
    sorry,
  }
end

lemma lem2 (n k : ℕ) : dyadic' (2 ^ n, pow (n + k)) = pow_half k :=
begin
  induction k with k hk,
  { simp [lem_n] },
  { unfold dyadic' at *,
    simp at *,
    have : n + k.succ = (n + k).succ, by refl,
    rw this, clear this,
    rw [pow_half_succ (n + k), pow_half_succ k] at hk,
    have : 2 ^ n • 2 • pow_half (n + k).succ = 2 • 2 ^ n • pow_half (n + k).succ,
      by { apply smul_algebra_smul_comm },
    norm_cast at *,
    rw this at hk,
    exact (smul_cancel 2 (2^n • pow_half (n + k).succ) (pow_half k.succ) (by norm_num)).2 hk }
end

example (n m : ℕ) : m • n • 2 = (m * n) • 2 :=
begin
  exact smul_smul m n 2,
end

-- theorem bar
-- (m m' x : ℤ)
-- (y : ℕ)
-- (hxy : 2 ^ y = x)
-- (p : ℤ)
-- (q : ℕ)
-- (hpq : 2 ^ q = p)
-- (h₂ : m * 2 ^ y = m' * 2 ^ q)
-- : dyadic_mk (m, ⟨p, q, hpq⟩) = dyadic_mk (m', ⟨x, y, hxy⟩) :=
-- begin
--  sorry,
-- end

-- noncomputable def dyadic' : localization (@submonoid.powers ℤ _ 2) → surreal :=
-- begin
--   apply quotient.lift,
--   swap,
--   { exact dyadic_mk' },
--   {
--     rintros ⟨m, p, q, hpq⟩ ⟨m', x, y, hxy⟩ h,
--     obtain ⟨⟨x', y', hxy'⟩ , h₂⟩ := localization.r_iff_exists.1 h,
--     -- rw [← hxy, ← hxy', ← hpq] at *,
--     simp only [subtype.coe_mk, mul_eq_mul_right_iff] at h₂,
--     cases h₂,
--   { sorry,
--   -- rwa bar
--   },
--   { have := nat.one_le_pow y' 2 (by norm_num),
--     linarith } }
-- end

-- noncomputable def dyadic : add_monoid_hom (localization pow_two) surreal :=
-- { to_fun := dyadic',
--   map_zero' := by {  sorry },
--   map_add' := by { sorry } }

end surreal

-- namespace rat

-- def is_dyadic (q : ℚ) : Prop := ∃ (n : ℕ), q.denom = 2^n

-- theorem denom_dvd' (n : ℤ) (d : ℕ) : ((mk_nat n d).denom) ∣ d := by exact_mod_cast denom_dvd n d

-- theorem num_denom'' {a : ℚ} : mk_nat a.num a.denom = a := num_denom

-- lemma denom_pow_two_mul_denom_pow_two (m₁ m₂ : ℤ) (n₁ n₂ : ℕ) :
--   ∃ k : ℕ, (mk_nat m₁ (2 ^ n₁) * mk_nat m₂ (2 ^ n₂)).denom = 2 ^ k :=
-- begin
--   let x := rat.mk m₁ (2 ^ n₁ : ℕ),
--   let y := rat.mk m₂ (2 ^ n₂ : ℕ),
--   have : (x * y).denom ∣ 2 ^ (n₁ + n₂), by
--   { calc (x * y).denom ∣ x.denom * y.denom : mul_denom_dvd _ _
--                    ... ∣ 2 ^ n₁ * 2 ^ n₂ : mul_dvd_mul (denom_dvd' _ _) (denom_dvd' _ _)
--                    ... = 2 ^ (n₁ + n₂) : (pow_add 2 n₁ n₂).symm },
--   obtain ⟨k, -, hk⟩ := (nat.dvd_prime_pow nat.prime_two).1 this,
--   exact ⟨k, hk⟩,
-- end

-- theorem dyadic.mul (x y : ℚ) : x.is_dyadic → y.is_dyadic → (x * y).is_dyadic :=
-- begin
--   rintros ⟨nx, hnx⟩ ⟨ny, hny⟩,
--   obtain ⟨k, hk⟩ := denom_pow_two_mul_denom_pow_two x.num y.num nx ny,
--   use k,
--   rwa [← hnx, ← hny, num_denom'', num_denom''] at hk,
-- end

-- lemma denom_pow_two_add_denom_pow_two (m₁ m₂ : ℤ) (n₁ n₂ : ℕ) :
--   ∃ k : ℕ, (rat.mk_nat m₁ (2 ^ n₁) + rat.mk_nat m₂ (2 ^ n₂)).denom = 2 ^ k :=
-- begin
--   let x := rat.mk m₁ (2 ^ n₁ : ℕ),
--   let y := rat.mk m₂ (2 ^ n₂ : ℕ),
--   have : (x + y).denom ∣ 2 ^ (n₁ + n₂), by
--   { calc (x + y).denom ∣ x.denom * y.denom : add_denom_dvd _ _
--                    ... ∣ 2 ^ n₁ * 2 ^ n₂ : mul_dvd_mul (denom_dvd' _ _) (denom_dvd' _ _)
--                    ... = 2 ^ (n₁ + n₂) : (pow_add 2 n₁ n₂).symm },
--   obtain ⟨k, -, hk⟩ := (nat.dvd_prime_pow nat.prime_two).1 this,
--   exact ⟨k, hk⟩,
-- end

-- theorem dyadic.add (x y : ℚ) : x.is_dyadic → y.is_dyadic → (x + y).is_dyadic :=
-- begin
--   rintros ⟨nx, hnx⟩ ⟨ny, hny⟩,
--   obtain ⟨k, hk⟩ := denom_pow_two_add_denom_pow_two x.num y.num nx ny,
--   use k,
--   rwa [← hnx, ← hny, num_denom'', num_denom''] at hk,
-- end

-- theorem dyadic.neg (x : ℚ): x.is_dyadic → (-x).is_dyadic :=
-- λ ⟨n, hn⟩, ⟨n, by simp[hn]⟩

-- def dyadic : subring ℚ :=
-- { carrier   := { x : ℚ | x.is_dyadic },
--   one_mem'  := ⟨0, by norm_num⟩,
--   mul_mem'  := dyadic.mul,
--   zero_mem' := ⟨0, by norm_num⟩,
--   add_mem'  := dyadic.add,
--   neg_mem'  := dyadic.neg }

-- def a : localization_map.away_map 2 rat.dyadic :=
-- { to_fun := λ n : ℤ, (n : rat.dyadic),
--   map_one' := by norm_num,
--   map_mul' := by norm_num,
--   map_zero' := rfl,
--   map_add' := by norm_num,
--   map_units' := by { rintro ⟨a, b, h⟩, unfold is_unit, fsplit, fsplit, use a, use (rat.mk' 1 (2^b) (ne_of_gt (nat.pow_pos 2)) (nat.coprime_one_left _)), use b,  },
--   surj' := by { rintro ⟨a, ⟨b, h⟩⟩, simp, use a.num,
--           use 2 ^ b, use b, norm_cast, rw ← h, have := @rat.mul_denom_eq_num a,  },
--           --@rat.mul_denom_eq_num a), },
--   eq_iff_exists' := by { intros x y, split, norm_cast, intro hxy, use 1, norm_num, exact hxy,
--           rintro ⟨⟨c, d, e⟩, hc⟩,
--            norm_cast, have : (c:ℤ) ≠ 0,
--           by { clear hc x y, apply ne_of_gt, rw ← e, apply pow_pos, dec_trivial },
--           exact mul_right_cancel' this hc,} }


-- end rat
