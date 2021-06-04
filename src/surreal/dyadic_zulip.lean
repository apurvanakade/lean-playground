import tactic
import set_theory.surreal
import ring_theory.localization

-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Dyadic.20numbers
--

namespace surreal
#check pow

def powers_half : ℕ → surreal := sorry

def powers_two : submonoid ℤ := submonoid.powers 2

lemma mem_powers_iff {α : Type*} [monoid α] (z x : α) :
  x ∈ submonoid.powers z ↔ ∃ n : ℕ, z ^ n = x := iff.rfl

@[simp] noncomputable def log (n : powers 2) : ℕ :=
classical.some n.property

@[simp] def pow (n : ℕ) : powers 2 := ⟨2 ^ n, n, rfl⟩

theorem log_pow_eq_self (n : ℕ) : log (pow n) = n :=
begin
  unfold log,
  generalize_proofs h,
  exact @nat.pow_right_injective 2 rfl.ge (classical.some h) n (classical.some_spec h),
end

theorem pow_log_eq_self (n : powers 2) : pow (log n) = n :=
begin
  dsimp,
  rcases n with ⟨_, hn⟩,
  congr,
  exact classical.some_spec hn,
end

noncomputable def log' (p : submonoid.powers 2) : ℕ :=
classical.some $ (mem_powers_iff 2 p.val).1 p.prop

def pow' (n : ℕ) : submonoid.powers 2 := ⟨2 ^ n, n, rfl⟩

theorem log_pow_eq_self' (n : ℕ) : log' (pow' n) = n :=
begin
  unfold log',
  generalize_proofs h,
  exact @nat.pow_right_injective 2 rfl.ge (classical.some h) n (classical.some_spec h),
end


theorem pow_log_eq_self' (n : submonoid.powers 2) : pow' (log' n) = n :=
begin
  unfold pow', unfold log',
  rcases n with ⟨_, hn⟩,
  congr,
  exact classical.some_spec hn,
end

noncomputable def dyadic_mk'' (p : ℤ × submonoid.powers 2) : surreal :=
p.fst • powers_half (log' p.snd)


@[simp]
theorem dyadic_mk'''' {p : ℤ × submonoid.powers 2} : dyadic_mk'' (p.fst, pow' p.snd) = p.fst • powers_half p.snd :=
begin
  unfold dyadic_mk'',
  congr,
  apply log_pow_eq_self',
end


@[simp]
noncomputable def dyadic_mk : ℤ × powers_two → surreal :=
λ p, p.fst • powers_half (classical.some p.snd.prop)

@[simp]
theorem dyadic_mk' {m n} : dyadic_mk (m, ⟨2 ^ n, n, rfl⟩) = m • powers_half n :=
begin
  dsimp,
  generalize_proofs h,
  congr,
  simp only [powers_two, mem_powers_iff, subtype.coe_mk] at h,
  suffices : (2 : ℤ) ^ (classical.some h) = 2 ^ n,
  { have h2 : (2 : ℤ) = (2 : ℕ) := rfl,
    simp_rw [h2, ←int.coe_nat_pow, int.coe_nat_inj'] at this,
    convert nat.pow_right_injective le_rfl this,
    ext m,
    simp_rw [h2, ←int.coe_nat_pow, int.coe_nat_inj'] },
  { exact classical.some_spec h }
end

lemma int.exists_nat_eq_of_nonneg {x : ℤ} (h : 0 ≤ x) : ∃ (y : ℕ), (y : ℤ) = x :=
begin
  cases x,
  { simp },
  { refine absurd h _,
    simp },
end

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
theorem dyadic_mk''' {m n} : dyadic_mk (m, ⟨2 ^ n, n, rfl⟩) = m • powers_half n :=
begin
  dsimp,
  generalize_proofs h,
  congr,
  simp only [powers_two, mem_powers_iff, subtype.coe_mk] at h,
  apply int.pow_right_injective le_rfl,
  simpa using classical.some_spec h
end


end surreal
