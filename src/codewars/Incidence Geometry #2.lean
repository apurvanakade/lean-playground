-- https://www.codewars.com/kata/5e889a3c0f55ed0032f1879f/train/lean

/-
  Incidence geometry in Lean, referenced from
  https://sites.math.washington.edu/~lee/Courses/444-2009/theorems-incidence.pdf
  and the lecture notes for MATH 4221 (not publicly available on the Internet)
-/

-- Undefined terms and axioms of incidence geometry
-- In incidence geometry, there are 3 undefined terms:
-- - Point
-- - Line
-- - "Incident with"/"lies on", e.g. point P is incident with / lies on line l
-- And there are 3 axioms:
-- - I₁: For every pair of distinct points P and Q there is exactly 1 line l such
--   that P and Q lie on l
-- - I₂: For every line l there exist at least two distinct points P and Q such
--   that both P and Q lie on l
-- - I₃: There exist three points that do not all lie on any one line
-- Note that the three points in I₃ are implicitly assumed to be distinct, because
-- otherwise one could construct a trivial model with only one point and no lines
-- that trivially satisfies the axioms, which is uninteresting, and some of the
-- theorems stated below do not hold in the trivial model
import tactic 

class incidence (point line : Type) (incident_with : point → line → Prop) :=
  (I₁ : ∀ P Q, P ≠ Q → ∃! l, incident_with P l ∧ incident_with Q l)
  (I₂ : ∀ l, ∃ P Q, P ≠ Q ∧ incident_with P l ∧ incident_with Q l)
  (I₃ : ∃ P Q R, P ≠ Q ∧ Q ≠ R ∧ P ≠ R ∧
    ∀ l, ¬(incident_with P l ∧ incident_with Q l ∧ incident_with R l))


theorem thm_3p6p2 (point line : Type) (incident_with : point → line → Prop)
  [incidence point line incident_with] (l : line) :
  ∃ P, ¬incident_with P l := 
begin 
-- from _inst_1.I₃ extract three points P, Q, R,
-- the proofs of distinctness hPQ, hQR, hPR, 
-- and the proof of incidence hl of P, Q, R on l
rcases _inst_1.I₃ with ⟨ P, Q, R, hPQ, hQR, hPR, hl⟩, 
specialize hl l,
push_neg at hl,

by_cases hpl: (incident_with P l), 
  by_cases hql: (incident_with Q l),

    -- both P and Q lie on l
    show ∃ (P : point), ¬incident_with P l, 
      use R,
      exact hl hpl hql,

    -- P lies on l but Q does not lie on l
    show ∃ (P : point), ¬incident_with P l,
      use Q,

    -- P does not lie on l
    show ∃ (P : point), ¬incident_with P l,
      use P,
end 