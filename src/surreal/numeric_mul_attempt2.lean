import set_theory.surreal


namespace pgame
open pgame

theorem foo : Π {x X y Y : pgame} (ox : x.numeric) (oX : X.numeric) (oy : y.numeric) (oY : Y.numeric),
(x < X → y < Y → x * Y + X * y < x * y + X * Y)
∧
(x ≤ X → y ≤ Y → x * Y + X * y ≤ x * y + X * Y)
| (mk xl xr xL xR) (mk Xl Xr XL XR) (mk yl yr yL yR) (mk Yl Yr YL YR) ox oX oy oY :=
begin
  let x := (mk xl xr xL xR),
  let X := (mk Xl Xr XL XR),
  let y := (mk yl yr yL yR),
  let Y := (mk Yl Yr YL YR),
  split,
  {
    intros hxX hyY,
    obtain ⟨i, hi⟩ := lt_def_le.1 hxX;
    obtain ⟨j, hj⟩ := lt_def_le.1 hyY,
    {
      rw lt_def_le,
      left,
      use sum.inr (sum.inl (i, j)),
      change x * Y + X * y ≤ x * y + (XL i * Y + X * YL j - XL i * YL j),
      have := (foo (oX.2.1 i) oX (oY.2.1 j) oY).2 (oX.move_left_le i) (oY.move_left_le j),
    repeat {sorry},
    },
    repeat {sorry},
  },
  repeat {sorry},
end
-- theorem foo : Π (x X y Y : pgame) (ox : x.numeric) (oX : X.numeric) (oy : y.numeric) (oY : Y.numeric),
-- (x < X → y < Y → x * Y + X * y < x * y + X * Y)
-- -- ∧
-- -- (x ≤ X → y ≤ Y → x * Y + y * X ≤ x * X + y * Y)
-- | (mk xl xr xL xR) (mk Xl Xr XL XR) (mk yl yr yL yR) (mk Yl Yr YL YR) ox oX oy oY :=
-- begin
--   let x := (mk xl xr xL xR),
--   let X := (mk Xl Xr XL XR),
--   let y := (mk yl yr yL yR),
--   let Y := (mk Yl Yr YL YR),
--   -- split,
--   {
--     intros hxX hyY,
--     -- have hxX' := le_of_lt ox oX hxX,
--     -- have hyY' := le_of_lt oy oY hyY,
--     obtain ⟨i, hi₁, hi₂⟩ := lt_def.1 hxX,
--     obtain ⟨j, hj₁, hj₂⟩ := lt_def.1 hyY,
--     {
--       rw lt_def,
--       left,
--       use sum.inr (sum.inl (i, j)),
--       split,
--       {
--         rintro (⟨⟨i', j'⟩ | ⟨i', j'⟩⟩ | ⟨i', j'⟩ | ⟨i', j'⟩),
--         {
-- -- change (x * Y).move_left(sum.inl (i', j')) + mk Xl Xr XL XR * mk yl yr yL yR <
-- --     (mk xl xr xL xR * mk yl yr yL yR + mk Xl Xr XL XR * mk Yl Yr YL YR).move_left (sum.inr (sum.inl (i, j))),
--            change
--            (xL i' * Y + x * YL j' - xL i' * YL j') + X * y < x * y + (XL i * Y + X * YL j - XL i * YL j),
--           specialize hi₁ i',
--           clear hi₂ hj₁ hj₂,
--           have := foo (xL i') (XL i) y Y (ox.2.1 i') (oX.2.1 i) oy oY hi₁ hyY,
--           repeat {sorry},
--         },
--         repeat {sorry},
--       },
--       rintro k,
--       change x * Y + X * y <
--     (x * y + (XL i * Y + X * YL j - XL i * YL j)).move_right k,
--       repeat {sorry} },
--     repeat {sorry}
--     },
-- end

-- theorem foo : Π (x X y Y : pgame) (ox : x.numeric) (oX : X.numeric) (oy : y.numeric) (oY : Y.numeric),
-- x < X → y < Y → x * Y + y * X < x * X + y * Y
-- | (mk xl xr xL xR) (mk Xl Xr XL XR) (mk yl yr yL yR) (mk Yl Yr YL YR) ox oX oy oY :=
-- begin
--   set x := (mk xl xr xL xR),
--   set X := (mk Xl Xr XL XR),
--   set y := (mk yl yr yL yR),
--   set Y := (mk Yl Yr YL YR),
--   intros hxX hyY,
--   rw lt_def at *,
--   dsimp at *,
--   rcases hxX, rcases hyY,
--   {
--     obtain ⟨i, hi₁, hi₂⟩ := hxX,
--     obtain ⟨j, hj₁, hj₂⟩ := hyY,
--     right,
--     sorry,
--   },
--   repeat {sorry},
-- end
#check lt_def
-- ⊢ ?m_1 < ?m_2 ↔
--     (∃ (i : ?m_2.left_moves),
--          (∀ (i' : ?m_1.left_moves), ?m_1.move_left i' < ?m_2.move_left i) ∧
--            ∀ (j : (?m_2.move_left i).right_moves), ?m_1 < (?m_2.move_left i).move_right j) ∨
--       ∃ (j : ?m_1.right_moves),
--         (∀ (i : (?m_1.move_right j).left_moves), (?m_1.move_right j).move_left i < ?m_2) ∧
--           ∀ (j' : ?m_2.right_moves), ?m_1.move_right j < ?m_2.move_right j'
end pgame
