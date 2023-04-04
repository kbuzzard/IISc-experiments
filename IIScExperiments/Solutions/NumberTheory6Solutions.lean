/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib

/-

# Prove the theorem, due to Kraichik, asserting that 13|2^70+3^70

This is the sixth question in Sierpinski's book "250 elementary problems
in number theory".

-/

example : 13 ∣ 2^70 + 3^70 := by
  -- use a computer algebra package to work out (2^70+3^70)/13
  use 192550423461109399456637645953021
  norm_num

-- There is a more honest proof, using Fermat's Little Theorem, but
-- Fermat's Little Theorem is in the half of mathlib3 which is not ported
-- to Lean 4 yet!
