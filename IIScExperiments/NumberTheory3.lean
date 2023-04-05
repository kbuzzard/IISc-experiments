/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import Mathlib.Tactic.Use
import Mathlib.Tactic.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite

/-

# Prove that there exists infinitely many positive integers n such that
# 4n² + 1 is divisible both by 5 and 13.

This is the third question in Sierpinski's book "250 elementary problems
in number theory".

Maths proof: if n=4 then 4n^2+1=65 is divisible by both 5 and 13
so if n is congruent to 4 mod 5 and mod 13 (i.e if n=4+65*t)
then this will work.

There are various ways to formalise the statement that some set
of naturals is infinite. We suggest two here (although proving
they're the same is fiddly)

-/

-- There are arbitrarily large solutions to `5 ∣ 4*n^2+1 ∧ 13 ∣ 4*n^2+1`
lemma arb_large_soln : ∀ N : ℕ, ∃ n > N, 5 ∣ 4*n^2+1 ∧ 13 ∣ 4*n^2+1 := by
  sorry

-- This is not number theory any more, it's switching between two
-- interpretations of "this set of naturals is infinite" 
-- for one way, use `Set.Infinite.exists_nat_lt`; for
-- the other, use contrapositive and `Finset.sup`

lemma infinite_iff_arb_large (S : Set ℕ) : S.Infinite ↔ ∀ N, ∃ n > N, n ∈ S := by
  sorry

-- Another way of stating the question (note different "|" symbols:
-- there's `|` for "such that" in set theory and `\|` for "divides" in number theory)
lemma infinite_set_of_solutions : {n : ℕ | 5 ∣ 4*n^2+1 ∧ 13 ∣ 4*n^2+1}.Infinite := by
  rw [infinite_iff_arb_large]
  exact arb_large_soln
