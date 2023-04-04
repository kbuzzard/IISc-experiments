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

-- The number-theoretic heart of the argument.
-- Note that "divides" is `\|` not `|`
lemma divides_of_cong_four (t : ℕ) : 5 ∣ 4 * (65 * t + 4)^2 + 1 ∧
13 ∣ 4 * (65 * t + 4)^2 + 1 := by
  refine ⟨?_, ?_⟩  
  { use 3380*t^2 + 416*t + 13
    ring }
  { use 1300*t^2 + 160*t + 5
    ring }

-- There are arbitrarily large solutions to `5 ∣ 4*n^2+1 ∧ 13 ∣ 4*n^2+1`
lemma arb_large_soln : ∀ N : ℕ, ∃ n > N, 5 ∣ 4*n^2+1 ∧ 13 ∣ 4*n^2+1 := by
  intro N
  -- need to find t such that 65t+4>N. Just set t=N for simplicity
  use 65 * N + 4
  refine ⟨?_, ?_⟩
  { linarith }
  { apply divides_of_cong_four }  

-- This is not number theory any more, it's switching between two
-- interpretations of "this set of naturals is infinite" 
lemma infinite_iff_arb_large (S : Set ℕ) : S.Infinite ↔ ∀ N, ∃ n > N, n ∈ S := by
  refine ⟨?_, ?_⟩ 
  { intro h
    have h2 := Set.Infinite.exists_nat_lt h
    intro n
    rcases h2 n with ⟨m, hm, h3⟩
    use m
    exact ⟨h3, hm⟩
  }
  { contrapose! 
    intro h
    rw [Set.not_infinite] at h
    let S2 : Finset ℕ := Set.Finite.toFinset h
    have h2 : ∃ B, ∀n ∈ S2, n ≤ B
    { use Finset.sup S2 id
      intro n hn
      apply Finset.le_sup hn }
    cases' h2 with N hN
    use N
    have h3 : ∀n : ℕ, n ∈ S ↔ n ∈ S2 := by
      intro n
      exact (Set.Finite.mem_toFinset h).symm
    intros n hn h4
    rw [h3] at h4
    specialize hN n h4
    linarith
  }

-- Another way of stating the question (note different "|" symbols:
-- there's `|` for "such that" in set theory and `\|` for "divides" in number theory)
lemma infinite_set_of_solutions : {n : ℕ | 5 ∣ 4*n^2+1 ∧ 13 ∣ 4*n^2+1}.Infinite := by
  rw [infinite_iff_arb_large]
  exact arb_large_soln
