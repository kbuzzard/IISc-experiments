/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
set_option linter.unusedVariables false
/-!

# Logic in Lean, example sheet 1 : "implies" (`→`)

We learn about propositions, and implications `P → Q` between them. You can get
this arrow by typing `\to` or `\r`. Mathematicians usually write the
implication arrow as `P ⇒ Q` but Lean prefers a single arrow.

## The absolute basics

`P : Prop` means that `P` is a true-false statement. `h : P` means
that `h` is a proof that `P` is true, or you can regard `h` as an
assumption that `P` is true; logically these are the same. Stuff above
the `⊢` symbol is your assumptions. The statement to the right of it is
the goal. Your job is to prove the goal from the assumptions.

## Tactics you will need

To solve the levels on this sheet you will need to know how to use the
following three tactics:

* `intro`
* `exact`
* `apply`

We'll be learning about 10 tactics in total to do logic.

## Worked examples

Click around in the proofs to see the tactic state (on the right) change.
The tactic is implemented and the state changes just before the comma.
I will use the following conventions: variables with capital
letters like `P`, `Q`, `R` denote propositions
(i.e. true/false statements) and variables whose names begin
with `h` like `h1` or `hP` are proofs or hypotheses.

-/ 

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

-- Here are some examples of `intro`, `exact` and `apply` being used.

-- Assume that `P` and `Q` and `R` are all true. Deduce that `P` is true.
example (hP : P) (hQ : Q) (hR : R) : P := by
  -- note that `exact P` doesn't work! `P` is the *statement*,
  -- and `hP` is the *proof*.
  exact hP

-- Same example: assume that `P` and `Q` and `R` are true, but this time
-- give the assumptions silly names. Deduce that `P` is true.
example (fish : P) (giraffe : Q) (dodecahedron : R) : P := by
  exact fish -- `fish` is the name of the assumption that `P` is true (but `hP` is a better name)

-- Assume `Q` is true. Prove that `P → Q`. 
example (hQ : Q) : P → Q := by
  -- the goal is of the form `X → Y` so we can use `intro`
  intro hP
  -- Our goal is now the same as a hypothesis so we can use `exact`
  exact hQ

-- Assume `P → Q` and `P` is true. Deduce `Q`.
example (h : P → Q) (hP : P) : Q := by
  apply h
  exact hP

/-

## Examples for you to try

Delete the `sorry`s and replace them with comma-separated tactic proofs
using `intro`, `exact` and `apply`.

-/

/-- Every proposition implies itself. -/
example : P → P := by
  sorry

/-

Note that `→` is not associative: in general `P → (Q → R)` and `(P → Q) → R`
might not be equivalent. This is like subtraction on numbers -- in general
`a - (b - c)` and `(a - b) - c` might not be equal.

So if we write `P → Q → R` then we'd better know what this means.
The convention in Lean is that it means `P → (Q → R)`. If you think
about it, this means that to deduce `R` you will need to prove both `P`
and `Q`. In general to prove `P1 → P2 → P3 → ... Pn` you can assume
`P1`, `P2`,...,`P(n-1)` and then you have to prove `Pn`. 

So the next level is asking you prove that `P → (Q → P)`.

-/
example : P → Q → P := by
  sorry

/-- If we know `P`, and we also know `P → Q`, we can deduce `Q`. 
This is called "Modus Ponens" by logicians. -/
example : P → (P → Q) → Q := by
  sorry

/-- `→` is transitive. That is, if `P → Q` and `Q → R` are true, then
  so is `P → R`. -/
example : (P → Q) → (Q → R) → (P → R) := by
  sorry

-- If `h : P → Q → R` with goal `⊢ R` and you `apply h`, you'll get
-- two goals! Note that tactics operate on only the first goal.
example : (P → Q → R) → (P → Q) → (P → R) := by
  sorry

/- 

Here are some harder puzzles. They won't teach you anything new about
Lean, they're just trickier. If you're not into logic puzzles
and you feel like you understand `intro`, `exact` and `apply`
then you can just skip these and move onto the next sheet
in this section, where you'll learn some more tactics.

-/

variable (S T : Prop)

example : (P → R) → (S → Q) → (R → T) → (Q → R) → S → T := by
  sorry

example : (P → Q) → ((P → Q) → P) → Q := by
  sorry

example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P := by
  sorry

example : ((Q → P) → P) → (Q → R) → (R → P) → P := by
  sorry

example : (((P → Q) → Q) → Q) → (P → Q) := by
  sorry

example :
    (((P → Q → Q) → ((P → Q) → Q)) → R) →
    ((((P → P) → Q) → (P → P → Q)) → R) →
    (((P → P → Q) → ((P → P) → Q)) → R) → R := by
  sorry

