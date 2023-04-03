/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import Mathlib.Tactic.Basic
set_option linter.unusedVariables false

/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases'`
* `constructor`

For pros, there's also `rintro`, `rcases`, `refine ⟨_, _⟩` 

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variable (P Q R : Prop)

example : P ∧ Q → P := by
  intro hPaQ
  cases' hPaQ with hP hQ
  exact hP

example : P ∧ Q → Q := by
  rintro ⟨hP, hQ⟩
  assumption

example : (P → Q → R) → (P ∧ Q → R) := by
  rintro hPQR ⟨hP, hQ⟩
  apply hPQR <;>
  assumption
  
example : P → Q → P ∧ Q := by
  intro hP
  intro hQ
  constructor
  { exact hP }
  { exact hQ }

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  rintro ⟨hP, hQ⟩
  exact ⟨hQ, hP⟩

example : P → P ∧ True := by
  intro hP
  constructor
  { exact hP }
  { trivial }

example : False → P ∧ False := by
  intro h
  exfalso
  exact h

/-- `∧` is transitive -/
example : (P ∧ Q) → (Q ∧ R) → (P ∧ R) := by
  rintro ⟨hP, hQ⟩ ⟨_, hR⟩
  exact ⟨hP, hR⟩

example : ((P ∧ Q) → R) → (P → Q → R) := by
  intros h hP hQ
  apply h
  constructor <;> 
  assumption



