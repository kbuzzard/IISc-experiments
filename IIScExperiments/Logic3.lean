/-false
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic.Basic
set_option linter.unusedVariables false

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → False`. So `¬ P` and `P → False`
are *definitionally equal*. 
## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `change`
* `by_contra` or `by_cases`

-/

-- Throughout this sheet, `P` and `Q` will denote propositions.

variable (P Q : Prop)

example : ¬ True → False := by
  sorry

example : False → ¬ True := by
  sorry

example : ¬ False → True := by
  sorry

example : True → ¬ False := by
  sorry

example : False → ¬ P := by
  sorry

example : P → ¬ P → False := by
  sorry

example : P → ¬ (¬ P) := by
  sorry

example : (P → Q) → (¬ Q → ¬ P) := by
  sorry

example : ¬ ¬ False → False := by
  sorry

example : ¬ ¬ P → P := by
  sorry

example : (¬ Q → ¬ P) → (P → Q) := by
  sorry