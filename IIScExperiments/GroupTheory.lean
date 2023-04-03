import Mathlib

/-- `MyGroup G` is the type of group structures on `G`, with
group law equal to multiplication. To use, write `[MyGroup G]`
and typeclass inference will take care of the rest. -/
class MyGroup (G : Type) extends One G, Mul G, Inv G : Type :=
(mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c))
(one_mul : ∀ a : G, 1 * a = a)
(inv_mul_self : ∀ a : G, a⁻¹ * a = 1)

/-

Let's not add these two axioms 

`(mul_one : ∀ a : G, a * 1 = a)`
`(mul_inv_self : ∀ a : G, a * a⁻¹ = 1)`

because they can be deduced from the three axioms we have!
They are so important, that the first thing we should do is
to prove them.

-/

variable (G : Type) in
#check MyGroup G -- it's a Type. It's "the set of all group structure on G"

namespace MyGroup

-- Let `G` be a group, and let `a`, `b` and `c` be elements of `G`.
variable {G : Type} [MyGroup G] (a b c : G)

-- A calculation shows that we can cancel on the left.
-- The calculation is: b = 1 * b = (a⁻¹ * a) * b = a⁻¹ * (a * b)
-- and now a * b = a * c and then do the same argument backwards.
lemma mul_left_cancel (h : a * b = a * c) : b = c := 
  sorry

lemma mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : 
    a * b = c := by
  sorry

-- The first of the missing two axioms
lemma mul_one (a : G) : a * 1 = a := by 
--  rw [mul_eq_of_eq_inv_mul, inv_mul_self] -- apparently too little info
  sorry

-- And the second
lemma mul_inv_self (a : G) : a * a⁻¹ = 1 := by
  sorry

/- Our next goal is to make Lean's simplifier able to solve
   goals like the below:

example (G : Type) [MyGroup G] (a b : G) : 
    (b⁻¹ * a⁻¹)⁻¹ * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * 1 * a = 1 := sorry


-/

-- We start by telling the simplifier about the axioms
attribute [simp]  one_mul mul_one inv_mul_self mul_inv_self mul_assoc

/-

Right now the simp set is not "confluent". When faced with
`(a⁻¹ * a) * b`, if the simplifier uses `inv_mul_self`
and then `one_mul` it simplifies the expression to `b`.
But if it uses `mul_assoc` first then it ends up 
as `a⁻¹ * (a * b)` which currenly doesn't simplify further.
Let's fix this problem, and the analogous problem 
with `(a * a⁻¹) * b`, by adding the appropriate lemmas
to the simp set.
-/

@[simp] lemma inv_mul_cancel_left : a⁻¹ * (a * b) = b := by
  sorry

@[simp] lemma mul_inv_cancel_left : a * (a⁻¹ * b) = b := by
  sorry

/- We're still not done: we don't know how inverse interacts
with the group structure. We don't know 1⁻¹, we don't
know (a⁻¹)⁻¹, and we don't know (a * b)⁻¹. Let's fix this.
Then we'll be done. We start with a preliminary lemma about
how left and right inverses in a group must coincide.
-/

lemma left_inv_eq_right_inv {a b c : G} (h1 : b * a = 1) (h2 : a * c = 1) : 
    b = c := by
  sorry

-- We now characterise `a⁻¹` as being the unique `b` such
-- that `a * b = 1`. This gives us a technique for proving
-- theorems about inverses.
lemma mul_eq_one_iff_eq_inv : a * b = 1 ↔ a⁻¹ = b := 
  sorry

-- Now we add three lemmas to the simp set explaining
-- how inverse interacts with 1, ⁻¹ and *. 
@[simp] lemma one_inv : (1 : G)⁻¹ = 1 := by
  sorry

@[simp] lemma inv_inv : (a⁻¹)⁻¹ = a := by
  sorry

@[simp] lemma mul_inv_rev : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry

-- And now we're done.
-- example of Knuth-Bendix theorem
example (G : Type) [MyGroup G] (a b : G) : 
  (b⁻¹ * a⁻¹)⁻¹ * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1 := by simp

-- bonus puzzle : if g^2=1 for all g in G, then G is abelian
example (G : Type) [MyGroup G] (h : ∀ g : G, g * g = 1) :
    ∀ g h : G, g * h = h * g := by
  -- hint: start with 
  -- `have hinv : ∀ g : G, g⁻¹ = g`
  sorry
