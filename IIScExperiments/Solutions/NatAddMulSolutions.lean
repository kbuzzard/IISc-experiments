import Mathlib.Algebra.Group.Defs

-- Define naturals recursively: 
inductive MyNat : Type
  -- zero is a natural;
| zero : MyNat
  -- the successor of a natural is a natural;
| succ : MyNat → MyNat
  -- and that's it

/-

What just happened? Lean added a new type (i.e set)
to the system, called `MyNat`, with an element `MyNat.zero`,
a function `succ : MyNat → MyNat`, and a principle
of induction/recursion (these are the same thing in Lean).
 
#check MyNat
#check MyNat.zero
#check @MyNat.succ
#check MyNat.rec

-/

namespace MyNat

-- definitions of some simple numbers

def one : MyNat := succ zero
def two : MyNat := succ one
def three : MyNat := succ two
def four : MyNat := succ three

-- this doesn't compile, because addition is not defined yet
-- example : two + two = four := sorry

-- Similarly, we can't prove succ(d)=d+1 because we
-- haven't defined addition yet. So let's do this.

-- We now define the (n + ⬝) function by recursion.
def add (n : MyNat) : MyNat → MyNat
| zero => n -- n + 0 is defined to be n
| (succ d) => succ (add n d) -- n + (succ d) is defined to be succ(n+d)

-- notation `0` for `MyNat.zero`
instance : Zero MyNat where
  zero := MyNat.zero

-- notation `1` for `MyNat.one`
instance : One MyNat where 
  one := MyNat.one

-- notation `a + b` for `MyNat.add a b`
instance : Add MyNat where
  add := MyNat.add

-- This lemma is true *by definition* so the proof is `rfl`,
-- which is the axiom saying that equality is reflexive.
lemma add_zero (n : MyNat) : n + 0 = n := by
  rfl

-- This lemma is also true by definition, so the proof is `rfl`
lemma add_succ (n m : MyNat) : n + succ m = succ (n + m) := by
  rfl

-- This lemma is also true by definition, because (writing s for succ)
-- 2+2=2+s(1)=s(2+1)=s(2+s0)=s(s(2+0))=s(s(2))=s(3)=4, and
-- each intermediate equality is true by definition.
lemma easy : two + two = four := by
  rfl

-- Both sides are defitionally s(s(s(0)))
lemma easy2 : two + one = one + two := by
  rfl

-- But ∀ a b, a + b = b + a is *not* true by definition; you need
-- to prove this by induction.

-- Here is some boilerplate to get the `induction'` tactic to work nicely
@[eliminator]
theorem induction : {P : MyNat → Prop} →
  (t : MyNat) → (zero : P (0 : MyNat)) → (succ : (a : MyNat) → P a → P (a.succ)) → P t :=
fun {_} t zero succ => MyNat.rec zero succ t

-- If you try and prove `add_comm` directly by induction, you can't even
-- do the base case! a + 0 = 0 + a; well, a + 0 = a by definition, but
-- 0 + a isn't a by definition, it's a by induction. So let's prove this first.
lemma zero_add (n : MyNat) : 0 + n = n := by
  induction' n with d hd
  { rfl } -- base case 0 + 0 = 0 true by definition
  { rw [add_succ] -- inductive step
    rw [hd] }

-- To prove the inductive step for a+b=b+a you need `succ_add`,
-- the complement of `add_succ`. Note the naminh convention.
lemma succ_add (a b : MyNat) : (succ a) + b = succ (a + b) := by
  induction' b with d hd
  -- base case
  { rfl }
  -- inductive step
  { rw [add_succ, add_succ, hd] }

-- Now we can prove commutativity of addition
lemma add_comm (a b : MyNat) : a + b = b + a := by
  induction' b with d hd
  -- base case
  · rw [add_zero]
    rw [zero_add]
  -- inductive step
  · rw [add_succ]
    rw [hd]
    rw [succ_add]

-- Addition is defined by recursion on the right, so when proving
-- associativity it's easiest to do induction on the rightmost variable.
lemma add_assoc (a b c : MyNat) : (a + b) + c = a + (b + c) := by
  induction' c with d hd
  · rfl
  · rw [add_succ, hd]
    rfl

-- Conclusion: naturals are an additive commutative monoid!
instance : AddCommMonoid MyNat where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm

-- See if you can do this one
theorem add_add_add (a b c d : MyNat) : (a + b) + (c + d) = (a + c) + (b + d) := by
  sorry -- just use associativity and commutativity

-- Mahesh asked why 0 ≠ 1. It's because recursion allows you to
-- make this definition
def is_zero : MyNat → Prop
| zero => True
| (succ _) => False

-- Now set up the API for this definition:

lemma is_zero_zero_eq_True : is_zero (0 : MyNat) = True := by
  rfl

lemma is_zero_succ_eq_False (n : MyNat) : is_zero (succ n) = False := by
  rfl

lemma is_zero_one_eq_False : is_zero 1 = False :=
  is_zero_succ_eq_False 0

-- Proof that 0 ≠ 1:
lemma zero_ne_one : (0 : MyNat) ≠ 1 := by
  intro h
  rw [← is_zero_one_eq_False]
  rw [← h]
  rw [is_zero_zero_eq_True]
  trivial

-- To prove injectivity of `succ` we use the `pred` definition
def pred : MyNat → MyNat
| zero => four -- a junk value: zero has no predecessor
| succ n => n

-- We will never use pred zero (like we never divide by 0)

lemma pred_succ (a : MyNat) : pred (succ a) = a := by
  rfl

theorem succ_inj (a b : MyNat) (h : succ a = succ b) : a = b := by
  suffices h : pred (succ a) = pred (succ b) by
  { rw [pred_succ, pred_succ] at h
    exact h }
  rw [h]

-- Can you do multiplication?

def mul (a : MyNat) : MyNat → MyNat
| zero => zero
| (succ b) => mul a b + a

instance : Mul MyNat where
  mul := mul

lemma one_def : 1 = succ 0 := rfl

theorem mul_zero (a : MyNat) : a * 0 = 0 := rfl

theorem mul_succ (a b : MyNat) : a * succ b = a * b + a := rfl

-- Induction will be crucial for the rest
theorem zero_mul (a : MyNat) : 0 * a = 0 := by
  sorry

theorem succ_eq_add_one (a : MyNat) : succ a = a + 1 := by
  sorry

theorem mul_one (a : MyNat) : a * 1 = a := by
  sorry

theorem one_mul (a : MyNat) : one * a = a := by
  sorry

theorem succ_mul (a b : MyNat) : succ a * b = a * b + b := by
  sorry
  
lemma mul_add (t a b : MyNat) : t * (a + b) = t * a + t * b := by
  sorry

lemma mul_assoc (a b c : MyNat) : (a * b) * c = a * (b * c) := by
  sorry

lemma succ_mul (a b : MyNat) : succ a * b = a * b + b := by
  sorry

lemma add_mul (a b t : MyNat) : (a + b) * t = a * t + b * t := by
  sorry

lemma mul_comm (a b : MyNat) : a * b = b * a := by
  sorry

end MyNat
