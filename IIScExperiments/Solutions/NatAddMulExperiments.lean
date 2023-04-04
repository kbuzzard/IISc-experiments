import Mathlib.Algebra.Group.Defs

inductive MyNat : Type
| zero : MyNat
| succ : MyNat → MyNat

namespace MyNat

-- notational typeclass for 0
instance : Zero MyNat where
  zero := MyNat.zero

#check (0 : MyNat)

theorem induction : {P : MyNat → Prop} →
  (t : MyNat) → (zero : P (0 : MyNat)) → (succ : (a : MyNat) → P a → P (a.succ)) → P t :=
fun {_} t zero succ => MyNat.rec zero succ t

def add (a : MyNat) : MyNat → MyNat
| zero => a
| (succ b) => succ (add a b)

-- notational typeclass for `+`
instance : Add MyNat where
  add := add

theorem add_zero (a : MyNat) : a + 0 = a := rfl

theorem add_succ (a b : MyNat) : a + succ b = succ (a + b) := rfl

theorem zero_add (a : MyNat) : 0 + a = a := by
  induction' a using MyNat.induction with d hd
  · rw [add_zero]
  · rw [add_succ, hd]

theorem succ_add (a b : MyNat) : succ a + b = succ (a + b) := by
  induction' b using MyNat.induction with d hd
  · rw [add_zero, add_zero]
  · rw [add_succ, add_succ, hd]

theorem add_comm (a b : MyNat) : a + b = b + a := by
  induction' b using MyNat.induction with d hd
  · rw [add_zero, zero_add]
  · rw [add_succ, succ_add, hd]

theorem add_assoc (a b c : MyNat) : (a + b) + c = a + (b + c) := by
  induction' c using MyNat.induction with d hd
  · rw [add_zero, add_zero]
  · rw [add_succ, add_succ, add_succ, hd]

theorem add_add_add (a b c d : MyNat) : (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [add_assoc, ← add_assoc b, add_comm b, add_assoc c, ← add_assoc a]

--theorem add_right_comm (a b c : MyNat) : a + b + c = a + c + b := by
--  rw [add_assoc, add_comm b, add_assoc]

def mul (a : MyNat) : MyNat → MyNat
| zero => zero
| (succ b) => mul a b + a

instance : Mul MyNat where
  mul := mul

def one : MyNat := succ 0

instance : One MyNat where
  one := MyNat.one

lemma one_def : 1 = succ 0 := rfl

theorem mul_zero (a : MyNat) : a * 0 = 0 := rfl

theorem mul_succ (a b : MyNat) : a * succ b = a * b + a := rfl

theorem zero_mul (a : MyNat) : 0 * a = 0 := by
  induction' a using MyNat.induction with d hd
  · rw [mul_zero]
  · rw [mul_succ, hd, add_zero]

theorem succ_eq_add_one (a : MyNat) : succ a = a + 1 := by
  rw [one_def, add_succ, add_zero]

theorem mul_one (a : MyNat) : a * 1 = a := by
  rw [one_def, mul_succ, mul_zero, zero_add]

theorem one_mul (a : MyNat) : one * a = a := by
  induction' a using MyNat.induction with d hd
  · rw [mul_zero]
  · rw [mul_succ, hd, one, add_succ, add_zero]

theorem succ_mul (a b : MyNat) : succ a * b = a * b + b := by
  induction' b using MyNat.induction with d hd
  · rw [mul_zero, mul_zero, add_zero]
  · rw [mul_succ, hd, mul_succ, succ_eq_add_one, succ_eq_add_one, add_add_add]

-- lemma mul_add (t a b : mynat) : t * (a + b) = t * a + t * b :=
-- lemma mul_assoc (a b c : mynat) : (a * b) * c = a * (b * c) :=
-- lemma succ_mul (a b : mynat) : succ a * b = a * b + b :=
-- lemma add_mul (a b t : mynat) : (a + b) * t = a * t + b * t :=
-- lemma mul_comm (a b : mynat) : a * b = b * a :=
end MyNat
