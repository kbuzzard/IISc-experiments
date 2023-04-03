import Mathlib.GroupTheory.FreeGroup

class MyGroup (G : Type) extends One G, Mul G, Inv G : Type :=
(mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c))
(one_mul : ∀ a : G, 1 * a = a)
(inv_mul_self : ∀ a : G, a⁻¹ * a = 1)

namespace MyGroup

variable {G : Type} [MyGroup G] (a b c : G)

lemma mul_left_cancel (h : a * b = a * c) : b = c := by
calc
     b = 1 * b         := by rw [one_mul]
     _ = a⁻¹ * a * b   := by rw [inv_mul_self]
     _ = a⁻¹ * (a * b) := by rw [mul_assoc]
     _ = a⁻¹ * (a * c) := by rw [h]
     _ = a⁻¹ * a * c   := by rw [mul_assoc]
     _ = 1 * c         := by rw [inv_mul_self]
     _ = c             := by rw [one_mul]

lemma mul_left_cancel' (h : a * b = a * c) : b = c := by
  rw [← one_mul b, ← inv_mul_self a, mul_assoc, h, ← mul_assoc, inv_mul_self, one_mul]

lemma mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : a * b = c := by
  apply mul_left_cancel a⁻¹
  rw [← mul_assoc, inv_mul_self, one_mul, h]

lemma mul_one (a : G) : a * 1 = a := by
  apply mul_eq_of_eq_inv_mul
  rw [inv_mul_self]

lemma mul_inv_self (a : G) : a * a⁻¹ = 1 := by
  apply mul_eq_of_eq_inv_mul
  rw [mul_one]

attribute [simp] mul_assoc one_mul mul_one inv_mul_self mul_inv_self 

@[simp] lemma inv_mul_cancel_left : a⁻¹ * (a * b) = b := by
  simp [← mul_assoc]

@[simp] lemma mul_inv_cancel_left : a * (a⁻¹ * b) = b := by
  simp [← mul_assoc]

lemma left_inv_eq_right_inv {a b c : G} (h1 : b * a = 1) (h2 : a * c = 1) : 
    b = c := by
  have h : b * (a * c) = (b * a) * c := (mul_assoc b a c).symm
  simpa [h2, h1] using h

lemma mul_eq_one_iff_eq_inv : a * b = 1 ↔ a⁻¹ = b :=
⟨left_inv_eq_right_inv (inv_mul_self a), by
  rintro rfl
  simp⟩

@[simp] lemma one_inv : (1 : G)⁻¹ = 1 := by
  simp [← mul_eq_one_iff_eq_inv]

@[simp] lemma inv_inv : (a⁻¹)⁻¹ = a := by
  simp [← mul_eq_one_iff_eq_inv]

@[simp] lemma mul_inv_rev : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  simp [← mul_eq_one_iff_eq_inv]

-- example of Knuth-Bendix theorem
example (G : Type) [MyGroup G] (a b : G) : 
  (b⁻¹ * a⁻¹)⁻¹ * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1 := by simp

-- bonus puzzle : if g^2=1 for all g in G, then G is abelian
example (G : Type) [MyGroup G] (h : ∀ g : G, g * g = 1) :
  ∀ g h : G, g * h = h * g := by
  -- let's just change `h` to something
  -- more useful:
  simp [mul_eq_one_iff_eq_inv] at h
  intros a b
  rw [← h (a * b)]
  rw [mul_inv_rev]
  simp [h]
