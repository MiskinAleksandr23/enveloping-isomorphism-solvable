import EnvelopingIsomorphism.Deformation.InsertionSum

/-! Scalar sign identities used in the finite Gerstenhaber cancellation. -/

namespace EnvelopingIsomorphism.Deformation

variable {R : Type*} [CommRing R]

theorem insertionSign_square (n : ℕ) : ((-1 : R) ^ n) * ((-1 : R) ^ n) = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  simp

theorem insertionSign_even_shift (p q : ℕ) : (-1 : R) ^ (p + 2 * q) = (-1 : R) ^ p := by
  rw [pow_add, pow_mul]
  simp

theorem insertionSign_degree (i n : ℕ) : (-1 : R) ^ (i * (n + 2)) = (-1 : R) ^ (i * n) := by
  rw [Nat.mul_add, Nat.mul_comm i 2, insertionSign_even_shift]

theorem insertionSign_nested (i j n r : ℕ) :
    ((-1 : R) ^ (i * n)) * ((-1 : R) ^ ((i + j) * r)) =
      ((-1 : R) ^ (i * (n + r))) * ((-1 : R) ^ (j * r)) := by
  simp only [Nat.add_mul, Nat.mul_add, pow_add]
  ac_rfl

theorem insertionSign_after (i j n r : ℕ) :
    ((-1 : R) ^ (i * n)) * ((-1 : R) ^ ((j + n) * r)) =
      ((-1 : R) ^ (n * r)) * (((-1 : R) ^ (j * r)) * ((-1 : R) ^ (i * n))) := by
  simp only [Nat.add_mul, pow_add]
  ac_rfl

theorem insertionSign_before (i j n r : ℕ) :
    ((-1 : R) ^ (i * n)) * ((-1 : R) ^ (j * r)) =
      ((-1 : R) ^ (n * r)) * (((-1 : R) ^ (j * r)) * ((-1 : R) ^ ((i + r) * n))) := by
  simp only [Nat.add_mul, pow_add, Nat.mul_comm r n]
  calc
    _ = 1 * (((-1 : R) ^ (i * n)) * ((-1 : R) ^ (j * r))) := (one_mul _).symm
    _ = (((-1 : R) ^ (n * r)) * ((-1 : R) ^ (n * r))) *
        (((-1 : R) ^ (i * n)) * ((-1 : R) ^ (j * r))) := by
      rw [insertionSign_square]
    _ = _ := by ac_rfl

variable {A : Type*} [AddCommGroup A] [Module R A]

/-- For positive inner arity, the exponent may be written using its shifted degree. -/
theorem curriedPreLie_pos_eq_sum (m n : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A (n + 1)) :
    curriedPreLie (n + 1) m f g =
      ∑ i : Fin (m + 1), (-1 : R) ^ (i.val * n) • curriedInsertAt m (n + 1) i f g := by
  rw [curriedPreLie_eq_sum_apply]
  simp only [insertionSign_degree]

end EnvelopingIsomorphism.Deformation
