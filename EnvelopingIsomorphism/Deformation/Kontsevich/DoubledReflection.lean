import EnvelopingIsomorphism.Deformation.Kontsevich.ConfigurationTopology

/-! The actual conjugation involution on original and doubled configuration labels. -/

namespace EnvelopingIsomorphism.Deformation.Kontsevich.Configuration

open ComplexConjugate

def doubledReflection {n m : ℕ} : DoubledLabel n m → DoubledLabel n m
  | Sum.inl (Sum.inl j) => Sum.inr j
  | Sum.inl (Sum.inr j) => Sum.inl (Sum.inr j)
  | Sum.inr j => Sum.inl (Sum.inl j)

theorem doubledReflection_involutive {n m : ℕ} :
    Function.Involutive (doubledReflection : DoubledLabel n m → _) := by
  intro v
  rcases v with (j | j) | j <;> rfl

@[simp] theorem doubledReflection_boundary {n m : ℕ} (j : Fin m) :
    (doubledReflection (n := n) (Sum.inl (Sum.inr j))) = Sum.inl (Sum.inr j) := rfl

theorem doubledPoint_reflection {n m : ℕ} (c : Configuration n m) (v : DoubledLabel n m) :
    c.doubledPoint (doubledReflection v) = conj (c.doubledPoint v) := by
  rcases v with (j | j) | j <;> simp [doubledReflection, doubledPoint, vertexPoint]

end EnvelopingIsomorphism.Deformation.Kontsevich.Configuration
