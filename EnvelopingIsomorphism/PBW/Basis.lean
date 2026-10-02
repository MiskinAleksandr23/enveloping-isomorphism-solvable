import EnvelopingIsomorphism.PBW.Compatibility
import EnvelopingIsomorphism.PBW.WordIndex
import EnvelopingIsomorphism.PBW.Presentation
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Ordered PBW coordinates, indexed by exponent vectors. -/

noncomputable section

namespace EnvelopingIsomorphism.PBW

variable {R L α : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable [LinearOrder α] (b : Module.Basis α R L)

/-- Irreducible words are equivalently finitely supported exponent vectors. -/
def normalIndexEquiv : {w // (reductionSystem b).Normal w} ≃ (α →₀ ℕ) where
  toFun w := wordIndex w.val
  invFun m := ⟨orderedWord m, (normal_iff_pairwise b _).2 (pairwise_orderedWord m)⟩
  left_inv w := Subtype.ext (orderedWord_wordIndex ((normal_iff_pairwise b _).1 w.property))
  right_inv := wordIndex_orderedWord

/-- The PBW basis of the module given by the enveloping presentation. -/
def quotientPBWBasis : Module.Basis (α →₀ ℕ) R
    ((List α →₀ R) ⧸ (reductionSystem b).relations) :=
  ((reductionSystem b).quotientBasis (reductionSystem_compatible b)).reindex
    (normalIndexEquiv b)

@[simp] theorem quotientPBWBasis_apply (m : α →₀ ℕ) :
    quotientPBWBasis b m = Submodule.Quotient.mk (Finsupp.single (orderedWord m) 1) := by
  simp [quotientPBWBasis, normalIndexEquiv]

@[simp] theorem orderedWord_zero : orderedWord (0 : α →₀ ℕ) = [] := by
  simpa using (orderedWord_wordIndex (show ([] : List α).Pairwise (· ≤ ·) by simp))

@[simp] theorem orderedWord_single (i : α) :
    orderedWord (Finsupp.single i 1) = [i] := by
  simpa using (orderedWord_wordIndex (List.pairwise_singleton (α := α) (R := (· ≤ ·)) i))

/-- The Poincaré–Birkhoff–Witt basis of the native universal enveloping algebra.
It works over any commutative ring for a Lie algebra equipped with a basis. -/
def pbwBasis : Module.Basis (α →₀ ℕ) R (UniversalEnvelopingAlgebra R L) :=
  (quotientPBWBasis b).map (presentationEquiv b)

@[simp] theorem pbwBasis_apply (m : α →₀ ℕ) :
    pbwBasis b m =
      ((orderedWord m).map (UniversalEnvelopingAlgebra.ι R ∘ b)).prod := by
  simp [pbwBasis]

@[simp] theorem pbwBasis_zero : pbwBasis b 0 = 1 := by simp

@[simp] theorem pbwBasis_single (i : α) :
    pbwBasis b (Finsupp.single i 1) = UniversalEnvelopingAlgebra.ι R (b i) := by
  simp

/-- The images of the original basis vectors remain linearly independent in the UEA. -/
theorem linearIndependent_ι_basis :
    LinearIndependent R (UniversalEnvelopingAlgebra.ι R ∘ b) := by
  have hi : Function.Injective (fun i : α ↦ Finsupp.single i (1 : ℕ)) := by
    intro i j h
    have hw := congrArg orderedWord h
    simpa using hw
  simpa only [Function.comp_def, pbwBasis_single] using
    (pbwBasis b).linearIndependent.comp (fun i : α ↦ Finsupp.single i (1 : ℕ)) hi

include b in
/-- PBW implies that the canonical Lie homomorphism is injective over any free module. -/
theorem ι_injective_of_basis : Function.Injective (UniversalEnvelopingAlgebra.ι R (L := L)) := by
  exact LinearMap.injective_of_linearIndependent b.span_eq (linearIndependent_ι_basis b)

/-- In particular, the canonical map is injective for every finite-dimensional Lie algebra. -/
theorem ι_injective (k L : Type*) [Field k] [LieRing L] [LieAlgebra k L]
    [Module.Finite k L] : Function.Injective (UniversalEnvelopingAlgebra.ι k (L := L)) :=
  ι_injective_of_basis (Module.finBasis k L)

end EnvelopingIsomorphism.PBW
