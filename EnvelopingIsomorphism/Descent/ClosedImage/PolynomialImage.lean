import EnvelopingIsomorphism.Descent.ClosedImage
import EnvelopingIsomorphism.Descent.ClosedImage.AffinePoints
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.FinitePresentation

/-! # Constructible polynomial images on algebraically closed field points -/

namespace EnvelopingIsomorphism.Descent

open Set Topology TopologicalSpace MvPolynomial

namespace AffinePoint

variable {k σ τ : Type*} [Field k] [Finite σ] [Finite τ]

instance : NoetherianSpace (AffinePoint k σ) :=
  isInducing_toPrime.noetherianSpace

theorem finitePresentation_aeval (F : τ → MvPolynomial σ k) :
    (aeval (R := k) F).toRingHom.FinitePresentation := by
  apply RingHom.FinitePresentation.of_finiteType.mp
  apply RingHom.FiniteType.of_comp_finiteType
    (f := algebraMap k (MvPolynomial τ k))
  have heq : (aeval (R := k) F).toRingHom.comp (algebraMap k (MvPolynomial τ k)) =
      algebraMap k (MvPolynomial σ k) := (aeval F).comp_algebraMap
  rw [heq, RingHom.finiteType_algebraMap]
  infer_instance

/-- Chevalley's theorem for finite polynomial maps on affine algebraic sets over
an algebraically closed field, stated directly on field-valued points. -/
theorem isConstructible_polynomialMap_image_zeros [IsAlgClosed k]
    (I : Ideal (MvPolynomial σ k)) (F : τ → MvPolynomial σ k) :
    IsConstructible (polynomialMap F '' zeros I) := by
  rw [polynomialMap_image_zeros_eq_preimage]
  apply IsConstructible.preimage continuous_toPrime
  · intro U hU hUc V hVc hV
    exact NoetherianSpace.isCompact _
  · apply PrimeSpectrum.isConstructible_comap_image (finitePresentation_aeval F)
    exact ((NoetherianSpace.isCompact _).isConstructible
      (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl).of_compl

end AffinePoint

end EnvelopingIsomorphism.Descent
