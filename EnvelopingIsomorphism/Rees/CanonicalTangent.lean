import EnvelopingIsomorphism.Rees.ReflectionSource
import EnvelopingIsomorphism.Deformation.Gauge.CanonicalTangentExactness

/-! The canonical graph tangent uses exactly the existing shared recovered Rees
source complex and its actual MC points. All identifications preserve values. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace EnvelopingIsomorphism.Rees.CanonicalTangent

open EnvelopingIsomorphism.Deformation EnvelopingIsomorphism.FormalSeries
open Gauge

variable {k L M : Type*} [Field k] [CharZero k]
  [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]
  (D : Identification.RecoveredData k L M)

local instance : CharZero (LaurentSchouten.Scalars k) := LaurentSchouten.scalarCharZero

abbrev baseCoefficient := PoissonMCFamily.constantBivector D.sourceWeightData

@[simp] theorem base_eq :
    CanonicalTangentExactness.baseBivector k D.size (baseCoefficient D) = ReflectionSource.base D := rfl

theorem base_isMaurerCartan : (polynomialSchoutenDGLA k D.size).laurent.IsMaurerCartan
    (CanonicalTangentExactness.baseBivector k D.size (baseCoefficient D)) :=
  ReflectionSource.base_isMaurerCartan D

@[simp] theorem sourceComplex_eq :
    LaurentSchouten.sourceComplex
      (CanonicalTangentExactness.baseBivector k D.size (baseCoefficient D)) (base_isMaurerCartan D) =
        ReflectionSource.Complex D := rfl

@[simp] theorem quadratic_eq :
    LaurentSchouten.sourceQuadratic
      (CanonicalTangentExactness.baseBivector k D.size (baseCoefficient D)) (base_isMaurerCartan D) =
        ReflectionSource.Quadratic D := rfl

/-- The actual canonical source MC type, on the same native quadratic operator. -/
abbrev SourceMC := LaurentSchouten.SourceMC
  (CanonicalTangentExactness.baseBivector k D.size (baseCoefficient D)) (base_isMaurerCartan D)

/-- This equivalence is the identity, including all Laurent coefficients. -/
def sourceMCEquiv : SourceMC D ≃ ReflectionSource.MC D := Equiv.refl _

@[simp] theorem sourceMCEquiv_val (b : SourceMC D) : (sourceMCEquiv D b).val = b.val := rfl
@[simp] theorem sourceMCEquiv_symm_val (b : ReflectionSource.MC D) :
    ((sourceMCEquiv D).symm b).val = b.val := rfl

abbrev source : SourceMC D := ReflectionSource.source D
abbrev target : SourceMC D := ReflectionSource.target D

@[simp] theorem source_val : (source D).val = PoissonMCFamily.perturbationSeries D.sourceWeightData := rfl
@[simp] theorem target_val : (target D).val = PoissonMCFamily.perturbationSeries D.targetWeightData := rfl

section CanonicalGraph
variable [Algebra ℝ k]

abbrev baseStar := CanonicalTangentExactness.baseStar k D.size (baseCoefficient D)
abbrev StarAssociative := CanonicalTangentExactness.StarAssociative k D.size (baseCoefficient D)
abbrev LowChainIdentity := CanonicalTangentExactness.LowChainIdentity k D.size (baseCoefficient D)

variable (hμ : StarAssociative D) (hc : LowChainIdentity D)

/-- The actual tangent already has the terminal reflection source type. -/
def tangent : LowTangent (ReflectionSource.Complex D)
    (LaurentConjugation.targetComplex (baseStar D) hμ) :=
  CanonicalTangentExactness.tangent k D.size (baseCoefficient D) (base_isMaurerCartan D) hμ hc

@[simp] theorem tangent_zero : (tangent D hμ hc).zero =
    CanonicalTangentExactness.zeroMap k D.size (baseCoefficient D) := rfl

@[simp] theorem tangent_one : (tangent D hμ hc).one =
    CanonicalTangentExactness.oneMap k D.size (baseCoefficient D) := rfl

instance tangent_isMiddleExact : (tangent D hμ hc).IsMiddleExact :=
  CanonicalTangentExactness.tangent_isMiddleExact k D.size (baseCoefficient D)
    (base_isMaurerCartan D) hμ hc

end CanonicalGraph
end EnvelopingIsomorphism.Rees.CanonicalTangent
