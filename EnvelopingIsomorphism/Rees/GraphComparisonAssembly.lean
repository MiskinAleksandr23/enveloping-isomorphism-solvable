import EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraphComparison
import EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraphChain
import EnvelopingIsomorphism.Deformation.Gauge.LaurentSourceAlgebra
import EnvelopingIsomorphism.Rees.CanonicalGraphGauge
import EnvelopingIsomorphism.Poisson.ComparisonMatrix
import EnvelopingIsomorphism.Rees.CompletedPoissonBridge

/-! Actual canonical graph comparison and reflection on recovered Rees data.
The geometric MC/path identities and base associativity/low-chain identity are
explicit inputs. No middle-exactness or existence of a reflected gauge is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

namespace EnvelopingIsomorphism.Rees.GraphComparisonAssembly

open EnvelopingIsomorphism.Deformation EnvelopingIsomorphism.FormalSeries
open Gauge PowerSeriesModule
open scoped LaurentAlgebra

variable {k L M : Type*} [Field k] [CharZero k] [Algebra ℝ k]
  [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]
  (D : Identification.RecoveredData k L M)

local instance : CharZero (LaurentSeries k) := LaurentSchouten.scalarCharZero

abbrev PathIdentity := CanonicalGraph.PathIdentity k D.size (CanonicalTangent.baseCoefficient D)
  (CanonicalTangent.base_isMaurerCartan D)

variable (hμ : CanonicalTangent.StarAssociative D) (hc : CanonicalTangent.LowChainIdentity D)
variable (hMC : CanonicalGraphGauge.MCIdentity D) (hPath : PathIdentity D)

local instance : MulAction (LaurentSchouten.SourceGroup k D.size)
    (CanonicalGraph.SourceMC k D.size (CanonicalTangent.baseCoefficient D)
      (CanonicalTangent.base_isMaurerCartan D)) :=
  LaurentSchouten.sourceMulAction
    (CanonicalGraph.sourceBase k D.size (CanonicalTangent.baseCoefficient D))
    (CanonicalTangent.base_isMaurerCartan D)
local instance : MulAction (GaugeUnit (CanonicalGraph.OperatorRing k D.size))
    (LaurentConjugation.TargetMC (CanonicalTangent.baseStar D) hμ) :=
  LaurentConjugation.targetMulAction (CanonicalTangent.baseStar D) hμ

/-- The concrete graph comparison whose low tangent is proved middle exact. -/
def comparison := CanonicalGraph.elementaryComparison k D.size (CanonicalTangent.baseCoefficient D)
  (CanonicalTangent.base_isMaurerCartan D) hμ hc hMC hPath

theorem actual_gauge_transports :
    CanonicalGraphGauge.gauge D • (comparison D hμ hc hMC hPath).quantize (ReflectionSource.source D) =
      (comparison D hμ hc hMC hPath).quantize (ReflectionSource.target D) :=
  CanonicalGraphGauge.gauge_transports D hμ hMC

/-- Gauge reflection gives one actual marked scalar algebra equivalence on
the native iterated completion, using the proved source automorphisms. -/
def equivalence : Poisson.Completed.Functions (Fin D.size) k ≃ₐ[Poisson.Completed.Scalars k]
    Poisson.Completed.Functions (Fin D.size) k :=
  (comparison D hμ hc hMC hPath).reflectedAlgEquiv
    (ReflectionSource.source D) (ReflectionSource.target D)
    LaurentSourceAlgebra.nativeRepresentation LaurentSourceAlgebra.native_source_preserves_mul
    (CanonicalGraphGauge.gauge D) (actual_gauge_transports D hμ hc hMC hPath)

theorem equivalence_constantCoeff (p : Poisson.Completed.Functions (Fin D.size) k) :
    PowerSeries.constantCoeff (equivalence D hμ hc hMC hPath p) = PowerSeries.constantCoeff p :=
  (comparison D hμ hc hMC hPath).reflectedAlgEquiv_constantCoeff
    (ReflectionSource.source D) (ReflectionSource.target D)
    LaurentSourceAlgebra.nativeRepresentation LaurentSourceAlgebra.native_source_preserves_mul
    (CanonicalGraphGauge.gauge D) (actual_gauge_transports D hμ hc hMC hPath) p

/-- The resulting actual algebra equivalence transports the actual native raw
source brackets. Identifying the recovered bracket with the first-jet formula
is a separate coefficient identity. -/
theorem equivalence_intertwines (p q : Poisson.Completed.Functions (Fin D.size) k) :
    equivalence D hμ hc hMC hPath
        (PowerSeriesModuleBridge.binaryBridge
          (single 0 (LaurentSourceAlgebra.nativeBivector (ReflectionSource.base D)) +
            PowerSeriesModule.map LaurentSourceAlgebra.nativeBivector (ReflectionSource.source D).val) p q) =
      PowerSeriesModuleBridge.binaryBridge
        (single 0 (LaurentSourceAlgebra.nativeBivector (ReflectionSource.base D)) +
          PowerSeriesModule.map LaurentSourceAlgebra.nativeBivector (ReflectionSource.target D).val)
        (equivalence D hμ hc hMC hPath p) (equivalence D hμ hc hMC hPath q) :=
  (comparison D hμ hc hMC hPath).reflectedAlgEquiv_intertwines
    (ReflectionSource.source D) (ReflectionSource.target D)
    LaurentSourceAlgebra.nativeRepresentation LaurentSourceAlgebra.native_source_preserves_mul
    (single 0 (LaurentSourceAlgebra.nativeBivector (ReflectionSource.base D)))
    LaurentSourceAlgebra.nativeBivector
    (fun s a b ↦ LaurentSourceAlgebra.native_source_intertwines
      (ReflectionSource.base D) (ReflectionSource.base_isMaurerCartan D) s (ReflectionSource.source D) a b)
    (CanonicalGraphGauge.gauge D) (actual_gauge_transports D hμ hc hMC hPath) p q

/-- The remaining geometric obligations, stated only for the actual canonical
graph coefficients over ℂ. There is no assumed gauge lift, middle exactness,
finite product law or comparison map in this proposition. -/
def CanonicalGraphIdentities : Prop :=
  ∀ (d : ℕ) (π₀ : CanonicalGraph.BaseBivector ℂ d)
    (hπ : (polynomialSchoutenDGLA ℂ d).laurent.IsMaurerCartan
      (CanonicalGraph.sourceBase ℂ d π₀)),
    CanonicalTangentExactness.StarAssociative ℂ d π₀ ∧
      CanonicalGraph.MCIdentity ℂ d π₀ hπ ∧ CanonicalGraph.PathIdentity ℂ d π₀ hπ

end EnvelopingIsomorphism.Rees.GraphComparisonAssembly

namespace EnvelopingIsomorphism.Rees.GraphComparisonAssembly

open EnvelopingIsomorphism.Deformation EnvelopingIsomorphism.FormalSeries
open Gauge
open scoped LaurentAlgebra

universe u v w
variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [LieRing M] [LieAlgebra ℂ M]
  (D : Identification.RecoveredData ℂ L M)
variable (hμ : CanonicalTangent.StarAssociative D) (hc : CanonicalTangent.LowChainIdentity D)
variable (hMC : CanonicalGraphGauge.MCIdentity D) (hPath : PathIdentity D)

/-- The reflected native algebra map preserves the actual h-scaled Rees Poisson
brackets on all completed inputs, with the coefficient identification proved. -/
theorem equivalence_scaled_poisson (p q : Poisson.Completed.Functions (Fin D.size) ℂ) :
    equivalence D hμ hc hMC hPath
        (Poisson.ComparisonMatrix.hbar •
          Poisson.Completed.bracket (Poisson.ComparisonMatrix.sourceCoefficients D) p q) =
      Poisson.ComparisonMatrix.hbar •
        Poisson.Completed.bracket (Poisson.ComparisonMatrix.targetCoefficients D)
          (equivalence D hμ hc hMC hPath p) (equivalence D hμ hc hMC hPath q) := by
  have h := equivalence_intertwines D hμ hc hMC hPath p q
  rw [CompletedPoissonBridge.source_binary_eq, CompletedPoissonBridge.target_binary_eq] at h
  exact h

theorem equivalence_marked (i : Fin D.size) :
    PowerSeries.constantCoeff (equivalence D hμ hc hMC hPath (Poisson.Completed.coordinate i)) =
      HahnSeries.C (MvPolynomial.X i) := by
  rw [equivalence_constantCoeff]
  rfl

/-- The complete concrete graph/reflection construction supplies the precise
native first-jet comparison matrix, without an assumed exactness or gauge lift. -/
def matrixComparison : ReesMatrixComparison D :=
  Poisson.ComparisonMatrix.ofHbarScaledCompletedPoisson D
    (equivalence D hμ hc hMC hPath).toAlgHom
    (equivalence_scaled_poisson D hμ hc hMC hPath)
    (equivalence_marked D hμ hc hMC hPath)

/-- Only the explicit geometric graph identities remain. The low chain equation
is derived from their first-order path coefficient before applying the proved
middle exactness and gauge reflection. -/
theorem comparisonHypothesis_of_graphIdentities
    (h : CanonicalGraphIdentities) : ComparisonHypothesis.{u} := by
  intro L M _ _ _ _ D
  obtain ⟨hμ, hMC, hPath⟩ := h D.size (CanonicalTangent.baseCoefficient D)
    (CanonicalTangent.base_isMaurerCartan D)
  have hc := CanonicalGraph.lowChainIdentity_of_path ℂ D.size (CanonicalTangent.baseCoefficient D)
    (CanonicalTangent.base_isMaurerCartan D) hμ hMC hPath
  exact ⟨matrixComparison D hμ hc hMC hPath⟩

/-- Conditional solvable identification from the same literal geometric graph
identities. This theorem does not assert that those identities are proved. -/
theorem statement_of_graphIdentities (h : CanonicalGraphIdentities) : Statement.{u, v, w} :=
  of_comparison (comparisonHypothesis_of_graphIdentities h)

end EnvelopingIsomorphism.Rees.GraphComparisonAssembly
