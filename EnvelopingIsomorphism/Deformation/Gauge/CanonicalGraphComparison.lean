import EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraphMC
import EnvelopingIsomorphism.Deformation.Gauge.LaurentSchoutenPath
import EnvelopingIsomorphism.Deformation.Gauge.LaurentVelocityPath
import EnvelopingIsomorphism.Deformation.Gauge.ElementaryComparison

/-! The concrete canonical graph comparison for gauge reflection.
Only the literal graph MC and differential path identities are supplied;
source exponentials, target integration, stabilizers and tangent exactness
are the actual previously proved constructions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

namespace EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraph

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule

variable (K : Type*) [Field K] [CharZero K] [Algebra ℝ K] (d : ℕ)
local instance : CharZero (LaurentSeries K) := LaurentSchouten.scalarCharZero

variable (π₀ : BaseBivector K d)
variable (hπ : (polynomialSchoutenDGLA K d).laurent.IsMaurerCartan (sourceBase K d π₀))

abbrev SourceComplex := LaurentSchouten.sourceComplex (sourceBase K d π₀) hπ
abbrev SourceMC := LaurentSchouten.SourceMC (sourceBase K d π₀) hπ

/-- The actual parameterized source exponential, with its established endpoints. -/
def sourcePath (N : ℕ) (y : (SourceComplex K d π₀ hπ).X 0) (b : SourceMC K d π₀ hπ) :=
  LaurentSchouten.elementaryPath (sourceBase K d π₀) N y b.val

/-- The raw target velocity computed from every distinguished vertex position. -/
def pathVelocity (N : ℕ) (y : (SourceComplex K d π₀ hπ).X 0) (b : SourceMC K d π₀ hπ) :=
  LaurentConjugation.rawVelocity (velocityTangent K d π₀) (sourcePath K d π₀ hπ N y b) N y

/-- The sole differential path equation still to be supplied by graph Stokes.
Both paths and all Taylor/tangent operations in this equation are actual fixed
canonical constructions; no integrated lift is assumed. -/
def PathIdentity : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (y : (SourceComplex K d π₀ hπ).X 0) (b : SourceMC K d π₀ hπ),
    pathMap LaurentConjugation.evaluateCoefficient
        (polynomialTaylorDerivative (taylor K d π₀) (sourcePath K d π₀ hπ N y b)) =
      pathOperator
        (orderedVelocity (PathOrderedExp.mapPath LaurentOperator.actionHom (pathVelocity K d π₀ hπ N y b)))
        (pathMap LaurentConjugation.evaluateCoefficient
          (quantizedPath (taylor K d π₀) (single 0 (targetBase K d π₀)) (sourcePath K d π₀ hπ N y b)))

def pathLift (N : ℕ) (y : (SourceComplex K d π₀ hπ).X 0) (b : SourceMC K d π₀ hπ) :
    GaugeUnit (OperatorRing K d) := orderedGauge (pathVelocity K d π₀ hπ N y b)

theorem pathLift_near (N : ℕ) (y : (SourceComplex K d π₀ hπ).X 0) (b : SourceMC K d π₀ hπ) :
    NearIdentity N (pathLift K d π₀ hπ N y b).series :=
  LaurentConjugation.rawVelocityGauge_near _ _ _ _

theorem pathLift_leading (N : ℕ) (hN : 0 < N)
    (y : (SourceComplex K d π₀ hπ).X 0) (b : SourceMC K d π₀ hπ) :
    LaurentConjugation.operatorCoordinates (PowerSeries.coeff N (pathLift K d π₀ hπ N y b).series) =
      CanonicalTangentExactness.zeroMap K d π₀ y :=
  LaurentConjugation.rawVelocityGauge_leading _ _ _ hN _

variable (hμ : CanonicalTangentExactness.StarAssociative K d π₀)
variable (hc : CanonicalTangentExactness.LowChainIdentity K d π₀)
variable (hMC : MCIdentity K d π₀ hπ) (hPath : PathIdentity K d π₀ hπ)

local instance : MulAction (LaurentSchouten.SourceGroup K d) (SourceMC K d π₀ hπ) :=
  LaurentSchouten.sourceMulAction (sourceBase K d π₀) hπ
local instance : MulAction (GaugeUnit (OperatorRing K d))
    (LaurentConjugation.TargetMC (targetBase K d π₀) hμ) :=
  LaurentConjugation.targetMulAction (targetBase K d π₀) hμ

include hPath in
theorem pathLift_action (N : ℕ) (hN : 0 < N)
    (y : (SourceComplex K d π₀ hπ).X 0) (b : SourceMC K d π₀ hπ) :
    pathLift K d π₀ hπ N y b • quantize K d π₀ hπ hμ hMC b =
      quantize K d π₀ hπ hμ hMC
        (LaurentSchouten.sourceElementary (sourceBase K d π₀) hπ N hN y • b) := by
  apply LaurentConjugation.rawOrderedGauge_lifts_mcPath (targetBase K d π₀) hμ
    (taylor K d π₀) (sourcePath K d π₀ hπ N y b) b.val
    (LaurentSchouten.sourceElementary (sourceBase K d π₀) hπ N hN y • b).val
  · exact LaurentSchouten.elementaryPath_eval_zero _ _ _ _
  · rw [LaurentSchouten.sourceElementary_smul, LaurentSchouten.sourceMove_val]
    exact LaurentSchouten.elementaryPath_eval_one _ _ hN _ _
  · rfl
  · rfl
  · exact LaurentConjugation.rawVelocity_positive _ _ _ hN _
  · exact hPath N hN y b

/-- All nongeometric fields of the comparison are instantiated by their actual
producers. Its tangent has the already proved IsMiddleExact instance. -/
def elementaryComparison :
    ElementaryComparison (CanonicalTangentExactness.tangent K d π₀ hπ hμ hc)
      (LaurentSchouten.sourceQuadratic (sourceBase K d π₀) hπ)
      (LaurentConjugation.targetQuadratic (targetBase K d π₀) hμ)
      (LaurentSchouten.SourceGroup K d) (OperatorRing K d) (OperatorRing K d) where
  sourceOperators := LaurentSchouten.sourceOperators
  targetCoordinates := LaurentConjugation.targetCoordinates (targetBase K d π₀) hμ
  taylor := taylor K d π₀
  linear_eq := rfl
  quantize := quantize K d π₀ hπ hμ hMC
  quantize_eq _ := rfl
  sourceElementary := LaurentSchouten.sourceElementary (sourceBase K d π₀) hπ
  source_near := LaurentSchouten.sourceElementary_near (sourceBase K d π₀) hπ
  source_agree := LaurentSchouten.sourceElementary_agree (sourceBase K d π₀) hπ
  source_leading := LaurentSchouten.sourceElementary_leading (sourceBase K d π₀) hπ
  target_leading := LaurentConjugation.target_smul_leading (targetBase K d π₀) hμ
  pathLift N _ := pathLift K d π₀ hπ N
  pathLift_near N _ := pathLift_near K d π₀ hπ N
  pathLift_leading := pathLift_leading K d π₀ hπ
  pathLift_action := pathLift_action K d π₀ hπ hμ hMC hPath
  boundary N _ := LaurentConjugation.targetBoundary (targetBase K d π₀) hμ N
  boundary_near N _ := LaurentConjugation.targetBoundary_near (targetBase K d π₀) hμ N
  boundary_leading := LaurentConjugation.targetBoundary_leading (targetBase K d π₀) hμ
  boundary_fixes := LaurentConjugation.targetBoundary_fixes (targetBase K d π₀) hμ

end EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraph
