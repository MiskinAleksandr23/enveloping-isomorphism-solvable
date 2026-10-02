import EnvelopingIsomorphism.Deformation.Gauge.CanonicalTangentExactness

/-! The actual canonical graph Taylor map on Maurer--Cartan families.
Its remaining input is stated as the literal graph curvature equation, not
as a supplied map of MC spaces or as a reflection assertion. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

namespace EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraph

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule

variable (K : Type*) [Field K] [CharZero K] [Algebra ℝ K] (d : ℕ)

local instance : CharZero (LaurentSeries K) := LaurentSchouten.scalarCharZero

abbrev Polynomial := MvPolynomial (Fin d) K
abbrev BaseBivector := CanonicalTangentCoefficients.Bivector K d
abbrev Scalars := LaurentSeries K
abbrev OperatorRing := LaurentSeries (Module.End K (Polynomial K d))

abbrev sourceBase (π₀ : BaseBivector K d) := CanonicalTangentExactness.baseBivector K d π₀
abbrev targetBase (π₀ : BaseBivector K d) := CanonicalTangentExactness.baseStar K d π₀

def taylor (π₀ : BaseBivector K d) :=
  laurentPlacementTaylorFamily (CanonicalTangentCoefficients.mcFamily K d) π₀

def velocityTangent (π₀ : BaseBivector K d) :=
  PlacedMixedGraphTaylorCoefficients.canonicalVelocityTangentFamily
    CanonicalTangentCoefficients.allVelocityGraphs π₀

omit [CharZero K] in
@[simp] theorem taylor_linear (π₀ : BaseBivector K d) :
    taylorLinear (taylor K d π₀) = CanonicalTangentExactness.oneMap K d π₀ := rfl

omit [CharZero K] in
@[simp] theorem velocityTangent_linear (π₀ : BaseBivector K d) :
    (velocityTangent K d π₀).linear = CanonicalTangentExactness.zeroMap K d π₀ := rfl

variable (π₀ : BaseBivector K d)
variable (hπ : (polynomialSchoutenDGLA K d).laurent.IsMaurerCartan (sourceBase K d π₀))

/-- The explicit still-geometric MC identity for the actual all-graph Taylor
coefficients on every positive Laurent source MC perturbation. -/
def MCIdentity : Prop :=
  ∀ b : LaurentSchouten.SourceMC (sourceBase K d π₀) hπ,
    quadraticCurvature (k := Scalars K)
      (V := LaurentModule K (Binary K (Polynomial K d)))
      (W := LaurentModule K (Ternary K (Polynomial K d)))
      (LaurentModule.differentialBinarySeries (targetBase K d π₀))
      (LaurentModule.insertBinarySeries (k := K) (A := Polynomial K d))
      (taylorApply (taylor K d π₀) b.val) = 0

variable (hμ : CanonicalTangentExactness.StarAssociative K d π₀)
variable (hMC : MCIdentity K d π₀ hπ)

/-- Once the literal graph MC identity is proved, the map into the actual
short Hochschild-complex MC space is constructed with its true Taylor values. -/
def quantize (b : LaurentSchouten.SourceMC (sourceBase K d π₀) hπ) :
    LaurentConjugation.TargetMC (targetBase K d π₀) hμ :=
  ⟨taylorApply (taylor K d π₀) b.val, taylorApply_constantCoeff _ _, hMC b⟩

@[simp] theorem quantize_val (b : LaurentSchouten.SourceMC (sourceBase K d π₀) hπ) :
    (quantize K d π₀ hπ hμ hMC b).val = taylorApply (taylor K d π₀) b.val := rfl

end EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraph
