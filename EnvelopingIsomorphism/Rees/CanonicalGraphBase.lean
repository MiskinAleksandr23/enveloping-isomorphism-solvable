import EnvelopingIsomorphism.Rees.CanonicalTangent
import EnvelopingIsomorphism.Rees.NativeGraphTaylorGauge

/-! The constant t-coefficient of the actual full graph Taylor evaluation is
the genuine canonical positive-h base star product. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace EnvelopingIsomorphism.Rees.CanonicalGraphBase
open EnvelopingIsomorphism.FormalSeries EnvelopingIsomorphism.Deformation
open Gauge MiddleExactPerturbation
open scoped Classical

section ConstantEvaluation
universe u v
variable {k : Type u} [Field k] {V W : Type v}
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Constant t-coefficients commute with the actual graph evaluation and its
positive-to-Laurent embedding, with no MC hypothesis. -/
theorem laurentScaledMCEvaluation_constantCoeff
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (ζ : PowerSeriesModule k V) :
    PowerSeriesModule.coeffV 0 (laurentScaledMCEvaluation C ζ) =
      toLaurent (baseMCImage C (PowerSeriesModule.coeffV 0 ζ)) := by
  change toLaurent (PowerSeriesModule.coeffV 0 (scaledMCEvaluation C ζ)) = _
  apply congrArg toLaurent
  apply PowerSeriesModule.ext
  intro m
  rw [coeff_scaledMCEvaluation, multilinear_constant_coefficient]
  rfl
end ConstantEvaluation

variable {k L : Type*} [Field k] [CharZero k] {d : ℕ}
  [LieRing L] [LieAlgebra k L] {b : Module.Basis (Fin d) k L} (D : WeightData b)

omit [CharZero k] in
theorem fullTaylor_constantCoeff
    (s : (j : ℕ) → Finset (KontsevichGraph (j+1)))
    (w : (j : ℕ) → KontsevichGraph (j+1) → k) :
    PowerSeriesModule.coeffV 0 (GraphTaylorIdentification.fullTaylor D s w) =
      toLaurent (baseMCImage (GraphTaylorCoefficients.effectiveFamily s w)
        (PoissonMCFamily.constantBivector D)) := by
  rw [GraphTaylorIdentification.fullTaylor, laurentScaledMCEvaluation_constantCoeff]
  rfl

variable [Algebra ℝ k]

/-- The canonical higher-arity data used by the existing F10/F11 constructors. -/
def higherSets (j : ℕ) : Finset (KontsevichGraph (j+2)) := Finset.univ

def higherWeights (j : ℕ) (Γ : KontsevichGraph (j+2)) : k :=
  Kontsevich.GeometricWeights.binaryWeightOver k (j+1) Γ

@[simp] theorem geometricFirstSets_univ :
    KontsevichGraph.geometricFirstSets higherSets = fun _ ↦ Finset.univ := by
  funext j
  cases j <;> rfl

omit [CharZero k] in
@[simp] theorem geometricFirstWeights_canonical :
    KontsevichGraph.geometricFirstWeights (higherWeights (k := k)) =
      Kontsevich.GeometricWeights.binaryWeightOver k :=
  Kontsevich.GeometricWeights.geometricFirstWeights_eq_binaryWeightOver k

omit [CharZero k] in
/-- The exact native base product used by canonical tangent exactness. -/
theorem fullTaylor_canonical_constantCoeff :
    PowerSeriesModule.coeffV 0 (GraphTaylorIdentification.fullTaylor D
      (fun _ ↦ Finset.univ) (Kontsevich.GeometricWeights.binaryWeightOver k)) =
    CanonicalTangentExactness.baseStar k d (PoissonMCFamily.constantBivector D) :=
  fullTaylor_constantCoeff D _ _

omit [CharZero k] in
theorem nativeGraphFamily_canonical_constantCoeff :
    PowerSeriesModule.coeffV 0 (GraphTaylorIdentification.nativeGraphFamily D
      (fun _ ↦ Finset.univ) (Kontsevich.GeometricWeights.binaryWeightOver k)) =
    CanonicalTangentExactness.baseStar k d (PoissonMCFamily.constantBivector D) := by
  rw [← GraphTaylorIdentification.fullTaylor_eq_nativeGraphFamily]
  exact fullTaylor_canonical_constantCoeff D

omit [CharZero k] in
theorem nativeFamily_canonical_constantCoeff :
    PowerSeriesModule.coeffV 0 (NativeGraphTaylorGauge.nativeFamily D higherSets
      (NativeGraphTaylorGauge.parameterHigher (higherWeights (k := k)))) =
    CanonicalTangentExactness.baseStar k d (PoissonMCFamily.constantBivector D) := by
  rw [NativeGraphTaylorGauge.nativeFamily_parameters, geometricFirstSets_univ,
    geometricFirstWeights_canonical]
  exact nativeGraphFamily_canonical_constantCoeff D

section Recovered
variable {M : Type*} [LieRing M] [LieAlgebra k M]
variable (R : Identification.RecoveredData k L M)

omit [CharZero k] in
theorem source_constantCoeff :
    PowerSeriesModule.coeffV 0 (GraphTaylorIdentification.fullTaylor R.sourceWeightData
      (fun _ ↦ Finset.univ) (Kontsevich.GeometricWeights.binaryWeightOver k)) =
      CanonicalTangent.baseStar R := fullTaylor_canonical_constantCoeff _

omit [CharZero k] in
theorem target_constantCoeff :
    PowerSeriesModule.coeffV 0 (GraphTaylorIdentification.fullTaylor R.targetWeightData
      (fun _ ↦ Finset.univ) (Kontsevich.GeometricWeights.binaryWeightOver k)) =
      CanonicalTangent.baseStar R := by
  rw [fullTaylor_canonical_constantCoeff, ← RecoveredPoissonMC.constantBivector_eq R]
end Recovered
end EnvelopingIsomorphism.Rees.CanonicalGraphBase
