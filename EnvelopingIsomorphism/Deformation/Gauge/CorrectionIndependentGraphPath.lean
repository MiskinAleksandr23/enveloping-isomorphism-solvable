import EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraphScalarPath

/-! The canonical MC path identity needs the canonical star and velocity
weights, but every curvature correction kernel vanishes on source MCs. This
keeps the off-shell correction convention explicit without changing the path. -/
noncomputable section
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Gauge.CorrectionIndependentGraphPath
open EnvelopingIsomorphism.FormalSeries PowerSeriesModule
open CanonicalMixedTangentAssembly LaurentTaylorArityBounds
open MixedGraphProfileCarrier MixedGraphAveraging GraphCoefficientProfiles MixedGraphDoubleEvaluation
variable {k : Type*} [Field k] [CharZero k] [Algebra ℝ k] {d : ℕ}
local instance : CharZero (LaurentSeries k) := LaurentSchouten.scalarCharZero
variable (u : (j : ℕ) → MixedGraphCorrectionProfiles.CorrectionGraph j → k)

theorem canonical_source_eq_target
    (h : MixedGraphBoundaryProfiles.ScalarMixedBoundaryRelation
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := k))
      (fun _ ↦ MixedGraphBoundaryProfiles.canonicalVelocityWeight (k := k)) u) (N : ℕ)
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d))))
    (Y : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Vector (k := k) (d := d))))
    (hα : PowerSeriesModule.applyBilinear
      (LaurentModule.extendBilinear (schoutenBracket k d 1 1)) α α = 0) :
    mixedDoubleApply α Y (evaluation (symmetrizedBinaryValue (k := k) (d := d))
      (MixedGraphSourceProfiles.fullSourceActionProfile
        (GraphBoundaryProfiles.canonicalBinaryWeight (k := k)) N)) =
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal N,
        PowerSeriesModule.applyBilinear LaurentConjugation.unaryCoefficientAction
          (MixedLaurentArityBounds.mixedTerm (CanonicalTangentCoefficients.velocityFamily k d) α Y ab.1)
          (LaurentTaylorArityBounds.arityTerm (CanonicalTangentCoefficients.mcFamily k d) α ab.2) := by
  have he := scalarMixedBoundaryRelation_double h N α Y
  rw [MixedGraphCorrectionPowerSeries.mixedDoubleApply_fullCorrectionProfile_eq_zero
    u N α Y hα, add_zero] at he
  exact he.trans (MixedGraphTargetPowerSeries.canonical_targetActionProfile_double N α Y)

theorem tangentEquation_of_scalarMixedBoundary
    (h : MixedGraphBoundaryProfiles.ScalarMixedBoundaryRelation
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := k))
      (fun _ ↦ MixedGraphBoundaryProfiles.canonicalVelocityWeight (k := k)) u)
    (π₀ : CanonicalGraph.BaseBivector k d)
    (hπ : (polynomialSchoutenDGLA k d).laurent.IsMaurerCartan (CanonicalGraph.sourceBase k d π₀))
    (b : LaurentSchouten.SourceMC (CanonicalGraph.sourceBase k d π₀) hπ)
    (Y : VectorSeries (k := k) (d := d)) (hY : coeffV 0 Y = 0) :
    taylorDerivativeApply (CanonicalGraph.taylor k d π₀) b.val (actionDirection π₀ b.val Y) =
      applyBilinear LaurentConjugation.unaryCoefficientAction
        (tangentApply (CanonicalGraph.velocityTangent k d π₀) b.val Y)
        (single 0 (CanonicalGraph.targetBase k d π₀) + taylorApply (CanonicalGraph.taylor k d π₀) b.val) := by
  apply tangentEquation_of_homogeneous π₀ b.val b.property.1 Y hY
  intro N
  have hs := MixedGraphSourceDoubleCompletion.canonical_sourceProfile_double N (fullInput π₀ b.val) Y
  have ht := canonical_source_eq_target u h N (fullInput π₀ b.val) Y
    (CanonicalGraphMCAlgebra.source_full_square_zero π₀ hπ b)
  exact hs.symm.trans ht

theorem pathIdentity_of_scalarMixedBoundary
    (h : MixedGraphBoundaryProfiles.ScalarMixedBoundaryRelation
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := k))
      (fun _ ↦ MixedGraphBoundaryProfiles.canonicalVelocityWeight (k := k)) u)
    (π₀ : CanonicalGraph.BaseBivector k d)
    (hπ : (polynomialSchoutenDGLA k d).laurent.IsMaurerCartan (CanonicalGraph.sourceBase k d π₀)) :
    CanonicalGraph.PathIdentity k d π₀ hπ := by
  apply CanonicalGraphPathAlgebra.pathIdentity_of_tangentEquation π₀ hπ
  intro b Y hY
  exact tangentEquation_of_scalarMixedBoundary u h π₀ hπ b Y hY

end EnvelopingIsomorphism.Deformation.Gauge.CorrectionIndependentGraphPath
