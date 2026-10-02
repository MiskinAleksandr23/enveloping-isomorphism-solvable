import EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraphComparison

/-! The canonical low-chain identity follows from the actual graph MC and path
identities by taking the first coefficient of an elementary source motion.
No middle exactness or reflected equivalence is used in this derivation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraph
open EnvelopingIsomorphism.FormalSeries PowerSeriesModule

variable (K : Type*) [Field K] [CharZero K] [Algebra ℝ K] (d : ℕ)
local instance : CharZero (LaurentSeries K) := LaurentSchouten.scalarCharZero
variable (π₀ : BaseBivector K d)
variable (hπ : (polynomialSchoutenDGLA K d).laurent.IsMaurerCartan (sourceBase K d π₀))

/-- The actual zero perturbation in the fixed native source MC space. -/
def zeroSource : SourceMC K d π₀ hπ :=
  ⟨0, by simp, by
    apply PowerSeriesModule.ext
    intro n
    simp [quadraticCurvature, coeffV_applyBilinear]⟩

variable (hμ : CanonicalTangentExactness.StarAssociative K d π₀)
variable (hMC : MCIdentity K d π₀ hπ) (hPath : PathIdentity K d π₀ hπ)
local instance : MulAction (LaurentSchouten.SourceGroup K d) (SourceMC K d π₀ hπ) :=
  LaurentSchouten.sourceMulAction (sourceBase K d π₀) hπ
local instance : MulAction (GaugeUnit (OperatorRing K d))
    (LaurentConjugation.TargetMC (targetBase K d π₀) hμ) :=
  LaurentConjugation.targetMulAction (targetBase K d π₀) hμ

include hμ hMC hPath in
/-- At any actual positive MC point, first coefficients of the established
path action recover the literal low tangent chain equation. -/
theorem lowChainIdentity_of_path_at (b : SourceMC K d π₀ hπ) :
    CanonicalTangentExactness.LowChainIdentity K d π₀ := by
  apply (CanonicalTangentExactness.lowChainIdentity_iff_native K d π₀ hπ hμ).2
  apply LinearMap.ext
  intro y
  let G := pathLift K d π₀ hπ 1 y b
  let b' : SourceMC K d π₀ hπ :=
    LaurentSchouten.sourceElementary (sourceBase K d π₀) hπ 1 (by decide) y • b
  have ha : G • quantize K d π₀ hπ hμ hMC b = quantize K d π₀ hπ hμ hMC b' :=
    pathLift_action K d π₀ hπ hμ hMC hPath 1 (by decide) y b
  have ht := LaurentConjugation.target_smul_leading (targetBase K d π₀) hμ 1 (by decide)
    G (pathLift_near K d π₀ hπ 1 y b) (quantize K d π₀ hπ hμ hMC b)
  rw [ha, quantize_val, quantize_val] at ht
  have he := taylorApply_leading_difference (taylor K d π₀) 1 (by decide) b'.val b.val
    b'.property.1 b.property.1
    (LaurentSchouten.sourceElementary_agree (sourceBase K d π₀) hπ 1 (by decide) y b)
  rw [he] at ht
  have hs : coeffV 1 b'.val - coeffV 1 b.val = -(SourceComplex K d π₀ hπ).d 0 1 y :=
    LaurentSchouten.sourceElementary_leading (sourceBase K d π₀) hπ 1 (by decide) y b
  have hg : LaurentConjugation.targetCoordinates (targetBase K d π₀) hμ
      (PowerSeries.coeff 1 G.series) = CanonicalTangentExactness.zeroMap K d π₀ y :=
    pathLift_leading K d π₀ hπ 1 (by decide) y b
  rw [hs, taylor_linear, map_neg, hg] at ht
  exact (neg_inj.mp ht).symm

include hμ hMC hPath in
/-- The geometric contract needs only the genuine MC and differential path
identities: its low-chain equation is already a theorem. -/
theorem lowChainIdentity_of_path : CanonicalTangentExactness.LowChainIdentity K d π₀ :=
  lowChainIdentity_of_path_at K d π₀ hπ hμ hMC hPath (zeroSource K d π₀ hπ)

end EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraph
