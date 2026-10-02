import EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraphMC
import EnvelopingIsomorphism.Deformation.GraphBoundaryBase
import EnvelopingIsomorphism.Deformation.Gauge.LaurentTaylorFullIdentity

/-! Exact source and target quadratic algebra used to assemble graph MC.
The all-arity coefficient identity is supplied separately by the scalar graph
boundary proof; every operation here is the native Laurent operation. -/

noncomputable section
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraphMCAlgebra
open EnvelopingIsomorphism.FormalSeries
open PowerSeriesModule
open scoped BigOperators Classical

section Quadratic
variable {R U W : Type*} [CommRing R] [AddCommGroup U] [Module R U]
  [AddCommGroup W] [Module R W]

/-- Exact quadratic expansion for any closed coefficient bilinear operation. -/
theorem full_square_eq_curvature (Q : U →ₗ[R] U →ₗ[R] W) (μ : U)
    (hμ : Q μ μ = 0) (b : PowerSeriesModule R U) :
    applyBilinear Q (single 0 μ + b) (single 0 μ + b) =
      quadraticCurvature (Q μ + Q.flip μ) Q b := by
  change extendBilinear Q (single 0 μ + b) (single 0 μ + b) = _
  simp only [map_add, LinearMap.add_apply, extendBilinear_apply]
  rw [applyBilinear_single_zero_left, map_single, hμ]
  have hz : (single 0 (0 : W) : PowerSeriesModule R W) = 0 := by ext n; simp
  rw [hz, zero_add, applyBilinear_single_zero_right, applyBilinear_single_zero_left]
  apply PowerSeriesModule.ext
  intro n
  simp only [quadraticCurvature, coeffV_add, coeffV_map, LinearMap.add_apply]
  abel

end Quadratic

variable {k : Type*} [Field k] [CharZero k] [Algebra ℝ k] {d : ℕ}
local instance : CharZero (LaurentSeries k) := LaurentSchouten.scalarCharZero

omit [Algebra ℝ k] in
/-- Symmetry of the actual Laurent degree-(1,1) bracket follows from its
faithful raw-coordinate evaluation, with both ordered contractions retained. -/
theorem bivectorBracket_symm (F G : LaurentSchouten.Bivector k d) :
    LaurentSchouten.bivectorBracket F G = LaurentSchouten.bivectorBracket G F := by
  apply LaurentSchouten.evaluateTrivector_injective
  rw [LaurentSchouten.evaluate_bivectorBracket, LaurentSchouten.evaluate_bivectorBracket,
    add_comm]

omit [Algebra ℝ k] in
theorem sourceBase_bracket_zero (π₀ : CanonicalGraph.BaseBivector k d)
    (hπ : (polynomialSchoutenDGLA k d).laurent.IsMaurerCartan (CanonicalGraph.sourceBase k d π₀)) :
    LaurentSchouten.bivectorBracket (CanonicalGraph.sourceBase k d π₀)
      (CanonicalGraph.sourceBase k d π₀) = 0 := by
  change LaurentModule.extendBilinear (schoutenBracket k d 1 1)
    (LaurentModule.single 1 π₀) (LaurentModule.single 1 π₀) = 0
  rw [LaurentModule.extendBilinear_single]
  exact (congrArg (LaurentModule.single (k := k) (1 + 1))
    (GraphBoundaryBase.poisson_of_baseMC π₀ hπ)).trans (LaurentModule.single_zero _)

omit [CharZero k] [Algebra ℝ k] in
/-- The genuine closed Laurent target insertion is the bilinear extension of
the actual polynomial insertion, on every bounded Laurent cochain input. -/
theorem insertBinarySeries_eq_extendBilinear :
    LaurentModule.insertBinarySeries (k := k) (A := MvPolynomial (Fin d) k) =
      LaurentModule.extendBilinear (PowerSeriesModule.insertBinaryLinear
        (k := k) (V := MvPolynomial (Fin d) k)) := by
  have hl : LaurentModule.insertLeftCoefficient (k := k) (A := MvPolynomial (Fin d) k) =
      PowerSeriesModule.insertLeftLinear := by
    apply LinearMap.ext
    intro B
    apply LinearMap.ext
    intro C
    rfl
  have hr : LaurentModule.insertRightCoefficient (k := k) (A := MvPolynomial (Fin d) k) =
      PowerSeriesModule.insertRightLinear := by
    apply LinearMap.ext
    intro B
    apply LinearMap.ext
    intro C
    rfl
  rw [LaurentModule.insertBinarySeries, hl, hr, PowerSeriesModule.insertBinaryLinear]
  apply LinearMap.ext
  intro B
  apply LinearMap.ext
  intro C
  exact (LaurentModule.extendBilinear_coeff_sub _ _ B C).symm

omit [Algebra ℝ k] in
/-- The existing twisted source MC equation is exactly the full translated
Laurent Schouten square equation, including its factor one half. -/
theorem source_full_square_zero (π₀ : CanonicalGraph.BaseBivector k d)
    (hπ : (polynomialSchoutenDGLA k d).laurent.IsMaurerCartan (CanonicalGraph.sourceBase k d π₀))
    (b : LaurentSchouten.SourceMC (CanonicalGraph.sourceBase k d π₀) hπ) :
    applyBilinear LaurentSchouten.bivectorBracket
      (LaurentTaylorArityBounds.fullInput π₀ b.val)
      (LaurentTaylorArityBounds.fullInput π₀ b.val) = 0 := by
  let μ := CanonicalGraph.sourceBase k d π₀
  let Q := (2 : LaurentSeries k)⁻¹ • (LaurentSchouten.bivectorBracket (K := k) (d := d))
  have hQ : Q μ μ = 0 := by
    change (2 : LaurentSeries k)⁻¹ • LaurentSchouten.bivectorBracket μ μ = 0
    rw [sourceBase_bracket_zero π₀ hπ, smul_zero]
  have hd : Q μ + Q.flip μ = LaurentSchouten.bivectorBracket μ := by
    apply LinearMap.ext
    intro X
    change (2 : LaurentSeries k)⁻¹ • LaurentSchouten.bivectorBracket μ X +
      (2 : LaurentSeries k)⁻¹ • LaurentSchouten.bivectorBracket X μ = _
    rw [bivectorBracket_symm X μ, ← smul_add, ← two_smul (LaurentSeries k),
      smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  have hb : quadraticCurvature (LaurentSchouten.bivectorBracket μ) Q b.val = 0 := by
    rw [← LaurentSchouten.sourceComplex_d_one μ hπ]
    exact b.property.2
  have hs := full_square_eq_curvature Q μ hQ b.val
  rw [hd, hb] at hs
  have hscale : applyBilinear Q (single 0 μ + b.val) (single 0 μ + b.val) =
      (2 : LaurentSeries k)⁻¹ • applyBilinear LaurentSchouten.bivectorBracket
        (single 0 μ + b.val) (single 0 μ + b.val) := by
    apply PowerSeriesModule.ext
    intro n
    simp only [coeffV_applyBilinear, Q, LinearMap.smul_apply, coeffV_smul, Finset.smul_sum]
  rw [hscale] at hs
  exact (smul_eq_zero.mp hs).resolve_left (inv_ne_zero two_ne_zero)

/-- Vanishing of the full actual target insertion square is exactly what
the original target curvature needs after subtracting its canonical base. -/
theorem target_MC_of_full_square_zero
    (h : GraphBoundaryProfiles.CanonicalScalarBoundaryRelation (k := k))
    (π₀ : CanonicalGraph.BaseBivector k d)
    (hπ : (polynomialSchoutenDGLA k d).laurent.IsMaurerCartan (CanonicalGraph.sourceBase k d π₀))
    (b : LaurentSchouten.SourceMC (CanonicalGraph.sourceBase k d π₀) hπ)
    (hsquare : applyBilinear LaurentModule.insertBinarySeries
      (LaurentFullGraphEvaluation.fullEvaluation (CanonicalTangentCoefficients.mcFamily k d) π₀ b.val b.property.1)
      (LaurentFullGraphEvaluation.fullEvaluation (CanonicalTangentCoefficients.mcFamily k d) π₀ b.val b.property.1) = 0) :
    quadraticCurvature (LaurentModule.differentialBinarySeries (CanonicalGraph.targetBase k d π₀))
      LaurentModule.insertBinarySeries (taylorApply (CanonicalGraph.taylor k d π₀) b.val) = 0 := by
  have hbase : LaurentModule.insertBinarySeries (CanonicalGraph.targetBase k d π₀)
      (CanonicalGraph.targetBase k d π₀) = 0 := by
    rw [← GraphBoundaryBase.toLaurent_insertion]
    rw [GraphBoundaryProfiles.canonical_insertion_zero h π₀ (GraphBoundaryBase.poisson_of_baseMC π₀ hπ),
      MiddleExactPerturbation.toLaurent_zero]
  rw [LaurentTaylorFullIdentity.fullEvaluation_eq_base_add_taylor] at hsquare
  have he := full_square_eq_curvature LaurentModule.insertBinarySeries
    (CanonicalGraph.targetBase k d π₀) hbase (taylorApply (CanonicalGraph.taylor k d π₀) b.val)
  exact he.symm.trans hsquare

end EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraphMCAlgebra
