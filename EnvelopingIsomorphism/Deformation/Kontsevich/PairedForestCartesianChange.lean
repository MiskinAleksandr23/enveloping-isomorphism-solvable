import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestProductChart
import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarCoarseCartesian
import Mathlib.MeasureTheory.Function.Jacobian

/-! Actual unsigned change of variables from a native paired forest face to
its coarse/planar product, in explicit standard volume coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCartesianChange
open Configuration PairedForestSimpleCluster PairedForestSmoothProduct PairedForestProductChart
open InteriorGraphFaceCoordinates ForestRadialFaceClassification BoxStokes MeasureTheory Set
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : kind 0 x o = .paired)

abbrev shapeCount := shapeN (anchor x o ho) (reference x o ho) (S x o ho)
abbrev coarseCount := coarseN 0 (anchor x o ho) (S x o ho)

include hdim in
theorem dimension_eq : PlanarCoarseCartesian.Dim (shapeCount x o ho) (coarseCount x o ho) m = r := by
  have h := (PlanarCoarseCartesian.cartesian (shapeCount x o ho) (coarseCount x o ho) m).toLinearEquiv.finrank_eq
  have hp := finrank_product hdim x o ho
  simpa only [Coord, Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using h.trans hp

/-- Angle first, interleaved planar pairs, coarse pairs, then boundary entries. -/
def cartesian : Coord r ≃L[ℝ] Product x o ho :=
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin r ↦ ℝ) (finCongr (dimension_eq hdim x o ho))).symm.trans
    (PlanarCoarseCartesian.cartesian (shapeCount x o ho) (coarseCount x o ho) m)

def cartesianMeas : Coord r ≃ᵐ Product x o ho :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin r ↦ ℝ) (finCongr (dimension_eq hdim x o ho))).symm.trans
    (PlanarCoarseCartesian.cartesianMeas (shapeCount x o ho) (coarseCount x o ho) m)

@[simp] theorem cartesianMeas_eq : (cartesianMeas hdim x o ho : _ → _) = cartesian hdim x o ho := rfl

theorem volume_preserving_cartesian : MeasurePreserving (cartesianMeas hdim x o ho) :=
  (PlanarCoarseCartesian.volume_preserving_cartesian _ _ _).comp
    ((volume_measurePreserving_piCongrLeft (fun _ : Fin r ↦ ℝ) (finCongr (dimension_eq hdim x o ho))).symm _)

variable (z : Source hdim x o)

def chart : OpenPartialHomeomorph (Coord r) (Coord r) :=
  (localChart hdim x o ho z).trans (cartesian hdim x o ho).symm.toHomeomorph.toOpenPartialHomeomorph

@[simp] theorem chart_source : (chart hdim x o ho z).source = (localChart hdim x o ho z).source := by
  simp only [chart, OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
    preimage_univ, inter_univ]

@[simp] theorem chart_apply (w : Coord r) :
    chart hdim x o ho z w = (cartesian hdim x o ho).symm (localChart hdim x o ho z w) := rfl

@[simp] theorem cartesian_chart (w : Coord r) :
    cartesian hdim x o ho (chart hdim x o ho z w) = localChart hdim x o ho z w :=
  (cartesian hdim x o ho).apply_symm_apply _

theorem chart_contDiffAt {w : Coord r} (hw : w ∈ (chart hdim x o ho z).source) :
    ContDiffAt ℝ ⊤ (chart hdim x o ho z) w :=
  (cartesian hdim x o ho).symm.contDiff.contDiffAt.comp w
    (localChart_contDiffAt hdim x o ho z ((chart_source hdim x o ho z) ▸ hw))

def jacobian (w : Coord r) : ℝ := (fderiv ℝ (chart hdim x o ho z) w).det

theorem jacobian_ne_zero {w : Coord r} (hw : w ∈ (localChart hdim x o ho z).source) :
    jacobian hdim x o ho z w ≠ 0 := by
  have hd := ((cartesian hdim x o ho).symm.hasFDerivAt.comp w
    ((localChart_contDiffAt hdim x o ho z hw).differentiableAt (by simp)).hasFDerivAt).fderiv
  change fderiv ℝ (chart hdim x o ho z) w = _ at hd
  unfold jacobian
  rw [hd]
  let e := LinearEquiv.ofBijective
    (((cartesian hdim x o ho).symm.toContinuousLinearMap.comp
      (fderiv ℝ (localChart hdim x o ho z) w)).toLinearMap)
    ((cartesian hdim x o ho).symm.bijective.comp (localChart_differential_bijective hdim x o ho z hw))
  exact e.isUnit_det'.ne_zero

theorem cartesian_preimage_image (s : Set (Coord r)) :
    cartesian hdim x o ho ⁻¹' (localChart hdim x o ho z '' s) = chart hdim x o ho z '' s := by
  ext w
  constructor
  · rintro ⟨v, hv, he⟩
    refine ⟨v, hv, ?_⟩
    rw [chart_apply, he, ContinuousLinearEquiv.symm_apply_apply]
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, (cartesian_chart hdim x o ho z v).symm⟩

/-- Native product-volume integral, with the actual absolute Jacobian. All
chart regularity and injectivity are supplied by the constructed chart. -/
theorem integral_image (s : Set (Coord r)) (hs : MeasurableSet s)
    (hsub : s ⊆ (localChart hdim x o ho z).source) (g : Product x o ho → ℝ) :
    (∫ p in localChart hdim x o ho z '' s, g p) =
      ∫ w in s, |jacobian hdim x o ho z w| * g (localChart hdim x o ho z w) := by
  have hc := (volume_preserving_cartesian hdim x o ho).setIntegral_preimage_emb
    (cartesianMeas hdim x o ho).measurableEmbedding g (localChart hdim x o ho z '' s)
  rw [cartesianMeas_eq, cartesian_preimage_image] at hc
  rw [← hc, integral_image_eq_integral_abs_det_fderiv_smul volume hs (f' := fun w ↦ fderiv ℝ (chart hdim x o ho z) w)]
  · simp only [cartesian_chart, smul_eq_mul, jacobian]
  · intro w hw
    exact ((chart_contDiffAt hdim x o ho z (by simpa only [chart_source] using hsub hw)).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  · exact (chart hdim x o ho z).injOn.mono (by simpa only [chart_source] using hsub)

/-- The same concrete formula also transports absolute integrability. -/
theorem integrableOn_image_iff (s : Set (Coord r)) (hs : MeasurableSet s)
    (hsub : s ⊆ (localChart hdim x o ho z).source) (g : Product x o ho → ℝ) :
    IntegrableOn g (localChart hdim x o ho z '' s) ↔
      IntegrableOn (fun w ↦ |jacobian hdim x o ho z w| * g (localChart hdim x o ho z w)) s := by
  have hc := (volume_preserving_cartesian hdim x o ho).integrableOn_comp_preimage
    (cartesianMeas hdim x o ho).measurableEmbedding
      (f := g) (s := localChart hdim x o ho z '' s)
  rw [cartesianMeas_eq, cartesian_preimage_image] at hc
  rw [← hc, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs (f' := fun w ↦ fderiv ℝ (chart hdim x o ho z) w)]
  · simp only [cartesian_chart, smul_eq_mul, jacobian, Function.comp_apply]
  · intro w hw
    exact ((chart_contDiffAt hdim x o ho z (by simpa only [chart_source] using hsub hw)).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  · exact (chart hdim x o ho z).injOn.mono (by simpa only [chart_source] using hsub)


/-- The literal transformed native density, including the reciprocal absolute
Jacobian of the actual standard-coordinate map. -/
def pushforward (f : Coord r → ℝ) (p : Product x o ho) : ℝ :=
  |jacobian hdim x o ho z (PairedForestProductOverlap.inverse hdim x o ho p)|⁻¹ *
    f (PairedForestProductOverlap.inverse hdim x o ho p)

theorem jacobian_mul_pushforward (f : Coord r → ℝ) {w : Coord r}
    (hw : w ∈ (localChart hdim x o ho z).source) :
    |jacobian hdim x o ho z w| * pushforward hdim x o ho z f (localChart hdim x o ho z w) = f w := by
  have hi := PairedForestProductOverlap.inverse_toProduct hdim x o ho (phase hdim x o ho z)
    ⟨w, localChart_source_subset hdim x o ho z hw⟩
  change PairedForestProductOverlap.inverse hdim x o ho (localChart hdim x o ho z w) = w at hi
  rw [pushforward, hi, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr (jacobian_ne_zero hdim x o ho z hw)), one_mul]

theorem integral_pushforward (s : Set (Coord r)) (hs : MeasurableSet s)
    (hsub : s ⊆ (localChart hdim x o ho z).source) (f : Coord r → ℝ) :
    (∫ p in localChart hdim x o ho z '' s, pushforward hdim x o ho z f p) = ∫ w in s, f w := by
  rw [integral_image hdim x o ho z s hs hsub]
  exact setIntegral_congr_fun hs (fun w hw ↦ jacobian_mul_pushforward hdim x o ho z f (hsub hw))

theorem integrableOn_pushforward_iff (s : Set (Coord r)) (hs : MeasurableSet s)
    (hsub : s ⊆ (localChart hdim x o ho z).source) (f : Coord r → ℝ) :
    IntegrableOn (pushforward hdim x o ho z f) (localChart hdim x o ho z '' s) ↔ IntegrableOn f s := by
  rw [integrableOn_image_iff hdim x o ho z s hs hsub]
  exact integrableOn_congr_fun (fun w hw ↦ jacobian_mul_pushforward hdim x o ho z f (hsub hw)) hs

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCartesianChange
