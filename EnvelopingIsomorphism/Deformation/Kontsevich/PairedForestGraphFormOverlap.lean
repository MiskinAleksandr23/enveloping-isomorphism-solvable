import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFaceEdgeForms
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestStaticFaceForms
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestProductOverlap
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestProductChart
import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceFactorization
import EnvelopingIsomorphism.Deformation.Kontsevich.NativePairedFaceIntegration
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestProductGraphDensity
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestWeightedSignedChange

/-! Actual paired native forest graph forms equal the genuine simple interior
face pullbacks, in the original edge order. Equality follows from full DR and
native angular differentiation, with no form-comparison hypothesis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestGraphFormOverlap
open Configuration ExtractedForestChildShapes ForestRadialFaceClassification
open PairedForestSimpleCluster PairedForestSmoothProduct PairedForestProductChart
open InteriorGraphFaceCoordinates RealForestFaceForms BoxStokes
open scoped Classical Topology
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : kind 0 x o = .paired) (z₀ : Source hdim x o)
variable {w : Coord r} (hw : w ∈ (localChart hdim x o ho z₀).source)
include hw

theorem nativePairForm_eq_pullback (p : DoubledPair (n+1) m) :
    nativePairForm hdim x o p w =
      (InteriorFaceEdgeForms.pairForm p (localChart hdim x o ho z₀ w)).compContinuousLinearMap
        (fderiv ℝ (localChart hdim x o ho z₀) w) := by
  have hs := (InteriorFaceDRCoordinates.contDiff_unit (i := (0 : Fin (n+1)))
    (a := anchor x o ho) (b := reference x o ho) (S := S x o ho) p).contDiffAt
      (x := localChart hdim x o ho z₀ w)
  have hunit (q : Source hdim x o) : InteriorFaceDRCoordinates.unit p
      (localChart hdim x o ho z₀ q.val) ≠ 0 :=
    InteriorFaceDRCoordinates.unit_ne_zero (anchor_mem x o ho) (reference_mem x o ho)
      (anchor_global x o ho) _
      (PairedForestProductOverlap.toProduct_openConditions hdim x o ho (phase hdim x o ho z₀) q) p
  have hp : (fun q ↦ (complexPhase (nativeUnit hdim x o p q) : ℂ)) =ᶠ[nhds w]
      (fun q ↦ (complexPhase (InteriorFaceDRCoordinates.unit p (localChart hdim x o ho z₀ q)) : ℂ)) := by
    apply Filter.eventuallyEq_of_mem ((ForestRadialFaceImmersion.isOpen_source hdim x o).mem_nhds
      (localChart_source_subset hdim x o ho z₀ hw))
    intro q hq
    have h := congrArg (fun d : CompactDRCoordinates.Ambient (n+1) m ↦ d.1 p)
      (PairedForestProductOverlap.ambient_toProduct hdim x o ho (phase hdim x o ho z₀) ⟨q,hq⟩)
    change InteriorFaceDRCoordinates.unit p (localChart hdim x o ho z₀ q) /
      (‖InteriorFaceDRCoordinates.unit p (localChart hdim x o ho z₀ q)‖ : ℂ) =
        (complexPhase (nativeUnit hdim x o p q) : ℂ) at h
    rw [← complexPhase_coe (hunit ⟨q,hq⟩)] at h
    exact h.symm
  unfold nativePairForm InteriorFaceEdgeForms.pairForm
  rw [angularPullback_eq_of_complexPhase_eventually (contDiff_nativeUnit hdim x o p).contDiffAt
    (hs.comp w (localChart_contDiffAt hdim x o ho z₀ hw))
    (nativeUnit_ne_zero hdim x o ⟨w,localChart_source_subset hdim x o ho z₀ hw⟩ p)
    (hunit ⟨w,localChart_source_subset hdim x o ho z₀ hw⟩) hp]
  exact angularPullback_comp_differentiable _ _ w (hs.differentiableAt (by simp))
    ((localChart_contDiffAt hdim x o ho z₀ hw).differentiableAt (by simp))

theorem nativeEdgeForm_eq_pullback (j : Fin (n+1)) (v : Fin (n+1) ⊕ Fin m)
    (hv : v ≠ Sum.inl j) :
    nativeEdgeForm hdim x o j v hv w =
      ((ClusterAngularCoordinates.extendedEdgeForm j v (toAngular (localChart hdim x o ho z₀ w))).compContinuousLinearMap
        (fderiv ℝ toAngular (localChart hdim x o ho z₀ w))).compContinuousLinearMap
          (fderiv ℝ (localChart hdim x o ho z₀) w) := by
  have he := InteriorFaceEdgeForms.edgeForm_eq_extended
    (anchor_mem x o ho) (reference_mem x o ho) (anchor_global x o ho) j v hv
    (localChart hdim x o ho z₀ w)
    (PairedForestProductOverlap.toProduct_openConditions hdim x o ho (phase hdim x o ho z₀)
      ⟨w, localChart_source_subset hdim x o ho z₀ hw⟩)
  rw [← he]
  unfold nativeEdgeForm InteriorFaceEdgeForms.edgeForm
  rw [nativePairForm_eq_pullback hdim x o ho z₀ hw, nativePairForm_eq_pullback hdim x o ho z₀ hw]
  ext V
  rfl

/-- Full graph equality, retaining the exact edge order and every actual
Fréchet derivative of the native and simple coordinate changes. -/
theorem graphForm_eq_pullback {q : ℕ} (edges : Fin q → ForestGraphTopForms.Edge (n+1) m) :
    (ForestOrthantGraphForms.graphForm 0 x edges (faceAmbient hdim x o w)).compContinuousLinearMap
      (fderiv ℝ (faceAmbient hdim x o) w) =
    (InteriorGraphFaceCoordinates.graphForm (fun j ↦ ((edges j).source, (edges j).target))
      (toAngular (localChart hdim x o ho z₀ w))).compContinuousLinearMap
        ((fderiv ℝ toAngular (localChart hdim x o ho z₀ w)).comp
          (fderiv ℝ (localChart hdim x o ho z₀) w)) := by
  ext V
  change Matrix.det (fun i j ↦ ForestGraphTopForms.edgeLinear (shapeData 0 x) (edges j)
    (ForestOrthantGraphForms.reflectedRealization 0 x (faceAmbient hdim x o w))
      ((fderiv ℝ (ForestOrthantGraphForms.reflectedRealization 0 x) (faceAmbient hdim x o w))
        ((fderiv ℝ (faceAmbient hdim x o) w) (V i)))) =
    Matrix.det (fun i j ↦ InteriorGraphFaceCoordinates.edgeLinear ((edges j).source, (edges j).target)
      (toAngular (localChart hdim x o ho z₀ w))
      ((fderiv ℝ toAngular (localChart hdim x o ho z₀ w))
        ((fderiv ℝ (localChart hdim x o ho z₀) w) (V i))))
  congr 1
  funext i j
  rw [ForestGraphTopForms.edgeLinear_apply]
  change _ = InteriorFiberAngleSplit.formLinear _ _
  rw [InteriorFiberAngleSplit.formLinear_apply]
  have hn := nativeEdgeForm_eq_orthant_edge hdim x o (edges j).source (edges j).target (edges j).nonloop w
  have hs := nativeEdgeForm_eq_pullback hdim x o ho z₀ hw (edges j).source (edges j).target (edges j).nonloop
  exact congrArg (fun ω : Coord r [⋀^Fin 1]→L[ℝ] ℝ ↦ ω (fun _ ↦ V i)) (hn.symm.trans hs)

/-- The version using literally the native GraphForms edge array of global
forest Stokes, without any relabeling or sign permutation. -/
theorem native_graphForm_eq_pullback (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source) :
    (ForestOrthantGraphForms.graphForm 0 x (fun j ↦ ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j))
      (faceAmbient hdim x o w)).compContinuousLinearMap (fderiv ℝ (faceAmbient hdim x o) w) =
    (InteriorGraphFaceCoordinates.graphForm (fun j ↦ ((edges j).source, (edges j).target))
      (toAngular (localChart hdim x o ho z₀ w))).compContinuousLinearMap
        ((fderiv ℝ toAngular (localChart hdim x o ho z₀ w)).comp
          (fderiv ℝ (localChart hdim x o ho z₀) w)) := by
  simpa only [ForestPositiveGraphForms.forestEdge, Equiv.swap_self, Equiv.refl_apply, Equiv.coe_refl, Sum.map_id_id, id_eq] using
    graphForm_eq_pullback hdim x o ho z₀ hw (fun j ↦ ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j))


/-- Literal native graph coefficient in the actual signed Cartesian chart. -/
theorem native_graphDensity_eq_jacobian (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source) :
    (ForestOrthantGraphForms.graphForm 0 x
      (fun j ↦ ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j))
      (faceAmbient hdim x o w)).compContinuousLinearMap
        (fderiv ℝ (faceAmbient hdim x o) w) (standardBasis r) =
    PairedForestCartesianChange.jacobian hdim x o ho z₀ w *
      PairedForestProductGraphDensity.productDensity hdim x o ho edges
        (localChart hdim x o ho z₀ w) := by
  rw [native_graphForm_eq_pullback hdim x o ho z₀ hw edges hloop]
  exact PairedForestProductGraphDensity.pullback_density hdim x o ho edges z₀ hw

open ForestGlobalGraphStokes ForestRadialFaceLocalization ForestOrthantRealization
open PairedForestOverlapJacobian MeasureTheory CompactOrthantStokes

/-- The genuine compact native face density, with its original ambient cutoff,
becomes the signed Jacobian times the simple graph density. -/
theorem nativeDensity_eq_jacobian
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (κ : Ambient 0 x → ℝ) (hmatch : LocalizationAgreement x ρ edges hloop κ) :
    NativePairedFaceIntegration.nativeDensity hdim x o ρ edges hloop κ w =
      PairedForestCartesianChange.jacobian hdim x o ho z₀ w *
        (productCutoff x o ho ρ (localChart hdim x o ho z₀ w) *
          PairedForestProductGraphDensity.productDensity hdim x o ho edges
            (localChart hdim x o ho z₀ w)) := by
  have hw' := localChart_source_subset hdim x o ho z₀ hw
  have hi := ForestPositiveChartSmooth.includeOrthant_ofAmbient 0 x
    (faceAmbient hdim x o w) (faceAmbient_nonneg hdim x o w hw'.1)
  have hm := hmatch (ForestPositiveChartSmooth.ofAmbient 0 x (faceAmbient hdim x o w))
  rw [hi, ChartCutoffSupport.zeroPullback_source _ _ hw'.2] at hm
  have hcut := productCutoff_toProduct hdim x o ho ρ (phase hdim x o ho z₀) ⟨w, hw'⟩
  have hD := ((sourceCoordinates hdim x).symm.hasFDerivAt.comp w
    (hasFDerivAt_faceEmbedding (axis hdim x o) 0 w)).fderiv
  change fderiv ℝ (faceAmbient hdim x o) w = _ at hD
  have hn := native_graphDensity_eq_jacobian hdim x o ho z₀ hw edges hloop
  rw [hD] at hn
  simp only [NativePairedFaceIntegration.nativeDensity, facePullback, localForm,
    linearForm, ContinuousAlternatingMap.compContinuousLinearMap_apply, fderiv_faceEmbedding]
  change ForestOrthantLocalization.localized 0 x ρ
    (fun j ↦ ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j)) κ
      (faceAmbient hdim x o w) _ = _
  rw [hm]
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  change productCutoff x o ho ρ (localChart hdim x o ho z₀ w) =
    CompactDRAmbientPartition.cutoff 0 ρ
      (ForestOrthantCharts.chart 0 x (ForestPositiveChartSmooth.ofAmbient 0 x (faceAmbient hdim x o w))) at hcut
  rw [← hcut]
  change productCutoff x o ho ρ (localChart hdim x o ho z₀ w) *
    ((ForestOrthantGraphForms.graphForm 0 x _ (faceAmbient hdim x o w)).compContinuousLinearMap
      ((sourceCoordinates hdim x).symm.toContinuousLinearMap.comp (faceTangent (axis hdim x o)))
        (standardBasis r)) = _
  rw [hn]
  ring


omit hw
open PairedForestCountableLocalization OrientedFormChangeVariables

variable (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
  (edges : Fin r → GraphForms.Edge n m)
  (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
  (κ : Ambient 0 x → ℝ)
  (hmatch : LocalizationAgreement x ρ edges hloop κ)
  (hρ : tsupport (CompactDRAmbientPartition.cutoff 0 ρ) ⊆ (ForestChartOrientation.smallChart 0 x).target)
  (ε : ℝ) (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
    ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y = |jacobian (ForestGlobalGraphStokes.chart hdim x) y|)

include hmatch hρ hε

/-- The supported native density carries exactly the outward product sign. -/
theorem signed_nativeDensity_eq_abs_jacobian {w : Coord r}
    (hw : w ∈ (localChart hdim x o ho z₀).source) :
    (ε * -((-1 : ℝ) ^ (axis hdim x o).val)) *
        NativePairedFaceIntegration.nativeDensity hdim x o ρ edges hloop κ w =
      |PairedForestCartesianChange.jacobian hdim x o ho z₀ w| *
        (productFaceSign hdim x o ho * (productCutoff x o ho ρ (localChart hdim x o ho z₀ w) *
          PairedForestProductGraphDensity.productDensity hdim x o ho edges (localChart hdim x o ho z₀ w))) := by
  rw [nativeDensity_eq_jacobian hdim x o ho z₀ hw ρ edges hloop κ hmatch]
  by_cases hz : productCutoff x o ho ρ (localChart hdim x o ho z₀ w) = 0
  · simp only [hz, zero_mul, mul_zero]
  · have hsmall := smallFace_of_productCutoff_ne_zero hdim x o ho ρ hρ (phase hdim x o ho z₀)
      ⟨w, localChart_source_subset hdim x o ho z₀ hw⟩ hz
    have h := cartesian_face_orientation hdim x o ho z₀ hw hsmall ε hε
    calc
      _ = (ε * -((-1 : ℝ) ^ (axis hdim x o).val) *
        PairedForestCartesianChange.jacobian hdim x o ho z₀ w) *
          (productCutoff x o ho ρ (localChart hdim x o ho z₀ w) *
            PairedForestProductGraphDensity.productDensity hdim x o ho edges (localChart hdim x o ho z₀ w)) := by ring
      _ = _ := by rw [h]; ring

/-- Genuine simple graph integrals on the countable chart pieces. -/
def localizedGraphIntegral (j : Index hdim x o ho) : ℝ :=
  ∫ p in localChart hdim x o ho j.val '' piece hdim x o ho j,
    productCutoff x o ho ρ p * PairedForestProductGraphDensity.productDensity hdim x o ho edges p

theorem signed_integral_piece_eq (j : Index hdim x o ho) :
    (ε * -((-1 : ℝ) ^ (axis hdim x o).val)) *
      (∫ w in piece hdim x o ho j, NativePairedFaceIntegration.nativeDensity hdim x o ρ edges hloop κ w) =
    productFaceSign hdim x o ho * localizedGraphIntegral hdim x o ho ρ edges j := by
  have heq : (∫ w in piece hdim x o ho j,
      NativePairedFaceIntegration.nativeDensity hdim x o ρ edges hloop κ w) =
      ∫ w in piece hdim x o ho j, PairedForestCartesianChange.jacobian hdim x o ho j.val w *
        (productCutoff x o ho ρ (localChart hdim x o ho j.val w) *
          PairedForestProductGraphDensity.productDensity hdim x o ho edges (localChart hdim x o ho j.val w)) :=
    setIntegral_congr_fun (measurableSet_piece hdim x o ho j) fun w hw ↦
      nativeDensity_eq_jacobian hdim x o ho j.val (piece_subset hdim x o ho j hw) ρ edges hloop κ hmatch
  rw [heq]
  exact signed_integral_weighted_image hdim x o ho j.val _
    (measurableSet_piece hdim x o ho j) (piece_subset hdim x o ho j) ρ hρ ε hε _

/-- Integrability of the literal graph density is inherited from the actual
compact native form, with no integrability assumption on the target density. -/
theorem integrableOn_localizedGraphDensity
    (hω : ContDiff ℝ 1 (localForm hdim x ρ edges hloop κ))
    (hc : HasCompactSupport (localForm hdim x ρ edges hloop κ))
    (j : Index hdim x o ho) :
    IntegrableOn (fun p ↦ productCutoff x o ho ρ p *
      PairedForestProductGraphDensity.productDensity hdim x o ho edges p)
      (localChart hdim x o ho j.val '' piece hdim x o ho j) := by
  have hsimp : simpleSign (m := m) x o ho ≠ 0 := by
    intro h
    simpa [h] using simpleSign_sq (m := m) x o ho
  have hsign : productFaceSign hdim x o ho ≠ 0 := by
    rcases productSign_eq_one_or_neg_one hdim x o ho with h | h <;>
      simp [productFaceSign, h, hsimp]
  apply (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hsign) _).mp
  apply (PairedForestCartesianChange.integrableOn_image_iff hdim x o ho j.val _
    (measurableSet_piece hdim x o ho j) (piece_subset hdim x o ho j) _).mpr
  have hn := (NativePairedFaceIntegration.integrableOn_nativeDensity hdim x o ρ edges hloop κ hω hc).mono_set
    ((piece_subset hdim x o ho j).trans (localChart_source_subset hdim x o ho j.val))
  exact IntegrableOn.congr_fun (hn.const_mul (ε * -((-1 : ℝ) ^ (axis hdim x o).val)))
    (fun w hw ↦ signed_nativeDensity_eq_abs_jacobian hdim x o ho j.val ρ edges hloop κ hmatch hρ ε hε
      (piece_subset hdim x o ho j hw)) (measurableSet_piece hdim x o ho j)

/-- A convergent sum of literal simple graph integrals equals the original
oriented native Stokes face contribution. -/
theorem hasSum_localizedGraphIntegral
    (hω : ContDiff ℝ 1 (localForm hdim x ρ edges hloop κ))
    (hc : HasCompactSupport (localForm hdim x ρ edges hloop κ)) :
    HasSum (fun j : Index hdim x o ho ↦
      productFaceSign hdim x o ho * localizedGraphIntegral hdim x o ho ρ edges j)
      (ε * contribution hdim x (localForm hdim x ρ edges hloop κ) o) := by
  have h := (hasSum_integral_piece hdim x o ho _
    (NativePairedFaceIntegration.integrableOn_nativeDensity hdim x o ρ edges hloop κ hω hc)).mul_left
      (ε * -((-1 : ℝ) ^ (axis hdim x o).val))
  rw [contribution_eq_integral_source hdim x o ρ edges hloop κ hmatch]
  have heq := fun j ↦ signed_integral_piece_eq hdim x o ho ρ edges hloop κ hmatch hρ ε hε j
  simp only [heq] at h
  simpa only [NativePairedFaceIntegration.nativeDensity, smul_eq_mul, mul_assoc] using h

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestGraphFormOverlap
