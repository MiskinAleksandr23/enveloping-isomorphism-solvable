import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestProductOrientation

/-! Signed change of variables on the actual paired forest face, with the
original global-chart orientation and actual product-volume coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestOverlapJacobian
open PairedForestSimpleCluster PairedForestSmoothProduct PairedForestProductChart
open BoxStokes OrientedFormChangeVariables ForestRadialFaceClassification
open Set MeasureTheory
open scoped Classical Topology
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : kind 0 x o = .paired)

/-- The orientation is chosen from the proved global Cartesian/native
coordinate diffeomorphism, not supplied as a new orientation premise. -/
def productSign : ℝ := (exists_product_orientation hdim x o ho).choose

theorem productSign_eq_one_or_neg_one : productSign hdim x o ho = 1 ∨ productSign hdim x o ho = -1 :=
  (exists_product_orientation hdim x o ho).choose_spec.1

theorem productSign_jacobian (y : Coord r) :
    productSign hdim x o ho * jacobian (productToNative hdim x o ho) y = |jacobian (productToNative hdim x o ho) y| :=
  (exists_product_orientation hdim x o ho).choose_spec.2 y

/-- The target orientation includes the actual simple-chart basis sign,
the radial-last outward sign, and the actual product-coordinate orientation. -/
def productFaceSign : ℝ := simpleSign (m := m) x o ho * (-((-1 : ℝ) ^ r)) * productSign hdim x o ho

theorem jacobian_nativeFaceMap_product (z : Source hdim x o) {w : Coord r}
    (hw : w ∈ (localChart hdim x o ho z).source) :
    jacobian (nativeFaceMap hdim x o ho (phase hdim x o ho z)) w =
      jacobian (productToNative hdim x o ho) (PairedForestCartesianChange.chart hdim x o ho z w) *
        PairedForestCartesianChange.jacobian hdim x o ho z w := by
  rw [nativeFaceMap_eq_productChart, jacobian, fderiv_comp w
    ((contDiff_productToNative hdim x o ho).differentiable (by simp)).differentiableAt
    ((PairedForestCartesianChange.chart_contDiffAt hdim x o ho z
      ((PairedForestCartesianChange.chart_source hdim x o ho z).symm ▸ hw)).differentiableAt (by simp))]
  change LinearMap.det ((fderiv ℝ (productToNative hdim x o ho) _).toLinearMap.comp
    (fderiv ℝ (PairedForestCartesianChange.chart hdim x o ho z) w).toLinearMap) = _
  rw [LinearMap.det_comp]
  rfl

/-- The exact native outward coefficient is transported to actual Cartesian
product volume. All change-of-basis signs have been constructed. -/
theorem cartesian_face_orientation (z : Source hdim x o) {w : Coord r}
    (hw : w ∈ (localChart hdim x o ho z).source)
    (hsmall : SmallFace hdim x o ⟨w, localChart_source_subset hdim x o ho z hw⟩)
    (ε : ℝ) (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y = |jacobian (ForestGlobalGraphStokes.chart hdim x) y|) :
    ε * (-((-1 : ℝ) ^ (axis hdim x o).val)) * PairedForestCartesianChange.jacobian hdim x o ho z w =
      productFaceSign hdim x o ho * |PairedForestCartesianChange.jacobian hdim x o ho z w| := by
  let q : Source hdim x o := ⟨w, localChart_source_subset hdim x o ho z hw⟩
  have hslit : (phase hdim x o ho z : ℂ)⁻¹ * (phase hdim x o ho q : ℂ) ∈ Complex.slitPlane := hw.2.2
  have h := native_face_orientation_of_slit hdim x o ho q hsmall (phase hdim x o ho z) hslit ε hε
  rw [jacobian_nativeFaceMap_product hdim x o ho z hw, abs_mul,
    ← productSign_jacobian hdim x o ho] at h
  apply mul_left_cancel₀ (jacobian_productToNative_ne_zero hdim x o ho _)
  calc
    _ = ε * (-((-1 : ℝ) ^ (axis hdim x o).val)) *
        (jacobian (productToNative hdim x o ho) (PairedForestCartesianChange.chart hdim x o ho z w) *
          PairedForestCartesianChange.jacobian hdim x o ho z w) := by ring
    _ = _ := h
    _ = _ := by unfold productFaceSign; ring

/-- Actual signed face change of variables. The map, both measures, its
regularity/injectivity, normal scale, and orientation transport are all proved. -/
theorem signed_integral_image (z : Source hdim x o) (s : Set (Coord r)) (hs : MeasurableSet s)
    (hsub : s ⊆ (localChart hdim x o ho z).source)
    (hsmall : ∀ w (hw : w ∈ s), SmallFace hdim x o ⟨w, localChart_source_subset hdim x o ho z (hsub hw)⟩)
    (ε : ℝ) (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y = |jacobian (ForestGlobalGraphStokes.chart hdim x) y|)
    (g : Product x o ho → ℝ) :
    ε * (-((-1 : ℝ) ^ (axis hdim x o).val)) *
      (∫ w in s, PairedForestCartesianChange.jacobian hdim x o ho z w * g (localChart hdim x o ho z w)) =
      productFaceSign hdim x o ho * (∫ p in localChart hdim x o ho z '' s, g p) := by
  rw [PairedForestCartesianChange.integral_image hdim x o ho z s hs hsub g,
    ← integral_const_mul, ← integral_const_mul]
  apply setIntegral_congr_fun hs
  intro w hw
  dsimp only
  rw [← mul_assoc, cartesian_face_orientation hdim x o ho z (hsub hw) (hsmall w hw) ε hε]
  ring

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestOverlapJacobian
