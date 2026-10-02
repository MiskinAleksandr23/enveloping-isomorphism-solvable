import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCoorientation
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCartesianChange

/-! Actual global change from Cartesian planar/coarse coordinates to the
native radial-last simple face coordinates. It is a smooth global bijection,
so its orientation is derived on the whole connected coordinate space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestOverlapJacobian
open PairedForestSimpleCluster PairedForestSmoothProduct PairedForestFullOverlap
open InteriorGraphFaceCoordinates InteriorFiberAngleSplit BoxStokes
open ForestRadialFaceImmersion OrientedFormChangeVariables Set
open scoped Classical Topology
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : ForestRadialFaceClassification.kind 0 x o = .paired)

def angularToProduct (q : Angular x o ho) : PairedForestSmoothProduct.Product x o ho :=
  ((q.2.2.2.1, fun j ↦ q.2.1 (shapeEnum.symm j) / circleParameter q.2.2.2.1),
    (fun j ↦ q.1 (coarseEnum.symm j), q.2.2.1))

theorem angularToProduct_toAngular (p : PairedForestSmoothProduct.Product x o ho) :
    angularToProduct x o ho (toAngular p) = p := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext j
      simp [angularToProduct, toAngular, circleParameter_ne_zero]
  · apply Prod.ext
    · funext j
      simp [angularToProduct, toAngular]
    · rfl

theorem toAngular_angularToProduct (q : Angular x o ho) (hq : q.toFree.radius = 0) :
    toAngular (angularToProduct x o ho q) = q := by
  apply Prod.ext
  · funext j
    simp [angularToProduct, toAngular]
  · apply Prod.ext
    · funext j
      simp only [angularToProduct, toAngular, Equiv.symm_apply_apply]
      exact mul_div_cancel₀ _ (circleParameter_ne_zero q.2.2.2.1)
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · exact hq.symm

theorem contDiff_angularToProduct : ContDiff ℝ ⊤ (angularToProduct x o ho) := by
  apply ContDiff.prodMk
  · apply ContDiff.prodMk (by fun_prop)
    apply contDiff_pi.mpr
    intro j
    have hn : ContDiff ℝ ⊤ (fun q : Angular x o ho ↦ q.2.1 (shapeEnum.symm j)) := by fun_prop
    have hd : ContDiff ℝ ⊤ (fun q : Angular x o ho ↦ circleParameter q.2.2.2.1) :=
      contDiff_circleParameter.comp (by fun_prop)
    simpa only [angularToProduct, div_eq_mul_inv, Pi.inv_apply] using
      hn.mul (hd.inv (fun q ↦ circleParameter_ne_zero q.2.2.2.1))

  · fun_prop [angularToProduct]

private theorem projection_tangent (y : Coord r) : faceProjection (Fin.last r) (faceTangent (Fin.last r) y) = y := by
  funext j
  simp [faceProjection, faceTangent]

private theorem tangent_projection (y : Coord (r + 1)) (hy : y (Fin.last r) = 0) :
    faceTangent (Fin.last r) (faceProjection (Fin.last r) y) = y := by
  funext j
  induction j using (Fin.last r).succAboveCases with
  | x => simpa [faceTangent] using hy.symm
  | p j => simp [faceTangent, faceProjection]

def productToNative (y : Coord r) : Coord r :=
  faceProjection (Fin.last r) (simpleCoordinates hdim x o ho
    (toAngular (PairedForestCartesianChange.cartesian hdim x o ho y)))

def nativeToProduct (y : Coord r) : Coord r :=
  (PairedForestCartesianChange.cartesian hdim x o ho).symm
    (angularToProduct x o ho ((simpleCoordinates hdim x o ho).symm (faceTangent (Fin.last r) y)))

theorem nativeToProduct_productToNative (y : Coord r) :
    nativeToProduct hdim x o ho (productToNative hdim x o ho y) = y := by
  unfold nativeToProduct productToNative
  rw [tangent_projection _ (by rw [simpleCoordinates_radius]; rfl),
    ContinuousLinearEquiv.symm_apply_apply, angularToProduct_toAngular, ContinuousLinearEquiv.symm_apply_apply]

theorem productToNative_nativeToProduct (y : Coord r) :
    productToNative hdim x o ho (nativeToProduct hdim x o ho y) = y := by
  unfold productToNative nativeToProduct
  rw [ContinuousLinearEquiv.apply_symm_apply, toAngular_angularToProduct]
  · rw [ContinuousLinearEquiv.apply_symm_apply, projection_tangent]
  · rw [← simpleCoordinates_radius hdim x o ho, ContinuousLinearEquiv.apply_symm_apply]
    simp [faceTangent]

theorem contDiff_productToNative : ContDiff ℝ ⊤ (productToNative hdim x o ho) :=
  (faceProjection (Fin.last r)).contDiff.comp
    ((simpleCoordinates hdim x o ho).contDiff.comp
      (contDiff_toAngular.comp (PairedForestCartesianChange.cartesian hdim x o ho).contDiff))

theorem contDiff_nativeToProduct : ContDiff ℝ ⊤ (nativeToProduct hdim x o ho) :=
  (PairedForestCartesianChange.cartesian hdim x o ho).symm.contDiff.comp
    ((contDiff_angularToProduct x o ho).comp
      ((simpleCoordinates hdim x o ho).symm.contDiff.comp (faceTangent (Fin.last r)).contDiff))

def productNativeHomeomorph : Coord r ≃ₜ Coord r where
  toFun := productToNative hdim x o ho
  invFun := nativeToProduct hdim x o ho
  left_inv := nativeToProduct_productToNative hdim x o ho
  right_inv := productToNative_nativeToProduct hdim x o ho
  continuous_toFun := (contDiff_productToNative hdim x o ho).continuous
  continuous_invFun := (contDiff_nativeToProduct hdim x o ho).continuous

/-- A single actual orientation sign works on the entire Cartesian product,
including every phase angle. No sign constancy is assumed on disconnected charts. -/
theorem exists_product_orientation : ∃ τ : ℝ, (τ = 1 ∨ τ = -1) ∧
    ∀ y, τ * jacobian (productToNative hdim x o ho) y = |jacobian (productToNative hdim x o ho) y| := by
  obtain ⟨τ, hτ, hs⟩ := SignedFormChangeVariables.exists_sign
    (productNativeHomeomorph hdim x o ho).toOpenPartialHomeomorph
    ((contDiff_productToNative hdim x o ho).of_le (by simp)).contDiffOn
    ((contDiff_nativeToProduct hdim x o ho).of_le (by simp)).contDiffOn
    univ (subset_refl _) isPreconnected_univ
  exact ⟨τ, hτ, fun y ↦ hs y (mem_univ y)⟩

theorem jacobian_productToNative_ne_zero (y : Coord r) : jacobian (productToNative hdim x o ho) y ≠ 0 :=
  SignedFormChangeVariables.jacobian_ne_zero (productNativeHomeomorph hdim x o ho).toOpenPartialHomeomorph
    ((contDiff_productToNative hdim x o ho).of_le (by simp)).contDiffOn
    ((contDiff_nativeToProduct hdim x o ho).of_le (by simp)).contDiffOn y (mem_univ y)

/-- The native simple face map is exactly the actual product chart followed
by the above globally defined native coordinate change. -/
theorem nativeFaceMap_eq_productChart (z : Source hdim x o) :
    nativeFaceMap hdim x o ho (phase hdim x o ho z) =
      productToNative hdim x o ho ∘ PairedForestCartesianChange.chart hdim x o ho z := by
  funext w
  unfold nativeFaceMap productToNative
  simp only [Function.comp_apply]
  rw [PairedForestCartesianChange.cartesian_chart]
  change faceProjection (Fin.last r) (simpleCoordinates hdim x o ho
      (overlap hdim x o ho (phase hdim x o ho z) (faceEmbedding (ForestRadialFaceClassification.axis hdim x o) 0 w))) =
    faceProjection (Fin.last r) (simpleCoordinates hdim x o ho (toAngular (toProduct hdim x o ho (phase hdim x o ho z) w)))
  congr 2
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · exact PairedForestNormalScale.simpleRadius_face hdim x o ho w

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestOverlapJacobian
