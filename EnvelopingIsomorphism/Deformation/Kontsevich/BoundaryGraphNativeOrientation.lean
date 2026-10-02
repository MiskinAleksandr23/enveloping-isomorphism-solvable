import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphNativeTransport

/-! The literal lower-radius BoxStokes face in the inherited native order.
The ambient order appends radius after coarse, shape, boundary and center.
Its outward face sign and its measure transport are both explicit. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphNativeOrientation
open scoped Classical BigOperators
open MeasureTheory
open BoundaryGraphFaceFactorization BoundaryGraphOrderedIntegrals BoundaryGraphNativeTransport
variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

def appendRadius (r : ℕ) : ((Fin r → ℝ) × ℝ) ≃ₗ[ℝ] (Fin (r+1) → ℝ) where
  toFun x := (Fin.last r).insertNth (α := fun _ ↦ ℝ) x.2 x.1
  invFun x := (fun j ↦ x j.castSucc, x (Fin.last r))
  left_inv x := by
    apply Prod.ext
    · funext j
      simpa only [Fin.succAbove_last] using Fin.insertNth_apply_succAbove (α := fun _ ↦ ℝ) (Fin.last r) x.2 x.1 j
    · exact Fin.insertNth_apply_same (α := fun _ ↦ ℝ) _ _ _
  right_inv x := by
    funext j
    cases j using Fin.lastCases with
    | last => exact Fin.insertNth_apply_same (α := fun _ ↦ ℝ) _ _ _
    | cast j => simpa only [Fin.succAbove_last] using Fin.insertNth_apply_succAbove (α := fun _ ↦ ℝ) (Fin.last r) (x (Fin.last r)) (fun j ↦ x j.castSucc) j
  map_add' x y := by
    funext j
    cases j using Fin.succAboveCases (Fin.last r) <;> simp
  map_smul' c x := by
    funext j
    cases j using Fin.succAboveCases (Fin.last r) <;> simp

def ambientNativeCoordinates : BoundaryClusterFreeCoordinates i a S m ≃L[ℝ]
    (Fin (D (i := i) (a := a) (S := S) (l := l) (u := u) + 1) → ℝ) :=
  (BoundaryClusterFreeCoordinates.splitRadius (i := i) (a := a) (S := S) (m := m)).toContinuousLinearEquiv.trans
    ((nativeCoordinates.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)).trans
      (appendRadius _).toContinuousLinearEquiv)

theorem ambientNativeCoordinates_symm_face (x : NativeReal (i := i) (a := a) (S := S) (l := l) (u := u)) :
    ambientNativeCoordinates.symm (BoxStokes.faceEmbedding (Fin.last _) 0 x) =
      BoundaryClusterFreeCoordinates.faceEmbedding (nativeCoordinates.symm x) := by
  change BoundaryClusterFreeCoordinates.splitRadius.symm
    (nativeCoordinates.symm (fun j ↦ ((Fin.last _).insertNth (α := fun _ ↦ ℝ) (0 : ℝ) x) j.castSucc),
      ((Fin.last _).insertNth (α := fun _ ↦ ℝ) (0 : ℝ) x) (Fin.last _)) = _
  have h : (fun j ↦ ((Fin.last _).insertNth (α := fun _ ↦ ℝ) (0 : ℝ) x) j.castSucc) = x := by
    funext j
    simpa only [Fin.succAbove_last] using Fin.insertNth_apply_succAbove (α := fun _ ↦ ℝ) (Fin.last _) (0 : ℝ) x j
  rw [h, Fin.insertNth_apply_same]
  rfl

theorem ambientNativeCoordinates_symm_faceTangent
    (j : Fin (D (i := i) (a := a) (S := S) (l := l) (u := u))) :
    ambientNativeCoordinates.symm (BoxStokes.faceTangent (Fin.last _) (BoxStokes.standardBasis _ j)) =
      BoundaryClusterFreeCoordinates.faceEmbedding (nativeFaceBasis (nativeIndexEnum.symm j)) := by
  change ambientNativeCoordinates.symm (BoxStokes.faceEmbedding (Fin.last _) 0 (Pi.single j (1 : ℝ))) = _
  rw [ambientNativeCoordinates_symm_face, nativeCoordinates_symm_single]

variable (edges : Fin (D (i := i) (a := a) (S := S) (l := l) (u := u)) → BoundaryGraphFaceFactorization.Edge n m)

def nativeAmbientForm : BoxStokes.Form (D (i := i) (a := a) (S := S) (l := l) (u := u)) :=
  fun x ↦ (graphForm (l := l) (u := u) edges (ambientNativeCoordinates.symm x)).compContinuousLinearMap
    ambientNativeCoordinates.symm.toContinuousLinearMap

/-- The face coefficient used by BoxStokes is exactly the existing native
graph density, not an assumed orientation or coefficient comparison. -/
theorem facePullback_nativeAmbientForm (x : NativeReal (i := i) (a := a) (S := S) (l := l) (u := u)) :
    BoxStokes.facePullback (nativeAmbientForm edges) (Fin.last _) 0 x (BoxStokes.standardBasis _) =
      nativeRealDensity edges x := by
  simp only [BoxStokes.facePullback, BoxStokes.fderiv_faceEmbedding, nativeAmbientForm,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, ambientNativeCoordinates_symm_face]
  change graphForm edges (BoundaryClusterFreeCoordinates.faceEmbedding (nativeCoordinates.symm x))
    (fun j ↦ ambientNativeCoordinates.symm (BoxStokes.faceTangent (Fin.last _) (BoxStokes.standardBasis _ j))) = _
  simp_rw [ambientNativeCoordinates_symm_faceTangent]
  rfl

/-- The standard outward lower-face sign is `-(-1)^D`, since the actual
radius coordinate is last in the displayed native ambient order. -/
def outwardNativeIntegral : ℝ :=
  -((-1 : ℝ) ^ D (i := i) (a := a) (S := S) (l := l) (u := u)) *
    ∫ x in nativeDomain, BoxStokes.facePullback (nativeAmbientForm edges) (Fin.last _) 0 x (BoxStokes.standardBasis _)

theorem outwardNativeIntegral_eq_ordered (ha : a ∈ S) (hi : i ∉ S) (hlu : l ≤ u) :
    outwardNativeIntegral edges =
      -((-1 : ℝ) ^ D (i := i) (a := a) (S := S) (l := l) (u := u)) *
      ∫ z in GeometricWeights.realDomain (shapeN a S) (shapeM l u) ×ˢ
        GeometricWeights.realDomain (coarseN i S) (outsideM l u + 1),
          orderedRealDensity edges hlu z ∂volume.prod volume := by
  unfold outwardNativeIntegral
  simp_rw [facePullback_nativeAmbientForm]
  rw [integral_native_eq_ordered ha hi hlu]

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphNativeOrientation
