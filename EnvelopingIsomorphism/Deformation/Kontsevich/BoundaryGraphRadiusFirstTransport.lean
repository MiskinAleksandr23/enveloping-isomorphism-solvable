import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphNativeMatching
import Mathlib.GroupTheory.Perm.Fin

/-! The simple real-cluster face in radial-first coordinates, matching the
literal radial-first convention used by ForestOrthantStokes. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphRadiusFirstTransport
open scoped Classical BigOperators
open MeasureTheory
open BoundaryGraphFaceFactorization BoundaryGraphOrderedIntegrals BoundaryGraphNativeTransport
open BoundaryGraphNativeOrientation
variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

def rotateRadius (r : ℕ) : (Fin (r+1) → ℝ) ≃L[ℝ] (Fin (r+1) → ℝ) :=
  (LinearEquiv.piCongrLeft' ℝ (fun _ ↦ ℝ) (finRotate (r+1))).toContinuousLinearEquiv

theorem rotateRadius_face (r : ℕ) (x : Fin r → ℝ) :
    rotateRadius r (BoxStokes.faceEmbedding (Fin.last r) 0 x) = BoxStokes.faceEmbedding 0 0 x := by
  funext j
  obtain ⟨j,rfl⟩ := (finRotate (r+1)).surjective j
  change ((Fin.last r).insertNth (α := fun _ ↦ ℝ) (0 : ℝ) x) ((finRotate (r+1)).symm (finRotate (r+1) j)) =
    (0 : Fin (r+1)).insertNth (α := fun _ ↦ ℝ) (0 : ℝ) x (finRotate (r+1) j)
  rw [Equiv.symm_apply_apply]
  cases j using Fin.lastCases with
  | last => simp
  | cast j =>
    have hr : finRotate (r+1) j.castSucc = j.succ := finRotate_of_lt j.isLt
    rw [hr]
    simpa only [Fin.succAbove_last, Fin.succAbove_zero] using
      (Fin.insertNth_apply_succAbove (α := fun _ ↦ ℝ) (Fin.last r) (0 : ℝ) x j).trans
        (Fin.insertNth_apply_succAbove (α := fun _ ↦ ℝ) (0 : Fin (r+1)) (0 : ℝ) x j).symm

theorem rotateRadius_symm_face (r : ℕ) (x : Fin r → ℝ) :
    (rotateRadius r).symm (BoxStokes.faceEmbedding 0 0 x) = BoxStokes.faceEmbedding (Fin.last r) 0 x := by
  rw [← rotateRadius_face, ContinuousLinearEquiv.symm_apply_apply]

/-- Moving the last radius axis to the first is the actual cyclic permutation. -/
theorem radiusPermutation_sign (r : ℕ) :
    (Equiv.Perm.sign (finRotate (r+1)) : ℝ) = (-1 : ℝ)^r := by
  simp [sign_finRotate]

/-- The genuine derivative determinant of the cyclic radius relocation. -/
theorem rotateRadius_det (r : ℕ) : (rotateRadius r).toLinearMap.det = (-1 : ℝ)^r := by
  rw [← LinearMap.det_toMatrix']
  have hm : LinearMap.toMatrix' (rotateRadius r).toLinearMap =
      (1 : Matrix (Fin (r+1)) (Fin (r+1)) ℝ).submatrix (finRotate (r+1)).symm id := by
    funext i j
    simp only [LinearMap.toMatrix'_apply, Matrix.submatrix_apply, Matrix.one_apply]
    change (Pi.single j (1 : ℝ) : Fin (r+1) → ℝ) ((finRotate (r+1)).symm i) = _
    simp only [Pi.single_apply, id_eq]
  rw [hm, Matrix.det_permute, Matrix.det_one, mul_one, Equiv.Perm.sign_symm]
  exact radiusPermutation_sign r


def radiusFirstCoordinates : BoundaryClusterFreeCoordinates i a S m ≃L[ℝ]
    (Fin (D (i := i) (a := a) (S := S) (l := l) (u := u) + 1) → ℝ) :=
  ambientNativeCoordinates.trans (rotateRadius _)

theorem radiusFirstCoordinates_symm_face (x : NativeReal (i := i) (a := a) (S := S) (l := l) (u := u)) :
    radiusFirstCoordinates.symm (BoxStokes.faceEmbedding 0 0 x) =
      BoundaryClusterFreeCoordinates.faceEmbedding (nativeCoordinates.symm x) := by
  simp only [radiusFirstCoordinates, ContinuousLinearEquiv.symm_trans_apply,
    rotateRadius_symm_face, ambientNativeCoordinates_symm_face]

variable (edges : Fin (D (i := i) (a := a) (S := S) (l := l) (u := u)) → BoundaryGraphFaceFactorization.Edge n m)

def radiusFirstForm : BoxStokes.Form (D (i := i) (a := a) (S := S) (l := l) (u := u)) :=
  fun x ↦ (graphForm (l := l) (u := u) edges (radiusFirstCoordinates.symm x)).compContinuousLinearMap
    radiusFirstCoordinates.symm.toContinuousLinearMap

theorem facePullback_radiusFirstForm (x : NativeReal (i := i) (a := a) (S := S) (l := l) (u := u)) :
    BoxStokes.facePullback (radiusFirstForm edges) 0 0 x (BoxStokes.standardBasis _) =
      nativeRealDensity edges x := by
  simp only [BoxStokes.facePullback, BoxStokes.fderiv_faceEmbedding, radiusFirstForm,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, radiusFirstCoordinates_symm_face]
  change graphForm edges (BoundaryClusterFreeCoordinates.faceEmbedding (nativeCoordinates.symm x))
    (fun j ↦ radiusFirstCoordinates.symm (BoxStokes.faceEmbedding 0 0 (Pi.single j (1 : ℝ)))) = _
  simp_rw [radiusFirstCoordinates_symm_face, nativeCoordinates_symm_single]
  rfl

/-- Literal zero-th lower-face integral in radial-first coordinates. -/
def outwardRadiusFirstIntegral : ℝ :=
  -((-1 : ℝ) ^ (0 : Fin (D (i := i) (a := a) (S := S) (l := l) (u := u) + 1)).val) *
    ∫ x in nativeDomain, BoxStokes.facePullback (radiusFirstForm edges) 0 0 x (BoxStokes.standardBasis _)

theorem outwardRadiusFirstIntegral_eq_ordered (ha : a ∈ S) (hi : i ∉ S) (hlu : l ≤ u) :
    outwardRadiusFirstIntegral edges =
      -(∫ z in GeometricWeights.realDomain (shapeN a S) (shapeM l u) ×ˢ
        GeometricWeights.realDomain (coarseN i S) (outsideM l u + 1),
          orderedRealDensity edges hlu z ∂volume.prod volume) := by
  unfold outwardRadiusFirstIntegral
  simp_rw [facePullback_radiusFirstForm]
  rw [integral_native_eq_ordered ha hi hlu]
  simp

/-- The two literal outward face conventions differ by precisely the
computed ambient cyclic-permutation orientation. -/
theorem outwardRadiusFirstIntegral_eq_native :
    outwardRadiusFirstIntegral edges = (-1 : ℝ)^D (i := i) (a := a) (S := S) (l := l) (u := u) *
      outwardNativeIntegral edges := by
  unfold outwardRadiusFirstIntegral outwardNativeIntegral
  simp_rw [facePullback_radiusFirstForm, facePullback_nativeAmbientForm]
  have h : ((-1 : ℝ)^D (i := i) (a := a) (S := S) (l := l) (u := u)) *
      ((-1 : ℝ)^D (i := i) (a := a) (S := S) (l := l) (u := u)) = 1 := by
    rw [← mul_pow]
    norm_num
  simp only [Fin.val_zero, pow_zero, neg_mul, one_mul]
  rw [mul_neg, ← mul_assoc, h, one_mul]

open BoundaryGraphOrderedCoordinates BoundaryGraphGraftReconstruction BoundaryGraphValenceSelection
open BoundaryGraphCanonicalFibreMatching KontsevichGraph.General
variable {q : Fin n → ℕ}

/-- The radial-first lower-face integral matches the actual finite graft
profile, with all inherited edge and chamber signs retained. -/
theorem normalized_radiusFirst_integral_eq_signed_graftProfile
    (Γ : Graph q m) (ha : a ∈ S) (hi : i ∉ S)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge q)
    (hcount : Fintype.card {j // (graphEdges Γ order j).1 ∈ S} = shapeDegree a S l u)
    (hlu : l < u)
    (hn : ∀ e : KontsevichGraph.General.Edge q, e.1 ∈ S → boundaryClusterCollapses S l u (Sum.inl (Γ.target e)))
    (hd : (orderedGraph Γ ha hi hlu).CoarseDistinct (centerSlot (le_of_lt hlu))) :
    (∏ v : Fin n, ((q v).factorial : ℝ)⁻¹) *
      ((2 * Real.pi) ^ (shapeDegree a S l u + coarseDegree i S l u))⁻¹ *
      outwardRadiusFirstIntegral (graphEdges Γ order) =
      -fibreSign Γ ha hi order hcount hlu *
        GraphGeneralWeightedGraft.graftProfile (centerSlot (le_of_lt hlu))
          (outerCoefficient Γ ha hi order hcount) (innerCoefficient Γ ha hi order hcount hlu)
          (orderedGraph Γ ha hi hlu) := by
  rw [outwardRadiusFirstIntegral_eq_ordered _ ha hi (le_of_lt hlu)]
  have h := normalized_integral_eq_signed_graftProfile Γ ha hi order hcount hlu hn hd
  calc
    _ = -((∏ v : Fin n, ((q v).factorial : ℝ)⁻¹) *
      ((2 * Real.pi) ^ (shapeDegree a S l u + coarseDegree i S l u))⁻¹ *
      (∫ z in GeometricWeights.realDomain (shapeN a S) (shapeM l u) ×ˢ
        GeometricWeights.realDomain (coarseN i S) (outsideM l u + 1),
          orderedRealDensity (graphEdges Γ order) (le_of_lt hlu) z ∂volume.prod volume)) := by ring
    _ = _ := by rw [h]; ring

/-- No structural, measure, orientation or convergence identity is assumed:
the nonzero actual face coefficient supplies every graph condition. -/
theorem normalized_radiusFirst_integral_eq_signed_graftProfile_of_nonzero
    (Γ : Graph q m) (ha : a ∈ S) (hi : i ∉ S)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge q)
    (hlu : l < u) (y : FaceCoordinates i a S m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u)
    (hne : nativeFaceDensity (l := l) (u := u) (graphEdges Γ order) y ≠ 0) :
    let hcount := BoundaryGraphDimensionVanishing.internal_count_eq_of_nativeFaceDensity_ne_zero (graphEdges Γ order)
      (graphEdges_noLoops Γ order) y hy hne
    (∏ v : Fin n, ((q v).factorial : ℝ)⁻¹) *
      ((2 * Real.pi) ^ (shapeDegree a S l u + coarseDegree i S l u))⁻¹ *
      outwardRadiusFirstIntegral (graphEdges Γ order) =
      -fibreSign Γ ha hi order hcount hlu *
        GraphGeneralWeightedGraft.graftProfile (centerSlot (le_of_lt hlu))
          (outerCoefficient Γ ha hi order hcount) (innerCoefficient Γ ha hi order hcount hlu)
          (orderedGraph Γ ha hi hlu) := by
  exact normalized_radiusFirst_integral_eq_signed_graftProfile Γ ha hi order _ hlu
    (BoundaryGraphAdmissibility.graph_noOutgoing_of_nativeFaceDensity_ne_zero Γ order y hy hne)
    (orderedGraph_coarseDistinct Γ ha hi hlu
      (BoundaryGraphAdmissibility.graph_coarseTarget_injective_of_nativeFaceDensity_ne_zero Γ order y hy hne))

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphRadiusFirstTransport
