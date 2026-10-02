import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityBoundaryGraphCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphRadiusFirstTransport

/-! Literal radial-first outward integral on the surviving all-interior
infinity face, in its genuine increasing shape chamber. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InfinityBoundaryGraphIntegral
open scoped Classical
open MeasureTheory BoundaryAnchoredInfinityFreeCoordinates InfinityBoundaryGraphFactorization
open InfinityBoundaryGraphCoordinates BoundaryGraphNativeOrientation BoundaryGraphRadiusFirstTransport
variable {n m : ℕ} {a : Fin n} {o : Fin m} {l u : Fin (m+1)}
variable (ho : o ∉ boundaryClusterBlock l u)
    (hall : ∀ j : Fin m, j ≠ o → j ∈ boundaryClusterBlock l u)

abbrev Degree (a : Fin n) (l u : Fin (m+1)) := GraphForms.dimension (shapeN a) (shapeM l u)

def faceCoordinates : FaceCoordinates a m o ≃L[ℝ] (Fin (Degree a l u) → ℝ) :=
  (shapeEquiv ho hall).trans (GraphForms.realCoordinates _ _).toContinuousLinearEquiv

def radialCoordinates : BoundaryAnchoredInfinityFreeCoordinates a m o ≃L[ℝ]
    (Fin (Degree a l u + 1) → ℝ) :=
  (ContinuousLinearEquiv.prodAssoc ℝ (BoundaryAnchoredInfinityFreeInterior a → ℂ)
    (BoundaryAnchoredInfinityFreeBoundary o → ℝ) ℝ).symm.trans
    (((faceCoordinates ho hall).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)).trans
      ((appendRadius _).toContinuousLinearEquiv.trans (rotateRadius _)))

theorem radialCoordinates_symm_face (x : Fin (Degree a l u) → ℝ) :
    (radialCoordinates ho hall).symm (BoxStokes.faceEmbedding 0 0 x) =
      faceEmbedding ((faceCoordinates ho hall).symm x) := by
  simp only [radialCoordinates, ContinuousLinearEquiv.symm_trans_apply, rotateRadius_symm_face]
  change (((faceCoordinates ho hall).symm
    (fun j ↦ (Fin.last _).insertNth (α := fun _ ↦ ℝ) (0 : ℝ) x j.castSucc)).1,
    ((faceCoordinates ho hall).symm
    (fun j ↦ (Fin.last _).insertNth (α := fun _ ↦ ℝ) (0 : ℝ) x j.castSucc)).2,
    (Fin.last _).insertNth (α := fun _ ↦ ℝ) (0 : ℝ) x (Fin.last _)) = _
  have he : (fun j ↦ (Fin.last _).insertNth (α := fun _ ↦ ℝ) (0 : ℝ) x j.castSucc) = x := by
    funext j
    simpa only [Fin.succAbove_last] using
      Fin.insertNth_apply_succAbove (α := fun _ ↦ ℝ) (Fin.last _) (0 : ℝ) x j
  rw [he, Fin.insertNth_apply_same]
  rfl

def nativeDomain : Set (Fin (Degree a l u) → ℝ) :=
  {x | (faceEmbedding ((faceCoordinates ho hall).symm x)).OpenConditions l u}

theorem nativeDomain_eq_realDomain (hlu : l ≤ u) :
    nativeDomain (a := a) ho hall = GeometricWeights.realDomain (shapeN a) (shapeM l u) := by
  ext x
  rw [nativeDomain, Set.mem_setOf_eq, face_open_iff_admissible hlu ho hall]
  change GraphForms.Admissible ((shapeEquiv ho hall)
      ((faceCoordinates ho hall).symm x)) ↔ _
  simp only [faceCoordinates, ContinuousLinearEquiv.symm_trans_apply, ContinuousLinearEquiv.apply_symm_apply]
  rfl

variable (edges : Fin (Degree a l u) → Edge n m)

def radialForm : BoxStokes.Form (Degree a l u) := fun x ↦
  (graphForm (l := l) (u := u) edges ((radialCoordinates ho hall).symm x)).compContinuousLinearMap
    (radialCoordinates ho hall).symm.toContinuousLinearMap

set_option maxHeartbeats 800000 in
theorem facePullback_eq_native (x : Fin (Degree a l u) → ℝ) :
    BoxStokes.facePullback (radialForm ho hall edges) 0 0 x (BoxStokes.standardBasis _) =
      ((graphForm (l := l) (u := u) edges (faceEmbedding ((faceCoordinates ho hall).symm x))).compContinuousLinearMap
        faceEmbedding) (fun j ↦ (faceCoordinates ho hall).symm (Pi.single j (1 : ℝ))) := by
  simp only [BoxStokes.facePullback, BoxStokes.fderiv_faceEmbedding, radialForm,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, radialCoordinates_symm_face]
  change graphForm (l := l) (u := u) _ (faceEmbedding ((faceCoordinates ho hall).symm x))
    (fun j ↦ (radialCoordinates ho hall).symm (BoxStokes.faceEmbedding 0 0 (Pi.single j (1 : ℝ)))) = _
  simp_rw [radialCoordinates_symm_face]
  rfl

set_option maxHeartbeats 800000 in
theorem facePullback_radialForm
    (hin : ∀ j, boundaryAnchoredInfinityCollapses l u (Sum.inl (edges j).2))
    (x : Fin (Degree a l u) → ℝ) (hx : x ∈ nativeDomain ho hall) :
    BoxStokes.facePullback (radialForm ho hall edges) 0 0 x (BoxStokes.standardBasis _) =
      GeometricWeights.realDensity (fun j ↦ shapeEdge (a := a) (edges j) (hin j)) x := by
  rw [facePullback_eq_native]
  rw [graphForm_face_eq_shape ho edges hin _ hx]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def]
  change GraphForms.topForm _ ((shapeEquiv ho hall) ((faceCoordinates ho hall).symm x))
    (fun j ↦ (shapeEquiv ho hall) ((faceCoordinates ho hall).symm (Pi.single j (1 : ℝ)))) = _
  simp only [faceCoordinates, ContinuousLinearEquiv.symm_trans_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hbasis (j : Fin (Degree a l u)) :
      (GraphForms.realCoordinates (shapeN a) (shapeM l u)).symm (Pi.single j (1 : ℝ)) =
        GraphForms.realBasis (shapeN a) (shapeM l u) j := by
    simp [GraphForms.realCoordinates, Module.Basis.equivFun_symm_apply]
  change GraphForms.topForm _ ((GraphForms.realCoordinates _ _).symm x)
    (fun j ↦ (GraphForms.realCoordinates _ _).symm (Pi.single j (1 : ℝ))) = _
  simp_rw [hbasis]
  rfl

def outwardIntegral : ℝ := -∫ x in nativeDomain ho hall,
  BoxStokes.facePullback (radialForm ho hall edges) 0 0 x (BoxStokes.standardBasis _)

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 800000 in
theorem outwardIntegral_eq_shape (hlu : l ≤ u)
    (hin : ∀ j, boundaryAnchoredInfinityCollapses l u (Sum.inl (edges j).2)) :
    outwardIntegral ho hall edges =
      -GeometricWeights.rawIntegral (fun j ↦ shapeEdge (a := a) (edges j) (hin j)) := by
  unfold outwardIntegral GeometricWeights.rawIntegral
  congr 1
  rw [← nativeDomain_eq_realDomain (a := a) ho hall hlu]
  apply setIntegral_congr_fun
  · rw [nativeDomain_eq_realDomain (a := a) ho hall hlu]
    exact (GeometricWeights.isOpen_realDomain (shapeN a) (shapeM l u)).measurableSet
  · intro x hx
    simpa only using facePullback_radialForm (a := a) (o := o) (l := l) (u := u) ho hall edges hin x hx

end EnvelopingIsomorphism.Deformation.Kontsevich.InfinityBoundaryGraphIntegral
