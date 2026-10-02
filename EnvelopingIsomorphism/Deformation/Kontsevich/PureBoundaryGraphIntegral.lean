import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryGraphQuotient
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphRadiusFirstTransport

/-! The literal radial-first outward integral of a two-point pure boundary
face is the negative of the genuine increasing-chamber quotient graph integral.
The chart, coordinate frame and outward sign are explicit. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryGraphIntegral
open scoped Classical BigOperators
open MeasureTheory GraphForms PureBoundaryClusterForms PureBoundaryGraphQuotient
open BoundaryGraphFaceFactorization BoundaryGraphNativeOrientation BoundaryGraphRadiusFirstTransport
variable {n m : ℕ} {l u : Fin (m + 1)}
variable (hlu : l ≤ u) (a b : Fin m)
  (ha : a ∈ boundaryClusterBlock l u) (hb : b ∈ boundaryClusterBlock l u)
  (hab : a ≠ b) (hcard : (boundaryClusterBlock l u).card = 2)

abbrev Degree := dimension n (outsideM l u + 1)

def faceCoordinates : Face n (boundaryClusterBlock l u) a b ≃L[ℝ]
    (Fin (Degree (n := n) (l := l) (u := u)) → ℝ) :=
  (twoPointCoordinates hlu a b ha hb hab hcard).trans
    (realCoordinates n (outsideM l u + 1)).toContinuousLinearEquiv

def radialCoordinates : Ambient n (boundaryClusterBlock l u) a b ≃L[ℝ]
    (Fin (Degree (n := n) (l := l) (u := u) + 1) → ℝ) :=
  (ContinuousLinearEquiv.prodComm ℝ _ _).trans
    (((faceCoordinates hlu a b ha hb hab hcard).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)).trans
      ((appendRadius _).toContinuousLinearEquiv.trans (rotateRadius _)))

theorem radialCoordinates_symm_face (x : Fin (Degree (n := n) (l := l) (u := u)) → ℝ) :
    (radialCoordinates hlu a b ha hb hab hcard).symm (BoxStokes.faceEmbedding 0 0 x) =
      faceInclusion _ a b ((faceCoordinates hlu a b ha hb hab hcard).symm x) := by
  simp only [radialCoordinates, ContinuousLinearEquiv.symm_trans_apply, rotateRadius_symm_face]
  change ((Fin.last _).insertNth (α := fun _ ↦ ℝ) (0 : ℝ) x (Fin.last _),
    (faceCoordinates hlu a b ha hb hab hcard).symm
    (fun j ↦ (Fin.last _).insertNth (α := fun _ ↦ ℝ) (0 : ℝ) x j.castSucc)) = _
  have he : (fun j ↦ (Fin.last _).insertNth (α := fun _ ↦ ℝ) (0 : ℝ) x j.castSucc) = x := by
    funext j
    simpa only [Fin.succAbove_last] using
      Fin.insertNth_apply_succAbove (α := fun _ ↦ ℝ) (Fin.last _) (0 : ℝ) x j
  rw [he, Fin.insertNth_apply_same]
  rfl

variable (edges : Fin (Degree (n := n) (l := l) (u := u)) → GraphForms.Edge n m)

def radialForm : BoxStokes.Form (Degree (n := n) (l := l) (u := u)) := fun x ↦
  (scaledGraphForm (boundaryClusterBlock l u) a b edges
    ((radialCoordinates hlu a b ha hb hab hcard).symm x)).compContinuousLinearMap
      (radialCoordinates hlu a b ha hb hab hcard).symm.toContinuousLinearMap

set_option maxHeartbeats 800000 in
theorem facePullback_radialForm (x : Fin (Degree (n := n) (l := l) (u := u)) → ℝ) :
    BoxStokes.facePullback (radialForm hlu a b ha hb hab hcard edges) 0 0 x
      (BoxStokes.standardBasis _) =
    GeometricWeights.realDensity (fun j ↦ quotientEdge hlu (edges j)) x := by
  simp only [BoxStokes.facePullback, BoxStokes.fderiv_faceEmbedding, radialForm,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, radialCoordinates_symm_face]
  change scaledGraphForm _ a b edges (faceInclusion _ a b
      ((faceCoordinates hlu a b ha hb hab hcard).symm x))
    (fun j ↦ (radialCoordinates hlu a b ha hb hab hcard).symm
      (BoxStokes.faceEmbedding 0 0 (Pi.single j (1 : ℝ)))) = _
  simp_rw [radialCoordinates_symm_face]
  change ((scaledGraphForm _ a b edges (faceInclusion _ a b
    ((faceCoordinates hlu a b ha hb hab hcard).symm x))).compContinuousLinearMap
    (faceInclusion _ a b))
    (fun j ↦ (faceCoordinates hlu a b ha hb hab hcard).symm (Pi.single j (1 : ℝ))) = _
  rw [← faceGraphForm_eq_restriction]
  rw [twoPoint_faceGraphForm_eq_quotient hlu a b ha hb hab hcard]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, faceCoordinates,
    ContinuousLinearEquiv.symm_trans_apply, ContinuousLinearEquiv.apply_symm_apply,
    Function.comp_def, ContinuousLinearEquiv.coe_coe]
  change topForm _ ((realCoordinates _ _).symm x)
    (fun j ↦ (realCoordinates _ _).symm (Pi.single j (1 : ℝ))) = _
  have hbasis (j : Fin (Degree (n := n) (l := l) (u := u))) :
      (realCoordinates n (outsideM l u + 1)).symm (Pi.single j (1 : ℝ)) =
        realBasis n (outsideM l u + 1) j := by
    simp [realCoordinates, Module.Basis.equivFun_symm_apply]
  simp_rw [hbasis]
  rfl

/-- The lower face is literal slot zero; its outward orientation is minus. -/
def outwardIntegral : ℝ := -∫ x in GeometricWeights.realDomain n (outsideM l u + 1),
  BoxStokes.facePullback (radialForm hlu a b ha hb hab hcard edges) 0 0 x (BoxStokes.standardBasis _)

theorem outwardIntegral_eq_quotient :
    outwardIntegral hlu a b ha hb hab hcard edges =
      -GeometricWeights.rawIntegral (fun j ↦ quotientEdge hlu (edges j)) := by
  unfold outwardIntegral GeometricWeights.rawIntegral
  simp_rw [facePullback_radialForm]

end EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryGraphIntegral
