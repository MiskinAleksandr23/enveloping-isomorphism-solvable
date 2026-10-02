import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestOverlapJacobian

/-! Exact Jacobian/coorientation relation on the actual paired forest face.
The target coordinate basis is the existing native radial-last simple basis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestOverlapJacobian
open PairedForestSimpleCluster PairedForestSmoothProduct PairedForestFullOverlap
open ClusterFaceOrientation.Interior BoxStokes OrientedFormChangeVariables
open ForestRadialFaceImmersion RadialFaceJacobian
open scoped Classical Topology
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : ForestRadialFaceClassification.kind 0 x o = .paired)

private theorem coordinates_apply (q : Angular x o ho)
    (j : ClusterAngularCoordinates.CoordinateIndex (0 : Fin (n + 1)) (anchor x o ho) (reference x o ho) (S x o ho) m) :
    simpleCoordinates hdim x o ho q (finCongr hdim
      (sourceIndex (anchor_mem x o ho) (reference_mem x o ho) (reference_ne_anchor x o ho) (anchor_global x o ho) j)) =
        ClusterAngularCoordinates.coordinateBasis.repr q j := by
  simp [simpleCoordinates, simpleBasis, Module.Basis.equivFun_apply, Module.Basis.repr_reindex,
    Finsupp.mapDomain_equiv_apply]

theorem simpleCoordinates_radius (q : Angular x o ho) :
    simpleCoordinates hdim x o ho q (Fin.last r) = q.toFree.radius := by
  let j := ClusterCoordinateOrder.radiusIndex
    (ClusterCoarseIndex (0 : Fin (n + 1)) (anchor x o ho) (S x o ho))
    (ClusterShapeIndex (anchor x o ho) (reference x o ho) (S x o ho)) m
  have hd : faceDimension (0 : Fin (n + 1)) (anchor x o ho) (reference x o ho) (S x o ho) m = r := by
    have h := dimension_eq (m := m) (anchor_mem x o ho) (reference_mem x o ho)
      (reference_ne_anchor x o ho) (anchor_global x o ho)
    omega
  have hj : finCongr hdim
      (sourceIndex (anchor_mem x o ho) (reference_mem x o ho) (reference_ne_anchor x o ho) (anchor_global x o ho) j) =
        Fin.last r := by
    apply Fin.ext
    simpa [sourceIndex, nativeEnum, j, Equiv.trans_apply] using hd
  rw [← hj, coordinates_apply]
  simp [j, ClusterCoordinateOrder.radiusIndex, ClusterAngularCoordinates.coordinateBasis,
    ClusterFreeCoordinates.radius, ClusterAngularCoordinates.toFree]

@[simp] theorem realOverlap_radius (u : Circle) (w : Coord (r + 1)) :
    realOverlap hdim x o ho u w (Fin.last r) = PairedForestNormalScale.simpleRadius hdim x o ho w :=
  simpleCoordinates_radius hdim x o ho (overlap hdim x o ho u w)

/-- The normal covector is derived from the actual radius identity. -/
theorem normal_differential (z : Source hdim x o) (v : Coord (r + 1)) :
    fderiv ℝ (realOverlap hdim x o ho (phase hdim x o ho z)) (facePoint hdim x o z) v (Fin.last r) =
      PairedForestNormalScale.normalScale hdim x o ho (facePoint hdim x o z) *
        v (ForestRadialFaceClassification.axis hdim x o) := by
  let proj := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (r + 1) ↦ ℝ) (Fin.last r)
  have h := (proj.hasFDerivAt.comp (facePoint hdim x o z)
    ((contDiffAt_realOverlap hdim x o ho z).differentiableAt (by simp)).hasFDerivAt).fderiv
  have he : proj ∘ realOverlap hdim x o ho (phase hdim x o ho z) =
      PairedForestNormalScale.simpleRadius hdim x o ho := funext (realOverlap_radius hdim x o ho _)
  rw [he] at h
  have hr := PairedForestNormalScale.fderiv_simpleRadius_face hdim x o ho z
  change fderiv ℝ (PairedForestNormalScale.simpleRadius hdim x o ho) (facePoint hdim x o z) = _ at hr
  rw [hr] at h
  exact (congrArg (fun L : Coord (r + 1) →L[ℝ] ℝ ↦ L v) h).symm

def nativeFaceMap (u : Circle) : Coord r → Coord r :=
  faceProjection (Fin.last r) ∘ realOverlap hdim x o ho u ∘ faceEmbedding (ForestRadialFaceClassification.axis hdim x o) 0

theorem fderiv_nativeFaceMap (z : Source hdim x o) :
    fderiv ℝ (nativeFaceMap hdim x o ho (phase hdim x o ho z)) z.val =
      faceDerivative (ForestRadialFaceClassification.axis hdim x o) (Fin.last r)
        (fderiv ℝ (realOverlap hdim x o ho (phase hdim x o ho z)) (facePoint hdim x o z)) := by
  have h := (faceProjection (Fin.last r)).hasFDerivAt.comp z.val
    ((((contDiffAt_realOverlap hdim x o ho z).differentiableAt (by simp)).hasFDerivAt).comp z.val
      (faceTangent (ForestRadialFaceClassification.axis hdim x o)).hasFDerivAt)
  exact h.fderiv

/-- Actual full determinant, actual positive normal scale, and actual native
face determinant, including the deleted-axis cofactor sign. -/
theorem jacobian_full_eq_normal_mul_face (z : Source hdim x o) :
    jacobian (realOverlap hdim x o ho (phase hdim x o ho z)) (facePoint hdim x o z) =
      (-1 : ℝ) ^ (r + (ForestRadialFaceClassification.axis hdim x o).val) *
        PairedForestNormalScale.normalScale hdim x o ho (facePoint hdim x o z) *
          jacobian (nativeFaceMap hdim x o ho (phase hdim x o ho z)) z.val := by
  rw [jacobian, det_eq_normal_mul_face _ (Fin.last r) _ _ (normal_differential hdim x o ho z)]
  rw [show (Fin.last r).val = r from rfl, ← fderiv_nativeFaceMap]
  rfl

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestOverlapJacobian
