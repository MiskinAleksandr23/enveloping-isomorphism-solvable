import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterSmoothForms

/-!
Exact radial-face restrictions of the actual free-coordinate forms for a finite
real cluster. Internal edges give the shape harmonic form, external edges give
the coarse harmonic form, and outgoing edges vanish by the real-source identity.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration ComplexConjugate

namespace BoundaryClusterFreeCoordinates

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

/-- An open face coordinate array defines an actual admissible zero-radius point. -/
def faceDomain (y : FaceCoordinates i a S m)
    (hy : (faceEmbedding y).OpenConditions l u) : BoundaryClusterFreeDomain i a S m l u :=
  ⟨faceEmbedding y, le_rfl, hy⟩

@[simp] theorem radius_faceEmbedding (y : FaceCoordinates i a S m) :
    (faceEmbedding y).radius = 0 := rfl

/-- The actual shape endpoint map restricted to the radial face. -/
def shapeFacePair (l u : Fin (m + 1)) (j : Fin n) (v : Fin n ⊕ Fin m) :
    FaceCoordinates i a S m → ℂ × ℂ :=
  shapePair l u j v ∘ faceEmbedding

/-- The actual coarse endpoint map on the face, retaining all free variables. -/
def coarseFacePair (l u : Fin (m + 1)) (j : Fin n) (v : Fin n ⊕ Fin m)
    (y : FaceCoordinates i a S m) : ℂ × ℂ :=
  ((faceEmbedding y).base j, (faceEmbedding y).targetBase l u v)

@[fun_prop] theorem contDiff_shapeFacePair (l u : Fin (m + 1)) (j : Fin n) (v : Fin n ⊕ Fin m) :
    ContDiff ℝ ⊤ (shapeFacePair (i := i) (a := a) (S := S) l u j v) :=
  (contDiff_shapePair l u j v).comp faceEmbedding.contDiff

@[fun_prop] theorem contDiff_coarseFacePair (l u : Fin (m + 1)) (j : Fin n) (v : Fin n ⊕ Fin m) :
    ContDiff ℝ ⊤ (coarseFacePair (i := i) (a := a) (S := S) l u j v) :=
  ((contDiff_base j).prodMk (contDiff_targetBase l u v)).comp faceEmbedding.contDiff

/-- The shape harmonic form with its actual full face differential. -/
def shapeFaceForm (l u : Fin (m + 1)) (j : Fin n) (v : Fin n ⊕ Fin m)
    (y : FaceCoordinates i a S m) : FaceCoordinates i a S m [⋀^Fin 1]→L[ℝ] ℝ :=
  (harmonicAngleForm (shapeFacePair l u j v y)).compContinuousLinearMap
    (fderiv ℝ (shapeFacePair l u j v) y)

/-- The coarse harmonic form with its actual full face differential. -/
def coarseFaceForm (l u : Fin (m + 1)) (j : Fin n) (v : Fin n ⊕ Fin m)
    (y : FaceCoordinates i a S m) : FaceCoordinates i a S m [⋀^Fin 1]→L[ℝ] ℝ :=
  (harmonicAngleForm (coarseFacePair l u j v y)).compContinuousLinearMap
    (fderiv ℝ (coarseFacePair l u j v) y)

theorem actualPair_comp_face (l u : Fin (m + 1)) (j : Fin n) (v : Fin n ⊕ Fin m) :
    actualPair (i := i) (a := a) (S := S) l u j v ∘ faceEmbedding = coarseFacePair l u j v := by
  funext y
  exact actualPair_face (faceEmbedding y) rfl j v

/-- Restricting the internal ratio gives exactly the shape harmonic pullback. -/
theorem internalEdgeForm_face (y : FaceCoordinates i a S m)
    (hy : (faceEmbedding y).OpenConditions l u) (j : Fin n) (v : Fin n ⊕ Fin m) (hj : j ∈ S) :
    (internalEdgeForm l u j v (faceEmbedding y)).compContinuousLinearMap faceEmbedding =
      shapeFaceForm l u j v y := by
  let x := faceDomain y hy
  rw [internalEdgeForm, angularPullback_comp_clm _ _ _
    ((x.contDiffAt_internalRatio j v hj).differentiableAt (by simp))]
  have hd : (shapeFacePair l u j v y).2 - conj (shapeFacePair l u j v y).1 ≠ 0 :=
    x.shape_denominator_ne_zero j v hj
  exact (harmonicAngleForm_pullback _ _
    ((contDiff_shapeFacePair l u j v).contDiffAt.differentiableAt (by simp)) hd).symm

/-- Restricting an external edge gives exactly the coarse harmonic pullback. -/
theorem actualEdgeForm_face_external (y : FaceCoordinates i a S m)
    (hy : (faceEmbedding y).OpenConditions l u) (j : Fin n) (v : Fin n ⊕ Fin m)
    (hv : v ≠ Sum.inl j)
    (hc : ¬(j ∈ S ∧ boundaryClusterCollapses S l u (Sum.inl v))) :
    (actualEdgeForm l u j v (faceEmbedding y)).compContinuousLinearMap faceEmbedding =
      coarseFaceForm l u j v y := by
  let x := faceDomain y hy
  rw [actualEdgeForm, angularPullback_comp_clm _ _ _
    ((x.contDiffAt_externalRatio_face rfl j v hv hc).differentiableAt (by simp))]
  have hfun : (fun z : BoundaryClusterFreeCoordinates i a S m =>
      harmonicRatio (actualPair l u j v z).1 (actualPair l u j v z).2) ∘
      faceEmbedding = (fun z : ℂ × ℂ => harmonicRatio z.1 z.2) ∘ coarseFacePair l u j v := by
    funext z
    exact congrArg (fun p : ℂ × ℂ => harmonicRatio p.1 p.2)
      (actualPair_face (faceEmbedding z) rfl j v)
  rw [hfun]
  have hd : (coarseFacePair l u j v y).2 - conj (coarseFacePair l u j v y).1 ≠ 0 :=
    x.external_denominator_ne_zero j v hv hc
  exact (harmonicAngleForm_pullback _ _
    ((contDiff_coarseFacePair l u j v).contDiffAt.differentiableAt (by simp)) hd).symm

theorem extendedEdgeForm_face_internal (y : FaceCoordinates i a S m)
    (hy : (faceEmbedding y).OpenConditions l u) (j : Fin n) (v : Fin n ⊕ Fin m)
    (hj : j ∈ S) (hc : boundaryClusterCollapses S l u (Sum.inl v)) :
    (extendedEdgeForm l u j v (faceEmbedding y)).compContinuousLinearMap faceEmbedding =
      shapeFaceForm l u j v y := by
  rw [extendedEdgeForm, if_pos ⟨hj, hc⟩]
  exact internalEdgeForm_face y hy j v hj

theorem extendedEdgeForm_face_external (y : FaceCoordinates i a S m)
    (hy : (faceEmbedding y).OpenConditions l u) (j : Fin n) (v : Fin n ⊕ Fin m)
    (hv : v ≠ Sum.inl j)
    (hc : ¬(j ∈ S ∧ boundaryClusterCollapses S l u (Sum.inl v))) :
    (extendedEdgeForm l u j v (faceEmbedding y)).compContinuousLinearMap faceEmbedding =
      coarseFaceForm l u j v y := by
  rw [extendedEdgeForm, if_neg hc]
  exact actualEdgeForm_face_external y hy j v hv hc

/-- The outgoing coarse pair factors through the real-source locus. -/
def outgoingFacePair (l u : Fin (m + 1)) (v : Fin n ⊕ Fin m)
    (y : FaceCoordinates i a S m) : ℝ × ℂ :=
  ((faceEmbedding y).center, (faceEmbedding y).targetBase l u v)

@[fun_prop] theorem contDiff_outgoingFacePair (l u : Fin (m + 1)) (v : Fin n ⊕ Fin m) :
    ContDiff ℝ ⊤ (outgoingFacePair (i := i) (a := a) (S := S) l u v) :=
  (contDiff_center.prodMk (contDiff_targetBase l u v)).comp faceEmbedding.contDiff

theorem coarseFacePair_outgoing (j : Fin n) (v : Fin n ⊕ Fin m) (hj : j ∈ S) :
    coarseFacePair (i := i) (a := a) (S := S) l u j v =
      boundarySourceEmbedding ∘ outgoingFacePair l u v := by
  funext y
  apply Prod.ext
  · exact (faceEmbedding y).base_eq_center j hj
  · rfl

/-- The coarse outgoing form vanishes in every face direction, by the genuine
harmonic-form identity on the real-source locus. -/
theorem coarseFaceForm_outgoing_eq_zero (y : FaceCoordinates i a S m)
    (hy : (faceEmbedding y).OpenConditions l u) (j : Fin n) (v : Fin n ⊕ Fin m)
    (hv : v ≠ Sum.inl j) (hj : j ∈ S)
    (hc : ¬boundaryClusterCollapses S l u (Sum.inl v)) :
    coarseFaceForm l u j v y = 0 := by
  let x := faceDomain y hy
  have hmask : ¬(j ∈ S ∧ boundaryClusterCollapses S l u (Sum.inl v)) := fun h => hc h.2
  have hne : (outgoingFacePair l u v y).2 ≠ ((outgoingFacePair l u v y).1 : ℂ) := by
    have h := x.external_base_ne j v hv hmask
    change (faceEmbedding y).targetBase l u v ≠ (faceEmbedding y).base j at h
    rw [(faceEmbedding y).base_eq_center j hj] at h
    exact h
  rw [coarseFaceForm, coarseFacePair_outgoing j v hj, fderiv_comp y
    boundarySourceEmbedding.differentiableAt
    ((contDiff_outgoingFacePair l u v).contDiffAt.differentiableAt (by simp)),
    boundarySourceEmbedding.fderiv]
  have hassoc :
      (harmonicAngleForm (boundarySourceEmbedding (outgoingFacePair l u v y))).compContinuousLinearMap
          (boundarySourceEmbedding.comp (fderiv ℝ (outgoingFacePair l u v) y)) =
        ((harmonicAngleForm (boundarySourceEmbedding (outgoingFacePair l u v y))).compContinuousLinearMap
          boundarySourceEmbedding).compContinuousLinearMap (fderiv ℝ (outgoingFacePair l u v) y) := by
    ext z
    rfl
  simp only [Function.comp_apply]
  rw [hassoc]
  change ((harmonicAngleForm (((outgoingFacePair l u v y).1 : ℂ), (outgoingFacePair l u v y).2)).compContinuousLinearMap
    boundarySourceEmbedding).compContinuousLinearMap (fderiv ℝ (outgoingFacePair l u v) y) = 0
  rw [harmonicAngleForm_boundary_source _ _ hne]
  ext z
  rfl

/-- Outgoing edges have zero restriction on the actual free radial face. -/
theorem extendedEdgeForm_face_outgoing (y : FaceCoordinates i a S m)
    (hy : (faceEmbedding y).OpenConditions l u) (j : Fin n) (v : Fin n ⊕ Fin m)
    (hv : v ≠ Sum.inl j) (hj : j ∈ S)
    (hc : ¬boundaryClusterCollapses S l u (Sum.inl v)) :
    (extendedEdgeForm l u j v (faceEmbedding y)).compContinuousLinearMap faceEmbedding = 0 := by
  rw [extendedEdgeForm_face_external y hy j v hv (fun h => hc h.2)]
  exact coarseFaceForm_outgoing_eq_zero y hy j v hv hj hc

/-- The actual radial-face coordinates of a zero-radius free point. -/
theorem faceEmbedding_splitRadius (x : BoundaryClusterFreeCoordinates i a S m) (hr : x.radius = 0) :
    faceEmbedding (splitRadius x).1 = x := by
  exact Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl hr.symm)))

end BoundaryClusterFreeCoordinates

namespace BoundaryClusterFreeDomain

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

/-- The internal face identity directly at an actual admissible zero-radius point. -/
theorem extendedEdgeForm_face_internal (x : BoundaryClusterFreeDomain i a S m l u)
    (hr : x.val.radius = 0) (j : Fin n) (v : Fin n ⊕ Fin m)
    (hj : j ∈ S) (hc : boundaryClusterCollapses S l u (Sum.inl v)) :
    (BoundaryClusterFreeCoordinates.extendedEdgeForm l u j v x.val).compContinuousLinearMap
      BoundaryClusterFreeCoordinates.faceEmbedding =
        BoundaryClusterFreeCoordinates.shapeFaceForm l u j v
          (BoundaryClusterFreeCoordinates.splitRadius x.val).1 := by
  let y := (BoundaryClusterFreeCoordinates.splitRadius x.val).1
  have he := BoundaryClusterFreeCoordinates.faceEmbedding_splitRadius x.val hr
  have hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u := by
    rw [he]
    exact x.property.2
  simpa only [y, he] using BoundaryClusterFreeCoordinates.extendedEdgeForm_face_internal y hy j v hj hc

theorem extendedEdgeForm_face_external (x : BoundaryClusterFreeDomain i a S m l u)
    (hr : x.val.radius = 0) (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j)
    (hc : ¬(j ∈ S ∧ boundaryClusterCollapses S l u (Sum.inl v))) :
    (BoundaryClusterFreeCoordinates.extendedEdgeForm l u j v x.val).compContinuousLinearMap
      BoundaryClusterFreeCoordinates.faceEmbedding =
        BoundaryClusterFreeCoordinates.coarseFaceForm l u j v
          (BoundaryClusterFreeCoordinates.splitRadius x.val).1 := by
  let y := (BoundaryClusterFreeCoordinates.splitRadius x.val).1
  have he := BoundaryClusterFreeCoordinates.faceEmbedding_splitRadius x.val hr
  have hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u := by
    rw [he]
    exact x.property.2
  simpa only [y, he] using BoundaryClusterFreeCoordinates.extendedEdgeForm_face_external y hy j v hv hc

theorem extendedEdgeForm_face_outgoing (x : BoundaryClusterFreeDomain i a S m l u)
    (hr : x.val.radius = 0) (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j)
    (hj : j ∈ S) (hc : ¬boundaryClusterCollapses S l u (Sum.inl v)) :
    (BoundaryClusterFreeCoordinates.extendedEdgeForm l u j v x.val).compContinuousLinearMap
      BoundaryClusterFreeCoordinates.faceEmbedding = 0 := by
  let y := (BoundaryClusterFreeCoordinates.splitRadius x.val).1
  have he := BoundaryClusterFreeCoordinates.faceEmbedding_splitRadius x.val hr
  have hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u := by
    rw [he]
    exact x.property.2
  simpa only [y, he] using BoundaryClusterFreeCoordinates.extendedEdgeForm_face_outgoing y hy j v hv hj hc

end BoundaryClusterFreeDomain

end EnvelopingIsomorphism.Deformation.Kontsevich
