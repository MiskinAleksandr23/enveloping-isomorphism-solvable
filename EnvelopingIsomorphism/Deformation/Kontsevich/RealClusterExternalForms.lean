import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterExternalForms

/-!
External edges of a finite real cluster.  Real coarse source or target
coordinates are inserted by actual continuous linear maps into the general
two-moving-endpoint chart.  Outgoing face forms vanish; incoming face forms
are the ordinary coarse harmonic forms.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open ComplexConjugate

section LinearRestriction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem realCluster_pullback_assoc (ω : G [⋀^Fin 1]→L[ℝ] ℝ)
    (f : E →L[ℝ] G) (g : F →L[ℝ] E) :
    (ω.compContinuousLinearMap f).compContinuousLinearMap g =
      ω.compContinuousLinearMap (f.comp g) := by
  ext v
  rfl

/-- Actual restriction of the previously constructed external form. -/
def restrictedExternalClusterForm (e : E →L[ℝ] GeneralExternalClusterParameters) (x : E) :
    E [⋀^Fin 1]→L[ℝ] ℝ :=
  (generalExternalClusterExtendedForm (e x)).compContinuousLinearMap e

theorem contDiffAt_restrictedExternalClusterForm
    (e : E →L[ℝ] GeneralExternalClusterParameters) (x : E)
    (h : ContDiffAt ℝ ⊤ generalExternalClusterExtendedForm (e x)) :
    ContDiffAt ℝ ⊤ (restrictedExternalClusterForm e) x := by
  let C : (GeneralExternalClusterParameters [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ]
      (E [⋀^Fin 1]→L[ℝ] ℝ) := ContinuousAlternatingMap.compContinuousLinearMapCLM e
  change ContDiffAt ℝ ⊤ (C ∘ generalExternalClusterExtendedForm ∘ e) x
  exact C.contDiff.contDiffAt.comp x (h.comp x e.contDiff.contDiffAt)

/-- The restriction remains the full pullback of the actual harmonic form. -/
theorem harmonicAngleForm_restrictedExternalClusterPair
    (e : E →L[ℝ] GeneralExternalClusterParameters) (x : E)
    (hd : (generalExternalClusterPair (e x)).2 - conj (generalExternalClusterPair (e x)).1 ≠ 0) :
    (harmonicAngleForm (generalExternalClusterPair (e x))).compContinuousLinearMap
      (fderiv ℝ (generalExternalClusterPair ∘ e) x) = restrictedExternalClusterForm e x := by
  rw [fderiv_comp x
    ((contDiffAt_generalExternalClusterPair (e x)).differentiableAt (by simp)) e.differentiableAt,
    e.fderiv, ← realCluster_pullback_assoc, harmonicAngleForm_generalExternalClusterPair _ hd]
  rfl

/-- Restrict the genuine general face identity through a commuting diagram of linear maps. -/
theorem restrictedExternalClusterForm_face
    (e : E →L[ℝ] GeneralExternalClusterParameters) (j : F →L[ℝ] E)
    (g : F →L[ℝ] GeneralExternalClusterFace)
    (hdiag : e.comp j = generalExternalClusterFaceEmbedding.comp g) (x : F)
    (hd : (g x).1.2 - conj (g x).1.1 ≠ 0) :
    (restrictedExternalClusterForm e (j x)).compContinuousLinearMap j =
      (harmonicAngleForm (g x).1).compContinuousLinearMap (generalExternalCoarseProjection.comp g) := by
  have hpoint : e (j x) = generalExternalClusterFaceEmbedding (g x) :=
    congrArg (fun f : F →L[ℝ] GeneralExternalClusterParameters => f x) hdiag
  rw [restrictedExternalClusterForm, hpoint, realCluster_pullback_assoc, hdiag,
    ← realCluster_pullback_assoc, generalExternalClusterExtendedForm_face _ hd,
    realCluster_pullback_assoc]

end LinearRestriction

/-- Insert a real target coordinate into an actual complex pair. -/
def boundaryTargetEmbedding : (ℂ × ℝ) →L[ℝ] ℂ × ℂ :=
  (ContinuousLinearMap.id ℝ ℂ).prodMap Complex.ofRealCLM

@[simp] theorem boundaryTargetEmbedding_apply (x : ℂ × ℝ) :
    boundaryTargetEmbedding x = (x.1, (x.2 : ℂ)) := rfl

abbrev RealOutgoingClusterParameters := (ℝ × ℂ) × (ℝ × (ℂ × ℂ))
abbrev RealOutgoingClusterFace := (ℝ × ℂ) × (ℂ × ℂ)

def realOutgoingAmbientEmbedding : RealOutgoingClusterParameters →L[ℝ] GeneralExternalClusterParameters :=
  boundarySourceEmbedding.prodMap (ContinuousLinearMap.id ℝ (ℝ × (ℂ × ℂ)))

def realOutgoingFaceLift : RealOutgoingClusterFace →L[ℝ] GeneralExternalClusterFace :=
  boundarySourceEmbedding.prodMap (ContinuousLinearMap.id ℝ (ℂ × ℂ))

def realOutgoingFaceEmbedding : RealOutgoingClusterFace →L[ℝ] RealOutgoingClusterParameters :=
  (ContinuousLinearMap.fst ℝ (ℝ × ℂ) (ℂ × ℂ)).prod
    (clusterFaceEmbedding.comp (ContinuousLinearMap.snd ℝ (ℝ × ℂ) (ℂ × ℂ)))

def realOutgoingCoarseProjection : RealOutgoingClusterFace →L[ℝ] ℝ × ℂ :=
  ContinuousLinearMap.fst ℝ (ℝ × ℂ) (ℂ × ℂ)

def realOutgoingClusterForm : RealOutgoingClusterParameters →
    RealOutgoingClusterParameters [⋀^Fin 1]→L[ℝ] ℝ :=
  restrictedExternalClusterForm realOutgoingAmbientEmbedding

@[simp] theorem realOutgoingAmbientEmbedding_apply (x : RealOutgoingClusterParameters) :
    realOutgoingAmbientEmbedding x = (((x.1.1 : ℂ), x.1.2), x.2) := rfl

@[simp] theorem realOutgoingFaceLift_apply (x : RealOutgoingClusterFace) :
    realOutgoingFaceLift x = (((x.1.1 : ℂ), x.1.2), x.2) := rfl

@[simp] theorem realOutgoingFaceEmbedding_apply (x : RealOutgoingClusterFace) :
    realOutgoingFaceEmbedding x = (x.1, (0, x.2)) := rfl

theorem realOutgoing_face_diagram :
    realOutgoingAmbientEmbedding.comp realOutgoingFaceEmbedding =
      generalExternalClusterFaceEmbedding.comp realOutgoingFaceLift := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- The full outgoing form is smooth off the real-source coarse collision. -/
theorem contDiffAt_realOutgoingClusterForm_face (x : RealOutgoingClusterFace)
    (hne : x.1.2 ≠ (x.1.1 : ℂ)) :
    ContDiffAt ℝ ⊤ realOutgoingClusterForm (realOutgoingFaceEmbedding x) := by
  apply contDiffAt_restrictedExternalClusterForm
  have h := contDiffAt_generalExternalClusterExtendedForm_face (realOutgoingFaceLift x)
    (by simpa [boundarySourceEmbedding] using sub_ne_zero.mpr hne)
    (by simpa using sub_ne_zero.mpr hne)
  exact h

/-- Every outgoing real-cluster external face form vanishes in all face directions,
including the real center, external endpoint, and both internal offsets. -/
theorem realOutgoingClusterForm_face (x : RealOutgoingClusterFace)
    (hne : x.1.2 ≠ (x.1.1 : ℂ)) :
    (realOutgoingClusterForm (realOutgoingFaceEmbedding x)).compContinuousLinearMap
      realOutgoingFaceEmbedding = 0 := by
  have hd : (realOutgoingFaceLift x).1.2 - conj (realOutgoingFaceLift x).1.1 ≠ 0 := by
    simpa using sub_ne_zero.mpr hne
  rw [realOutgoingClusterForm, restrictedExternalClusterForm_face _ _ _ realOutgoing_face_diagram x hd]
  have hmap : generalExternalCoarseProjection.comp realOutgoingFaceLift =
      boundarySourceEmbedding.comp realOutgoingCoarseProjection := by
    apply ContinuousLinearMap.ext
    intro y
    rfl
  rw [hmap, ← realCluster_pullback_assoc]
  change ((harmonicAngleForm ((x.1.1 : ℂ), x.1.2)).compContinuousLinearMap
    boundarySourceEmbedding).compContinuousLinearMap realOutgoingCoarseProjection = 0
  rw [harmonicAngleForm_boundary_source _ _ hne]
  ext v
  rfl

/-- The outgoing real-cluster form is the actual interior harmonic pullback. -/
theorem harmonicAngleForm_realOutgoingClusterPair (x : RealOutgoingClusterParameters)
    (hd : (generalExternalClusterPair (realOutgoingAmbientEmbedding x)).2 -
      conj (generalExternalClusterPair (realOutgoingAmbientEmbedding x)).1 ≠ 0) :
    (harmonicAngleForm (generalExternalClusterPair (realOutgoingAmbientEmbedding x))).compContinuousLinearMap
      (fderiv ℝ (generalExternalClusterPair ∘ realOutgoingAmbientEmbedding) x) =
        realOutgoingClusterForm x :=
  harmonicAngleForm_restrictedExternalClusterPair _ _ hd

abbrev RealIncomingClusterParameters := (ℂ × ℝ) × (ℝ × (ℂ × ℂ))
abbrev RealIncomingClusterFace := (ℂ × ℝ) × (ℂ × ℂ)

def realIncomingAmbientEmbedding : RealIncomingClusterParameters →L[ℝ] GeneralExternalClusterParameters :=
  boundaryTargetEmbedding.prodMap (ContinuousLinearMap.id ℝ (ℝ × (ℂ × ℂ)))

def realIncomingFaceLift : RealIncomingClusterFace →L[ℝ] GeneralExternalClusterFace :=
  boundaryTargetEmbedding.prodMap (ContinuousLinearMap.id ℝ (ℂ × ℂ))

def realIncomingFaceEmbedding : RealIncomingClusterFace →L[ℝ] RealIncomingClusterParameters :=
  (ContinuousLinearMap.fst ℝ (ℂ × ℝ) (ℂ × ℂ)).prod
    (clusterFaceEmbedding.comp (ContinuousLinearMap.snd ℝ (ℂ × ℝ) (ℂ × ℂ)))

def realIncomingCoarseProjection : RealIncomingClusterFace →L[ℝ] ℂ × ℝ :=
  ContinuousLinearMap.fst ℝ (ℂ × ℝ) (ℂ × ℂ)

def realIncomingClusterForm : RealIncomingClusterParameters →
    RealIncomingClusterParameters [⋀^Fin 1]→L[ℝ] ℝ :=
  restrictedExternalClusterForm realIncomingAmbientEmbedding

@[simp] theorem realIncomingAmbientEmbedding_apply (x : RealIncomingClusterParameters) :
    realIncomingAmbientEmbedding x = ((x.1.1, (x.1.2 : ℂ)), x.2) := rfl

@[simp] theorem realIncomingFaceLift_apply (x : RealIncomingClusterFace) :
    realIncomingFaceLift x = ((x.1.1, (x.1.2 : ℂ)), x.2) := rfl

@[simp] theorem realIncomingFaceEmbedding_apply (x : RealIncomingClusterFace) :
    realIncomingFaceEmbedding x = (x.1, (0, x.2)) := rfl

theorem realIncoming_face_diagram :
    realIncomingAmbientEmbedding.comp realIncomingFaceEmbedding =
      generalExternalClusterFaceEmbedding.comp realIncomingFaceLift := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- Reflection introduces no extra coarse collision when the target is real. -/
theorem realIncoming_face_denominator_ne_zero (x : RealIncomingClusterFace)
    (hne : x.1.1 ≠ (x.1.2 : ℂ)) :
    (realIncomingFaceLift x).1.2 - conj (realIncomingFaceLift x).1.1 ≠ 0 := by
  change (x.1.2 : ℂ) - conj x.1.1 ≠ 0
  intro h
  have h' : (x.1.2 : ℂ) - x.1.1 = 0 := by simpa using congrArg conj h
  exact hne (sub_eq_zero.mp h').symm

/-- Incoming real-cluster external forms are smooth off the coarse collision. -/
theorem contDiffAt_realIncomingClusterForm_face (x : RealIncomingClusterFace)
    (hne : x.1.1 ≠ (x.1.2 : ℂ)) :
    ContDiffAt ℝ ⊤ realIncomingClusterForm (realIncomingFaceEmbedding x) := by
  apply contDiffAt_restrictedExternalClusterForm
  exact contDiffAt_generalExternalClusterExtendedForm_face (realIncomingFaceLift x)
    (realIncoming_face_denominator_ne_zero x hne)
    (by simpa using sub_ne_zero.mpr hne.symm)

/-- Incoming edges retain exactly the actual coarse harmonic form with real
target, and have no internal-offset component on the face. -/
theorem realIncomingClusterForm_face (x : RealIncomingClusterFace)
    (hne : x.1.1 ≠ (x.1.2 : ℂ)) :
    (realIncomingClusterForm (realIncomingFaceEmbedding x)).compContinuousLinearMap
      realIncomingFaceEmbedding =
        (harmonicAngleForm (x.1.1, (x.1.2 : ℂ))).compContinuousLinearMap
          (boundaryTargetEmbedding.comp realIncomingCoarseProjection) := by
  rw [realIncomingClusterForm, restrictedExternalClusterForm_face _ _ _ realIncoming_face_diagram x
    (realIncoming_face_denominator_ne_zero x hne)]
  have hmap : generalExternalCoarseProjection.comp realIncomingFaceLift =
      boundaryTargetEmbedding.comp realIncomingCoarseProjection := by
    apply ContinuousLinearMap.ext
    intro y
    rfl
  rw [hmap]
  rfl

/-- The incoming real-cluster form is the actual interior harmonic pullback. -/
theorem harmonicAngleForm_realIncomingClusterPair (x : RealIncomingClusterParameters)
    (hd : (generalExternalClusterPair (realIncomingAmbientEmbedding x)).2 -
      conj (generalExternalClusterPair (realIncomingAmbientEmbedding x)).1 ≠ 0) :
    (harmonicAngleForm (generalExternalClusterPair (realIncomingAmbientEmbedding x))).compContinuousLinearMap
      (fderiv ℝ (generalExternalClusterPair ∘ realIncomingAmbientEmbedding) x) =
        realIncomingClusterForm x :=
  harmonicAngleForm_restrictedExternalClusterPair _ _ hd

end EnvelopingIsomorphism.Deformation.Kontsevich
