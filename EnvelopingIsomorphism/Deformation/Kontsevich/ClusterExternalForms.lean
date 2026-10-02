import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterAngleForms

/-!
External cluster edges with both endpoints moving independently.  The centers
and both offsets vary; at radius zero the actual harmonic form restricts to
the coarse pair form.  This covers incoming and outgoing cluster edges alike.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open ComplexConjugate

/-- Coarse endpoint pair, radius, and the two endpoint offsets. -/
abbrev GeneralExternalClusterParameters := (ℂ × ℂ) × (ℝ × (ℂ × ℂ))
abbrev GeneralExternalClusterFace := (ℂ × ℂ) × (ℂ × ℂ)

/-- Both endpoints can move, with distinct coarse base points on the regular face. -/
def generalExternalClusterPair (x : GeneralExternalClusterParameters) : ℂ × ℂ :=
  (x.1.1 + (x.2.1 : ℂ) * x.2.2.1, x.1.2 + (x.2.1 : ℂ) * x.2.2.2)

def generalExternalClusterRatio (x : GeneralExternalClusterParameters) : ℂ :=
  harmonicRatio (generalExternalClusterPair x).1 (generalExternalClusterPair x).2

def generalExternalClusterExtendedForm (x : GeneralExternalClusterParameters) :
    GeneralExternalClusterParameters [⋀^Fin 1]→L[ℝ] ℝ :=
  angularPullback generalExternalClusterRatio x

def generalExternalClusterFaceEmbedding :
    GeneralExternalClusterFace →L[ℝ] GeneralExternalClusterParameters :=
  (ContinuousLinearMap.fst ℝ (ℂ × ℂ) (ℂ × ℂ)).prod
    (clusterFaceEmbedding.comp (ContinuousLinearMap.snd ℝ (ℂ × ℂ) (ℂ × ℂ)))

def generalExternalCoarseProjection : GeneralExternalClusterFace →L[ℝ] ℂ × ℂ :=
  ContinuousLinearMap.fst ℝ (ℂ × ℂ) (ℂ × ℂ)

@[simp] theorem generalExternalClusterFaceEmbedding_apply (x : GeneralExternalClusterFace) :
    generalExternalClusterFaceEmbedding x = (x.1, (0, x.2)) := rfl

@[simp] theorem generalExternalCoarseProjection_apply (x : GeneralExternalClusterFace) :
    generalExternalCoarseProjection x = x.1 := rfl

@[simp] theorem generalExternalClusterPair_face (x : GeneralExternalClusterFace) :
    generalExternalClusterPair (generalExternalClusterFaceEmbedding x) = x.1 := by
  simp [generalExternalClusterPair]

theorem contDiffAt_generalExternalClusterPair (x : GeneralExternalClusterParameters) :
    ContDiffAt ℝ ⊤ generalExternalClusterPair x := by
  have hc : ContDiffAt ℝ ⊤ (fun y : GeneralExternalClusterParameters => y.1.1) x :=
    contDiffAt_fst.comp x contDiffAt_fst
  have hd : ContDiffAt ℝ ⊤ (fun y : GeneralExternalClusterParameters => y.1.2) x :=
    contDiffAt_snd.comp x contDiffAt_fst
  have hrr : ContDiffAt ℝ ⊤ (fun y : GeneralExternalClusterParameters => y.2.1) x :=
    contDiffAt_fst.comp x contDiffAt_snd
  have hr : ContDiffAt ℝ ⊤ (fun y : GeneralExternalClusterParameters => (y.2.1 : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hrr
  have ha : ContDiffAt ℝ ⊤ (fun y : GeneralExternalClusterParameters => y.2.2.1) x :=
    contDiffAt_fst.comp x (contDiffAt_snd.comp x contDiffAt_snd)
  have hb : ContDiffAt ℝ ⊤ (fun y : GeneralExternalClusterParameters => y.2.2.2) x :=
    contDiffAt_snd.comp x (contDiffAt_snd.comp x contDiffAt_snd)
  exact (hc.add (hr.mul ha)).prodMk (hd.add (hr.mul hb))

theorem contDiffAt_generalExternalClusterRatio (x : GeneralExternalClusterParameters)
    (hd : (generalExternalClusterPair x).2 - conj (generalExternalClusterPair x).1 ≠ 0) :
    ContDiffAt ℝ ⊤ generalExternalClusterRatio x := by
  change ContDiffAt ℝ ⊤ ((fun z : ℂ × ℂ => harmonicRatio z.1 z.2) ∘
    generalExternalClusterPair) x
  exact (contDiffAt_harmonicRatio _ _ hd).comp x (contDiffAt_generalExternalClusterPair x)

/-- Smoothness at an external face, with arbitrary independent endpoint velocities. -/
theorem contDiffAt_generalExternalClusterExtendedForm_face (x : GeneralExternalClusterFace)
    (hd : x.1.2 - conj x.1.1 ≠ 0) (hne : x.1.2 - x.1.1 ≠ 0) :
    ContDiffAt ℝ ⊤ generalExternalClusterExtendedForm (generalExternalClusterFaceEmbedding x) := by
  apply contDiffAt_angularPullback
  · exact contDiffAt_generalExternalClusterRatio _
      (by simpa [generalExternalClusterPair] using hd)
  · simpa [generalExternalClusterRatio, generalExternalClusterPair, harmonicRatio] using
      div_ne_zero hne hd

/-- Every regular external edge restricts to the coarse harmonic form,
regardless of whether its source, target, or both endpoints move. -/
theorem generalExternalClusterExtendedForm_face (x : GeneralExternalClusterFace)
    (hd : x.1.2 - conj x.1.1 ≠ 0) :
    (generalExternalClusterExtendedForm (generalExternalClusterFaceEmbedding x)).compContinuousLinearMap
      generalExternalClusterFaceEmbedding =
        (harmonicAngleForm x.1).compContinuousLinearMap generalExternalCoarseProjection := by
  have hf := contDiffAt_generalExternalClusterRatio
    (generalExternalClusterFaceEmbedding x) (by simpa [generalExternalClusterPair] using hd)
  rw [generalExternalClusterExtendedForm,
    angularPullback_comp_clm _ _ _ (hf.differentiableAt (by simp))]
  have hfun : generalExternalClusterRatio ∘ generalExternalClusterFaceEmbedding =
      (fun z : ℂ × ℂ => harmonicRatio z.1 z.2) ∘ generalExternalCoarseProjection := by
    funext y
    simp [generalExternalClusterRatio, generalExternalClusterPair]
  rw [hfun, ← angularPullback_comp_clm _ generalExternalCoarseProjection x
    ((contDiffAt_harmonicRatio x.1.1 x.1.2 hd).differentiableAt (by simp))]
  rfl

/-- The extended form equals the actual harmonic pullback throughout its regular domain. -/
theorem harmonicAngleForm_generalExternalClusterPair (x : GeneralExternalClusterParameters)
    (hd : (generalExternalClusterPair x).2 - conj (generalExternalClusterPair x).1 ≠ 0) :
    (harmonicAngleForm (generalExternalClusterPair x)).compContinuousLinearMap
      (fderiv ℝ generalExternalClusterPair x) = generalExternalClusterExtendedForm x :=
  harmonicAngleForm_pullback _ _
    ((contDiffAt_generalExternalClusterPair x).differentiableAt (by simp)) hd

end EnvelopingIsomorphism.Deformation.Kontsevich
