import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterExternalForms

/-!
# Forms for a cluster collapsing to a finite real center

The internal harmonic ratio is invariant under a varying real translation and
nonzero real scale. Consequently the entire internal form, including center and
radial tangents, is the pullback of the shape's harmonic form. No circle-valued
shape normalization is needed for this boundary type.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open ComplexConjugate
open scoped Topology

theorem angularPullback_congr_eventually {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℂ} {x : E} (h : f =ᶠ[nhds x] g) : angularPullback f x = angularPullback g x := by
  rw [angularPullback, angularPullback, h.eq_of_nhds, h.fderiv_eq]

abbrev RealClusterPairParameters := ℝ × (ℝ × (ℂ × ℂ))
abbrev RealClusterPairFace := ℝ × (ℂ × ℂ)

def realClusterPair (x : RealClusterPairParameters) : ℂ × ℂ :=
  ((x.1 : ℂ) + (x.2.1 : ℂ) * x.2.2.1, (x.1 : ℂ) + (x.2.1 : ℂ) * x.2.2.2)

def realClusterShapeProjection : RealClusterPairParameters →L[ℝ] ℂ × ℂ :=
  (ContinuousLinearMap.snd ℝ ℝ (ℂ × ℂ)).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℂ × ℂ)))

def realClusterFaceShapeProjection : RealClusterPairFace →L[ℝ] ℂ × ℂ :=
  ContinuousLinearMap.snd ℝ ℝ (ℂ × ℂ)

def realClusterFaceEmbedding : RealClusterPairFace →L[ℝ] RealClusterPairParameters :=
  (ContinuousLinearMap.fst ℝ ℝ (ℂ × ℂ)).prod
    (clusterFaceEmbedding.comp (ContinuousLinearMap.snd ℝ ℝ (ℂ × ℂ)))

@[simp] theorem realClusterShapeProjection_apply (x : RealClusterPairParameters) :
    realClusterShapeProjection x = x.2.2 := rfl

@[simp] theorem realClusterFaceEmbedding_apply (x : RealClusterPairFace) :
    realClusterFaceEmbedding x = (x.1, (0, x.2)) := rfl

theorem realClusterPair_denominator (x : RealClusterPairParameters) :
    (realClusterPair x).2 - conj (realClusterPair x).1 =
      (x.2.1 : ℂ) * (x.2.2.2 - conj x.2.2.1) := by
  simp only [realClusterPair, map_add, map_mul, Complex.conj_ofReal]
  ring

/-- Both radial factors cancel in the actual harmonic ratio. -/
theorem harmonicRatio_realClusterPair (x : RealClusterPairParameters) (hr : x.2.1 ≠ 0) :
    harmonicRatio (realClusterPair x).1 (realClusterPair x).2 =
      harmonicRatio x.2.2.1 x.2.2.2 := by
  rw [harmonicRatio, realClusterPair_denominator]
  have hnum : (realClusterPair x).2 - (realClusterPair x).1 = (x.2.1 : ℂ) * (x.2.2.2 - x.2.2.1) := by
    simp only [realClusterPair]
    ring
  rw [hnum]
  exact mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr hr)

theorem contDiff_realClusterPair : ContDiff ℝ ⊤ realClusterPair := by
  have hp : ContDiff ℝ ⊤ (fun x : RealClusterPairParameters => (x.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_fst
  have hr : ContDiff ℝ ⊤ (fun x : RealClusterPairParameters => (x.2.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_fst.comp contDiff_snd)
  have hu : ContDiff ℝ ⊤ (fun x : RealClusterPairParameters => x.2.2.1) := by fun_prop
  have hv : ContDiff ℝ ⊤ (fun x : RealClusterPairParameters => x.2.2.2) := by fun_prop
  exact (hp.add (hr.mul hu)).prodMk (hp.add (hr.mul hv))

/-- The exact shape harmonic form, independent of the coarse real center and radial parameter. -/
def realClusterInternalForm (x : RealClusterPairParameters) :
    RealClusterPairParameters [⋀^Fin 1]→L[ℝ] ℝ :=
  (harmonicAngleForm (realClusterShapeProjection x)).compContinuousLinearMap realClusterShapeProjection

theorem realClusterInternalForm_face (x : RealClusterPairFace) :
    (realClusterInternalForm (realClusterFaceEmbedding x)).compContinuousLinearMap realClusterFaceEmbedding =
      (harmonicAngleForm x.2).compContinuousLinearMap realClusterFaceShapeProjection := by
  ext v
  rfl

theorem contDiffAt_realClusterInternalForm (x : RealClusterPairParameters)
    (hd : x.2.2.2 - conj x.2.2.1 ≠ 0) (hn : x.2.2.2 - x.2.2.1 ≠ 0) :
    ContDiffAt ℝ ⊤ realClusterInternalForm x := by
  have hform := contDiffAt_harmonicAngleForm x.2.2.1 x.2.2.2 hd (div_ne_zero hn hd)
  exact (ContinuousAlternatingMap.compContinuousLinearMapCLM realClusterShapeProjection).contDiff.contDiffAt.comp x
    (hform.comp x realClusterShapeProjection.contDiff.contDiffAt)

/-- The regularized internal form is closed on the full ambient parameter domain. -/
theorem extDeriv_realClusterInternalForm (x : RealClusterPairParameters)
    (hd : x.2.2.2 - conj x.2.2.1 ≠ 0) (hn : x.2.2.2 - x.2.2.1 ≠ 0) :
    extDeriv realClusterInternalForm x = 0 := by
  have hratio : harmonicRatio x.2.2.1 x.2.2.2 ≠ 0 := div_ne_zero hn hd
  have hω := (contDiffAt_harmonicAngleForm x.2.2.1 x.2.2.2 hd hratio).differentiableAt (by simp)
  have heq : realClusterInternalForm = fun y =>
      (harmonicAngleForm (realClusterShapeProjection y)).compContinuousLinearMap
        (fderiv ℝ realClusterShapeProjection y) := by
    funext y
    rw [ContinuousLinearMap.fderiv]
    rfl
  have hf : ContDiffAt ℝ ⊤ realClusterShapeProjection x := realClusterShapeProjection.contDiff.contDiffAt
  rw [heq, extDeriv_pullback (f := realClusterShapeProjection) (x := x) hω hf (by simp)]
  change (extDeriv harmonicAngleForm (x.2.2.1, x.2.2.2)).compContinuousLinearMap
    (fderiv ℝ realClusterShapeProjection x) = 0
  rw [extDeriv_harmonicAngleForm _ _ hd hratio]
  ext v
  rfl

/-- At every nonzero scale the extension equals the actual harmonic pullback, in all tangents. -/
theorem harmonicAngleForm_realClusterPair (x : RealClusterPairParameters) (hr : x.2.1 ≠ 0)
    (hd : x.2.2.2 - conj x.2.2.1 ≠ 0) :
    (harmonicAngleForm (realClusterPair x)).compContinuousLinearMap (fderiv ℝ realClusterPair x) =
      realClusterInternalForm x := by
  have hpden : (realClusterPair x).2 - conj (realClusterPair x).1 ≠ 0 := by
    rw [realClusterPair_denominator]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) hd
  rw [harmonicAngleForm_pullback _ _ (contDiff_realClusterPair.contDiffAt.differentiableAt (by simp)) hpden]
  change angularPullback (fun y => harmonicRatio (realClusterPair y).1 (realClusterPair y).2) x = _
  have hne : ∀ᶠ y : RealClusterPairParameters in nhds x, y.2.1 ≠ 0 :=
    (isOpen_ne_fun (by fun_prop) continuous_const).mem_nhds hr
  have heq : (fun y : RealClusterPairParameters => harmonicRatio (realClusterPair y).1 (realClusterPair y).2)
      =ᶠ[nhds x] fun y => harmonicRatio y.2.2.1 y.2.2.2 :=
    hne.mono fun y hy => harmonicRatio_realClusterPair y hy
  rw [angularPullback_congr_eventually heq]
  have h := (harmonicAngleForm_pullback realClusterShapeProjection x realClusterShapeProjection.differentiableAt hd).symm
  rw [ContinuousLinearMap.fderiv] at h
  exact h

end EnvelopingIsomorphism.Deformation.Kontsevich
