import EnvelopingIsomorphism.Deformation.Kontsevich.TwoInteriorCollision

/-!
Harmonic angular forms in an arbitrary interior-cluster chart.  The two
endpoint offsets vary independently, while the upper-half-plane center is
fixed.  Cancelling the real radial factor gives a smooth form at the collision
face and its exact internal angular restriction.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open ComplexConjugate
open scoped UpperHalfPlane Topology

/-- Radius and two independently varying complex offsets. -/
abbrev ClusterPairParameters := ℝ × (ℂ × ℂ)

/-- Two points collapsing toward a fixed interior center. -/
def internalClusterPair (c : ℍ) (x : ClusterPairParameters) : ℂ × ℂ :=
  ((c : ℂ) + (x.1 : ℂ) * x.2.1, (c : ℂ) + (x.1 : ℂ) * x.2.2)

/-- The harmonic denominator in the interior-cluster chart. -/
def internalClusterDenominator (c : ℍ) (x : ClusterPairParameters) : ℂ :=
  (c : ℂ) - conj (c : ℂ) + (x.1 : ℂ) * (x.2.2 - conj x.2.1)

/-- The harmonic ratio after removing its real radial factor. -/
def internalClusterRegularizedRatio (c : ℍ) (x : ClusterPairParameters) : ℂ :=
  (x.2.2 - x.2.1) / internalClusterDenominator c x

theorem internalClusterPair_denominator (c : ℍ) (x : ClusterPairParameters) :
    (internalClusterPair c x).2 - conj (internalClusterPair c x).1 =
      internalClusterDenominator c x := by
  simp only [internalClusterPair, internalClusterDenominator, map_add, map_mul,
    Complex.conj_ofReal]
  ring

theorem harmonicRatio_internalClusterPair_factor (c : ℍ) (x : ClusterPairParameters) :
    harmonicRatio (internalClusterPair c x).1 (internalClusterPair c x).2 =
      (x.1 : ℂ) * internalClusterRegularizedRatio c x := by
  rw [harmonicRatio, internalClusterPair_denominator]
  have hnum : (internalClusterPair c x).2 - (internalClusterPair c x).1 =
      (x.1 : ℂ) * (x.2.2 - x.2.1) := by
    simp only [internalClusterPair]
    ring
  rw [hnum, internalClusterRegularizedRatio, mul_div_assoc]

theorem internalClusterCenterDenominator_ne_zero (c : ℍ) :
    (c : ℂ) - conj (c : ℂ) ≠ 0 :=
  harmonicDenominator_ne_zero c.im_pos c.im_pos.le

@[simp] theorem internalClusterDenominator_zero (c : ℍ) (z : ℂ × ℂ) :
    internalClusterDenominator c (0, z) = (c : ℂ) - conj (c : ℂ) := by
  simp [internalClusterDenominator]

@[simp] theorem internalClusterRegularizedRatio_zero (c : ℍ) (z : ℂ × ℂ) :
    internalClusterRegularizedRatio c (0, z) =
      (z.2 - z.1) / ((c : ℂ) - conj (c : ℂ)) := by
  simp [internalClusterRegularizedRatio]

theorem contDiffAt_internalClusterRegularizedRatio (c : ℍ) (x : ClusterPairParameters)
    (hd : internalClusterDenominator c x ≠ 0) :
    ContDiffAt ℝ ⊤ (internalClusterRegularizedRatio c) x := by
  have hr : ContDiffAt ℝ ⊤ (fun y : ClusterPairParameters => (y.1 : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x contDiffAt_fst
  have ha : ContDiffAt ℝ ⊤ (fun y : ClusterPairParameters => y.2.1) x :=
    contDiffAt_fst.comp x contDiffAt_snd
  have hb : ContDiffAt ℝ ⊤ (fun y : ClusterPairParameters => y.2.2) x :=
    contDiffAt_snd.comp x contDiffAt_snd
  have hc : ContDiffAt ℝ ⊤ (fun y : ClusterPairParameters => conj y.2.1) x :=
    Complex.conjCLE.contDiff.contDiffAt.comp x ha
  have hden : ContDiffAt ℝ ⊤ (internalClusterDenominator c) x :=
    contDiffAt_const.add (hr.mul (hb.sub hc))
  change ContDiffAt ℝ ⊤ (fun y : ClusterPairParameters =>
    (y.2.2 - y.2.1) / internalClusterDenominator c y) x
  simpa only [div_eq_mul_inv, Pi.inv_apply] using (hb.sub ha).mul (hden.inv hd)

theorem contDiffAt_internalClusterRegularizedRatio_zero (c : ℍ) (z : ℂ × ℂ) :
    ContDiffAt ℝ ⊤ (internalClusterRegularizedRatio c) (0, z) :=
  contDiffAt_internalClusterRegularizedRatio c (0, z)
    (by simpa using internalClusterCenterDenominator_ne_zero c)

/-- The actual angular pullback of the regularized ratio. -/
def internalClusterExtendedForm (c : ℍ) (x : ClusterPairParameters) :
    ClusterPairParameters [⋀^Fin 1]→L[ℝ] ℝ :=
  (angularForm (internalClusterRegularizedRatio c x)).compContinuousLinearMap
    (fderiv ℝ (internalClusterRegularizedRatio c) x)

theorem internalClusterExtendedForm_eq (c : ℍ) (x : ClusterPairParameters) :
    internalClusterExtendedForm c x = ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
      ((angularLinearCoefficient (internalClusterRegularizedRatio c x)⁻¹).comp
        (fderiv ℝ (internalClusterRegularizedRatio c) x)) := by
  ext v
  rfl

theorem contDiffAt_internalClusterExtendedForm (c : ℍ) (x : ClusterPairParameters)
    (hd : internalClusterDenominator c x ≠ 0) (hz : x.2.2 - x.2.1 ≠ 0) :
    ContDiffAt ℝ ⊤ (internalClusterExtendedForm c) x := by
  have hf := contDiffAt_internalClusterRegularizedRatio c x hd
  have hratio : internalClusterRegularizedRatio c x ≠ 0 := div_ne_zero hz hd
  rw [funext (internalClusterExtendedForm_eq c)]
  exact (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := ClusterPairParameters) (F := ℝ) (0 : Fin 1)).contDiff.contDiffAt.comp x
      ((angularLinearCoefficient.contDiff.contDiffAt.comp x (hf.inv hratio)).clm_comp
        (hf.fderiv_right (by simp)))

/-- Smoothness at every internal collision face with distinct offsets. -/
theorem contDiffAt_internalClusterExtendedForm_zero (c : ℍ) (z : ℂ × ℂ)
    (hz : z.1 ≠ z.2) :
    ContDiffAt ℝ ⊤ (internalClusterExtendedForm c) (0, z) :=
  contDiffAt_internalClusterExtendedForm c (0, z)
    (by simpa using internalClusterCenterDenominator_ne_zero c) (sub_ne_zero.mpr hz.symm)

/-- The difference of the endpoint offsets, with its full linear differential. -/
def clusterDifference : (ℂ × ℂ) →L[ℝ] ℂ :=
  ContinuousLinearMap.snd ℝ ℂ ℂ - ContinuousLinearMap.fst ℝ ℂ ℂ

@[simp] theorem clusterDifference_apply (z : ℂ × ℂ) : clusterDifference z = z.2 - z.1 := rfl

/-- Inclusion of the radius-zero collision face. -/
def clusterFaceEmbedding : (ℂ × ℂ) →L[ℝ] ClusterPairParameters :=
  (0 : (ℂ × ℂ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℂ × ℂ))

@[simp] theorem clusterFaceEmbedding_apply (z : ℂ × ℂ) :
    clusterFaceEmbedding z = (0, z) := rfl

/-- The exact face restriction is `Im(d(b-a)/(b-a))`. -/
theorem internalClusterExtendedForm_face (c : ℍ) (z : ℂ × ℂ) :
    (internalClusterExtendedForm c (0, z)).compContinuousLinearMap clusterFaceEmbedding =
      (angularForm (z.2 - z.1)).compContinuousLinearMap clusterDifference := by
  let d : ℂ := (c : ℂ) - conj (c : ℂ)
  let C : (ℂ × ℂ) →L[ℝ] ℂ := d⁻¹ • clusterDifference
  have hd : d ≠ 0 := internalClusterCenterDenominator_ne_zero c
  have hfun : internalClusterRegularizedRatio c ∘ clusterFaceEmbedding =
      (C : (ℂ × ℂ) → ℂ) := by
    funext u
    simp [internalClusterRegularizedRatio, internalClusterDenominator, C, d,
      div_eq_mul_inv, mul_comm]
  have hchain : fderiv ℝ (internalClusterRegularizedRatio c ∘ clusterFaceEmbedding) z =
      (fderiv ℝ (internalClusterRegularizedRatio c) (0, z)).comp
        (fderiv ℝ (clusterFaceEmbedding : (ℂ × ℂ) → ClusterPairParameters) z) :=
    fderiv_comp z
      ((contDiffAt_internalClusterRegularizedRatio_zero c z).differentiableAt (by simp))
      clusterFaceEmbedding.differentiableAt
  rw [hfun] at hchain
  simp only [ContinuousLinearMap.fderiv] at hchain
  ext v
  have heval := congrArg (fun f : (ℂ × ℂ) →L[ℝ] ℂ => f (v 0)) hchain.symm
  change fderiv ℝ (internalClusterRegularizedRatio c) (0, z) (clusterFaceEmbedding (v 0)) =
    d⁻¹ * ((v 0).2 - (v 0).1) at heval
  simp only [internalClusterExtendedForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    angularForm_apply, Function.comp_apply, heval, internalClusterRegularizedRatio_zero,
    clusterDifference_apply]
  change ((d⁻¹ * ((v 0).2 - (v 0).1)) / ((z.2 - z.1) / d)).im =
    (((v 0).2 - (v 0).1) / (z.2 - z.1)).im
  rw [mul_comm d⁻¹, ← div_eq_mul_inv, div_div_div_comm, div_self hd, div_one]

theorem differentiableAt_internalClusterPair (c : ℍ) (x : ClusterPairParameters) :
    DifferentiableAt ℝ (internalClusterPair c) x := by
  have hr : DifferentiableAt ℝ (fun y : ClusterPairParameters => (y.1 : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x differentiableAt_fst
  have ha : DifferentiableAt ℝ (fun y : ClusterPairParameters => y.2.1) x :=
    differentiableAt_fst.comp x differentiableAt_snd
  have hb : DifferentiableAt ℝ (fun y : ClusterPairParameters => y.2.2) x :=
    differentiableAt_snd.comp x differentiableAt_snd
  exact ((differentiableAt_const (c : ℂ)).add (hr.mul ha)).prodMk
    ((differentiableAt_const (c : ℂ)).add (hr.mul hb))

/-- At nonzero radius the extended form is the full pullback of the genuine
harmonic angle form, including all radius and offset directions. -/
theorem harmonicAngleForm_internalClusterPair (c : ℍ) (x : ClusterPairParameters)
    (hr : x.1 ≠ 0) (hz : x.2.2 - x.2.1 ≠ 0)
    (hd : internalClusterDenominator c x ≠ 0) :
    (harmonicAngleForm (internalClusterPair c x)).compContinuousLinearMap
        (fderiv ℝ (internalClusterPair c) x) = internalClusterExtendedForm c x := by
  have hpden : (internalClusterPair c x).2 - conj (internalClusterPair c x).1 ≠ 0 := by
    rwa [internalClusterPair_denominator]
  have hcomp : (fun z : ℂ × ℂ => harmonicRatio z.1 z.2) ∘ internalClusterPair c =
      fun y : ClusterPairParameters => (y.1 : ℂ) * internalClusterRegularizedRatio c y :=
    funext (harmonicRatio_internalClusterPair_factor c)
  have hreal : HasFDerivAt (fun y : ClusterPairParameters => (y.1 : ℂ))
      (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ (ℂ × ℂ))) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hasFDerivAt_fst
  have hreg : HasFDerivAt (internalClusterRegularizedRatio c)
      (fderiv ℝ (internalClusterRegularizedRatio c) x) x :=
    ((contDiffAt_internalClusterRegularizedRatio c x hd).differentiableAt (by simp)).hasFDerivAt
  rw [harmonicAngleForm_pullback _ _ (differentiableAt_internalClusterPair c x) hpden,
    hcomp, (hreal.fun_mul hreg).fderiv, harmonicRatio_internalClusterPair_factor]
  ext v
  simp only [internalClusterExtendedForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    angularForm_apply]
  change (((x.1 : ℂ) * (fderiv ℝ (internalClusterRegularizedRatio c) x (v 0)) +
      internalClusterRegularizedRatio c x * ((v 0).1 : ℂ)) /
        ((x.1 : ℂ) * internalClusterRegularizedRatio c x)).im =
      ((fderiv ℝ (internalClusterRegularizedRatio c) x (v 0)) /
        internalClusterRegularizedRatio c x).im
  exact twoInterior_logDerivative x.1 (v 0).1 _ _ hr (div_ne_zero hz hd)

/-- An edge from a collapsing source to a fixed external target. -/
def externalClusterPair (c : ℍ) (d : ℂ) (x : ℝ × ℂ) : ℂ × ℂ :=
  ((c : ℂ) + (x.1 : ℂ) * x.2, d)

/-- External edges do not require removal of a radial factor. -/
def externalClusterRatio (c : ℍ) (d : ℂ) (x : ℝ × ℂ) : ℂ :=
  harmonicRatio (externalClusterPair c d x).1 (externalClusterPair c d x).2

@[simp] theorem externalClusterPair_zero (c : ℍ) (d z : ℂ) :
    externalClusterPair c d (0, z) = ((c : ℂ), d) := by
  simp [externalClusterPair]

@[simp] theorem externalClusterRatio_zero (c : ℍ) (d z : ℂ) :
    externalClusterRatio c d (0, z) = harmonicRatio c d := by
  simp [externalClusterRatio]

theorem contDiffAt_externalClusterPair (c : ℍ) (d : ℂ) (x : ℝ × ℂ) :
    ContDiffAt ℝ ⊤ (externalClusterPair c d) x := by
  have hr : ContDiffAt ℝ ⊤ (fun y : ℝ × ℂ => (y.1 : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x contDiffAt_fst
  exact (contDiffAt_const.add (hr.mul contDiffAt_snd)).prodMk contDiffAt_const

theorem contDiffAt_externalClusterRatio (c : ℍ) (d : ℂ) (x : ℝ × ℂ)
    (hd : (externalClusterPair c d x).2 - conj (externalClusterPair c d x).1 ≠ 0) :
    ContDiffAt ℝ ⊤ (externalClusterRatio c d) x := by
  change ContDiffAt ℝ ⊤ ((fun z : ℂ × ℂ => harmonicRatio z.1 z.2) ∘
    externalClusterPair c d) x
  exact (contDiffAt_harmonicRatio _ _ hd).comp x (contDiffAt_externalClusterPair c d x)

theorem contDiffAt_externalClusterRatio_zero (c : ℍ) (d z : ℂ)
    (hd : d ≠ conj (c : ℂ)) : ContDiffAt ℝ ⊤ (externalClusterRatio c d) (0, z) :=
  contDiffAt_externalClusterRatio c d (0, z) (by simpa using sub_ne_zero.mpr hd)

/-- The actual pulled-back external angular form, defined through its ratio. -/
def externalClusterExtendedForm (c : ℍ) (d : ℂ) (x : ℝ × ℂ) :
    (ℝ × ℂ) [⋀^Fin 1]→L[ℝ] ℝ :=
  (angularForm (externalClusterRatio c d x)).compContinuousLinearMap
    (fderiv ℝ (externalClusterRatio c d) x)

theorem externalClusterExtendedForm_eq (c : ℍ) (d : ℂ) (x : ℝ × ℂ) :
    externalClusterExtendedForm c d x = ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
      ((angularLinearCoefficient (externalClusterRatio c d x)⁻¹).comp
        (fderiv ℝ (externalClusterRatio c d) x)) := by
  ext v
  rfl

theorem contDiffAt_externalClusterExtendedForm (c : ℍ) (d : ℂ) (x : ℝ × ℂ)
    (hd : (externalClusterPair c d x).2 - conj (externalClusterPair c d x).1 ≠ 0)
    (hn : externalClusterRatio c d x ≠ 0) :
    ContDiffAt ℝ ⊤ (externalClusterExtendedForm c d) x := by
  have hf := contDiffAt_externalClusterRatio c d x hd
  rw [funext (externalClusterExtendedForm_eq c d)]
  exact (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := ℝ × ℂ) (F := ℝ) (0 : Fin 1)).contDiff.contDiffAt.comp x
      ((angularLinearCoefficient.contDiff.contDiffAt.comp x (hf.inv hn)).clm_comp
        (hf.fderiv_right (by simp)))

/-- The external-edge form is smooth at the face when the external target avoids
both the center and its reflection. -/
theorem contDiffAt_externalClusterExtendedForm_zero (c : ℍ) (d z : ℂ)
    (hd : d ≠ conj (c : ℂ)) (hne : d ≠ (c : ℂ)) :
    ContDiffAt ℝ ⊤ (externalClusterExtendedForm c d) (0, z) := by
  apply contDiffAt_externalClusterExtendedForm
  · simpa using sub_ne_zero.mpr hd
  · rw [externalClusterRatio_zero, harmonicRatio]
    exact div_ne_zero (sub_ne_zero.mpr hne) (sub_ne_zero.mpr hd)

/-- There is no modification of the harmonic form on the external-edge chart. -/
theorem harmonicAngleForm_externalClusterPair (c : ℍ) (d : ℂ) (x : ℝ × ℂ)
    (hd : (externalClusterPair c d x).2 - conj (externalClusterPair c d x).1 ≠ 0) :
    (harmonicAngleForm (externalClusterPair c d x)).compContinuousLinearMap
        (fderiv ℝ (externalClusterPair c d) x) = externalClusterExtendedForm c d x :=
  harmonicAngleForm_pullback _ _
    ((contDiffAt_externalClusterPair c d x).differentiableAt (by simp)) hd

/-- With the external target and center frozen, external-edge forms vanish in
all internal-offset directions on the collision face. -/
theorem externalClusterExtendedForm_face (c : ℍ) (d z : ℂ)
    (hd : d ≠ conj (c : ℂ)) :
    (externalClusterExtendedForm c d (0, z)).compContinuousLinearMap
      twoInteriorFaceEmbedding = 0 := by
  have hfun : externalClusterRatio c d ∘ twoInteriorFaceEmbedding =
      fun _ : ℂ => harmonicRatio c d := by
    funext u
    simp
  have hchain : fderiv ℝ (externalClusterRatio c d ∘ twoInteriorFaceEmbedding) z =
      (fderiv ℝ (externalClusterRatio c d) (0, z)).comp
        (fderiv ℝ (twoInteriorFaceEmbedding : ℂ → ℝ × ℂ) z) :=
    fderiv_comp z
      ((contDiffAt_externalClusterRatio_zero c d z hd).differentiableAt (by simp))
      twoInteriorFaceEmbedding.differentiableAt
  rw [hfun] at hchain
  rw [fderiv_const_apply] at hchain
  simp only [ContinuousLinearMap.fderiv] at hchain
  ext v
  have heval := congrArg (fun f : ℂ →L[ℝ] ℂ => f (v 0)) hchain.symm
  change fderiv ℝ (externalClusterRatio c d) (0, z) (twoInteriorFaceEmbedding (v 0)) = 0 at heval
  simp only [externalClusterExtendedForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    angularForm_apply, Function.comp_apply, heval, zero_div, Complex.zero_im]
  rfl

section AngularPullback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Angular pullback on an arbitrary real parameter space. -/
def angularPullback (f : E → ℂ) (x : E) : E [⋀^Fin 1]→L[ℝ] ℝ :=
  (angularForm (f x)).compContinuousLinearMap (fderiv ℝ f x)

theorem angularPullback_eq (f : E → ℂ) (x : E) :
    angularPullback f x = ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
      ((angularLinearCoefficient (f x)⁻¹).comp (fderiv ℝ f x)) := by
  ext v
  rfl

theorem contDiffAt_angularPullback (f : E → ℂ) (x : E)
    (hf : ContDiffAt ℝ ⊤ f x) (hn : f x ≠ 0) :
    ContDiffAt ℝ ⊤ (angularPullback f) x := by
  rw [funext (angularPullback_eq f)]
  exact (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).contDiff.contDiffAt.comp x
      ((angularLinearCoefficient.contDiff.contDiffAt.comp x (hf.inv hn)).clm_comp
        (hf.fderiv_right (by simp)))

theorem angularPullback_comp_clm (f : E → ℂ) (e : F →L[ℝ] E) (x : F)
    (hf : DifferentiableAt ℝ f (e x)) :
    (angularPullback f (e x)).compContinuousLinearMap e = angularPullback (f ∘ e) x := by
  rw [angularPullback, angularPullback, fderiv_comp x hf e.differentiableAt,
    e.fderiv]
  ext v
  rfl

/-- A nonzero real factor has no angular logarithmic derivative, even when
it varies in arbitrary parameter directions. -/
theorem angularPullback_real_mul (r : E → ℝ) (f : E → ℂ) (x : E)
    (hrd : DifferentiableAt ℝ r x) (hfd : DifferentiableAt ℝ f x)
    (hr : r x ≠ 0) (hf : f x ≠ 0) :
    angularPullback (fun y => (r y : ℂ) * f y) x = angularPullback f x := by
  have hreal : HasFDerivAt (fun y => (r y : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ r x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hrd.hasFDerivAt
  rw [angularPullback, (hreal.fun_mul hfd.hasFDerivAt).fderiv]
  ext v
  simp only [angularPullback, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    angularForm_apply]
  change (((r x : ℂ) * fderiv ℝ f x (v 0) +
      f x * (fderiv ℝ r x (v 0) : ℂ)) / ((r x : ℂ) * f x)).im =
    (fderiv ℝ f x (v 0) / f x).im
  exact twoInterior_logDerivative (r x) (fderiv ℝ r x (v 0)) _ _ hr hf

/-- Division by a fixed nonzero complex number leaves the angular form unchanged. -/
theorem angularPullback_clm_div (T : E →L[ℝ] ℂ) (d : ℂ) (hd : d ≠ 0) (x : E) :
    angularPullback (fun y => T y / d) x = (angularForm (T x)).compContinuousLinearMap T := by
  let C : E →L[ℝ] ℂ := d⁻¹ • T
  have hfun : (fun y => T y / d) = (C : E → ℂ) := by
    funext y
    simp [C, div_eq_mul_inv, mul_comm]
  rw [hfun, angularPullback, C.fderiv]
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, angularForm_apply,
    Function.comp_apply]
  change ((d⁻¹ * T (v 0)) / (d⁻¹ * T x)).im = (T (v 0) / T x).im
  rw [mul_comm d⁻¹ (T (v 0)), mul_comm d⁻¹ (T x), ← div_eq_mul_inv,
    ← div_eq_mul_inv, div_div_div_comm, div_self hd, div_one]

end AngularPullback

/-- Center and two offsets on an internal collision face. -/
abbrev VariableClusterFace := ℂ × (ℂ × ℂ)

/-- Offset difference on the full face, independent of its center. -/
def variableClusterDifference : VariableClusterFace →L[ℝ] ℂ :=
  clusterDifference.comp (ContinuousLinearMap.snd ℝ ℂ (ℂ × ℂ))

@[simp] theorem variableClusterDifference_apply (x : VariableClusterFace) :
    variableClusterDifference x = x.2.2 - x.2.1 := rfl

/-- The actual face ratio when the coarse center is allowed to move. -/
def variableClusterFaceRatio (x : VariableClusterFace) : ℂ :=
  (x.2.2 - x.2.1) / (x.1 - conj x.1)

/-- Changes of the center contribute no angular form because its reflection
denominator has constant phase. This includes every center tangent direction. -/
theorem angularPullback_variableClusterFaceRatio (x : VariableClusterFace)
    (hc : 0 < x.1.im) (hz : x.2.2 - x.2.1 ≠ 0) :
    angularPullback variableClusterFaceRatio x =
      (angularForm (x.2.2 - x.2.1)).compContinuousLinearMap variableClusterDifference := by
  let r : VariableClusterFace → ℝ := fun y => (2 * y.1.im)⁻¹
  let T : VariableClusterFace →L[ℝ] ℂ := Complex.I⁻¹ • variableClusterDifference
  have hfun : variableClusterFaceRatio = fun y => (r y : ℂ) * T y := by
    funext y
    simp [variableClusterFaceRatio, Complex.sub_conj, r, T, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc]
  have hi : ContDiffAt ℝ ⊤ (fun y : VariableClusterFace => 2 * y.1.im) x :=
    contDiffAt_const.mul (Complex.imCLM.contDiff.contDiffAt.comp x contDiffAt_fst)
  have hreal : (2 * x.1.im : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hr : DifferentiableAt ℝ r x := (hi.inv hreal).differentiableAt (by simp)
  have hT : T x ≠ 0 := by
    change Complex.I⁻¹ * (x.2.2 - x.2.1) ≠ 0
    exact mul_ne_zero (inv_ne_zero Complex.I_ne_zero) hz
  rw [hfun, angularPullback_real_mul r T x hr T.differentiableAt (inv_ne_zero hreal) hT]
  have hTfun : (T : VariableClusterFace → ℂ) =
      fun y => variableClusterDifference y / Complex.I := by
    funext y
    simp [T, div_eq_mul_inv, mul_comm]
  rw [hTfun]
  exact angularPullback_clm_div variableClusterDifference Complex.I Complex.I_ne_zero x

/-- The full ambient chart also allows the coarse center to move. -/
abbrev VariableClusterParameters := ℂ × ClusterPairParameters

def variableInternalClusterPair (x : VariableClusterParameters) : ℂ × ℂ :=
  (x.1 + (x.2.1 : ℂ) * x.2.2.1, x.1 + (x.2.1 : ℂ) * x.2.2.2)

def variableInternalClusterDenominator (x : VariableClusterParameters) : ℂ :=
  x.1 - conj x.1 + (x.2.1 : ℂ) * (x.2.2.2 - conj x.2.2.1)

def variableInternalClusterRegularizedRatio (x : VariableClusterParameters) : ℂ :=
  (x.2.2.2 - x.2.2.1) / variableInternalClusterDenominator x

def variableInternalClusterExtendedForm (x : VariableClusterParameters) :
    VariableClusterParameters [⋀^Fin 1]→L[ℝ] ℝ :=
  angularPullback variableInternalClusterRegularizedRatio x

def variableClusterFaceEmbedding : VariableClusterFace →L[ℝ] VariableClusterParameters :=
  (ContinuousLinearMap.fst ℝ ℂ (ℂ × ℂ)).prod
    (clusterFaceEmbedding.comp (ContinuousLinearMap.snd ℝ ℂ (ℂ × ℂ)))

@[simp] theorem variableClusterFaceEmbedding_apply (x : VariableClusterFace) :
    variableClusterFaceEmbedding x = (x.1, (0, x.2)) := rfl

theorem variableInternalClusterRegularizedRatio_face :
    variableInternalClusterRegularizedRatio ∘ variableClusterFaceEmbedding =
      variableClusterFaceRatio := by
  funext x
  simp [variableInternalClusterRegularizedRatio, variableInternalClusterDenominator,
    variableClusterFaceRatio]

theorem contDiffAt_variableInternalClusterRegularizedRatio (x : VariableClusterParameters)
    (hd : variableInternalClusterDenominator x ≠ 0) :
    ContDiffAt ℝ ⊤ variableInternalClusterRegularizedRatio x := by
  have hc : ContDiffAt ℝ ⊤ (fun y : VariableClusterParameters => y.1) x := contDiffAt_fst
  have hr : ContDiffAt ℝ ⊤ (fun y : VariableClusterParameters => (y.2.1 : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x (contDiffAt_fst.comp x contDiffAt_snd)
  have ha : ContDiffAt ℝ ⊤ (fun y : VariableClusterParameters => y.2.2.1) x :=
    contDiffAt_fst.comp x (contDiffAt_snd.comp x contDiffAt_snd)
  have hb : ContDiffAt ℝ ⊤ (fun y : VariableClusterParameters => y.2.2.2) x :=
    contDiffAt_snd.comp x (contDiffAt_snd.comp x contDiffAt_snd)
  have hcc := Complex.conjCLE.contDiff.contDiffAt.comp x hc
  have hca := Complex.conjCLE.contDiff.contDiffAt.comp x ha
  have hden : ContDiffAt ℝ ⊤ variableInternalClusterDenominator x :=
    (hc.sub hcc).add (hr.mul (hb.sub hca))
  change ContDiffAt ℝ ⊤ (fun y : VariableClusterParameters =>
    (y.2.2.2 - y.2.2.1) / variableInternalClusterDenominator y) x
  simpa only [div_eq_mul_inv, Pi.inv_apply] using (hb.sub ha).mul (hden.inv hd)

theorem variableInternalClusterDenominator_face_ne_zero (x : VariableClusterFace)
    (hc : 0 < x.1.im) :
    variableInternalClusterDenominator (variableClusterFaceEmbedding x) ≠ 0 := by
  simpa [variableInternalClusterDenominator] using harmonicDenominator_ne_zero hc hc.le

/-- Smoothness holds in center, radius, and both offset variables at once. -/
theorem contDiffAt_variableInternalClusterExtendedForm_face (x : VariableClusterFace)
    (hc : 0 < x.1.im) (hz : x.2.2 - x.2.1 ≠ 0) :
    ContDiffAt ℝ ⊤ variableInternalClusterExtendedForm (variableClusterFaceEmbedding x) :=
  contDiffAt_angularPullback _ _
    (contDiffAt_variableInternalClusterRegularizedRatio _
      (variableInternalClusterDenominator_face_ne_zero x hc))
    (div_ne_zero hz (variableInternalClusterDenominator_face_ne_zero x hc))

/-- The general internal face factor has no coarse-center component. -/
theorem variableInternalClusterExtendedForm_face (x : VariableClusterFace)
    (hc : 0 < x.1.im) (hz : x.2.2 - x.2.1 ≠ 0) :
    (variableInternalClusterExtendedForm (variableClusterFaceEmbedding x)).compContinuousLinearMap
      variableClusterFaceEmbedding =
        (angularForm (x.2.2 - x.2.1)).compContinuousLinearMap variableClusterDifference := by
  rw [variableInternalClusterExtendedForm, angularPullback_comp_clm _ _ _
    ((contDiffAt_variableInternalClusterRegularizedRatio _
      (variableInternalClusterDenominator_face_ne_zero x hc)).differentiableAt (by simp)),
    variableInternalClusterRegularizedRatio_face]
  exact angularPullback_variableClusterFaceRatio x hc hz

theorem differentiableAt_variableInternalClusterPair (x : VariableClusterParameters) :
    DifferentiableAt ℝ variableInternalClusterPair x := by
  have hc : DifferentiableAt ℝ (fun y : VariableClusterParameters => y.1) x := differentiableAt_fst
  have hrr : DifferentiableAt ℝ (fun y : VariableClusterParameters => y.2.1) x :=
    differentiableAt_fst.comp x differentiableAt_snd
  have hr : DifferentiableAt ℝ (fun y : VariableClusterParameters => (y.2.1 : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x hrr
  have ha : DifferentiableAt ℝ (fun y : VariableClusterParameters => y.2.2.1) x :=
    differentiableAt_fst.comp x (differentiableAt_snd.comp x differentiableAt_snd)
  have hb : DifferentiableAt ℝ (fun y : VariableClusterParameters => y.2.2.2) x :=
    differentiableAt_snd.comp x (differentiableAt_snd.comp x differentiableAt_snd)
  exact (hc.add (hr.mul ha)).prodMk (hc.add (hr.mul hb))

theorem variableInternalClusterPair_denominator (x : VariableClusterParameters) :
    (variableInternalClusterPair x).2 - conj (variableInternalClusterPair x).1 =
      variableInternalClusterDenominator x := by
  simp only [variableInternalClusterPair, variableInternalClusterDenominator,
    map_add, map_mul, Complex.conj_ofReal]
  ring

theorem harmonicRatio_variableInternalClusterPair_factor (x : VariableClusterParameters) :
    harmonicRatio (variableInternalClusterPair x).1 (variableInternalClusterPair x).2 =
      (x.2.1 : ℂ) * variableInternalClusterRegularizedRatio x := by
  rw [harmonicRatio, variableInternalClusterPair_denominator]
  have hnum : (variableInternalClusterPair x).2 - (variableInternalClusterPair x).1 =
      (x.2.1 : ℂ) * (x.2.2.2 - x.2.2.1) := by
    simp only [variableInternalClusterPair]
    ring
  rw [hnum, variableInternalClusterRegularizedRatio, mul_div_assoc]

/-- Interior equality for the complete chart, with a varying coarse center. -/
theorem harmonicAngleForm_variableInternalClusterPair (x : VariableClusterParameters)
    (hr : x.2.1 ≠ 0) (hz : x.2.2.2 - x.2.2.1 ≠ 0)
    (hd : variableInternalClusterDenominator x ≠ 0) :
    (harmonicAngleForm (variableInternalClusterPair x)).compContinuousLinearMap
      (fderiv ℝ variableInternalClusterPair x) = variableInternalClusterExtendedForm x := by
  have hpden : (variableInternalClusterPair x).2 - conj (variableInternalClusterPair x).1 ≠ 0 := by
    rwa [variableInternalClusterPair_denominator]
  rw [harmonicAngleForm_pullback _ _ (differentiableAt_variableInternalClusterPair x) hpden]
  change angularPullback ((fun z : ℂ × ℂ => harmonicRatio z.1 z.2) ∘
    variableInternalClusterPair) x = angularPullback variableInternalClusterRegularizedRatio x
  have hfun : (fun z : ℂ × ℂ => harmonicRatio z.1 z.2) ∘ variableInternalClusterPair =
      fun y : VariableClusterParameters => (y.2.1 : ℂ) * variableInternalClusterRegularizedRatio y :=
    funext harmonicRatio_variableInternalClusterPair_factor
  rw [hfun]
  exact angularPullback_real_mul (fun y : VariableClusterParameters => y.2.1) _ x
    (differentiableAt_fst.comp x differentiableAt_snd)
    ((contDiffAt_variableInternalClusterRegularizedRatio x hd).differentiableAt (by simp))
    hr (div_ne_zero hz hd)

/-- Both coarse endpoints may vary for an external edge. -/
abbrev VariableExternalClusterParameters := (ℂ × ℂ) × (ℝ × ℂ)
abbrev VariableExternalClusterFace := (ℂ × ℂ) × ℂ

def variableExternalClusterPair (x : VariableExternalClusterParameters) : ℂ × ℂ :=
  (x.1.1 + (x.2.1 : ℂ) * x.2.2, x.1.2)

def variableExternalClusterRatio (x : VariableExternalClusterParameters) : ℂ :=
  harmonicRatio (variableExternalClusterPair x).1 (variableExternalClusterPair x).2

def variableExternalClusterExtendedForm (x : VariableExternalClusterParameters) :
    VariableExternalClusterParameters [⋀^Fin 1]→L[ℝ] ℝ :=
  angularPullback variableExternalClusterRatio x

def variableExternalClusterFaceEmbedding :
    VariableExternalClusterFace →L[ℝ] VariableExternalClusterParameters :=
  (ContinuousLinearMap.fst ℝ (ℂ × ℂ) ℂ).prod
    (twoInteriorFaceEmbedding.comp (ContinuousLinearMap.snd ℝ (ℂ × ℂ) ℂ))

def externalCoarseProjection : VariableExternalClusterFace →L[ℝ] ℂ × ℂ :=
  ContinuousLinearMap.fst ℝ (ℂ × ℂ) ℂ

@[simp] theorem variableExternalClusterFaceEmbedding_apply (x : VariableExternalClusterFace) :
    variableExternalClusterFaceEmbedding x = (x.1, (0, x.2)) := rfl

@[simp] theorem externalCoarseProjection_apply (x : VariableExternalClusterFace) :
    externalCoarseProjection x = x.1 := rfl

@[simp] theorem variableExternalClusterPair_face (x : VariableExternalClusterFace) :
    variableExternalClusterPair (variableExternalClusterFaceEmbedding x) = x.1 := by
  simp [variableExternalClusterPair]

theorem contDiffAt_variableExternalClusterPair (x : VariableExternalClusterParameters) :
    ContDiffAt ℝ ⊤ variableExternalClusterPair x := by
  have hc : ContDiffAt ℝ ⊤ (fun y : VariableExternalClusterParameters => y.1.1) x :=
    contDiffAt_fst.comp x contDiffAt_fst
  have hd : ContDiffAt ℝ ⊤ (fun y : VariableExternalClusterParameters => y.1.2) x :=
    contDiffAt_snd.comp x contDiffAt_fst
  have hrr : ContDiffAt ℝ ⊤ (fun y : VariableExternalClusterParameters => y.2.1) x :=
    contDiffAt_fst.comp x contDiffAt_snd
  have hr : ContDiffAt ℝ ⊤ (fun y : VariableExternalClusterParameters => (y.2.1 : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hrr
  have ha : ContDiffAt ℝ ⊤ (fun y : VariableExternalClusterParameters => y.2.2) x :=
    contDiffAt_snd.comp x contDiffAt_snd
  exact (hc.add (hr.mul ha)).prodMk hd

theorem contDiffAt_variableExternalClusterRatio (x : VariableExternalClusterParameters)
    (hd : (variableExternalClusterPair x).2 - conj (variableExternalClusterPair x).1 ≠ 0) :
    ContDiffAt ℝ ⊤ variableExternalClusterRatio x := by
  change ContDiffAt ℝ ⊤ ((fun z : ℂ × ℂ => harmonicRatio z.1 z.2) ∘
    variableExternalClusterPair) x
  exact (contDiffAt_harmonicRatio _ _ hd).comp x (contDiffAt_variableExternalClusterPair x)

/-- General external forms remain smooth while all coarse and internal variables vary. -/
theorem contDiffAt_variableExternalClusterExtendedForm_face (x : VariableExternalClusterFace)
    (hd : x.1.2 - conj x.1.1 ≠ 0) (hne : x.1.2 - x.1.1 ≠ 0) :
    ContDiffAt ℝ ⊤ variableExternalClusterExtendedForm (variableExternalClusterFaceEmbedding x) := by
  apply contDiffAt_angularPullback
  · exact contDiffAt_variableExternalClusterRatio _ (by simpa [variableExternalClusterPair] using hd)
  · simpa [variableExternalClusterRatio, variableExternalClusterPair, harmonicRatio] using div_ne_zero hne hd

/-- The general external face factor is precisely the coarse harmonic form,
with its full center and external-target differentials. -/
theorem variableExternalClusterExtendedForm_face (x : VariableExternalClusterFace)
    (hd : x.1.2 - conj x.1.1 ≠ 0) :
    (variableExternalClusterExtendedForm (variableExternalClusterFaceEmbedding x)).compContinuousLinearMap
      variableExternalClusterFaceEmbedding =
        (harmonicAngleForm x.1).compContinuousLinearMap externalCoarseProjection := by
  have hf := contDiffAt_variableExternalClusterRatio
    (variableExternalClusterFaceEmbedding x) (by simpa [variableExternalClusterPair] using hd)
  rw [variableExternalClusterExtendedForm,
    angularPullback_comp_clm _ _ _ (hf.differentiableAt (by simp))]
  have hfun : variableExternalClusterRatio ∘ variableExternalClusterFaceEmbedding =
      (fun z : ℂ × ℂ => harmonicRatio z.1 z.2) ∘ externalCoarseProjection := by
    funext y
    simp [variableExternalClusterRatio, variableExternalClusterPair]
  rw [hfun, ← angularPullback_comp_clm _ externalCoarseProjection x
    ((contDiffAt_harmonicRatio x.1.1 x.1.2 hd).differentiableAt (by simp))]
  rfl

/-- On the genuine configuration domain the general external chart gives the
actual harmonic pullback. -/
theorem harmonicAngleForm_variableExternalClusterPair (x : VariableExternalClusterParameters)
    (hd : (variableExternalClusterPair x).2 - conj (variableExternalClusterPair x).1 ≠ 0) :
    (harmonicAngleForm (variableExternalClusterPair x)).compContinuousLinearMap
      (fderiv ℝ variableExternalClusterPair x) = variableExternalClusterExtendedForm x :=
  harmonicAngleForm_pullback _ _
    ((contDiffAt_variableExternalClusterPair x).differentiableAt (by simp)) hd

end EnvelopingIsomorphism.Deformation.Kontsevich
