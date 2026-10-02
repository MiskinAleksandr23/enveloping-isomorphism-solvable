import EnvelopingIsomorphism.Deformation.Kontsevich.ForestGraphForms
import EnvelopingIsomorphism.Deformation.Kontsevich.GraphFormsClosed

/-! Actual ordered determinant products of the extended forest edge forms.
Local logarithmic potentials prove smoothness and closedness in every degree
on the genuine reflected parameter submodule, including radial corners. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestGraphTopForms

open ForestGraphForms ContinuousAlternatingMap Filter
open scoped Classical Topology

/-- Original directed graph edges with the actual nonloop condition. -/
structure Edge (n m : ℕ) where
  source : Fin n
  target : Fin n ⊕ Fin m
  nonloop : target ≠ Sum.inl source

variable {T : RootedTree} [Fintype T] {n m : ℕ} (D : ForestPositiveScale.ShapeData T n m)

def edgeRatio (e : Edge n m) (x : ParameterSpace D) : ℂ :=
  numeratorUnit D e.source e.target e.nonloop x / denominatorUnit D e.source e.target x

theorem edgeRatio_ne_zero (e : Edge n m) (x : ParameterSpace D) (hx : Regular D x) : edgeRatio D e x ≠ 0 :=
  div_ne_zero (hx (harmonicNumeratorPair e.source e.target e.nonloop))
    (hx (harmonicDenominatorPair e.source e.target))

theorem contDiffAt_edgeRatio (e : Edge n m) (x : ParameterSpace D) (hx : Regular D x) :
    ContDiffAt ℝ ⊤ (edgeRatio D e) x := by
  change ContDiffAt ℝ ⊤ (fun y : ParameterSpace D =>
    numeratorUnit D e.source e.target e.nonloop y / denominatorUnit D e.source e.target y) x
  have hn : ContDiffAt ℝ ⊤ (numeratorUnit D e.source e.target e.nonloop) x := (contDiff_unit D _).contDiffAt
  have hd : ContDiffAt ℝ ⊤ (denominatorUnit D e.source e.target) x := (contDiff_unit D _).contDiffAt
  simpa only [div_eq_mul_inv, Pi.inv_apply] using
    hn.mul (hd.inv (hx (harmonicDenominatorPair e.source e.target)))

theorem edgeForm_eq_ratio_pullback (e : Edge n m) (x : ParameterSpace D) (hx : Regular D x) :
    ForestGraphForms.edgeForm D e.source e.target e.nonloop x = angularPullback (edgeRatio D e) x :=
  (angularPullback_div _ _ x ((contDiff_unit D _).differentiable (by simp)).differentiableAt
    ((contDiff_unit D _).differentiable (by simp)).differentiableAt
      (hx (harmonicNumeratorPair e.source e.target e.nonloop))
      (hx (harmonicDenominatorPair e.source e.target))).symm

/-- The actual linear representative of the already defined extended edge one-form. -/
def edgeLinear (e : Edge n m) (x : ParameterSpace D) : ParameterSpace D →L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ParameterSpace D) (F := ℝ)
    (0 : Fin 1)).symm (ForestGraphForms.edgeForm D e.source e.target e.nonloop x)

theorem edgeLinear_apply (e : Edge n m) (x v : ParameterSpace D) :
    edgeLinear D e x v = ForestGraphForms.edgeForm D e.source e.target e.nonloop x (fun _ : Fin 1 => v) := by
  have h := (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ParameterSpace D)
    (F := ℝ) (0 : Fin 1)).apply_symm_apply (ForestGraphForms.edgeForm D e.source e.target e.nonloop x)
  exact congrArg (fun ω : ParameterSpace D [⋀^Fin 1]→L[ℝ] ℝ => ω (fun _ => v)) h

theorem edgeLinear_eq_angularCoefficient (e : Edge n m) (x : ParameterSpace D) (hx : Regular D x) :
    edgeLinear D e x = (angularLinearCoefficient (edgeRatio D e x)⁻¹).comp (fderiv ℝ (edgeRatio D e) x) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [edgeLinear_apply, edgeForm_eq_ratio_pullback D e x hx]
  simp only [angularPullback, ContinuousAlternatingMap.compContinuousLinearMap_apply, angularForm_apply]
  change ((fderiv ℝ (edgeRatio D e) x v) / edgeRatio D e x).im =
    ((edgeRatio D e x)⁻¹ * fderiv ℝ (edgeRatio D e) x v).im
  rw [div_eq_inv_mul]

def edgePotential (e : Edge n m) (x₀ : ParameterSpace D) : ParameterSpace D → ℝ :=
  localAnglePotential (edgeRatio D e) x₀

theorem contDiffAt_edgePotential (e : Edge n m) (x₀ : ParameterSpace D) (hx₀ : Regular D x₀) :
    ContDiffAt ℝ ⊤ (edgePotential D e x₀) x₀ :=
  contDiffAt_localAnglePotential (edgeRatio_ne_zero D e x₀ hx₀) (contDiffAt_edgeRatio D e x₀ hx₀)

theorem eventually_hasFDerivAt_edgePotential (e : Edge n m) (x₀ : ParameterSpace D) (hx₀ : Regular D x₀) :
    ∀ᶠ x in 𝓝 x₀, HasFDerivAt (edgePotential D e x₀) (edgeLinear D e x) x := by
  have hs := eventually_localAngle_slit (edgeRatio_ne_zero D e x₀ hx₀)
    (contDiffAt_edgeRatio D e x₀ hx₀).continuousAt
  have hr : ∀ᶠ x in 𝓝 x₀, Regular D x := (isOpen_regular D).mem_nhds hx₀
  filter_upwards [hs, hr] with x hxs hx
  rw [edgeLinear_eq_angularCoefficient D e x hx]
  exact hasFDerivAt_localAnglePotential (edgeRatio_ne_zero D e x₀ hx₀)
    ((contDiffAt_edgeRatio D e x hx).differentiableAt (by simp)) hxs

/-- Ordered determinant product of the actual extended edge forms. -/
def topForm {r : ℕ} (edges : Fin r → Edge n m) (x : ParameterSpace D) : ParameterSpace D [⋀^Fin r]→L[ℝ] ℝ :=
  (coordinateVolume r).compContinuousLinearMap (ContinuousLinearMap.pi fun a => edgeLinear D (edges a) x)

theorem topForm_apply {r : ℕ} (edges : Fin r → Edge n m) (x : ParameterSpace D) (v : Fin r → ParameterSpace D) :
    topForm D edges x v = Matrix.det (fun a b => edgeLinear D (edges b) x (v a)) := rfl

def potentialMap {r : ℕ} (edges : Fin r → Edge n m) (x₀ : ParameterSpace D) : ParameterSpace D → (Fin r → ℝ) :=
  fun x a => edgePotential D (edges a) x₀ x

theorem contDiffAt_potentialMap {r : ℕ} (edges : Fin r → Edge n m) (x₀ : ParameterSpace D) (hx₀ : Regular D x₀) :
    ContDiffAt ℝ ⊤ (potentialMap D edges x₀) x₀ :=
  contDiffAt_pi.mpr fun a => contDiffAt_edgePotential D (edges a) x₀ hx₀

theorem eventually_topForm_eq_potentialPullback {r : ℕ} (edges : Fin r → Edge n m)
    (x₀ : ParameterSpace D) (hx₀ : Regular D x₀) :
    topForm D edges =ᶠ[𝓝 x₀] fun x => (coordinateVolume r).compContinuousLinearMap
      (fderiv ℝ (potentialMap D edges x₀) x) := by
  have hder : ∀ᶠ x in 𝓝 x₀, ∀ a, HasFDerivAt (edgePotential D (edges a) x₀) (edgeLinear D (edges a) x) x :=
    Filter.eventually_all.mpr fun a => eventually_hasFDerivAt_edgePotential D (edges a) x₀ hx₀
  filter_upwards [hder] with x hx
  have hpi : HasFDerivAt (potentialMap D edges x₀) (ContinuousLinearMap.pi fun a => edgeLinear D (edges a) x) x :=
    hasFDerivAt_pi.mpr hx
  rw [hpi.fderiv]
  rfl

theorem extDeriv_topForm {r : ℕ} (edges : Fin r → Edge n m) (x₀ : ParameterSpace D) (hx₀ : Regular D x₀) :
    extDeriv (topForm D edges) x₀ = 0 := by
  rw [(eventually_topForm_eq_potentialPullback D edges x₀ hx₀).extDeriv_eq]
  have hc : DifferentiableAt ℝ (fun _ : Fin r → ℝ => coordinateVolume r) (potentialMap D edges x₀ x₀) :=
    differentiableAt_const _
  rw [extDeriv_pullback hc (contDiffAt_potentialMap D edges x₀ hx₀) (by simp)]
  ext v
  simp [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]

theorem contDiffAt_topForm {r : ℕ} (edges : Fin r → Edge n m) (x₀ : ParameterSpace D) (hx₀ : Regular D x₀) :
    ContDiffAt ℝ ⊤ (topForm D edges) x₀ := by
  have hD : ContDiffAt ℝ ⊤ (fderiv ℝ (potentialMap D edges x₀)) x₀ :=
    (contDiffAt_potentialMap D edges x₀ hx₀).fderiv_right (by simp)
  have hP : ContDiffAt ℝ ⊤ (fun x => (coordinateVolume r).compContinuousLinearMap
      (fderiv ℝ (potentialMap D edges x₀) x)) x₀ :=
    (contDiff_compContinuousLinearMap (coordinateVolume r)).contDiffAt.comp x₀ hD
  exact hP.congr_of_eventuallyEq (eventually_topForm_eq_potentialPullback D edges x₀ hx₀)

theorem contDiffOn_topForm {r : ℕ} (edges : Fin r → Edge n m) :
    ContDiffOn ℝ ⊤ (topForm D edges) {x | Regular D x} :=
  fun x hx => (contDiffAt_topForm D edges x hx).contDiffWithinAt

/-- At positive internal radii this is exactly the determinant of the actual
harmonic edge pullbacks on reflected tangent directions, in the original edge order. -/
theorem topForm_eq_harmonicDeterminant {r : ℕ} (edges : Fin r → Edge n m)
    (x : ParameterSpace D) (hx : Regular D x) (hpos : ForestMarkedFrameInverse.PositiveInternal T x.val.1)
    (v : Fin r → ParameterSpace D) :
    topForm D edges x v = Matrix.det (fun a b =>
      ((harmonicAngleForm (ForestGraphForms.edgeMap D (edges b).source (edges b).target x)).compContinuousLinearMap
        (fderiv ℝ (ForestGraphForms.edgeMap D (edges b).source (edges b).target) x)) (fun _ : Fin 1 => v a)) := by
  rw [topForm_apply]
  congr 1
  funext a b
  rw [edgeLinear_apply, ← harmonic_pullback_eq_edgeForm D (edges b).source (edges b).target (edges b).nonloop x hx hpos]

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestGraphTopForms
