import EnvelopingIsomorphism.Deformation.Kontsevich.GraphCoordinateDomain
import EnvelopingIsomorphism.Deformation.Kontsevich.LocalAnglePotential
import EnvelopingIsomorphism.Deformation.Kontsevich.AlternatingPullbackSmooth

/-!
# Smooth closed graph forms on the native admissible domain

For the determinant product, local rotated logarithmic potentials identify the
actual form with a pullback of a constant coordinate volume form. This proves
closedness without a new exterior-product calculus or an integral identity.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.GraphForms

open ContinuousAlternatingMap Filter Set
open ComplexConjugate
open scoped Topology

variable {n m : ℕ}

theorem contDiff_interiorPoint (i : Fin (n + 1)) : ContDiff ℝ ⊤ (interiorPoint (m := m) i) := by
  cases i using Fin.cases with
  | zero => exact contDiff_const
  | succ j => exact ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.fst ℝ (Fin n → ℂ) (Fin m → ℝ))).contDiff

theorem contDiff_vertexPoint (v : Vertex n m) : ContDiff ℝ ⊤ (vertexPoint v) := by
  cases v with
  | inl i => exact contDiff_interiorPoint i
  | inr j => exact (vertexTangent (Sum.inr j : Vertex n m)).contDiff

theorem contDiff_edgeMap (e : Edge n m) : ContDiff ℝ ⊤ (edgeMap e) :=
  (contDiff_interiorPoint e.source).prodMk (contDiff_vertexPoint e.target)

def edgeRatio (e : Edge n m) (x : Coordinates n m) : ℂ :=
  harmonicRatio (edgeMap e x).1 (edgeMap e x).2

theorem Admissible.edge_denominator_ne_zero {x : Coordinates n m} (hx : Admissible x)
    (e : Edge n m) : (edgeMap e x).2 - conj (edgeMap e x).1 ≠ 0 := by
  simpa only [edgeMap, toConfiguration_interior, toConfiguration_vertexPoint] using
    (toConfiguration ⟨x, hx⟩).vertex_harmonicDenominator_ne_zero e.source e.target

theorem Admissible.edgeRatio_ne_zero {x : Coordinates n m} (hx : Admissible x)
    (e : Edge n m) (he : e.target ≠ Sum.inl e.source) : edgeRatio e x ≠ 0 := by
  simpa only [edgeRatio, edgeMap, toConfiguration_interior, toConfiguration_vertexPoint] using
    (toConfiguration ⟨x, hx⟩).vertex_harmonicRatio_ne_zero e.source e.target he

theorem contDiffAt_edgeRatio (e : Edge n m) {x : Coordinates n m} (hx : Admissible x) :
    ContDiffAt ℝ ⊤ (edgeRatio e) x := by
  change ContDiffAt ℝ ⊤ (fun y : Coordinates n m =>
    harmonicRatio (edgeMap e y).1 (edgeMap e y).2) x
  exact (contDiffAt_harmonicRatio (edgeMap e x).1 (edgeMap e x).2
    (hx.edge_denominator_ne_zero e)).comp x (contDiff_edgeMap e).contDiffAt

theorem contDiffAt_edgeForm (e : Edge n m) (he : e.target ≠ Sum.inl e.source)
    {x : Coordinates n m} (hx : Admissible x) : ContDiffAt ℝ ⊤ (edgeForm e) x := by
  have hω := contDiffAt_harmonicAngleForm _ _ (hx.edge_denominator_ne_zero e)
    (hx.edgeRatio_ne_zero e he)
  exact (ContinuousAlternatingMap.compContinuousLinearMapCLM (edgeTangent e)).contDiff.contDiffAt.comp x
    (hω.comp x (contDiff_edgeMap e).contDiffAt)

theorem contDiffOn_edgeForm (e : Edge n m) (he : e.target ≠ Sum.inl e.source) :
    ContDiffOn ℝ ⊤ (edgeForm e) (admissibleSet n m) :=
  fun _ hx => (contDiffAt_edgeForm e he hx).contDiffWithinAt

theorem extDeriv_edgeForm_eq_zero (e : Edge n m) (he : e.target ≠ Sum.inl e.source)
    {x : Coordinates n m} (hx : Admissible x) : extDeriv (edgeForm e) x = 0 := by
  have heq : edgeForm e = fun y => (harmonicAngleForm (edgeMap e y)).compContinuousLinearMap
      (fderiv ℝ (edgeMap e) y) := funext (edgeForm_eq_pullback e)
  have hω := (contDiffAt_harmonicAngleForm _ _ (hx.edge_denominator_ne_zero e)
    (hx.edgeRatio_ne_zero e he)).differentiableAt (by simp)
  rw [heq, extDeriv_pullback (f := edgeMap e) (ω := harmonicAngleForm) (x := x)
      hω (contDiff_edgeMap e).contDiffAt (by simp),
    extDeriv_harmonicAngleForm _ _ (hx.edge_denominator_ne_zero e) (hx.edgeRatio_ne_zero e he)]
  ext v
  rfl

theorem edgeForm_eq_ratio_pullback (e : Edge n m) {x : Coordinates n m} (hx : Admissible x) :
    edgeForm e x = (angularForm (edgeRatio e x)).compContinuousLinearMap
      (fderiv ℝ (edgeRatio e) x) := by
  have h := harmonicAngleForm_pullback (edgeMap e) x (hasFDerivAt_edgeMap e x).differentiableAt
    (hx.edge_denominator_ne_zero e)
  rw [(hasFDerivAt_edgeMap e x).fderiv] at h
  exact h

theorem edgeLinear_eq_angularCoefficient (e : Edge n m) {x : Coordinates n m} (hx : Admissible x) :
    edgeLinear e x = (angularLinearCoefficient (edgeRatio e x)⁻¹).comp (fderiv ℝ (edgeRatio e) x) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [edgeLinear_apply, edgeForm_eq_ratio_pullback e hx,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, angularForm_apply]
  change ((fderiv ℝ (edgeRatio e) x v) / edgeRatio e x).im =
    ((edgeRatio e x)⁻¹ * fderiv ℝ (edgeRatio e) x v).im
  rw [div_eq_inv_mul]

def edgePotential (e : Edge n m) (x₀ : Coordinates n m) : Coordinates n m → ℝ :=
  localAnglePotential (edgeRatio e) x₀

theorem contDiffAt_edgePotential (e : Edge n m) (he : e.target ≠ Sum.inl e.source)
    {x₀ : Coordinates n m} (hx₀ : Admissible x₀) :
    ContDiffAt ℝ ⊤ (edgePotential e x₀) x₀ :=
  contDiffAt_localAnglePotential (hx₀.edgeRatio_ne_zero e he) (contDiffAt_edgeRatio e hx₀)

theorem eventually_hasFDerivAt_edgePotential (e : Edge n m) (he : e.target ≠ Sum.inl e.source)
    {x₀ : Coordinates n m} (hx₀ : Admissible x₀) :
    ∀ᶠ x in 𝓝 x₀, HasFDerivAt (edgePotential e x₀) (edgeLinear e x) x := by
  have hslit := eventually_localAngle_slit (hx₀.edgeRatio_ne_zero e he)
    (contDiffAt_edgeRatio e hx₀).continuousAt
  have hadm : ∀ᶠ x in 𝓝 x₀, Admissible x := (isOpen_admissibleSet n m).mem_nhds hx₀
  filter_upwards [hslit, hadm] with x hxs hx
  rw [edgeLinear_eq_angularCoefficient e hx]
  exact hasFDerivAt_localAnglePotential (hx₀.edgeRatio_ne_zero e he)
    ((contDiffAt_edgeRatio e hx).differentiableAt (by simp)) hxs

/-- The local list of actual angular potentials in the same order as the edges. -/
def potentialMap {r : ℕ} (edges : Fin r → Edge n m) (x₀ : Coordinates n m) :
    Coordinates n m → (Fin r → ℝ) :=
  fun x a => edgePotential (edges a) x₀ x

theorem contDiffAt_potentialMap {r : ℕ} (edges : Fin r → Edge n m)
    (he : ∀ a, (edges a).target ≠ Sum.inl (edges a).source)
    {x₀ : Coordinates n m} (hx₀ : Admissible x₀) :
    ContDiffAt ℝ ⊤ (potentialMap edges x₀) x₀ :=
  contDiffAt_pi.mpr fun a => contDiffAt_edgePotential (edges a) (he a) hx₀

theorem eventually_topForm_eq_potentialPullback {r : ℕ} (edges : Fin r → Edge n m)
    (he : ∀ a, (edges a).target ≠ Sum.inl (edges a).source)
    {x₀ : Coordinates n m} (hx₀ : Admissible x₀) :
    topForm edges =ᶠ[𝓝 x₀] fun x => (coordinateVolume r).compContinuousLinearMap
      (fderiv ℝ (potentialMap edges x₀) x) := by
  have hder : ∀ᶠ x in 𝓝 x₀, ∀ a, HasFDerivAt (edgePotential (edges a) x₀)
      (edgeLinear (edges a) x) x :=
    Filter.eventually_all.mpr fun a => eventually_hasFDerivAt_edgePotential (edges a) (he a) hx₀
  filter_upwards [hder] with x hx
  have hpi : HasFDerivAt (potentialMap edges x₀)
      (ContinuousLinearMap.pi fun a => edgeLinear (edges a) x) x := hasFDerivAt_pi.mpr hx
  rw [hpi.fderiv]
  rfl

/-- Every ordered determinant product of non-loop harmonic edge forms is
actually closed on the native admissible domain, in arbitrary degree. -/
theorem extDeriv_topForm_eq_zero {r : ℕ} (edges : Fin r → Edge n m)
    (he : ∀ a, (edges a).target ≠ Sum.inl (edges a).source)
    {x₀ : Coordinates n m} (hx₀ : Admissible x₀) : extDeriv (topForm edges) x₀ = 0 := by
  rw [(eventually_topForm_eq_potentialPullback edges he hx₀).extDeriv_eq]
  have hc : DifferentiableAt ℝ (fun _ : Fin r → ℝ => coordinateVolume r) (potentialMap edges x₀ x₀) :=
    differentiableAt_const _
  rw [extDeriv_pullback hc (contDiffAt_potentialMap edges he hx₀) (by simp)]
  ext v
  simp [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]

/-- Smoothness of the actual form-valued determinant product, in arbitrary
degree, follows from its local potential pullback and the smooth alternating
pullback operator. -/
theorem contDiffAt_topForm {r : ℕ} (edges : Fin r → Edge n m)
    (he : ∀ a, (edges a).target ≠ Sum.inl (edges a).source)
    {x₀ : Coordinates n m} (hx₀ : Admissible x₀) : ContDiffAt ℝ ⊤ (topForm edges) x₀ := by
  have hD : ContDiffAt ℝ ⊤ (fderiv ℝ (potentialMap edges x₀)) x₀ :=
    (contDiffAt_potentialMap edges he hx₀).fderiv_right (by simp)
  have hP : ContDiffAt ℝ ⊤ (fun x => (coordinateVolume r).compContinuousLinearMap
      (fderiv ℝ (potentialMap edges x₀) x)) x₀ :=
    (contDiff_compContinuousLinearMap (coordinateVolume r)).contDiffAt.comp x₀ hD
  exact hP.congr_of_eventuallyEq (eventually_topForm_eq_potentialPullback edges he hx₀)

theorem contDiffOn_topForm {r : ℕ} (edges : Fin r → Edge n m)
    (he : ∀ a, (edges a).target ≠ Sum.inl (edges a).source) :
    ContDiffOn ℝ ⊤ (topForm edges) (admissibleSet n m) :=
  fun _ hx => (contDiffAt_topForm edges he hx).contDiffWithinAt

theorem extDeriv_topForm_eqOn_zero {r : ℕ} (edges : Fin r → Edge n m)
    (he : ∀ a, (edges a).target ≠ Sum.inl (edges a).source) :
    Set.EqOn (extDeriv (topForm edges)) 0 (admissibleSet n m) :=
  fun _ hx => extDeriv_topForm_eq_zero edges he hx

theorem contDiffAt_topDensity (edges : Fin (dimension n m) → Edge n m)
    (he : ∀ a, (edges a).target ≠ Sum.inl (edges a).source)
    {x : Coordinates n m} (hx : Admissible x) : ContDiffAt ℝ ⊤ (topDensity edges) x :=
  (ContinuousAlternatingMap.apply ℝ _ ℝ (realBasis n m)).contDiff.contDiffAt.comp x
    (contDiffAt_topForm edges he hx)

theorem contDiffOn_topDensity (edges : Fin (dimension n m) → Edge n m)
    (he : ∀ a, (edges a).target ≠ Sum.inl (edges a).source) :
    ContDiffOn ℝ ⊤ (topDensity edges) (admissibleSet n m) :=
  fun _ hx => (contDiffAt_topDensity edges he hx).contDiffWithinAt

end EnvelopingIsomorphism.Deformation.Kontsevich.GraphForms
