import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarInnerFacePullback
import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarAngularVanishing

/-! The genuine internal harmonic face wedge in first-edge planar coordinates.
This provides its actual form equality and integral vanishing; transporting
a localized forest lower-face measure remains a separate theorem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PlanarInnerFaceVanishing

open InteriorFiberAngleSplit PlanarOrderedAngularForms PlanarInnerFacePullback
open ContinuousAlternatingMap Set MeasureTheory

/-- The actual restricted extended harmonic edge, retaining its center. -/
def edgeForm {N : ℕ} (σ : Equiv.Perm (Point N)) (s t : Point N) (z : ℂ) (x : Parameters N) :
    Parameters N [⋀^Fin 1]→L[ℝ] ℝ :=
  ((variableInternalClusterExtendedForm
    (variableClusterFaceEmbedding (facePositions σ s t z x))).compContinuousLinearMap
      variableClusterFaceEmbedding).compContinuousLinearMap
        (fderiv ℝ (facePositions σ s t z) x)

/-- Ordered wedge of the actual internal harmonic factors of an interior face. -/
def topForm {N : ℕ} (e : OrderedEdges N) (z : ℂ) (x : Parameters N) :
    Parameters N [⋀^Fin (Dim N + 1)]→L[ℝ] ℝ :=
  (coordinateVolume (Dim N + 1)).compContinuousLinearMap
    (ContinuousLinearMap.pi fun j ↦ formLinear (edgeForm (reference e) (e j).1 (e j).2 z x))

def density {N : ℕ} (e : OrderedEdges N) (z : ℂ) (x : Parameters N) : ℝ :=
  topForm e z x (fiberFrame N)

theorem topForm_eq_angular {N : ℕ} (e : OrderedEdges N)
    (he : ∀ j, (e j).1 ≠ (e j).2) (z : ℂ) (hz : 0 < z.im)
    (x : Parameters N) (hx : x.2 ∈ shapeConfiguration N) :
    topForm e z x = PlanarOrderedAngularForms.topForm e (reference e) x := by
  unfold topForm PlanarOrderedAngularForms.topForm edgeForm
  simp_rw [internalFace_pullback _ _ _ (he _) z hz x hx]

theorem density_eq_angular {N : ℕ} (e : OrderedEdges N)
    (he : ∀ j, (e j).1 ≠ (e j).2) (z : ℂ) (hz : 0 < z.im)
    (x : Parameters N) (hx : x.2 ∈ shapeConfiguration N) :
    density e z x = PlanarOrderedAngularForms.density e (reference e) x := by
  unfold density PlanarOrderedAngularForms.density
  rw [topForm_eq_angular e he z hz x hx]

/-- Absolute convergence and vanishing for the actual internal face wedge.
There is no analytic premise and no assumption equating two integrals. -/
theorem integral_eq_zero {N : ℕ} (e : OrderedEdges (N + 1))
    (he : ∀ j, (e j).1 ≠ (e j).2) (z : ℂ) (hz : 0 < z.im) :
    IntegrableOn (density e z) (integrationRegion (N + 1)) ∧
      (∫ x in integrationRegion (N + 1), density e z x) = 0 := by
  have h := PlanarAngularVanishing.ordered_integral_eq_zero e
  have heq : ∀ x ∈ integrationRegion (N + 1),
      PlanarOrderedAngularForms.density e (reference e) x = density e z x :=
    fun x hx ↦ (density_eq_angular e he z hz x hx.2).symm
  refine ⟨h.1.congr_fun heq (measurableSet_integrationRegion _), ?_⟩
  rw [← setIntegral_congr_fun (measurableSet_integrationRegion _) heq]
  exact h.2

end EnvelopingIsomorphism.Deformation.Kontsevich.PlanarInnerFaceVanishing
