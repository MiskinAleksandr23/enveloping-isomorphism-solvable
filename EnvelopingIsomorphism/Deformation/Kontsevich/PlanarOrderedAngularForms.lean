import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarNormalizedCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarActualCutoffLimit

/-! Ordered planar angular forms with an arbitrary first nonloop edge.
The coefficients below are evaluations of the literal pulled-back edge forms.
They do not define a replacement for the native forest face measure. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PlanarOrderedAngularForms

open InteriorFiberAngleSplit PlanarNormalizedCoordinates
open Set MeasureTheory ContinuousAlternatingMap
open scoped Topology

abbrev OrderedEdges (N : ℕ) := Fin (Dim N + 1) → Point N × Point N

/-- Pull back every edge in its original order along the actual relabeled planar positions. -/
def topForm {N : ℕ} (e : OrderedEdges N) (σ : Equiv.Perm (Point N)) (x : Parameters N) :
    Parameters N [⋀^Fin (Dim N + 1)]→L[ℝ] ℝ :=
  (coordinateVolume (Dim N + 1)).compContinuousLinearMap
    (ContinuousLinearMap.pi fun j ↦ formLinear (relabeledEdgeForm σ (e j).1 (e j).2 x))

def density {N : ℕ} (e : OrderedEdges N) (σ : Equiv.Perm (Point N)) (x : Parameters N) : ℝ :=
  topForm e σ x (fiberFrame N)

theorem density_eq_det {N : ℕ} (e : OrderedEdges N) (σ : Equiv.Perm (Point N)) (x : Parameters N) :
    density e σ x = Matrix.det (fun r c ↦
      relabeledEdgeForm σ (e c).1 (e c).2 x (fun _ : Fin 1 ↦ fiberFrame N r)) := rfl

/-- Edge reordering has exactly its determinant sign, independently of vertex relabeling. -/
theorem topForm_permute {N : ℕ} (e : OrderedEdges N) (σ : Equiv.Perm (Point N))
    (τ : Equiv.Perm (Fin (Dim N + 1))) (x : Parameters N) :
    topForm (fun j ↦ e (τ j)) σ x = (Equiv.Perm.sign τ : ℝ) • topForm e σ x := by
  ext v
  exact Matrix.det_permute' τ (fun r c ↦
    relabeledEdgeForm σ (e c).1 (e c).2 x (fun _ : Fin 1 ↦ v r))

theorem relabeledEdgeForm_loop {N : ℕ} (σ : Equiv.Perm (Point N)) (a : Point N) (x : Parameters N) :
    relabeledEdgeForm σ a a x = 0 := by
  rw [relabeledEdgeForm_eq]
  ext v
  simp [rotatedEdgeForm, rotatedDifference, rotatedDerivative, shapeDerivative]

theorem density_eq_zero_of_loop {N : ℕ} (e : OrderedEdges N) (σ : Equiv.Perm (Point N))
    (j : Fin (Dim N + 1)) (hj : (e j).1 = (e j).2) (x : Parameters N) : density e σ x = 0 := by
  rw [density_eq_det]
  apply Matrix.det_eq_zero_of_column_eq_zero j
  intro r
  rw [hj, relabeledEdgeForm_loop]
  rfl

def reference {N : ℕ} (e : OrderedEdges N) : Equiv.Perm (Point N) :=
  referencePermutation (e 0).1 (e 0).2

def remainingEdges {N : ℕ} (e : OrderedEdges N) : InteriorFiberAngleSplit.Edges N :=
  fun j ↦ ((reference e).symm (e j.succ).1, (reference e).symm (e j.succ).2)

theorem remainingEdges_nonloop {N : ℕ} (e : OrderedEdges N)
    (he : ∀ j, (e j).1 ≠ (e j).2) : ∀ j, (remainingEdges e j).1 ≠ (remainingEdges e j).2 :=
  fun j ↦ (reference e).symm.injective.ne (he j.succ)

/-- Choosing the first edge as reference leaves the ordered wedge unchanged;
the reference column is literally dθ, so no edge-permutation sign is introduced. -/
theorem topForm_eq_fiberTopForm {N : ℕ} (e : OrderedEdges N) (hfirst : (e 0).1 ≠ (e 0).2)
    (x : Parameters N) : topForm e (reference e) x = fiberTopForm (remainingEdges e) x := by
  have hforms : (fun j ↦ relabeledEdgeForm (reference e) (e j).1 (e j).2 x) =
      orderedEdgeForms (remainingEdges e) x := by
    funext j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · change relabeledEdgeForm (reference e) (e 0).1 (e 0).2 x = rotatedEdgeForm 0 1 x
      rw [referenceEdgeForm]
      exact relabeled_referenceEdgeForm (reference e) _ _
        (referencePermutation_anchor _ _ hfirst) (referencePermutation_reference _ _) x
    · rfl
  unfold topForm fiberTopForm
  simp_rw [congrFun hforms]

theorem density_eq_fiberDensity {N : ℕ} (e : OrderedEdges N) (hfirst : (e 0).1 ≠ (e 0).2)
    (x : Parameters N) : density e (reference e) x = fiberDensity (remainingEdges e) x := by
  unfold density fiberDensity
  rw [topForm_eq_fiberTopForm e hfirst]

/-- Inverse index conversion between the actual primitive and angular shape forms. -/
def primitiveEdges {N : ℕ} (e : InteriorFiberAngleSplit.Edges (N + 1)) : RatioCutoffStokes.Edges N :=
  fun j ↦ e ((RatioCutoffStokes.angularIndex N).symm j)

@[simp] theorem angularEdges_primitiveEdges {N : ℕ} (e : InteriorFiberAngleSplit.Edges (N + 1)) :
    RatioCutoffStokes.angularEdges (primitiveEdges e) = e := by
  funext j
  simp [RatioCutoffStokes.angularEdges, primitiveEdges]

theorem primitiveEdges_nonloop {N : ℕ} (e : InteriorFiberAngleSplit.Edges (N + 1))
    (he : ∀ j, (e j).1 ≠ (e j).2) : ∀ j, (primitiveEdges e j).1 ≠ (primitiveEdges e j).2 :=
  fun j ↦ he _

/-- Vanishing for an arbitrary original ordered nonloop list with at least three
vertices, in its actual first-edge reference coordinates. Native forest face
integration still requires the geometric change of coordinates and measure. -/
theorem integral_density_eq_zero {N : ℕ} (e : OrderedEdges (N + 1))
    (he : ∀ j, (e j).1 ≠ (e j).2)
    (hL1 : IntegrableOn (shapeDensity (remainingEdges e)) (shapeConfiguration (N + 1)))
    (herror : Filter.Tendsto (fun ε : ℝ ↦ ∫ η in shapeConfiguration (N + 1),
      PlanarActualCutoffLimit.error (primitiveEdges (remainingEdges e)) ε η)
      (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    IntegrableOn (density e (reference e)) (integrationRegion (N + 1)) ∧
      (∫ x in integrationRegion (N + 1), density e (reference e) x) = 0 := by
  have h := PlanarActualCutoffLimit.integral_rotatedFiberDensity_eq_zero
    (primitiveEdges (remainingEdges e))
    (primitiveEdges_nonloop _ (remainingEdges_nonloop e he))
    (by simpa using hL1) herror
  simpa only [angularEdges_primitiveEdges,
    show density e (reference e) = fiberDensity (remainingEdges e) from
      funext (density_eq_fiberDensity e (he 0))] using h

end EnvelopingIsomorphism.Deformation.Kontsevich.PlanarOrderedAngularForms
