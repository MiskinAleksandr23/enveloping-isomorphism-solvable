import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterCoordinateIndices
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterLocalCompact
import EnvelopingIsomorphism.Deformation.Kontsevich.RealClusterForms

/-!
# Free smooth coordinates for a finite real cluster

The cluster anchor has shape coordinate `I`, and the global anchor is stationary
at `I`. All other interior shape/coarse positions are free complex coordinates.
One real coordinate per boundary label records either its inner shape position
or its stationary outside position. The center and radius are real.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration Topology

abbrev BoundaryClusterFreeCoordinates {n : ℕ} (i a : Fin n) (S : Finset (Fin n)) (m : ℕ) :=
  (BoundaryClusterCoarseIndex i S → ℂ) × (BoundaryClusterShapeIndex a S → ℂ) ×
    (Fin m → ℝ) × ℝ × ℝ

namespace BoundaryClusterFreeCoordinates

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)}

def center (x : BoundaryClusterFreeCoordinates i a S m) : ℝ := x.2.2.2.1

def radius (x : BoundaryClusterFreeCoordinates i a S m) : ℝ := x.2.2.2.2

def base (x : BoundaryClusterFreeCoordinates i a S m) (j : Fin n) : ℂ :=
  if hj : j ∈ S then (x.center : ℂ)
  else if hji : j = i then Complex.I else x.1 ⟨j, hj, hji⟩

def velocity (x : BoundaryClusterFreeCoordinates i a S m) (j : Fin n) : ℂ :=
  if hj : j ∈ S then if hja : j = a then Complex.I else x.2.1 ⟨j, hj, hja⟩ else 0

def boundaryBase (l u : Fin (m + 1)) (x : BoundaryClusterFreeCoordinates i a S m) (j : Fin m) : ℝ :=
  if j ∈ boundaryClusterBlock l u then x.center else x.2.2.1 j

def boundaryVelocity (l u : Fin (m + 1)) (x : BoundaryClusterFreeCoordinates i a S m) (j : Fin m) : ℝ :=
  if j ∈ boundaryClusterBlock l u then x.2.2.1 j else 0

def parameters (l u : Fin (m + 1)) (x : BoundaryClusterFreeCoordinates i a S m) :
    BoundaryClusterParameterSpace n m :=
  (x.center, x.base, x.velocity, x.boundaryBase l u, x.boundaryVelocity l u)

@[fun_prop] theorem contDiff_center : ContDiff ℝ ⊤ (center : BoundaryClusterFreeCoordinates i a S m → ℝ) := by
  unfold center
  fun_prop

@[fun_prop] theorem contDiff_radius : ContDiff ℝ ⊤ (radius : BoundaryClusterFreeCoordinates i a S m → ℝ) := by
  unfold radius
  fun_prop

@[fun_prop] theorem contDiff_base (j : Fin n) :
    ContDiff ℝ ⊤ (fun x : BoundaryClusterFreeCoordinates i a S m => x.base j) := by
  unfold base
  split_ifs
  · exact Complex.ofRealCLM.contDiff.comp contDiff_center
  · fun_prop
  · fun_prop

@[fun_prop] theorem contDiff_velocity (j : Fin n) :
    ContDiff ℝ ⊤ (fun x : BoundaryClusterFreeCoordinates i a S m => x.velocity j) := by
  unfold velocity
  split_ifs <;> fun_prop

@[fun_prop] theorem contDiff_boundaryBase (l u : Fin (m + 1)) (j : Fin m) :
    ContDiff ℝ ⊤ (fun x : BoundaryClusterFreeCoordinates i a S m => x.boundaryBase l u j) := by
  unfold boundaryBase
  split_ifs <;> fun_prop

@[fun_prop] theorem contDiff_boundaryVelocity (l u : Fin (m + 1)) (j : Fin m) :
    ContDiff ℝ ⊤ (fun x : BoundaryClusterFreeCoordinates i a S m => x.boundaryVelocity l u j) := by
  unfold boundaryVelocity
  split_ifs <;> fun_prop

@[fun_prop] theorem contDiff_parameters (l u : Fin (m + 1)) :
    ContDiff ℝ ⊤ (parameters (i := i) (a := a) (S := S) l u) := by
  unfold parameters
  exact contDiff_center.prodMk ((contDiff_pi.mpr contDiff_base).prodMk
    ((contDiff_pi.mpr contDiff_velocity).prodMk
      ((contDiff_pi.mpr (contDiff_boundaryBase l u)).prodMk
        (contDiff_pi.mpr (contDiff_boundaryVelocity l u)))))

@[fun_prop] theorem continuous_center : Continuous (center : BoundaryClusterFreeCoordinates i a S m → ℝ) :=
  contDiff_center.continuous

@[fun_prop] theorem continuous_radius : Continuous (radius : BoundaryClusterFreeCoordinates i a S m → ℝ) :=
  contDiff_radius.continuous

@[fun_prop] theorem continuous_base (j : Fin n) :
    Continuous (fun x : BoundaryClusterFreeCoordinates i a S m => x.base j) :=
  (contDiff_base j).continuous

@[fun_prop] theorem continuous_velocity (j : Fin n) :
    Continuous (fun x : BoundaryClusterFreeCoordinates i a S m => x.velocity j) :=
  (contDiff_velocity j).continuous

@[fun_prop] theorem continuous_boundaryBase (l u : Fin (m + 1)) (j : Fin m) :
    Continuous (fun x : BoundaryClusterFreeCoordinates i a S m => x.boundaryBase l u j) :=
  (contDiff_boundaryBase l u j).continuous

@[fun_prop] theorem continuous_boundaryVelocity (l u : Fin (m + 1)) (j : Fin m) :
    Continuous (fun x : BoundaryClusterFreeCoordinates i a S m => x.boundaryVelocity l u j) :=
  (contDiff_boundaryVelocity l u j).continuous

@[fun_prop] theorem continuous_parameters (l u : Fin (m + 1)) :
    Continuous (parameters (i := i) (a := a) (S := S) l u) :=
  (contDiff_parameters l u).continuous

theorem base_eq_center (x : BoundaryClusterFreeCoordinates i a S m) (j : Fin n) (hj : j ∈ S) :
    x.base j = (x.center : ℂ) := by simp [base, hj]

theorem base_normalized (x : BoundaryClusterFreeCoordinates i a S m) (hi : i ∉ S) :
    x.base i = Complex.I := by simp [base, hi]

theorem velocity_anchor (x : BoundaryClusterFreeCoordinates i a S m) (ha : a ∈ S) :
    x.velocity a = Complex.I := by simp [velocity, ha]

theorem velocity_zero_off (x : BoundaryClusterFreeCoordinates i a S m) (j : Fin n) (hj : j ∉ S) :
    x.velocity j = 0 := by simp [velocity, hj]

theorem boundaryBase_eq_center (x : BoundaryClusterFreeCoordinates i a S m) (l u : Fin (m + 1))
    (j : Fin m) (hj : j ∈ boundaryClusterBlock l u) : x.boundaryBase l u j = x.center := by
  simp [boundaryBase, hj]

theorem boundaryVelocity_zero_off (x : BoundaryClusterFreeCoordinates i a S m) (l u : Fin (m + 1))
    (j : Fin m) (hj : j ∉ boundaryClusterBlock l u) : x.boundaryVelocity l u j = 0 := by
  simp [boundaryVelocity, hj]

@[simp] theorem base_coarse (x : BoundaryClusterFreeCoordinates i a S m)
    (j : BoundaryClusterCoarseIndex i S) : x.base j.val = x.1 j := by
  simp only [base, dif_neg j.property.1, dif_neg j.property.2]
  exact congrArg x.1 (Subtype.ext rfl)

@[simp] theorem velocity_shape (x : BoundaryClusterFreeCoordinates i a S m)
    (j : BoundaryClusterShapeIndex a S) : x.velocity j.val = x.2.1 j := by
  simp only [velocity, dif_pos j.property.1, dif_neg j.property.2]
  exact congrArg x.2.1 (Subtype.ext rfl)

theorem closed_conditions (x : BoundaryClusterFreeCoordinates i a S m) (l u : Fin (m + 1))
    (ha : a ∈ S) (hi : i ∉ S) :
    BoundaryClusterData.closedCoordinateConditions i a S l u (x.parameters l u) :=
  ⟨x.base_eq_center, x.base_normalized hi, x.velocity_zero_off, x.velocity_anchor ha,
    x.boundaryBase_eq_center l u, x.boundaryVelocity_zero_off l u⟩

def ScaleConditions (l u : Fin (m + 1)) (x : BoundaryClusterFreeCoordinates i a S m) : Prop :=
  (∀ j k, ¬(j = k ∨ (j ∈ S ∧ k ∈ S)) →
    x.radius * ‖x.velocity j - x.velocity k‖ < ‖x.base j - x.base k‖) ∧
  (∀ j k, j < k → ¬(j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u) →
    x.radius * |x.boundaryVelocity l u k - x.boundaryVelocity l u j| <
      x.boundaryBase l u k - x.boundaryBase l u j)

theorem isOpen_scaleConditions (l u : Fin (m + 1)) :
    IsOpen {x : BoundaryClusterFreeCoordinates i a S m | x.ScaleConditions l u} := by
  simp only [ScaleConditions, Set.setOf_and, Set.setOf_forall]
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro k
    apply isOpen_iInter_of_finite
    intro h
    exact isOpen_lt (by fun_prop) (by fun_prop)
  · apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro k
    apply isOpen_iInter_of_finite
    intro h
    apply isOpen_iInter_of_finite
    intro hblock
    exact isOpen_lt (by fun_prop) (by fun_prop)

/-- All nonradial restrictions are actual strict geometric inequalities. -/
def OpenConditions (l u : Fin (m + 1)) (x : BoundaryClusterFreeCoordinates i a S m) : Prop :=
  BoundaryClusterData.openCoordinateConditions i a S l u (x.parameters l u) ∧ x.ScaleConditions l u

theorem isOpen_openConditions (l u : Fin (m + 1)) :
    IsOpen {x : BoundaryClusterFreeCoordinates i a S m | x.OpenConditions l u} :=
  (BoundaryClusterData.isOpen_openCoordinateConditions.preimage (continuous_parameters l u)).inter
    (isOpen_scaleConditions l u)

/-- Every open admissible free coordinate array gives genuine geometric data. -/
theorem exists_datum (x : BoundaryClusterFreeCoordinates i a S m) (l u : Fin (m + 1))
    (hx : x.OpenConditions l u) :
    ∃ D : BoundaryClusterData i a m S l u, D.coordinates = x.parameters l u := by
  change x.parameters l u ∈ Set.range BoundaryClusterData.coordinates
  rw [BoundaryClusterData.range_coordinates]
  exact ⟨hx.1, x.closed_conditions l u hx.1.1 hx.1.2.1⟩

end BoundaryClusterFreeCoordinates

def BoundaryClusterFreeDomain {n : ℕ} (i a : Fin n) (S : Finset (Fin n)) (m : ℕ)
    (l u : Fin (m + 1)) :=
  {x : BoundaryClusterFreeCoordinates i a S m // 0 ≤ x.radius ∧ x.OpenConditions l u}

namespace BoundaryClusterFreeDomain

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

instance : TopologicalSpace (BoundaryClusterFreeDomain i a S m l u) :=
  inferInstanceAs (TopologicalSpace {x : BoundaryClusterFreeCoordinates i a S m //
    0 ≤ x.radius ∧ x.OpenConditions l u})

end BoundaryClusterFreeDomain

end EnvelopingIsomorphism.Deformation.Kontsevich
