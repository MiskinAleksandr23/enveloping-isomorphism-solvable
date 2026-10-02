import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterCoordinateIndices
import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterLocalCompact
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
Actual free coordinates for a pure boundary cluster. The normalized interior
point is fixed at I; the endpoint boundary shape coordinates are fixed at 0
and 1. Every other boundary slot is its shape coordinate inside the block and
its stationary coarse position outside the block.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration Topology

abbrev PureBoundaryClusterFreeCoordinates {n : ℕ} (i : Fin n) (m : ℕ) (a b : Fin m) :=
  (PureBoundaryInteriorIndex i → ℂ) × (PureBoundaryFreeIndex a b → ℝ) × ℝ × ℝ

namespace PureBoundaryClusterFreeCoordinates

variable {n m : ℕ} {i : Fin n} {a b : Fin m}

def center (x : PureBoundaryClusterFreeCoordinates i m a b) : ℝ := x.2.2.1

def radius (x : PureBoundaryClusterFreeCoordinates i m a b) : ℝ := x.2.2.2

def interior (x : PureBoundaryClusterFreeCoordinates i m a b) (j : Fin n) : ℂ :=
  if hj : j = i then Complex.I else x.1 ⟨j, hj⟩

/-- The two removed slots are genuinely fixed, rather than imposed as equations. -/
def boundaryCoordinate (x : PureBoundaryClusterFreeCoordinates i m a b) (j : Fin m) : ℝ :=
  if hja : j = a then 0 else if hjb : j = b then 1 else x.2.1 ⟨j, hja, hjb⟩

def boundaryBase (l u : Fin (m + 1)) (x : PureBoundaryClusterFreeCoordinates i m a b) (j : Fin m) : ℝ :=
  if j ∈ boundaryClusterBlock l u then x.center else x.boundaryCoordinate j

def boundaryVelocity (l u : Fin (m + 1)) (x : PureBoundaryClusterFreeCoordinates i m a b) (j : Fin m) : ℝ :=
  if j ∈ boundaryClusterBlock l u then x.boundaryCoordinate j else 0

def parameters (l u : Fin (m + 1)) (x : PureBoundaryClusterFreeCoordinates i m a b) :
    PureBoundaryClusterParameterSpace n m :=
  (x.center, x.interior, x.boundaryBase l u, x.boundaryVelocity l u)

@[fun_prop] theorem contDiff_center : ContDiff ℝ ⊤ (center : PureBoundaryClusterFreeCoordinates i m a b → ℝ) := by
  unfold center
  fun_prop

@[fun_prop] theorem contDiff_radius : ContDiff ℝ ⊤ (radius : PureBoundaryClusterFreeCoordinates i m a b → ℝ) := by
  unfold radius
  fun_prop

@[fun_prop] theorem contDiff_interior (j : Fin n) :
    ContDiff ℝ ⊤ (fun x : PureBoundaryClusterFreeCoordinates i m a b => x.interior j) := by
  unfold interior
  split_ifs <;> fun_prop

@[fun_prop] theorem contDiff_boundaryCoordinate (j : Fin m) :
    ContDiff ℝ ⊤ (fun x : PureBoundaryClusterFreeCoordinates i m a b => x.boundaryCoordinate j) := by
  unfold boundaryCoordinate
  split_ifs <;> fun_prop

@[fun_prop] theorem contDiff_boundaryBase (l u : Fin (m + 1)) (j : Fin m) :
    ContDiff ℝ ⊤ (fun x : PureBoundaryClusterFreeCoordinates i m a b => x.boundaryBase l u j) := by
  unfold boundaryBase
  split_ifs <;> fun_prop

@[fun_prop] theorem contDiff_boundaryVelocity (l u : Fin (m + 1)) (j : Fin m) :
    ContDiff ℝ ⊤ (fun x : PureBoundaryClusterFreeCoordinates i m a b => x.boundaryVelocity l u j) := by
  unfold boundaryVelocity
  split_ifs <;> fun_prop

@[fun_prop] theorem contDiff_parameters (l u : Fin (m + 1)) :
    ContDiff ℝ ⊤ (parameters (i := i) (a := a) (b := b) l u) := by
  unfold parameters
  exact contDiff_center.prodMk ((contDiff_pi.mpr contDiff_interior).prodMk
    ((contDiff_pi.mpr (contDiff_boundaryBase l u)).prodMk
      (contDiff_pi.mpr (contDiff_boundaryVelocity l u))))

@[fun_prop] theorem continuous_center : Continuous (center : PureBoundaryClusterFreeCoordinates i m a b → ℝ) :=
  contDiff_center.continuous

@[fun_prop] theorem continuous_radius : Continuous (radius : PureBoundaryClusterFreeCoordinates i m a b → ℝ) :=
  contDiff_radius.continuous

@[fun_prop] theorem continuous_interior (j : Fin n) :
    Continuous (fun x : PureBoundaryClusterFreeCoordinates i m a b => x.interior j) :=
  (contDiff_interior j).continuous

@[fun_prop] theorem continuous_boundaryBase (l u : Fin (m + 1)) (j : Fin m) :
    Continuous (fun x : PureBoundaryClusterFreeCoordinates i m a b => x.boundaryBase l u j) :=
  (contDiff_boundaryBase l u j).continuous

@[fun_prop] theorem continuous_boundaryVelocity (l u : Fin (m + 1)) (j : Fin m) :
    Continuous (fun x : PureBoundaryClusterFreeCoordinates i m a b => x.boundaryVelocity l u j) :=
  (contDiff_boundaryVelocity l u j).continuous

@[fun_prop] theorem continuous_parameters (l u : Fin (m + 1)) :
    Continuous (parameters (i := i) (a := a) (b := b) l u) := (contDiff_parameters l u).continuous

@[simp] theorem interior_normalized (x : PureBoundaryClusterFreeCoordinates i m a b) :
    x.interior i = Complex.I := by simp [interior]

@[simp] theorem interior_free (x : PureBoundaryClusterFreeCoordinates i m a b)
    (j : PureBoundaryInteriorIndex i) : x.interior j = x.1 j := by
  simp only [interior, dif_neg j.property]

@[simp] theorem boundaryCoordinate_free (x : PureBoundaryClusterFreeCoordinates i m a b)
    (j : PureBoundaryFreeIndex a b) : x.boundaryCoordinate j = x.2.1 j := by
  simp only [boundaryCoordinate, dif_neg j.property.1, dif_neg j.property.2]

@[simp] theorem boundaryCoordinate_left (x : PureBoundaryClusterFreeCoordinates i m a b) :
    x.boundaryCoordinate a = 0 := by simp [boundaryCoordinate]

@[simp] theorem boundaryCoordinate_right (x : PureBoundaryClusterFreeCoordinates i m a b)
    (hab : a ≠ b) : x.boundaryCoordinate b = 1 := by simp [boundaryCoordinate, hab.symm]

theorem closed_conditions (x : PureBoundaryClusterFreeCoordinates i m a b) (l u : Fin (m + 1))
    (hl : a.val = l.val) (hu : b.val + 1 = u.val) (hab : a < b) :
    PureBoundaryClusterData.closedCoordinateConditions i l u a b (x.parameters l u) := by
  have hb : b ∈ boundaryClusterBlock l u := by
    rw [mem_boundaryClusterBlock]
    constructor <;> omega
  refine ⟨x.interior_normalized, ?_, ?_, ?_, ?_⟩
  · intro j hj
    simp [parameters, boundaryBase, hj]
  · intro j hj
    simp [parameters, boundaryVelocity, hj]
  · change x.boundaryVelocity l u a = 0
    by_cases ha : a ∈ boundaryClusterBlock l u <;> simp [boundaryVelocity, ha]
  · change x.boundaryVelocity l u b = 1
    simp [boundaryVelocity, hb, x.boundaryCoordinate_right hab.ne]

/-- Strict scale inequalities have no variable equality test in their domain. -/
def ScaleConditions (l u : Fin (m + 1)) (x : PureBoundaryClusterFreeCoordinates i m a b) : Prop :=
  ∀ j k, j < k → ¬(j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u) →
    x.radius * |x.boundaryVelocity l u k - x.boundaryVelocity l u j| <
      x.boundaryBase l u k - x.boundaryBase l u j

def OpenConditions (l u : Fin (m + 1)) (x : PureBoundaryClusterFreeCoordinates i m a b) : Prop :=
  PureBoundaryClusterData.openCoordinateConditions l u a b (x.parameters l u) ∧ x.ScaleConditions l u

theorem isOpen_scaleConditions (l u : Fin (m + 1)) :
    IsOpen {x : PureBoundaryClusterFreeCoordinates i m a b | x.ScaleConditions l u} := by
  simp only [ScaleConditions, Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro k
  apply isOpen_iInter_of_finite
  intro hjk
  apply isOpen_iInter_of_finite
  intro hblock
  exact isOpen_lt (by fun_prop) (by fun_prop)

theorem isOpen_openConditions (l u : Fin (m + 1)) :
    IsOpen {x : PureBoundaryClusterFreeCoordinates i m a b | x.OpenConditions l u} :=
  (PureBoundaryClusterData.isOpen_openCoordinateConditions.preimage (continuous_parameters l u)).inter
    (isOpen_scaleConditions l u)

/-- A free point satisfying the open inequalities gives native primitive data. -/
def toDatum (x : PureBoundaryClusterFreeCoordinates i m a b) (l u : Fin (m + 1))
    (hx : x.OpenConditions l u) : PureBoundaryClusterData i m l u a b :=
  PureBoundaryClusterData.ofCoordinates (x.parameters l u) hx.1
    (x.closed_conditions l u hx.1.1 hx.1.2.1 hx.1.2.2.1)

@[simp] theorem toDatum_parameters (x : PureBoundaryClusterFreeCoordinates i m a b)
    (l u : Fin (m + 1)) (hx : x.OpenConditions l u) :
    (x.toDatum l u hx).coordinates = x.parameters l u :=
  PureBoundaryClusterData.coordinates_ofCoordinates _ _ _

/-- The actual scaled real boundary position. -/
def scaledBoundary (l u : Fin (m + 1)) (x : PureBoundaryClusterFreeCoordinates i m a b) (j : Fin m) : ℝ :=
  x.boundaryBase l u j + x.radius * x.boundaryVelocity l u j

@[fun_prop] theorem contDiff_scaledBoundary (l u : Fin (m + 1)) (j : Fin m) :
    ContDiff ℝ ⊤ (fun x : PureBoundaryClusterFreeCoordinates i m a b => x.scaledBoundary l u j) :=
  (contDiff_boundaryBase l u j).add (contDiff_radius.mul (contDiff_boundaryVelocity l u j))

/-- All original position coordinates, with the interior normalization already built in. -/
def scaledCoordinates (l u : Fin (m + 1)) (x : PureBoundaryClusterFreeCoordinates i m a b) :
    (Fin n → ℂ) × (Fin m → ℝ) := (x.interior, x.scaledBoundary l u)

@[fun_prop] theorem contDiff_scaledCoordinates (l u : Fin (m + 1)) :
    ContDiff ℝ ⊤ (scaledCoordinates (i := i) (a := a) (b := b) l u) :=
  (contDiff_pi.mpr contDiff_interior).prodMk (contDiff_pi.mpr (contDiff_scaledBoundary l u))

end PureBoundaryClusterFreeCoordinates

def PureBoundaryClusterFreeDomain {n : ℕ} (i : Fin n) (m : ℕ)
    (l u : Fin (m + 1)) (a b : Fin m) :=
  {x : PureBoundaryClusterFreeCoordinates i m a b // 0 ≤ x.radius ∧ x.OpenConditions l u}

namespace PureBoundaryClusterFreeDomain

variable {n m : ℕ} {i : Fin n} {l u : Fin (m + 1)} {a b : Fin m}

instance : TopologicalSpace (PureBoundaryClusterFreeDomain i m l u a b) :=
  inferInstanceAs (TopologicalSpace {x : PureBoundaryClusterFreeCoordinates i m a b //
    0 ≤ x.radius ∧ x.OpenConditions l u})

end PureBoundaryClusterFreeDomain

end EnvelopingIsomorphism.Deformation.Kontsevich
