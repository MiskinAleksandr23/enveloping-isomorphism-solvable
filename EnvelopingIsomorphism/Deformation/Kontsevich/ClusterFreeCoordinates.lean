import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterCoordinateIndices
import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterLocalCompact
import EnvelopingIsomorphism.Deformation.Kontsevich.CircleAngleForm

/-!
# Free coarse, shape, circle, boundary, and radial coordinates for a cluster

The first marked velocity is zero, the second is a unit complex direction.
Every other cluster velocity and every non-normalized coarse representative is
a free complex coordinate. Boundary positions and the radius are real.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration Topology

abbrev ClusterFreeCoordinates {n : ℕ} (i a b : Fin n) (S : Finset (Fin n)) (m : ℕ) :=
  (ClusterCoarseIndex i a S → ℂ) × (ClusterShapeIndex a b S → ℂ) ×
    (Fin m → ℝ) × Circle × ℝ

namespace ClusterFreeCoordinates

variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

def representative (S : Finset (Fin n)) (a j : Fin n) : Fin n := if j ∈ S then a else j

theorem representative_mem (S : Finset (Fin n)) (a j : Fin n) :
    representative S a j = a ∨ representative S a j ∉ S := by
  by_cases hj : j ∈ S <;> simp [representative, hj]

def base (x : ClusterFreeCoordinates i a b S m) (j : Fin n) : ℂ :=
  if h : representative S a j = i then Complex.I
  else x.1 ⟨representative S a j, representative_mem S a j, h⟩

def velocity (x : ClusterFreeCoordinates i a b S m) (j : Fin n) : ℂ :=
  if hja : j = a then 0 else if hjb : j = b then (x.2.2.2.1 : ℂ)
  else if hj : j ∈ S then x.2.1 ⟨j, hj, hja, hjb⟩ else 0

def parameters (x : ClusterFreeCoordinates i a b S m) : InteriorClusterParameterSpace n m :=
  (x.base, x.velocity, x.2.2.1)

def radius (x : ClusterFreeCoordinates i a b S m) : ℝ := x.2.2.2.2

@[fun_prop] theorem continuous_base (j : Fin n) :
    Continuous (fun x : ClusterFreeCoordinates i a b S m => x.base j) := by
  unfold base
  split_ifs <;> fun_prop

@[fun_prop] theorem continuous_velocity (j : Fin n) :
    Continuous (fun x : ClusterFreeCoordinates i a b S m => x.velocity j) := by
  unfold velocity
  split_ifs <;> fun_prop

@[fun_prop] theorem continuous_parameters :
    Continuous (parameters : ClusterFreeCoordinates i a b S m → _) := by
  exact (continuous_pi continuous_base).prodMk
    ((continuous_pi continuous_velocity).prodMk (by fun_prop))

@[fun_prop] theorem continuous_radius : Continuous (radius : ClusterFreeCoordinates i a b S m → ℝ) := by
  unfold radius
  fun_prop

theorem base_normalized (x : ClusterFreeCoordinates i a b S m) (hanchor : i ∈ S → a = i) :
    x.base i = Complex.I := by
  by_cases hi : i ∈ S
  · simp [base, representative, hi, hanchor hi]
  · simp [base, representative, hi]

theorem base_eq_of_same (x : ClusterFreeCoordinates i a b S m) {j k : Fin n}
    (h : sameInteriorClusterBase S j k) : x.base j = x.base k := by
  rcases h with rfl | ⟨hj, hk⟩
  · rfl
  · simp only [base, representative, if_pos hj, if_pos hk]

@[simp] theorem velocity_anchor (x : ClusterFreeCoordinates i a b S m) : x.velocity a = 0 := by
  simp [velocity]

theorem velocity_reference (x : ClusterFreeCoordinates i a b S m) (hba : b ≠ a) :
    x.velocity b = (x.2.2.2.1 : ℂ) := by
  simp [velocity, hba]

theorem velocity_zero_off (x : ClusterFreeCoordinates i a b S m) (ha : a ∈ S) (hb : b ∈ S)
    (j : Fin n) (hj : j ∉ S) : x.velocity j = 0 := by
  have hja : j ≠ a := fun h => hj (h ▸ ha)
  have hjb : j ≠ b := fun h => hj (h ▸ hb)
  simp [velocity, hja, hjb, hj]

theorem velocity_normalized (x : ClusterFreeCoordinates i a b S m) (ha : a ∈ S) (hb : b ∈ S)
    (hanchor : i ∈ S → a = i) : x.velocity i = 0 := by
  by_cases hi : i ∈ S
  · exact (congrArg x.velocity (hanchor hi)).symm.trans x.velocity_anchor
  · exact x.velocity_zero_off ha hb i hi

theorem closed_conditions (x : ClusterFreeCoordinates i a b S m)
    (ha : a ∈ S) (hb : b ∈ S) (hanchor : i ∈ S → a = i) :
    SingleInteriorCluster.closedCoordinateConditions i S x.parameters :=
  ⟨x.base_normalized hanchor, x.velocity_normalized ha hb hanchor,
    fun _ _ h => x.base_eq_of_same h, x.velocity_zero_off ha hb⟩

/-- All strict inequalities are imposed openly in the free product coordinates. -/
def OpenConditions (x : ClusterFreeCoordinates i a b S m) : Prop :=
  SingleInteriorCluster.openCoordinateConditions S x.parameters ∧
    (∀ j, x.radius * ‖x.velocity j‖ < (x.base j).im) ∧
    (∀ j k, ¬sameInteriorClusterBase S j k →
      x.radius * ‖x.velocity j - x.velocity k‖ < ‖x.base j - x.base k‖)

theorem isOpen_openConditions :
    IsOpen {x : ClusterFreeCoordinates i a b S m | x.OpenConditions} := by
  apply IsOpen.inter (SingleInteriorCluster.isOpen_openCoordinateConditions.preimage continuous_parameters)
  apply IsOpen.inter
  · have hopen : IsOpen (⋂ j : Fin n, {x : ClusterFreeCoordinates i a b S m |
        x.radius * ‖x.velocity j‖ < (x.base j).im}) := by
      apply isOpen_iInter_of_finite
      intro j
      exact isOpen_lt (continuous_radius.mul (continuous_velocity j).norm)
        (Complex.continuous_im.comp (continuous_base j))
    convert! hopen using 1
    ext x
    simp
    rfl
  · have hopen : IsOpen (⋂ (j : Fin n) (k : Fin n), {x : ClusterFreeCoordinates i a b S m |
        ¬sameInteriorClusterBase S j k → x.radius * ‖x.velocity j - x.velocity k‖ < ‖x.base j - x.base k‖}) := by
      apply isOpen_iInter_of_finite
      intro j
      apply isOpen_iInter_of_finite
      intro k
      by_cases h : sameInteriorClusterBase S j k
      · simp [h]
      · simpa only [h, not_false_eq_true, true_implies, Pi.mul_apply, Pi.sub_apply] using
          isOpen_lt (continuous_radius.mul ((continuous_velocity j).sub (continuous_velocity k)).norm)
            ((continuous_base j).sub (continuous_base k)).norm
    convert! hopen using 1
    ext x
    simp
    rfl

end ClusterFreeCoordinates

end EnvelopingIsomorphism.Deformation.Kontsevich
