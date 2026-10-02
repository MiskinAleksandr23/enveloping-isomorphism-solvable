import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterEmbedding
import Mathlib.Topology.Compactness.LocallyCompact

/-!
Local compactness of the actual normalized interior-cluster parameter slice.
Single-cluster coordinates form a locally closed subset of a finite product of
complex and real spaces. Admissible scales form a locally closed subspace, and
normalizing the two reference velocities imposes closed conditions.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Topology Set
open scoped UpperHalfPlane

abbrev InteriorClusterParameterSpace (n m : ℕ) :=
  (Fin n → ℂ) × (Fin n → ℂ) × (Fin m → ℝ)

/-- The prescribed base-equality relation, independent of all coordinates. -/
def sameInteriorClusterBase {n : ℕ} (S : Finset (Fin n)) (j l : Fin n) : Prop :=
  j = l ∨ (j ∈ S ∧ l ∈ S)

namespace SingleInteriorCluster

variable {n m : ℕ} {i : Fin n} {S : Finset (Fin n)}

/-- The actual finite coordinate embedding of the primitive cluster data. -/
def parameterCoordinates (D : SingleInteriorCluster i m S) : InteriorClusterParameterSpace n m :=
  D.toInteriorCollisionData.coordinates

theorem isEmbedding_parameterCoordinates :
    IsEmbedding (parameterCoordinates : SingleInteriorCluster i m S → InteriorClusterParameterSpace n m) :=
  InteriorCollisionData.isEmbedding_coordinates.comp isEmbedding_toInteriorCollisionData

def closedCoordinateConditions (i : Fin n) (S : Finset (Fin n))
    (x : InteriorClusterParameterSpace n m) : Prop :=
  x.1 i = Complex.I ∧ x.2.1 i = 0 ∧
    (∀ j l, sameInteriorClusterBase S j l → x.1 j = x.1 l) ∧
    (∀ j, j ∉ S → x.2.1 j = 0)

def openCoordinateConditions (S : Finset (Fin n))
    (x : InteriorClusterParameterSpace n m) : Prop :=
  S.Nonempty ∧ (∀ j, 0 < (x.1 j).im) ∧
    (∀ j l, ¬sameInteriorClusterBase S j l → x.1 j ≠ x.1 l) ∧
    (∀ j l, j ≠ l → sameInteriorClusterBase S j l → x.2.1 j ≠ x.2.1 l) ∧
    StrictMono x.2.2

/-- Every coordinate point satisfying the displayed conditions reconstructs
an actual cluster datum; the image description is an equality, not a containment. -/
theorem range_parameterCoordinates :
    Set.range (parameterCoordinates : SingleInteriorCluster i m S → InteriorClusterParameterSpace n m) =
      {x | openCoordinateConditions S x} ∩ {x | closedCoordinateConditions i S x} := by
  ext x
  constructor
  · rintro ⟨D, rfl⟩
    refine ⟨⟨D.cluster_nonempty, fun j => (D.base j).im_pos, ?_, ?_, D.boundary_strictMono⟩,
      ?_⟩
    · intro j l hmask hbase
      exact hmask ((D.base_eq_iff j l).mp (UpperHalfPlane.ext hbase))
    · intro j l hne hmask hvel
      exact hne (D.separated j l ((D.base_eq_iff j l).mpr hmask) hvel)
    · refine ⟨?_, D.velocity_normalized, ?_, D.velocity_zero_off⟩
      · exact congrArg (fun z : ℍ => (z : ℂ)) D.base_normalized
      · intro j l hmask
        exact congrArg (fun z : ℍ => (z : ℂ)) ((D.base_eq_iff j l).mpr hmask)
  · rintro ⟨⟨hS, hpos, hsep, hvel, hboundary⟩, hnorm, hzero, heq, hoff⟩
    have hbaseiff (j l : Fin n) : x.1 j = x.1 l ↔ sameInteriorClusterBase S j l := by
      constructor
      · intro h
        by_contra hmask
        exact hsep j l hmask h
      · exact heq j l
    let D : SingleInteriorCluster i m S :=
      { base := fun j => ⟨x.1 j, hpos j⟩
        velocity := x.2.1
        boundary := x.2.2
        separated := by
          intro j l hbase hvelocity
          by_contra hne
          exact hvel j l hne ((hbaseiff j l).mp (congrArg (fun z : ℍ => (z : ℂ)) hbase))
            hvelocity
        boundary_strictMono := hboundary
        base_normalized := UpperHalfPlane.ext hnorm
        velocity_normalized := hzero
        cluster_nonempty := hS
        base_eq_iff := by
          intro j l
          exact ⟨fun h => (hbaseiff j l).mp (congrArg (fun z : ℍ => (z : ℂ)) h),
            fun h => UpperHalfPlane.ext ((hbaseiff j l).mpr h)⟩
        velocity_zero_off := hoff }
    exact ⟨D, rfl⟩

private theorem continuous_baseCoordinate (j : Fin n) :
    Continuous (fun x : InteriorClusterParameterSpace n m => x.1 j) :=
  (continuous_apply j).comp continuous_fst

private theorem continuous_velocityCoordinate (j : Fin n) :
    Continuous (fun x : InteriorClusterParameterSpace n m => x.2.1 j) :=
  (continuous_apply j).comp (continuous_fst.comp continuous_snd)

private theorem continuous_boundaryCoordinate (j : Fin m) :
    Continuous (fun x : InteriorClusterParameterSpace n m => x.2.2 j) :=
  (continuous_apply j).comp (continuous_snd.comp continuous_snd)

theorem isClosed_closedCoordinateConditions :
    IsClosed {x : InteriorClusterParameterSpace n m | closedCoordinateConditions i S x} := by
  classical
  have heq : IsClosed {x : InteriorClusterParameterSpace n m |
      ∀ j l, sameInteriorClusterBase S j l → x.1 j = x.1 l} := by
    rw [setOf_forall]
    apply isClosed_iInter
    intro j
    rw [setOf_forall]
    apply isClosed_iInter
    intro l
    by_cases hmask : sameInteriorClusterBase S j l
    · simpa only [hmask, true_implies] using
        isClosed_eq (continuous_baseCoordinate j) (continuous_baseCoordinate l)
    · simp [hmask]
  have hoff : IsClosed {x : InteriorClusterParameterSpace n m | ∀ j, j ∉ S → x.2.1 j = 0} := by
    rw [setOf_forall]
    apply isClosed_iInter
    intro j
    by_cases hj : j ∉ S
    · simpa only [hj, not_false_eq_true, true_implies] using
        isClosed_eq (continuous_velocityCoordinate j)
          (show Continuous (fun _ : InteriorClusterParameterSpace n m => (0 : ℂ)) from continuous_const)
    · simp [hj]
  exact (isClosed_eq (continuous_baseCoordinate i) continuous_const).inter
    ((isClosed_eq (continuous_velocityCoordinate i) continuous_const).inter (heq.inter hoff))

theorem isOpen_openCoordinateConditions :
    IsOpen {x : InteriorClusterParameterSpace n m | openCoordinateConditions S x} := by
  classical
  have hS : IsOpen {x : InteriorClusterParameterSpace n m | S.Nonempty} := by
    by_cases h : S.Nonempty <;> simp [h]
  have hpos : IsOpen {x : InteriorClusterParameterSpace n m | ∀ j, 0 < (x.1 j).im} := by
    rw [setOf_forall]
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_baseCoordinate j))
  have hsep : IsOpen {x : InteriorClusterParameterSpace n m |
      ∀ j l, ¬sameInteriorClusterBase S j l → x.1 j ≠ x.1 l} := by
    rw [setOf_forall]
    apply isOpen_iInter_of_finite
    intro j
    rw [setOf_forall]
    apply isOpen_iInter_of_finite
    intro l
    by_cases hmask : sameInteriorClusterBase S j l
    · simp [hmask]
    · simpa [hmask, Set.compl_setOf] using
        (isClosed_eq (continuous_baseCoordinate j) (continuous_baseCoordinate l)).isOpen_compl
  have hvel : IsOpen {x : InteriorClusterParameterSpace n m |
      ∀ j l, j ≠ l → sameInteriorClusterBase S j l → x.2.1 j ≠ x.2.1 l} := by
    rw [setOf_forall]
    apply isOpen_iInter_of_finite
    intro j
    rw [setOf_forall]
    apply isOpen_iInter_of_finite
    intro l
    by_cases hne : j ≠ l
    · by_cases hmask : sameInteriorClusterBase S j l
      · simpa [hne, hmask, Set.compl_setOf] using
          (isClosed_eq (continuous_velocityCoordinate j) (continuous_velocityCoordinate l)).isOpen_compl
      · simp [hmask]
    · simp [hne]
  have hboundary : IsOpen {x : InteriorClusterParameterSpace n m | StrictMono x.2.2} := by
    change IsOpen {x : InteriorClusterParameterSpace n m | ∀ j l, j < l → x.2.2 j < x.2.2 l}
    rw [setOf_forall]
    apply isOpen_iInter_of_finite
    intro j
    rw [setOf_forall]
    apply isOpen_iInter_of_finite
    intro l
    by_cases hjl : j < l
    · simpa only [hjl, true_implies] using
        isOpen_lt (continuous_boundaryCoordinate j) (continuous_boundaryCoordinate l)
    · simp [hjl]
  exact hS.inter (hpos.inter (hsep.inter (hvel.inter hboundary)))

theorem isLocallyClosed_range_parameterCoordinates :
    IsLocallyClosed (Set.range (parameterCoordinates :
      SingleInteriorCluster i m S → InteriorClusterParameterSpace n m)) := by
  rw [range_parameterCoordinates]
  exact ⟨_, _, isOpen_openCoordinateConditions, isClosed_closedCoordinateConditions, rfl⟩

instance : LocallyCompactSpace (SingleInteriorCluster i m S) :=
  isEmbedding_parameterCoordinates.isInducing.locallyCompactSpace
    isLocallyClosed_range_parameterCoordinates

end SingleInteriorCluster

namespace InteriorClusterDomain

variable {n m : ℕ} {i : Fin n} {S : Finset (Fin n)}

/-- All strict scale inequalities, using the fixed base-equality pattern. -/
def openScaleConditions (x : SingleInteriorCluster i m S × ℝ) : Prop :=
  (∀ j, x.2 * ‖x.1.velocity j‖ < (x.1.base j).im) ∧
    (∀ j l, ¬sameInteriorClusterBase S j l →
      x.2 * ‖x.1.velocity j - x.1.velocity l‖ < ‖(x.1.base j : ℂ) - (x.1.base l : ℂ)‖)

theorem admissibleScale_iff_openScaleConditions (x : SingleInteriorCluster i m S × ℝ) :
    x.1.toInteriorCollisionData.AdmissibleScale x.2 ↔ 0 ≤ x.2 ∧ openScaleConditions x := by
  constructor
  · intro hx
    refine ⟨hx.nonneg, hx.height, fun j l hmask => ?_⟩
    exact hx.separation j l (fun h => hmask ((x.1.base_eq_iff j l).mp h))
  · rintro ⟨hnonneg, hheight, hsep⟩
    refine ⟨hnonneg, hheight, fun j l hne => ?_⟩
    exact hsep j l (fun hmask => hne ((x.1.base_eq_iff j l).mpr hmask))

theorem isOpen_openScaleConditions :
    IsOpen {x : SingleInteriorCluster i m S × ℝ | openScaleConditions x} := by
  classical
  have hvel (j : Fin n) : Continuous (fun x : SingleInteriorCluster i m S × ℝ => x.1.velocity j) :=
    (SingleInteriorCluster.continuous_velocity_apply j).comp continuous_fst
  have hbase (j : Fin n) : Continuous (fun x : SingleInteriorCluster i m S × ℝ => (x.1.base j : ℂ)) :=
    (SingleInteriorCluster.continuous_base j).comp continuous_fst
  have hheight : IsOpen {x : SingleInteriorCluster i m S × ℝ |
      ∀ j, x.2 * ‖x.1.velocity j‖ < (x.1.base j).im} := by
    rw [setOf_forall]
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_lt (continuous_snd.mul (hvel j).norm) (Complex.continuous_im.comp (hbase j))
  have hsep : IsOpen {x : SingleInteriorCluster i m S × ℝ |
      ∀ j l, ¬sameInteriorClusterBase S j l →
        x.2 * ‖x.1.velocity j - x.1.velocity l‖ < ‖(x.1.base j : ℂ) - (x.1.base l : ℂ)‖} := by
    rw [setOf_forall]
    apply isOpen_iInter_of_finite
    intro j
    rw [setOf_forall]
    apply isOpen_iInter_of_finite
    intro l
    by_cases hmask : sameInteriorClusterBase S j l
    · simp [hmask]
    · simpa only [hmask, not_false_eq_true, true_implies, Pi.mul_apply, Pi.sub_apply] using
        isOpen_lt (continuous_snd.mul ((hvel j).sub (hvel l)).norm) ((hbase j).sub (hbase l)).norm
  exact hheight.inter hsep

/-- The actual admissible scale domain is locally closed in the data-scale product. -/
theorem isLocallyClosed_admissibleScale :
    IsLocallyClosed {x : SingleInteriorCluster i m S × ℝ |
      x.1.toInteriorCollisionData.AdmissibleScale x.2} := by
  refine ⟨{x | openScaleConditions x}, {x | 0 ≤ x.2}, isOpen_openScaleConditions,
    isClosed_le continuous_const continuous_snd, ?_⟩
  ext x
  simp only [mem_setOf_eq, mem_inter_iff, admissibleScale_iff_openScaleConditions, and_comm]

instance : LocallyCompactSpace (InteriorClusterDomain i m S) := by
  change LocallyCompactSpace {x : SingleInteriorCluster i m S × ℝ |
    x.1.toInteriorCollisionData.AdmissibleScale x.2}
  exact isLocallyClosed_admissibleScale.locallyCompactSpace

end InteriorClusterDomain

namespace NormalizedInteriorClusterSlice

variable {n m : ℕ} {i : Fin n} {S : Finset (Fin n)} {a b : Fin n}

/-- Translation and length normalization are closed conditions on the actual domain. -/
theorem isClosed_normalization :
    IsClosed {x : InteriorClusterDomain i m S | x.datum.velocity a = 0 ∧ ‖x.datum.velocity b‖ = 1} := by
  have ha : Continuous (fun x : InteriorClusterDomain i m S => x.datum.velocity a) :=
    (SingleInteriorCluster.continuous_velocity_apply a).comp InteriorClusterDomain.continuous_datum
  have hb : Continuous (fun x : InteriorClusterDomain i m S => x.datum.velocity b) :=
    (SingleInteriorCluster.continuous_velocity_apply b).comp InteriorClusterDomain.continuous_datum
  exact (isClosed_eq ha continuous_const).inter (isClosed_eq hb.norm continuous_const)

/-- Local compactness is proved from the primitive coordinates and inequalities. -/
instance : LocallyCompactSpace (NormalizedInteriorClusterSlice i m S a b) := by
  change LocallyCompactSpace {x : InteriorClusterDomain i m S |
    x.datum.velocity a = 0 ∧ ‖x.datum.velocity b‖ = 1}
  exact isClosed_normalization.locallyCompactSpace

end NormalizedInteriorClusterSlice

end EnvelopingIsomorphism.Deformation.Kontsevich
