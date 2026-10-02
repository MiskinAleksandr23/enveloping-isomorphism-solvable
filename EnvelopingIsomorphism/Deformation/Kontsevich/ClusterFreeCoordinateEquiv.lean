import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterFreeCoordinates

/-!
# The exact free-coordinate homeomorphism for a normalized interior cluster

The free parameters satisfy the explicit open geometric conditions and a
nonnegative radius. They reconstruct the actual cluster datum, and restriction
to the free labels recovers the parameters continuously in both directions.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration Topology

def ClusterFreeDomain {n : ℕ} (i a b : Fin n) (S : Finset (Fin n)) (m : ℕ) :=
  {x : ClusterFreeCoordinates i a b S m // 0 ≤ x.radius ∧ x.OpenConditions}

namespace ClusterFreeCoordinates

variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

theorem representative_coarse (j : ClusterCoarseIndex i a S) :
    representative S a j.val = j.val := by
  rcases j.property.1 with hj | hj
  · simp [representative, hj]
  · simp [representative, hj]

@[simp] theorem base_coarse (x : ClusterFreeCoordinates i a b S m)
    (j : ClusterCoarseIndex i a S) : x.base j.val = x.1 j := by
  simp only [base, representative_coarse, dif_neg j.property.2]
  exact congrArg x.1 (Subtype.ext rfl)

@[simp] theorem velocity_shape (x : ClusterFreeCoordinates i a b S m)
    (j : ClusterShapeIndex a b S) : x.velocity j.val = x.2.1 j := by
  simp only [velocity, dif_neg j.property.2.1, dif_neg j.property.2.2,
    dif_pos j.property.1]
  exact congrArg x.2.1 (Subtype.ext rfl)

end ClusterFreeCoordinates

namespace ClusterFreeDomain

variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

instance : TopologicalSpace (ClusterFreeDomain i a b S m) :=
  inferInstanceAs (TopologicalSpace {x : ClusterFreeCoordinates i a b S m //
    0 ≤ x.radius ∧ x.OpenConditions})

private theorem exists_datum (x : ClusterFreeDomain i a b S m)
    (ha : a ∈ S) (hb : b ∈ S) (hanchor : i ∈ S → a = i) :
    ∃ D : SingleInteriorCluster i m S, D.parameterCoordinates = x.val.parameters := by
  change x.val.parameters ∈ Set.range SingleInteriorCluster.parameterCoordinates
  rw [SingleInteriorCluster.range_parameterCoordinates]
  exact ⟨x.property.2.1, x.val.closed_conditions ha hb hanchor⟩

/-- Reconstruction uses the proved exact range of the actual coordinate embedding. -/
def datum (ha : a ∈ S) (hb : b ∈ S) (hanchor : i ∈ S → a = i)
    (x : ClusterFreeDomain i a b S m) : SingleInteriorCluster i m S :=
  (exists_datum x ha hb hanchor).choose

theorem datum_parameters (ha : a ∈ S) (hb : b ∈ S) (hanchor : i ∈ S → a = i)
    (x : ClusterFreeDomain i a b S m) :
    (datum ha hb hanchor x).parameterCoordinates = x.val.parameters :=
  (exists_datum x ha hb hanchor).choose_spec

@[simp] theorem datum_base (ha : a ∈ S) (hb : b ∈ S) (hanchor : i ∈ S → a = i)
    (x : ClusterFreeDomain i a b S m) (j : Fin n) :
    ((datum ha hb hanchor x).base j : ℂ) = x.val.base j :=
  congrArg (fun y : InteriorClusterParameterSpace n m => y.1 j)
    (datum_parameters ha hb hanchor x)

@[simp] theorem datum_velocity (ha : a ∈ S) (hb : b ∈ S) (hanchor : i ∈ S → a = i)
    (x : ClusterFreeDomain i a b S m) (j : Fin n) :
    (datum ha hb hanchor x).velocity j = x.val.velocity j :=
  congrArg (fun y : InteriorClusterParameterSpace n m => y.2.1 j)
    (datum_parameters ha hb hanchor x)

@[simp] theorem datum_boundary (ha : a ∈ S) (hb : b ∈ S) (hanchor : i ∈ S → a = i)
    (x : ClusterFreeDomain i a b S m) :
    (datum ha hb hanchor x).boundary = x.val.2.2.1 :=
  congrArg (fun y : InteriorClusterParameterSpace n m => y.2.2)
    (datum_parameters ha hb hanchor x)

@[fun_prop] theorem continuous_datum (ha : a ∈ S) (hb : b ∈ S)
    (hanchor : i ∈ S → a = i) : Continuous (datum (m := m) ha hb hanchor) := by
  apply SingleInteriorCluster.isEmbedding_parameterCoordinates.isInducing.continuous_iff.mpr
  simp only [Function.comp_def, datum_parameters]
  change Continuous (fun x : {x : ClusterFreeCoordinates i a b S m //
    0 ≤ x.radius ∧ x.OpenConditions} => x.val.parameters)
  exact ClusterFreeCoordinates.continuous_parameters.comp continuous_subtype_val

theorem datum_admissible (ha : a ∈ S) (hb : b ∈ S) (hanchor : i ∈ S → a = i)
    (x : ClusterFreeDomain i a b S m) :
    (datum ha hb hanchor x).toInteriorCollisionData.AdmissibleScale x.val.radius := by
  apply (InteriorClusterDomain.admissibleScale_iff_openScaleConditions
    (datum ha hb hanchor x, x.val.radius)).mpr
  refine ⟨x.property.1, ?_, ?_⟩
  · intro j
    simpa only [datum_velocity, ← UpperHalfPlane.coe_im, datum_base] using x.property.2.2.1 j
  · intro j k h
    simpa only [datum_velocity, datum_base] using x.property.2.2.2 j k h

def toSlice (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i)
    (x : ClusterFreeDomain i a b S m) : NormalizedInteriorClusterSlice i m S a b :=
  ⟨⟨(datum ha hb hanchor x, x.val.radius), datum_admissible ha hb hanchor x⟩,
    by simp only [InteriorClusterDomain.datum, datum_velocity,
      ClusterFreeCoordinates.velocity_anchor, ClusterFreeCoordinates.velocity_reference _ hba,
      Circle.norm_coe]
       exact ⟨trivial, trivial⟩⟩

@[fun_prop] theorem continuous_toSlice (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) : Continuous (toSlice (m := m) ha hb hba hanchor) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact (continuous_datum ha hb hanchor).prodMk
    (ClusterFreeCoordinates.continuous_radius.comp continuous_subtype_val)

end ClusterFreeDomain

namespace NormalizedInteriorClusterSlice

variable {n m : ℕ} {i : Fin n} {S : Finset (Fin n)} {a b : Fin n}

def freeCoordinates (x : NormalizedInteriorClusterSlice i m S a b) :
    ClusterFreeCoordinates i a b S m :=
  (fun j => (x.val.datum.base j.val : ℂ), fun j => x.val.datum.velocity j.val,
    x.val.datum.boundary, ⟨x.val.datum.velocity b, mem_sphere_zero_iff_norm.mpr x.property.2⟩, x.val.scale)

@[simp] theorem freeCoordinates_base (x : NormalizedInteriorClusterSlice i m S a b)
    (ha : a ∈ S) (j : Fin n) : x.freeCoordinates.base j = (x.val.datum.base j : ℂ) := by
  have hrep : x.val.datum.base (ClusterFreeCoordinates.representative S a j) = x.val.datum.base j := by
    by_cases hj : j ∈ S
    · simp only [ClusterFreeCoordinates.representative, if_pos hj]
      exact x.val.datum.base_eq_of_mem ha hj
    · simp [ClusterFreeCoordinates.representative, hj]
  unfold ClusterFreeCoordinates.base
  split_ifs with h
  · rw [h] at hrep
    exact (congrArg (fun z : UpperHalfPlane => (z : ℂ))
      (x.val.datum.base_normalized.symm.trans hrep))
  · exact congrArg (fun z : UpperHalfPlane => (z : ℂ)) hrep

@[simp] theorem freeCoordinates_velocity (x : NormalizedInteriorClusterSlice i m S a b)
    (j : Fin n) : x.freeCoordinates.velocity j = x.val.datum.velocity j := by
  unfold ClusterFreeCoordinates.velocity
  split_ifs with hja hjb hj
  · simpa only [hja] using x.property.1.symm
  · subst j
    rfl
  · rfl
  · exact (x.val.datum.velocity_zero_off j hj).symm

@[simp] theorem freeCoordinates_parameters (x : NormalizedInteriorClusterSlice i m S a b)
    (ha : a ∈ S) : x.freeCoordinates.parameters = x.val.datum.parameterCoordinates := by
  apply Prod.ext
  · exact funext (freeCoordinates_base x ha)
  · exact Prod.ext (funext x.freeCoordinates_velocity) rfl

@[simp] theorem freeCoordinates_radius (x : NormalizedInteriorClusterSlice i m S a b) :
    x.freeCoordinates.radius = x.val.scale := rfl

theorem freeCoordinates_openConditions (x : NormalizedInteriorClusterSlice i m S a b)
    (ha : a ∈ S) : x.freeCoordinates.OpenConditions := by
  refine ⟨?_, ?_, ?_⟩
  · rw [freeCoordinates_parameters x ha]
    have h := SingleInteriorCluster.range_parameterCoordinates ▸
      (show x.val.datum.parameterCoordinates ∈ Set.range
        (SingleInteriorCluster.parameterCoordinates (i := i) (m := m) (S := S)) from
          ⟨x.val.datum, rfl⟩)
    exact h.1
  · intro j
    simpa only [freeCoordinates_radius, freeCoordinates_velocity, freeCoordinates_base x ha,
      InteriorClusterDomain.scale, InteriorClusterDomain.datum, UpperHalfPlane.coe_im]
      using x.val.property.height j
  · intro j k h
    simpa only [freeCoordinates_radius, freeCoordinates_velocity, freeCoordinates_base x ha,
      InteriorClusterDomain.scale, InteriorClusterDomain.datum] using
      x.val.property.separation j k (fun hbase => h ((x.val.datum.base_eq_iff j k).mp hbase))

def toFreeDomain (ha : a ∈ S) (x : NormalizedInteriorClusterSlice i m S a b) :
    ClusterFreeDomain i a b S m :=
  ⟨x.freeCoordinates, x.val.property.nonneg, x.freeCoordinates_openConditions ha⟩

@[fun_prop] theorem continuous_freeCoordinates :
    Continuous (freeCoordinates : NormalizedInteriorClusterSlice i m S a b → _) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro j
    exact ((SingleInteriorCluster.continuous_base j.val).comp
      InteriorClusterDomain.continuous_datum).comp continuous_subtype_val
  · apply Continuous.prodMk
    · apply continuous_pi
      intro j
      fun_prop
    · apply Continuous.prodMk
      · fun_prop
      · apply Continuous.prodMk
        · apply Continuous.subtype_mk
          fun_prop
        · fun_prop

@[fun_prop] theorem continuous_toFreeDomain (ha : a ∈ S) :
    Continuous (toFreeDomain (i := i) (b := b) (m := m) ha) :=
  continuous_freeCoordinates.subtype_mk _

end NormalizedInteriorClusterSlice

namespace ClusterFreeDomain

variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

@[simp] theorem freeCoordinates_toSlice (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (x : ClusterFreeDomain i a b S m) :
    (toSlice ha hb hba hanchor x).freeCoordinates = x.val := by
  apply Prod.ext
  · funext j
    change ((datum ha hb hanchor x).base j.val : ℂ) = x.val.1 j
    rw [datum_base, ClusterFreeCoordinates.base_coarse]
  · apply Prod.ext
    · funext j
      change (datum ha hb hanchor x).velocity j.val = x.val.2.1 j
      rw [datum_velocity, ClusterFreeCoordinates.velocity_shape]
    · apply Prod.ext
      · exact datum_boundary ha hb hanchor x
      · apply Prod.ext
        · apply Circle.coe_injective
          change (datum ha hb hanchor x).velocity b = (x.val.2.2.2.1 : ℂ)
          rw [datum_velocity, ClusterFreeCoordinates.velocity_reference _ hba]
        · rfl

@[simp] theorem toFreeDomain_toSlice (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (x : ClusterFreeDomain i a b S m) :
    (toSlice ha hb hba hanchor x).toFreeDomain ha = x :=
  Subtype.ext (freeCoordinates_toSlice ha hb hba hanchor x)

@[simp] theorem toSlice_toFreeDomain (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (x : NormalizedInteriorClusterSlice i m S a b) :
    toSlice ha hb hba hanchor (x.toFreeDomain ha) = x := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply SingleInteriorCluster.isEmbedding_parameterCoordinates.injective
    exact (datum_parameters ha hb hanchor (x.toFreeDomain ha)).trans
      (x.freeCoordinates_parameters ha)
  · rfl

@[simp] theorem toSlice_base (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (x : ClusterFreeDomain i a b S m) (j : Fin n) :
    ((toSlice ha hb hba hanchor x).val.datum.base j : ℂ) = x.val.base j :=
  datum_base ha hb hanchor x j

@[simp] theorem toSlice_velocity (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (x : ClusterFreeDomain i a b S m) (j : Fin n) :
    (toSlice ha hb hba hanchor x).val.datum.velocity j = x.val.velocity j :=
  datum_velocity ha hb hanchor x j

@[simp] theorem toSlice_boundary (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (x : ClusterFreeDomain i a b S m) :
    (toSlice ha hb hba hanchor x).val.datum.boundary = x.val.2.2.1 :=
  datum_boundary ha hb hanchor x

@[simp] theorem toSlice_scale (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (x : ClusterFreeDomain i a b S m) :
    (toSlice ha hb hba hanchor x).val.scale = x.val.radius := rfl

end ClusterFreeDomain

/-- Actual free coarse/shape/circle/radius coordinates for the normalized slice. -/
def clusterFreeHomeomorph {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i) :
    ClusterFreeDomain i a b S m ≃ₜ NormalizedInteriorClusterSlice i m S a b where
  toFun := ClusterFreeDomain.toSlice ha hb hba hanchor
  invFun := NormalizedInteriorClusterSlice.toFreeDomain ha
  left_inv := ClusterFreeDomain.toFreeDomain_toSlice ha hb hba hanchor
  right_inv := ClusterFreeDomain.toSlice_toFreeDomain ha hb hba hanchor
  continuous_toFun := ClusterFreeDomain.continuous_toSlice ha hb hba hanchor
  continuous_invFun := NormalizedInteriorClusterSlice.continuous_toFreeDomain ha

@[simp] theorem clusterFreeHomeomorph_apply {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i)
    (x : ClusterFreeDomain i a b S m) :
    clusterFreeHomeomorph ha hb hba hanchor x = ClusterFreeDomain.toSlice ha hb hba hanchor x := rfl

@[simp] theorem clusterFreeHomeomorph_symm_apply {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i)
    (x : NormalizedInteriorClusterSlice i m S a b) :
    (clusterFreeHomeomorph ha hb hba hanchor).symm x = x.toFreeDomain ha := rfl

end EnvelopingIsomorphism.Deformation.Kontsevich
