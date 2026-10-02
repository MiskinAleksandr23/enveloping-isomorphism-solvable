import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterFreeCoordinates

/-! The exact free-coordinate homeomorphism for a normalized finite real
cluster. Both maps reconstruct their parameters from the actual data arrays. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration Topology

namespace BoundaryClusterFreeDomain

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

def datum (x : BoundaryClusterFreeDomain i a S m l u) : BoundaryClusterData i a m S l u :=
  (x.val.exists_datum l u x.property.2).choose

theorem datum_parameters (x : BoundaryClusterFreeDomain i a S m l u) :
    x.datum.coordinates = x.val.parameters l u :=
  (x.val.exists_datum l u x.property.2).choose_spec

@[simp] theorem datum_center (x : BoundaryClusterFreeDomain i a S m l u) :
    x.datum.center = x.val.center := congrArg Prod.fst x.datum_parameters

@[simp] theorem datum_base (x : BoundaryClusterFreeDomain i a S m l u) (j : Fin n) :
    x.datum.base j = x.val.base j :=
  congrArg (fun y : BoundaryClusterParameterSpace n m => y.2.1 j) x.datum_parameters

@[simp] theorem datum_velocity (x : BoundaryClusterFreeDomain i a S m l u) (j : Fin n) :
    x.datum.velocity j = x.val.velocity j :=
  congrArg (fun y : BoundaryClusterParameterSpace n m => y.2.2.1 j) x.datum_parameters

@[simp] theorem datum_boundaryBase (x : BoundaryClusterFreeDomain i a S m l u) (j : Fin m) :
    x.datum.boundaryBase j = x.val.boundaryBase l u j :=
  congrArg (fun y : BoundaryClusterParameterSpace n m => y.2.2.2.1 j) x.datum_parameters

@[simp] theorem datum_boundaryVelocity (x : BoundaryClusterFreeDomain i a S m l u) (j : Fin m) :
    x.datum.boundaryVelocity j = x.val.boundaryVelocity l u j :=
  congrArg (fun y : BoundaryClusterParameterSpace n m => y.2.2.2.2 j) x.datum_parameters

@[fun_prop] theorem continuous_datum :
    Continuous (datum : BoundaryClusterFreeDomain i a S m l u → _) := by
  apply BoundaryClusterData.isEmbedding_coordinates.isInducing.continuous_iff.mpr
  simp only [Function.comp_def, datum_parameters]
  change Continuous (fun x : {x : BoundaryClusterFreeCoordinates i a S m //
    0 ≤ x.radius ∧ x.OpenConditions l u} => x.val.parameters l u)
  exact (BoundaryClusterFreeCoordinates.continuous_parameters l u).comp continuous_subtype_val

theorem datum_admissible (x : BoundaryClusterFreeDomain i a S m l u) :
    x.datum.AdmissibleScale x.val.radius := by
  apply (BoundaryClusterDomain.admissibleScale_iff_openScaleConditions (x.datum, x.val.radius)).mpr
  refine ⟨x.property.1, ?_, ?_⟩
  · intro j k h
    simpa only [datum_velocity, datum_base] using x.property.2.2.1 j k h
  · intro j k hjk hblock
    simpa only [datum_boundaryVelocity, datum_boundaryBase] using x.property.2.2.2 j k hjk hblock

def toDomain (x : BoundaryClusterFreeDomain i a S m l u) : BoundaryClusterDomain i a m S l u :=
  ⟨(x.datum, x.val.radius), x.datum_admissible⟩

@[fun_prop] theorem continuous_toDomain :
    Continuous (toDomain : BoundaryClusterFreeDomain i a S m l u → _) :=
  (continuous_datum.prodMk
    (BoundaryClusterFreeCoordinates.continuous_radius.comp continuous_subtype_val)).subtype_mk _

@[simp] theorem toDomain_center (x : BoundaryClusterFreeDomain i a S m l u) :
    x.toDomain.datum.center = x.val.center := x.datum_center

@[simp] theorem toDomain_base (x : BoundaryClusterFreeDomain i a S m l u) (j : Fin n) :
    x.toDomain.datum.base j = x.val.base j := x.datum_base j

@[simp] theorem toDomain_velocity (x : BoundaryClusterFreeDomain i a S m l u) (j : Fin n) :
    x.toDomain.datum.velocity j = x.val.velocity j := x.datum_velocity j

@[simp] theorem toDomain_boundaryBase (x : BoundaryClusterFreeDomain i a S m l u) (j : Fin m) :
    x.toDomain.datum.boundaryBase j = x.val.boundaryBase l u j := x.datum_boundaryBase j

@[simp] theorem toDomain_boundaryVelocity (x : BoundaryClusterFreeDomain i a S m l u) (j : Fin m) :
    x.toDomain.datum.boundaryVelocity j = x.val.boundaryVelocity l u j := x.datum_boundaryVelocity j

@[simp] theorem toDomain_scale (x : BoundaryClusterFreeDomain i a S m l u) :
    x.toDomain.scale = x.val.radius := rfl

end BoundaryClusterFreeDomain

namespace BoundaryClusterDomain

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

def freeCoordinates (x : BoundaryClusterDomain i a m S l u) : BoundaryClusterFreeCoordinates i a S m :=
  (fun j => x.datum.base j.val, fun j => x.datum.velocity j.val,
    fun j => if j ∈ boundaryClusterBlock l u then x.datum.boundaryVelocity j else x.datum.boundaryBase j,
    x.datum.center, x.scale)

@[simp] theorem freeCoordinates_center (x : BoundaryClusterDomain i a m S l u) :
    x.freeCoordinates.center = x.datum.center := rfl

@[simp] theorem freeCoordinates_radius (x : BoundaryClusterDomain i a m S l u) :
    x.freeCoordinates.radius = x.scale := rfl

@[simp] theorem freeCoordinates_base (x : BoundaryClusterDomain i a m S l u) (j : Fin n) :
    x.freeCoordinates.base j = x.datum.base j := by
  unfold BoundaryClusterFreeCoordinates.base
  split_ifs with hj hji
  · exact (x.datum.base_eq_center j hj).symm
  · subst j
    exact x.datum.base_normalized.symm
  · rfl

@[simp] theorem freeCoordinates_velocity (x : BoundaryClusterDomain i a m S l u) (j : Fin n) :
    x.freeCoordinates.velocity j = x.datum.velocity j := by
  unfold BoundaryClusterFreeCoordinates.velocity
  split_ifs with hj hja
  · subst j
    exact x.datum.velocity_anchor.symm
  · rfl
  · exact (x.datum.velocity_zero_off j hj).symm

@[simp] theorem freeCoordinates_boundaryBase (x : BoundaryClusterDomain i a m S l u) (j : Fin m) :
    x.freeCoordinates.boundaryBase l u j = x.datum.boundaryBase j := by
  by_cases hj : j ∈ boundaryClusterBlock l u
  · simpa only [BoundaryClusterFreeCoordinates.boundaryBase, if_pos hj, freeCoordinates_center] using
      (x.datum.boundaryBase_eq_center j hj).symm
  · simp only [BoundaryClusterFreeCoordinates.boundaryBase, if_neg hj, freeCoordinates]

@[simp] theorem freeCoordinates_boundaryVelocity (x : BoundaryClusterDomain i a m S l u) (j : Fin m) :
    x.freeCoordinates.boundaryVelocity l u j = x.datum.boundaryVelocity j := by
  by_cases hj : j ∈ boundaryClusterBlock l u
  · simp only [BoundaryClusterFreeCoordinates.boundaryVelocity, if_pos hj, freeCoordinates]
  · simpa only [BoundaryClusterFreeCoordinates.boundaryVelocity, if_neg hj] using
      (x.datum.boundaryVelocity_zero_off j hj).symm

@[simp] theorem freeCoordinates_parameters (x : BoundaryClusterDomain i a m S l u) :
    x.freeCoordinates.parameters l u = x.datum.coordinates := by
  exact Prod.ext x.freeCoordinates_center (Prod.ext (funext x.freeCoordinates_base)
    (Prod.ext (funext x.freeCoordinates_velocity)
      (Prod.ext (funext x.freeCoordinates_boundaryBase) (funext x.freeCoordinates_boundaryVelocity))))

theorem freeCoordinates_openConditions (x : BoundaryClusterDomain i a m S l u) :
    x.freeCoordinates.OpenConditions l u := by
  refine ⟨?_, ?_, ?_⟩
  · rw [freeCoordinates_parameters]
    have h : x.datum.coordinates ∈ Set.range
        (BoundaryClusterData.coordinates (i := i) (a := a) (m := m) (S := S) (l := l) (u := u)) :=
      ⟨x.datum, rfl⟩
    rw [BoundaryClusterData.range_coordinates] at h
    exact h.1
  · intro j k h
    simpa only [freeCoordinates_radius, freeCoordinates_velocity, freeCoordinates_base,
      BoundaryClusterDomain.scale, BoundaryClusterDomain.datum] using x.property.separation j k
        (fun hbase => h ((x.datum.base_eq_iff j k).mp hbase))
  · intro j k hjk hblock
    simpa only [freeCoordinates_radius, freeCoordinates_boundaryVelocity, freeCoordinates_boundaryBase,
      BoundaryClusterDomain.scale, BoundaryClusterDomain.datum] using x.property.boundary_separation j k hjk hblock

def toFreeDomain (x : BoundaryClusterDomain i a m S l u) : BoundaryClusterFreeDomain i a S m l u :=
  ⟨x.freeCoordinates, x.property.nonneg, x.freeCoordinates_openConditions⟩

@[fun_prop] theorem continuous_freeCoordinates :
    Continuous (freeCoordinates : BoundaryClusterDomain i a m S l u → _) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro j
    fun_prop
  · apply Continuous.prodMk
    · apply continuous_pi
      intro j
      fun_prop
    · apply Continuous.prodMk
      · apply continuous_pi
        intro j
        by_cases hj : j ∈ boundaryClusterBlock l u
        · simp only [if_pos hj]
          fun_prop
        · simp only [if_neg hj]
          fun_prop
      · apply Continuous.prodMk <;> fun_prop

@[fun_prop] theorem continuous_toFreeDomain :
    Continuous (toFreeDomain : BoundaryClusterDomain i a m S l u → _) :=
  continuous_freeCoordinates.subtype_mk _

end BoundaryClusterDomain

namespace BoundaryClusterFreeDomain

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

@[simp] theorem freeCoordinates_toDomain (x : BoundaryClusterFreeDomain i a S m l u) :
    x.toDomain.freeCoordinates = x.val := by
  apply Prod.ext
  · funext j
    change x.toDomain.datum.base j.val = x.val.1 j
    rw [toDomain_base, BoundaryClusterFreeCoordinates.base_coarse]
  · apply Prod.ext
    · funext j
      change x.toDomain.datum.velocity j.val = x.val.2.1 j
      rw [toDomain_velocity, BoundaryClusterFreeCoordinates.velocity_shape]
    · apply Prod.ext
      · funext j
        by_cases hj : j ∈ boundaryClusterBlock l u
        · simp only [BoundaryClusterDomain.freeCoordinates, if_pos hj, toDomain_boundaryVelocity,
            BoundaryClusterFreeCoordinates.boundaryVelocity]
        · simp only [BoundaryClusterDomain.freeCoordinates, if_neg hj, toDomain_boundaryBase,
            BoundaryClusterFreeCoordinates.boundaryBase]
      · exact Prod.ext x.toDomain_center rfl

@[simp] theorem toFreeDomain_toDomain (x : BoundaryClusterFreeDomain i a S m l u) :
    x.toDomain.toFreeDomain = x := Subtype.ext x.freeCoordinates_toDomain

@[simp] theorem toDomain_toFreeDomain (x : BoundaryClusterDomain i a m S l u) :
    x.toFreeDomain.toDomain = x := by
  apply Subtype.ext
  apply Prod.ext
  · apply BoundaryClusterData.coordinates_injective
    exact x.toFreeDomain.datum_parameters.trans x.freeCoordinates_parameters
  · rfl

end BoundaryClusterFreeDomain

/-- Free complex/real coordinates for the actual geometric domain, with no extra hypotheses. -/
def boundaryClusterFreeHomeomorph {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)} :
    BoundaryClusterFreeDomain i a S m l u ≃ₜ BoundaryClusterDomain i a m S l u where
  toFun := BoundaryClusterFreeDomain.toDomain
  invFun := BoundaryClusterDomain.toFreeDomain
  left_inv := BoundaryClusterFreeDomain.toFreeDomain_toDomain
  right_inv := BoundaryClusterFreeDomain.toDomain_toFreeDomain
  continuous_toFun := BoundaryClusterFreeDomain.continuous_toDomain
  continuous_invFun := BoundaryClusterDomain.continuous_toFreeDomain

@[simp] theorem boundaryClusterFreeHomeomorph_apply {n m : ℕ} {i a : Fin n}
    {S : Finset (Fin n)} {l u : Fin (m + 1)} (x : BoundaryClusterFreeDomain i a S m l u) :
    boundaryClusterFreeHomeomorph x = x.toDomain := rfl

@[simp] theorem boundaryClusterFreeHomeomorph_symm_apply {n m : ℕ} {i a : Fin n}
    {S : Finset (Fin n)} {l u : Fin (m + 1)} (x : BoundaryClusterDomain i a m S l u) :
    boundaryClusterFreeHomeomorph.symm x = x.toFreeDomain := rfl

@[simp] theorem boundaryClusterFreeHomeomorph_scale {n m : ℕ} {i a : Fin n}
    {S : Finset (Fin n)} {l u : Fin (m + 1)} (x : BoundaryClusterFreeDomain i a S m l u) :
    (boundaryClusterFreeHomeomorph x).scale = x.val.radius := rfl

@[simp] theorem boundaryClusterFreeHomeomorph_symm_radius {n m : ℕ} {i a : Fin n}
    {S : Finset (Fin n)} {l u : Fin (m + 1)} (x : BoundaryClusterDomain i a m S l u) :
    (boundaryClusterFreeHomeomorph.symm x).val.radius = x.scale := rfl

end EnvelopingIsomorphism.Deformation.Kontsevich
