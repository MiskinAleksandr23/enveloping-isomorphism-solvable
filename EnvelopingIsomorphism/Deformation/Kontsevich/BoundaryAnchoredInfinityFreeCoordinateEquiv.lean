import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryAnchoredInfinityFreeCoordinates

/-! The actual free-coordinate homeomorphism for the boundary-anchored infinity domain. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration Topology

namespace BoundaryAnchoredInfinityFreeDomain

variable {n m : ℕ} {a : Fin n} {l u : Fin (m + 1)} {o : Fin m}

def datum (x : BoundaryAnchoredInfinityFreeDomain a m l u o) : BoundaryAnchoredInfinityData a m l u o :=
  x.val.toDatum l u x.property.2

@[simp] theorem datum_parameters (x : BoundaryAnchoredInfinityFreeDomain a m l u o) :
    x.datum.coords = x.val.parameters l u := x.val.toDatum_parameters l u x.property.2

@[simp] theorem datum_shape (x : BoundaryAnchoredInfinityFreeDomain a m l u o) (j : Fin n) :
    (x.datum.shape j : ℂ) = x.val.shape j :=
  congrArg (fun y : BoundaryAnchoredInfinityParameterSpace n m => y.1 j) x.datum_parameters

@[simp] theorem datum_boundaryBase (x : BoundaryAnchoredInfinityFreeDomain a m l u o) (j : Fin m) :
    x.datum.boundaryBase j = x.val.boundaryBase l u j :=
  congrArg (fun y : BoundaryAnchoredInfinityParameterSpace n m => y.2.1 j) x.datum_parameters

@[simp] theorem datum_boundaryVelocity (x : BoundaryAnchoredInfinityFreeDomain a m l u o) (j : Fin m) :
    x.datum.boundaryVelocity j = x.val.boundaryVelocity l u j :=
  congrArg (fun y : BoundaryAnchoredInfinityParameterSpace n m => y.2.2 j) x.datum_parameters

@[fun_prop] theorem continuous_datum :
    Continuous (datum : BoundaryAnchoredInfinityFreeDomain a m l u o → _) := by
  apply BoundaryAnchoredInfinityData.isEmbedding_coords.isInducing.continuous_iff.mpr
  simp only [Function.comp_def, datum_parameters]
  exact (BoundaryAnchoredInfinityFreeCoordinates.continuous_parameters l u).comp continuous_subtype_val

theorem datum_admissible (x : BoundaryAnchoredInfinityFreeDomain a m l u o) :
    x.datum.AdmissibleScale x.val.radius := by
  refine ⟨x.property.1, fun j k hjk hblock => ?_⟩
  simpa only [datum_boundaryBase, datum_boundaryVelocity] using x.property.2.2 j k hjk hblock

def toDomain (x : BoundaryAnchoredInfinityFreeDomain a m l u o) : BoundaryAnchoredInfinityDomain a m l u o :=
  ⟨(x.datum, x.val.radius), x.datum_admissible⟩

@[simp] theorem toDomain_shape (x : BoundaryAnchoredInfinityFreeDomain a m l u o) (j : Fin n) :
    (x.toDomain.datum.shape j : ℂ) = x.val.shape j := x.datum_shape j

@[simp] theorem toDomain_boundaryBase (x : BoundaryAnchoredInfinityFreeDomain a m l u o) (j : Fin m) :
    x.toDomain.datum.boundaryBase j = x.val.boundaryBase l u j := x.datum_boundaryBase j

@[simp] theorem toDomain_boundaryVelocity (x : BoundaryAnchoredInfinityFreeDomain a m l u o) (j : Fin m) :
    x.toDomain.datum.boundaryVelocity j = x.val.boundaryVelocity l u j := x.datum_boundaryVelocity j

@[simp] theorem toDomain_scale (x : BoundaryAnchoredInfinityFreeDomain a m l u o) :
    x.toDomain.scale = x.val.radius := rfl

@[fun_prop] theorem continuous_toDomain :
    Continuous (toDomain : BoundaryAnchoredInfinityFreeDomain a m l u o → _) :=
  (continuous_datum.prodMk
    (BoundaryAnchoredInfinityFreeCoordinates.continuous_radius.comp continuous_subtype_val)).subtype_mk _

theorem configuration_interior (x : BoundaryAnchoredInfinityFreeDomain a m l u o)
    (hr : 0 < x.val.radius) (j : Fin n) :
    ((x.datum.configuration (x.datum_admissible.isSafeScale hr) hr le_rfl).interior j : ℂ) =
      x.val.scaledInterior j := by
  change (x.val.radius : ℂ) * (x.datum.shape j : ℂ) = _
  rw [datum_shape]
  rfl

theorem configuration_boundary (x : BoundaryAnchoredInfinityFreeDomain a m l u o)
    (hr : 0 < x.val.radius) (j : Fin m) :
    (x.datum.configuration (x.datum_admissible.isSafeScale hr) hr le_rfl).boundary j =
      x.val.scaledBoundary l u j := by
  change x.datum.boundaryBase j + x.val.radius * x.datum.boundaryVelocity j = _
  rw [datum_boundaryBase, datum_boundaryVelocity]
  rfl

end BoundaryAnchoredInfinityFreeDomain

namespace BoundaryAnchoredInfinityDomain

variable {n m : ℕ} {a : Fin n} {l u : Fin (m + 1)} {o : Fin m}

def freeCoordinates (x : BoundaryAnchoredInfinityDomain a m l u o) :
    BoundaryAnchoredInfinityFreeCoordinates a m o :=
  (fun j => (x.datum.shape j.val : ℂ),
    fun j => if j.val ∈ boundaryClusterBlock l u then x.datum.boundaryVelocity j.val else x.datum.boundaryBase j.val,
    x.scale)

@[simp] theorem freeCoordinates_radius (x : BoundaryAnchoredInfinityDomain a m l u o) :
    x.freeCoordinates.radius = x.scale := rfl

@[simp] theorem freeCoordinates_shape (x : BoundaryAnchoredInfinityDomain a m l u o) (j : Fin n) :
    x.freeCoordinates.shape j = (x.datum.shape j : ℂ) := by
  unfold BoundaryAnchoredInfinityFreeCoordinates.shape
  split_ifs with hj
  · subst j
    simpa using (congrArg (fun z : UpperHalfPlane => (z : ℂ)) x.datum.shape_anchor).symm
  · rfl

@[simp] theorem freeCoordinates_boundaryCoordinate (x : BoundaryAnchoredInfinityDomain a m l u o) (j : Fin m) :
    x.freeCoordinates.boundaryCoordinate l j =
      if j ∈ boundaryClusterBlock l u then x.datum.boundaryVelocity j else x.datum.boundaryBase j := by
  unfold BoundaryAnchoredInfinityFreeCoordinates.boundaryCoordinate
  by_cases hj : j = o
  · subst j
    rw [dif_pos rfl, if_neg x.datum.outside_not_mem, x.datum.boundaryBase_anchor]
  · rw [dif_neg hj]
    rfl

@[simp] theorem freeCoordinates_boundaryBase (x : BoundaryAnchoredInfinityDomain a m l u o) (j : Fin m) :
    x.freeCoordinates.boundaryBase l u j = x.datum.boundaryBase j := by
  unfold BoundaryAnchoredInfinityFreeCoordinates.boundaryBase
  by_cases hj : j ∈ boundaryClusterBlock l u
  · rw [if_pos hj]
    exact (x.datum.boundaryBase_zero_on j hj).symm
  · rw [if_neg hj, freeCoordinates_boundaryCoordinate, if_neg hj]

@[simp] theorem freeCoordinates_boundaryVelocity (x : BoundaryAnchoredInfinityDomain a m l u o) (j : Fin m) :
    x.freeCoordinates.boundaryVelocity l u j = x.datum.boundaryVelocity j := by
  unfold BoundaryAnchoredInfinityFreeCoordinates.boundaryVelocity
  by_cases hj : j ∈ boundaryClusterBlock l u
  · rw [if_pos hj, freeCoordinates_boundaryCoordinate, if_pos hj]
  · rw [if_neg hj]
    exact (x.datum.boundaryVelocity_zero_off j hj).symm

@[simp] theorem freeCoordinates_parameters (x : BoundaryAnchoredInfinityDomain a m l u o) :
    x.freeCoordinates.parameters l u = x.datum.coords :=
  Prod.ext (funext x.freeCoordinates_shape)
    (Prod.ext (funext x.freeCoordinates_boundaryBase) (funext x.freeCoordinates_boundaryVelocity))

theorem freeCoordinates_openConditions (x : BoundaryAnchoredInfinityDomain a m l u o) :
    x.freeCoordinates.OpenConditions l u := by
  refine ⟨?_, fun j k hjk hblock => ?_⟩
  · rw [freeCoordinates_parameters]
    have h : x.datum.coords ∈ Set.range (BoundaryAnchoredInfinityData.coords
        (a := a) (l := l) (u := u) (o := o)) := ⟨x.datum, rfl⟩
    rw [BoundaryAnchoredInfinityData.range_coords] at h
    exact h.1
  · simpa only [freeCoordinates_radius, freeCoordinates_boundaryBase, freeCoordinates_boundaryVelocity,
      datum, scale] using x.property.boundary_separation j k hjk hblock

def toFreeDomain (x : BoundaryAnchoredInfinityDomain a m l u o) : BoundaryAnchoredInfinityFreeDomain a m l u o :=
  ⟨x.freeCoordinates, x.property.nonneg, x.freeCoordinates_openConditions⟩

@[fun_prop] theorem continuous_freeCoordinates :
    Continuous (freeCoordinates : BoundaryAnchoredInfinityDomain a m l u o → _) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro j
    exact (BoundaryAnchoredInfinityData.continuous_shape_apply j.val).comp continuous_datum
  · apply Continuous.prodMk
    · apply continuous_pi
      intro j
      by_cases hj : j.val ∈ boundaryClusterBlock l u
      · simp only [if_pos hj]
        exact (BoundaryAnchoredInfinityData.continuous_boundaryVelocity_apply j.val).comp continuous_datum
      · simp only [if_neg hj]
        exact (BoundaryAnchoredInfinityData.continuous_boundaryBase_apply j.val).comp continuous_datum
    · exact continuous_scale

@[fun_prop] theorem continuous_toFreeDomain :
    Continuous (toFreeDomain : BoundaryAnchoredInfinityDomain a m l u o → _) :=
  continuous_freeCoordinates.subtype_mk _

end BoundaryAnchoredInfinityDomain

namespace BoundaryAnchoredInfinityFreeDomain

variable {n m : ℕ} {a : Fin n} {l u : Fin (m + 1)} {o : Fin m}

@[simp] theorem freeCoordinates_toDomain (x : BoundaryAnchoredInfinityFreeDomain a m l u o) :
    x.toDomain.freeCoordinates = x.val := by
  apply Prod.ext
  · funext j
    change (x.toDomain.datum.shape j.val : ℂ) = x.val.1 j
    rw [toDomain_shape, BoundaryAnchoredInfinityFreeCoordinates.shape_free]
  · apply Prod.ext
    · funext j
      change (if j.val ∈ boundaryClusterBlock l u then x.toDomain.datum.boundaryVelocity j.val
        else x.toDomain.datum.boundaryBase j.val) = x.val.2.1 j
      by_cases hj : j.val ∈ boundaryClusterBlock l u
      · rw [if_pos hj, toDomain_boundaryVelocity, BoundaryAnchoredInfinityFreeCoordinates.boundaryVelocity,
          if_pos hj, BoundaryAnchoredInfinityFreeCoordinates.boundaryCoordinate_free]
      · rw [if_neg hj, toDomain_boundaryBase, BoundaryAnchoredInfinityFreeCoordinates.boundaryBase,
          if_neg hj, BoundaryAnchoredInfinityFreeCoordinates.boundaryCoordinate_free]
    · rfl

@[simp] theorem toFreeDomain_toDomain (x : BoundaryAnchoredInfinityFreeDomain a m l u o) :
    x.toDomain.toFreeDomain = x := Subtype.ext x.freeCoordinates_toDomain

@[simp] theorem toDomain_toFreeDomain (x : BoundaryAnchoredInfinityDomain a m l u o) :
    x.toFreeDomain.toDomain = x := by
  apply Subtype.ext
  apply Prod.ext
  · apply BoundaryAnchoredInfinityData.coords_injective
    exact x.toFreeDomain.datum_parameters.trans x.freeCoordinates_parameters
  · rfl

end BoundaryAnchoredInfinityFreeDomain

def boundaryAnchoredInfinityFreeHomeomorph {n m : ℕ} {a : Fin n} {l u : Fin (m + 1)} {o : Fin m} :
    BoundaryAnchoredInfinityFreeDomain a m l u o ≃ₜ BoundaryAnchoredInfinityDomain a m l u o where
  toFun := BoundaryAnchoredInfinityFreeDomain.toDomain
  invFun := BoundaryAnchoredInfinityDomain.toFreeDomain
  left_inv := BoundaryAnchoredInfinityFreeDomain.toFreeDomain_toDomain
  right_inv := BoundaryAnchoredInfinityFreeDomain.toDomain_toFreeDomain
  continuous_toFun := BoundaryAnchoredInfinityFreeDomain.continuous_toDomain
  continuous_invFun := BoundaryAnchoredInfinityDomain.continuous_toFreeDomain

end EnvelopingIsomorphism.Deformation.Kontsevich
