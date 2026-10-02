import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterFreeCoordinates

/-! The actual free-coordinate homeomorphism for a pure boundary cluster,
with both fixed endpoint shape coordinates eliminated. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration Topology

namespace PureBoundaryClusterFreeDomain

variable {n m : ℕ} {i : Fin n} {l u : Fin (m + 1)} {a b : Fin m}

def datum (x : PureBoundaryClusterFreeDomain i m l u a b) : PureBoundaryClusterData i m l u a b :=
  x.val.toDatum l u x.property.2

@[simp] theorem datum_parameters (x : PureBoundaryClusterFreeDomain i m l u a b) :
    x.datum.coordinates = x.val.parameters l u := x.val.toDatum_parameters l u x.property.2

@[simp] theorem datum_center (x : PureBoundaryClusterFreeDomain i m l u a b) :
    x.datum.center = x.val.center := congrArg Prod.fst x.datum_parameters

@[simp] theorem datum_interior (x : PureBoundaryClusterFreeDomain i m l u a b) (j : Fin n) :
    (x.datum.interior j : ℂ) = x.val.interior j :=
  congrArg (fun y : PureBoundaryClusterParameterSpace n m => y.2.1 j) x.datum_parameters

@[simp] theorem datum_boundaryBase (x : PureBoundaryClusterFreeDomain i m l u a b) (j : Fin m) :
    x.datum.boundaryBase j = x.val.boundaryBase l u j :=
  congrArg (fun y : PureBoundaryClusterParameterSpace n m => y.2.2.1 j) x.datum_parameters

@[simp] theorem datum_boundaryVelocity (x : PureBoundaryClusterFreeDomain i m l u a b) (j : Fin m) :
    x.datum.boundaryVelocity j = x.val.boundaryVelocity l u j :=
  congrArg (fun y : PureBoundaryClusterParameterSpace n m => y.2.2.2 j) x.datum_parameters

@[fun_prop] theorem continuous_datum :
    Continuous (datum : PureBoundaryClusterFreeDomain i m l u a b → _) := by
  apply PureBoundaryClusterData.isEmbedding_coordinates.isInducing.continuous_iff.mpr
  simp only [Function.comp_def, datum_parameters]
  exact (PureBoundaryClusterFreeCoordinates.continuous_parameters l u).comp continuous_subtype_val

theorem datum_admissible (x : PureBoundaryClusterFreeDomain i m l u a b) :
    x.datum.AdmissibleScale x.val.radius := by
  refine ⟨x.property.1, fun j k hjk hblock => ?_⟩
  simpa only [datum_boundaryBase, datum_boundaryVelocity] using x.property.2.2 j k hjk hblock

def toDomain (x : PureBoundaryClusterFreeDomain i m l u a b) : PureBoundaryClusterDomain i m l u a b :=
  ⟨(x.datum, x.val.radius), x.datum_admissible⟩

@[simp] theorem toDomain_center (x : PureBoundaryClusterFreeDomain i m l u a b) :
    x.toDomain.datum.center = x.val.center := x.datum_center

@[simp] theorem toDomain_interior (x : PureBoundaryClusterFreeDomain i m l u a b) (j : Fin n) :
    (x.toDomain.datum.interior j : ℂ) = x.val.interior j := x.datum_interior j

@[simp] theorem toDomain_boundaryBase (x : PureBoundaryClusterFreeDomain i m l u a b) (j : Fin m) :
    x.toDomain.datum.boundaryBase j = x.val.boundaryBase l u j := x.datum_boundaryBase j

@[simp] theorem toDomain_boundaryVelocity (x : PureBoundaryClusterFreeDomain i m l u a b) (j : Fin m) :
    x.toDomain.datum.boundaryVelocity j = x.val.boundaryVelocity l u j := x.datum_boundaryVelocity j

@[simp] theorem toDomain_scale (x : PureBoundaryClusterFreeDomain i m l u a b) :
    x.toDomain.scale = x.val.radius := rfl

@[fun_prop] theorem continuous_toDomain :
    Continuous (toDomain : PureBoundaryClusterFreeDomain i m l u a b → _) :=
  (continuous_datum.prodMk
    (PureBoundaryClusterFreeCoordinates.continuous_radius.comp continuous_subtype_val)).subtype_mk _

@[simp] theorem normalized_interior (x : PureBoundaryClusterFreeDomain i m l u a b)
    (hr : 0 < x.val.radius) (j : Fin n) :
    ((x.datum.normalized (x.datum_admissible.isSafeScale hr) hr le_rfl).val.interior j : ℂ) =
      x.val.interior j := x.datum_interior j

@[simp] theorem normalized_boundary (x : PureBoundaryClusterFreeDomain i m l u a b)
    (hr : 0 < x.val.radius) (j : Fin m) :
    (x.datum.normalized (x.datum_admissible.isSafeScale hr) hr le_rfl).val.boundary j =
      x.val.scaledBoundary l u j := by
  rw [PureBoundaryClusterData.normalized_boundary, datum_boundaryBase, datum_boundaryVelocity]
  rfl

end PureBoundaryClusterFreeDomain

namespace PureBoundaryClusterDomain

variable {n m : ℕ} {i : Fin n} {l u : Fin (m + 1)} {a b : Fin m}

/-- Read the genuinely free coordinates from the primitive datum and radius. -/
def freeCoordinates (x : PureBoundaryClusterDomain i m l u a b) : PureBoundaryClusterFreeCoordinates i m a b :=
  (fun j => (x.datum.interior j.val : ℂ),
    fun j => if j.val ∈ boundaryClusterBlock l u then x.datum.boundaryVelocity j.val else x.datum.boundaryBase j.val,
    x.datum.center, x.scale)

@[simp] theorem freeCoordinates_center (x : PureBoundaryClusterDomain i m l u a b) :
    x.freeCoordinates.center = x.datum.center := rfl

@[simp] theorem freeCoordinates_radius (x : PureBoundaryClusterDomain i m l u a b) :
    x.freeCoordinates.radius = x.scale := rfl

@[simp] theorem freeCoordinates_interior (x : PureBoundaryClusterDomain i m l u a b) (j : Fin n) :
    x.freeCoordinates.interior j = (x.datum.interior j : ℂ) := by
  unfold PureBoundaryClusterFreeCoordinates.interior
  split_ifs with hj
  · subst j
    simpa using (congrArg (fun z : UpperHalfPlane => (z : ℂ)) x.datum.interior_normalized).symm
  · rfl

@[simp] theorem freeCoordinates_boundaryCoordinate (x : PureBoundaryClusterDomain i m l u a b) (j : Fin m) :
    x.freeCoordinates.boundaryCoordinate j =
      if j ∈ boundaryClusterBlock l u then x.datum.boundaryVelocity j else x.datum.boundaryBase j := by
  unfold PureBoundaryClusterFreeCoordinates.boundaryCoordinate
  by_cases hja : j = a
  · subst j
    rw [dif_pos rfl, if_pos x.datum.left_mem, x.datum.boundaryVelocity_left]
  · by_cases hjb : j = b
    · subst j
      rw [dif_neg hja, dif_pos rfl, if_pos x.datum.right_mem, x.datum.boundaryVelocity_right]
    · rw [dif_neg hja, dif_neg hjb]
      rfl

@[simp] theorem freeCoordinates_boundaryBase (x : PureBoundaryClusterDomain i m l u a b) (j : Fin m) :
    x.freeCoordinates.boundaryBase l u j = x.datum.boundaryBase j := by
  unfold PureBoundaryClusterFreeCoordinates.boundaryBase
  by_cases hj : j ∈ boundaryClusterBlock l u
  · rw [if_pos hj, freeCoordinates_center]
    exact (x.datum.boundaryBase_eq_center j hj).symm
  · rw [if_neg hj, freeCoordinates_boundaryCoordinate, if_neg hj]

@[simp] theorem freeCoordinates_boundaryVelocity (x : PureBoundaryClusterDomain i m l u a b) (j : Fin m) :
    x.freeCoordinates.boundaryVelocity l u j = x.datum.boundaryVelocity j := by
  unfold PureBoundaryClusterFreeCoordinates.boundaryVelocity
  by_cases hj : j ∈ boundaryClusterBlock l u
  · rw [if_pos hj, freeCoordinates_boundaryCoordinate, if_pos hj]
  · rw [if_neg hj]
    exact (x.datum.boundaryVelocity_zero_off j hj).symm

@[simp] theorem freeCoordinates_parameters (x : PureBoundaryClusterDomain i m l u a b) :
    x.freeCoordinates.parameters l u = x.datum.coordinates :=
  Prod.ext x.freeCoordinates_center (Prod.ext (funext x.freeCoordinates_interior)
    (Prod.ext (funext x.freeCoordinates_boundaryBase) (funext x.freeCoordinates_boundaryVelocity)))

theorem freeCoordinates_openConditions (x : PureBoundaryClusterDomain i m l u a b) :
    x.freeCoordinates.OpenConditions l u := by
  refine ⟨?_, fun j k hjk hblock => ?_⟩
  · rw [freeCoordinates_parameters]
    have h : x.datum.coordinates ∈ Set.range (PureBoundaryClusterData.coordinates
        (i := i) (l := l) (u := u) (a := a) (b := b)) := ⟨x.datum, rfl⟩
    rw [PureBoundaryClusterData.range_coordinates] at h
    exact h.1
  · simpa only [freeCoordinates_radius, freeCoordinates_boundaryBase, freeCoordinates_boundaryVelocity,
      datum, scale] using x.property.boundary_separation j k hjk hblock

def toFreeDomain (x : PureBoundaryClusterDomain i m l u a b) : PureBoundaryClusterFreeDomain i m l u a b :=
  ⟨x.freeCoordinates, x.property.nonneg, x.freeCoordinates_openConditions⟩

@[fun_prop] theorem continuous_freeCoordinates :
    Continuous (freeCoordinates : PureBoundaryClusterDomain i m l u a b → _) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro j
    exact (PureBoundaryClusterData.continuous_interior_apply j.val).comp continuous_datum
  · apply Continuous.prodMk
    · apply continuous_pi
      intro j
      by_cases hj : j.val ∈ boundaryClusterBlock l u
      · simp only [if_pos hj]
        exact (PureBoundaryClusterData.continuous_boundaryVelocity_apply j.val).comp continuous_datum
      · simp only [if_neg hj]
        exact (PureBoundaryClusterData.continuous_boundaryBase_apply j.val).comp continuous_datum
    · exact ((PureBoundaryClusterData.continuous_center).comp continuous_datum).prodMk continuous_scale

@[fun_prop] theorem continuous_toFreeDomain :
    Continuous (toFreeDomain : PureBoundaryClusterDomain i m l u a b → _) :=
  continuous_freeCoordinates.subtype_mk _

end PureBoundaryClusterDomain

namespace PureBoundaryClusterFreeDomain

variable {n m : ℕ} {i : Fin n} {l u : Fin (m + 1)} {a b : Fin m}

@[simp] theorem freeCoordinates_toDomain (x : PureBoundaryClusterFreeDomain i m l u a b) :
    x.toDomain.freeCoordinates = x.val := by
  apply Prod.ext
  · funext j
    change (x.toDomain.datum.interior j.val : ℂ) = x.val.1 j
    rw [toDomain_interior, PureBoundaryClusterFreeCoordinates.interior_free]
  · apply Prod.ext
    · funext j
      change (if j.val ∈ boundaryClusterBlock l u then x.toDomain.datum.boundaryVelocity j.val
        else x.toDomain.datum.boundaryBase j.val) = x.val.2.1 j
      by_cases hj : j.val ∈ boundaryClusterBlock l u
      · rw [if_pos hj, toDomain_boundaryVelocity, PureBoundaryClusterFreeCoordinates.boundaryVelocity,
          if_pos hj, PureBoundaryClusterFreeCoordinates.boundaryCoordinate_free]
      · rw [if_neg hj, toDomain_boundaryBase, PureBoundaryClusterFreeCoordinates.boundaryBase,
          if_neg hj, PureBoundaryClusterFreeCoordinates.boundaryCoordinate_free]
    · exact Prod.ext x.toDomain_center rfl

@[simp] theorem toFreeDomain_toDomain (x : PureBoundaryClusterFreeDomain i m l u a b) :
    x.toDomain.toFreeDomain = x := Subtype.ext x.freeCoordinates_toDomain

@[simp] theorem toDomain_toFreeDomain (x : PureBoundaryClusterDomain i m l u a b) :
    x.toFreeDomain.toDomain = x := by
  apply Subtype.ext
  apply Prod.ext
  · apply PureBoundaryClusterData.coordinates_injective
    exact x.toFreeDomain.datum_parameters.trans x.freeCoordinates_parameters
  · rfl

end PureBoundaryClusterFreeDomain

/-- The actual admissible free half-space domain is homeomorphic to the native cluster domain. -/
def pureBoundaryClusterFreeHomeomorph {n m : ℕ} {i : Fin n} {l u : Fin (m + 1)} {a b : Fin m} :
    PureBoundaryClusterFreeDomain i m l u a b ≃ₜ PureBoundaryClusterDomain i m l u a b where
  toFun := PureBoundaryClusterFreeDomain.toDomain
  invFun := PureBoundaryClusterDomain.toFreeDomain
  left_inv := PureBoundaryClusterFreeDomain.toFreeDomain_toDomain
  right_inv := PureBoundaryClusterFreeDomain.toDomain_toFreeDomain
  continuous_toFun := PureBoundaryClusterFreeDomain.continuous_toDomain
  continuous_invFun := PureBoundaryClusterDomain.continuous_toFreeDomain

end EnvelopingIsomorphism.Deformation.Kontsevich
