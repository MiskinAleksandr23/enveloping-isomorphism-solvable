import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterCoordinateModel
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterFreeCoordinateEquiv
import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterInsertionCoordinates
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Original-label coordinates for an actual finite real-cluster insertion. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealClusterInsertionCoordinates

open Configuration

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)}

abbrev FreeIndex (i : Fin n) := InteriorClusterInsertionCoordinates.FreeIndex i
abbrev FreeCoordinates (i : Fin n) (m : ℕ) := InteriorClusterInsertionCoordinates.FreeCoordinates i m
abbrev LabelIndex (i a : Fin n) (S : Finset (Fin n)) :=
  BoundaryClusterCoarseIndex i S ⊕ BoundaryClusterShapeIndex a S ⊕ Unit

theorem anchor_ne_global (ha : a ∈ S) (hi : i ∉ S) : a ≠ i := by
  intro h
  exact hi (h ▸ ha)

theorem shape_ne_global (hi : i ∉ S) (j : BoundaryClusterShapeIndex a S) : j.val ≠ i := by
  intro h
  exact hi (h ▸ j.property.1)

/-- The explicit label partition, retaining the original label on every summand. -/
def labelEquiv (ha : a ∈ S) (hi : i ∉ S) : LabelIndex i a S ≃ FreeIndex i where
  toFun
    | .inl j => ⟨j.val, j.property.2⟩
    | .inr (.inl j) => ⟨j.val, shape_ne_global hi j⟩
    | .inr (.inr _) => ⟨a, anchor_ne_global ha hi⟩
  invFun j := if hj : j.val ∉ S then .inl ⟨j.val, hj, j.property⟩
    else if hja : j.val = a then .inr (.inr ())
    else .inr (.inl ⟨j.val, by tauto, hja⟩)
  left_inv j := by
    rcases j with j | j | u
    · simp only [dif_pos j.property.1]; rfl
    · simp only [dif_neg (not_not.mpr j.property.1), dif_neg j.property.2]; rfl
    · cases u; simp [ha]
  right_inv j := by
    apply Subtype.ext
    dsimp
    split_ifs <;> simp_all

@[simp] theorem labelEquiv_coarse (ha : a ∈ S) (hi : i ∉ S)
    (j : BoundaryClusterCoarseIndex i S) :
    labelEquiv ha hi (.inl j) = ⟨j.val, j.property.2⟩ := rfl

@[simp] theorem labelEquiv_shape (ha : a ∈ S) (hi : i ∉ S)
    (j : BoundaryClusterShapeIndex a S) :
    labelEquiv ha hi (.inr (.inl j)) = ⟨j.val, shape_ne_global hi j⟩ := rfl

@[simp] theorem labelEquiv_anchor (ha : a ∈ S) (hi : i ∉ S) :
    labelEquiv ha hi (.inr (.inr ())) = ⟨a, anchor_ne_global ha hi⟩ := rfl

/-- Output coordinates: coarse pairs, shape pairs, boundaries, anchor real
part, anchor imaginary part.  The inverse uses the explicit label partition. -/
def outputCoordinates (ha : a ∈ S) (hi : i ∉ S) :
    FreeCoordinates i m ≃L[ℝ] BoundaryClusterFreeCoordinates i a S m :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun z =>
      (fun j => z.1 ⟨j.val, j.property.2⟩,
       fun j => z.1 ⟨j.val, shape_ne_global hi j⟩,
       z.2, (z.1 ⟨a, anchor_ne_global ha hi⟩).re,
       (z.1 ⟨a, anchor_ne_global ha hi⟩).im)
    invFun := fun x =>
      (fun j => match (labelEquiv ha hi).symm j with
        | .inl q => x.1 q
        | .inr (.inl q) => x.2.1 q
        | .inr (.inr _) => Complex.equivRealProdCLM.symm x.2.2.2,
       x.2.2.1)
    left_inv := by
      intro z
      apply Prod.ext
      · funext j
        obtain ⟨j, rfl⟩ := (labelEquiv ha hi).surjective j
        rcases j with j | j | u
        · simp only [Equiv.symm_apply_apply]; rfl
        · simp only [Equiv.symm_apply_apply]; rfl
        · simp only [Equiv.symm_apply_apply]
          exact Complex.equivRealProdCLM.symm_apply_apply _
      · rfl
    right_inv := by
      intro x
      apply Prod.ext
      · funext j
        change (match (labelEquiv ha hi).symm
          (labelEquiv ha hi (.inl j)) with
          | .inl q => x.1 q
          | .inr (.inl q) => x.2.1 q
          | .inr (.inr _) => Complex.equivRealProdCLM.symm x.2.2.2) = x.1 j
        simp only [Equiv.symm_apply_apply]
      · apply Prod.ext
        · funext j
          change (match (labelEquiv ha hi).symm
            (labelEquiv ha hi (.inr (.inl j))) with
            | .inl q => x.1 q
            | .inr (.inl q) => x.2.1 q
            | .inr (.inr _) => Complex.equivRealProdCLM.symm x.2.2.2) = x.2.1 j
          simp only [Equiv.symm_apply_apply]
        · apply Prod.ext
          · rfl
          · change Complex.equivRealProdCLM
              (match (labelEquiv ha hi).symm
                (labelEquiv ha hi (.inr (.inr ()))) with
              | .inl q => x.1 q
              | .inr (.inl q) => x.2.1 q
              | .inr (.inr _) => Complex.equivRealProdCLM.symm x.2.2.2) = x.2.2.2
            simp only [Equiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]
    map_add' := by intros; rfl
    map_smul' := by intros; ext <;> simp [Complex.real_smul] }

/-- Actual positions, with the stationary global anchor omitted. -/
def insertion (l u : Fin (m + 1)) (x : BoundaryClusterFreeCoordinates i a S m) : FreeCoordinates i m :=
  (fun j => x.base j.val + (x.radius : ℂ) * x.velocity j.val,
   fun j => x.boundaryBase l u j + x.radius * x.boundaryVelocity l u j)

theorem insertion_coarse (l u : Fin (m + 1)) (x : BoundaryClusterFreeCoordinates i a S m)
    (j : BoundaryClusterCoarseIndex i S) :
    (insertion l u x).1 ⟨j.val, j.property.2⟩ = x.1 j := by
  simp [insertion, x.velocity_zero_off j.val j.property.1]

theorem insertion_shape (l u : Fin (m + 1)) (x : BoundaryClusterFreeCoordinates i a S m)
    (hi : i ∉ S) (j : BoundaryClusterShapeIndex a S) :
    (insertion l u x).1 ⟨j.val, shape_ne_global hi j⟩ =
      (x.center : ℂ) + (x.radius : ℂ) * x.2.1 j := by
  simp [insertion, x.base_eq_center j.val j.property.1]

theorem insertion_anchor (l u : Fin (m + 1)) (x : BoundaryClusterFreeCoordinates i a S m)
    (ha : a ∈ S) (hi : i ∉ S) :
    (insertion l u x).1 ⟨a, anchor_ne_global ha hi⟩ =
      (x.center : ℂ) + (x.radius : ℂ) * Complex.I := by
  simp [insertion, x.base_eq_center a ha, x.velocity_anchor ha]

theorem insertion_boundary (l u : Fin (m + 1)) (x : BoundaryClusterFreeCoordinates i a S m)
    (j : Fin m) :
    (insertion l u x).2 j =
      if j ∈ boundaryClusterBlock l u then x.center + x.radius * x.2.2.1 j else x.2.2.1 j := by
  by_cases hj : j ∈ boundaryClusterBlock l u
  · simp only [insertion, BoundaryClusterFreeCoordinates.boundaryBase,
      BoundaryClusterFreeCoordinates.boundaryVelocity, if_pos hj]
  · simp only [insertion, BoundaryClusterFreeCoordinates.boundaryBase,
      BoundaryClusterFreeCoordinates.boundaryVelocity, if_neg hj, mul_zero, add_zero]

/-- The exact native formula retains the center and radius as the two real
coordinates of the normalized interior shape anchor. -/
theorem outputCoordinates_insertion (l u : Fin (m + 1))
    (x : BoundaryClusterFreeCoordinates i a S m) (ha : a ∈ S) (hi : i ∉ S) :
    outputCoordinates ha hi (insertion l u x) =
      (x.1, fun j => (x.center : ℂ) + (x.radius : ℂ) * x.2.1 j,
       fun j => if j ∈ boundaryClusterBlock l u then x.center + x.radius * x.2.2.1 j
         else x.2.2.1 j, x.center, x.radius) := by
  apply Prod.ext
  · funext j; exact insertion_coarse l u x j
  · apply Prod.ext
    · funext j; exact insertion_shape l u x hi j
    · apply Prod.ext
      · funext j; exact insertion_boundary l u x j
      · change Complex.equivRealProdCLM ((insertion l u x).1 ⟨a, anchor_ne_global ha hi⟩) = _
        rw [insertion_anchor l u x ha hi]
        ext <;> simp

/-- On the actual geometric domain these are exactly the previously defined
scaled interior positions under the free-coordinate homeomorphism. -/
theorem insertion_toDomain_interior {l u : Fin (m + 1)}
    (x : BoundaryClusterFreeDomain i a S m l u) (j : FreeIndex i) :
    (insertion l u x.val).1 j =
      x.toDomain.datum.scaledInterior x.toDomain.scale j.val := by
  simp only [insertion, BoundaryClusterData.scaledInterior,
    BoundaryClusterFreeDomain.toDomain_scale, BoundaryClusterFreeDomain.toDomain_base,
    BoundaryClusterFreeDomain.toDomain_velocity]

/-- Exact agreement on every original real boundary label. -/
theorem insertion_toDomain_boundary {l u : Fin (m + 1)}
    (x : BoundaryClusterFreeDomain i a S m l u) (j : Fin m) :
    (insertion l u x.val).2 j =
      x.toDomain.datum.scaledBoundary x.toDomain.scale j := by
  simp only [insertion, BoundaryClusterData.scaledBoundary,
    BoundaryClusterFreeDomain.toDomain_scale, BoundaryClusterFreeDomain.toDomain_boundaryBase,
    BoundaryClusterFreeDomain.toDomain_boundaryVelocity]

end EnvelopingIsomorphism.Deformation.Kontsevich.RealClusterInsertionCoordinates
