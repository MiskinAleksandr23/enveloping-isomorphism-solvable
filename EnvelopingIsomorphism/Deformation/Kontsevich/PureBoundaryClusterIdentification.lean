import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterCompactification
import EnvelopingIsomorphism.Deformation.Kontsevich.RelativeCoordinateIdentification

/-! Actual parameter identification at every radius for a pure external cluster.
The boundary endpoints recover center/radius, and a collapsing pair with the
endpoint reference of shape length one recovers every non-anchor shape value. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration

namespace PureBoundaryClusterData

variable {n m : ℕ} {i : Fin n} {l u : Fin (m + 1)} {a b : Fin m}

def shapePair (a j : Fin m) (hja : j ≠ a) : DoubledPair n m :=
  ⟨(Sum.inl (Sum.inr a), Sum.inl (Sum.inr j)),
    fun h => hja (Sum.inr.inj (Sum.inl.inj h)).symm⟩

def shapeTriple (a b j : Fin m) (hja : j ≠ a) (hba : b ≠ a) : DoubledTriple n m :=
  ⟨(Sum.inl (Sum.inr a), Sum.inl (Sum.inr j), Sum.inl (Sum.inr b)),
    (shapePair (n := n) a j hja).property, (shapePair (n := n) a b hba).property⟩

theorem resolvedCoordinates_interior (D : PureBoundaryClusterData i m l u a b) (r : ℝ)
    (j : Fin n) : (D.resolvedCoordinates r).1 (Sum.inl j) = ((D.interior j : ℂ) : OnePoint ℂ) := by
  simp [resolvedCoordinates, doubledBase, doubledVelocity]

theorem resolvedCoordinates_boundary (D : PureBoundaryClusterData i m l u a b) (r : ℝ)
    (j : Fin m) : (D.resolvedCoordinates r).1 (Sum.inr j) =
      ((D.scaledBoundary r j : ℂ) : OnePoint ℂ) := by
  simp [resolvedCoordinates, doubledBase, doubledVelocity, scaledBoundary]

theorem shape_pairBase (D : PureBoundaryClusterData i m l u a b) (j : Fin m)
    (hj : j ∈ boundaryClusterBlock l u) (hja : j ≠ a) : D.pairBase (shapePair a j hja) = 0 := by
  change (D.boundaryBase j : ℂ) - (D.boundaryBase a : ℂ) = 0
  rw [D.boundaryBase_eq_center j hj, D.boundaryBase_eq_center a D.left_mem, sub_self]

theorem resolvedCoordinates_shape_direction (D : PureBoundaryClusterData i m l u a b) (r : ℝ)
    (j : Fin m) (hj : j ∈ boundaryClusterBlock l u) (hja : j ≠ a) :
    (D.resolvedCoordinates r).2.1 (shapePair a j hja) = complexPhase (D.boundaryVelocity j : ℂ) := by
  change (if D.pairBase _ = 0 then _ else _) = _
  rw [if_pos (D.shape_pairBase j hj hja)]
  change complexPhase ((D.boundaryVelocity j : ℂ) - (D.boundaryVelocity a : ℂ)) = _
  rw [D.boundaryVelocity_left, Complex.ofReal_zero, sub_zero]

theorem resolvedCoordinates_shape_ratio (D : PureBoundaryClusterData i m l u a b) (r : ℝ)
    (j : Fin m) (hj : j ∈ boundaryClusterBlock l u) (hja : j ≠ a) (hba : b ≠ a) :
    ((D.resolvedCoordinates r).2.2 (shapeTriple a b j hja hba) : ℝ) =
      unitNormRatio (D.boundaryVelocity j : ℂ) := by
  change ((if D.pairBase _ = 0 ∧ D.pairBase _ = 0 then _ else _) : Set.Icc (0 : ℝ) 1).val = _
  rw [if_pos ⟨D.shape_pairBase j hj hja, D.shape_pairBase b D.right_mem hba⟩]
  change ‖(D.boundaryVelocity j : ℂ) - (D.boundaryVelocity a : ℂ)‖ /
    (‖(D.boundaryVelocity j : ℂ) - (D.boundaryVelocity a : ℂ)‖ +
      ‖(D.boundaryVelocity b : ℂ) - (D.boundaryVelocity a : ℂ)‖) = _
  simp only [D.boundaryVelocity_left, D.boundaryVelocity_right, Complex.ofReal_zero,
    Complex.ofReal_one, sub_zero, norm_one, unitNormRatio]

theorem resolvedCoordinates_shape_ratio_lt_one (D : PureBoundaryClusterData i m l u a b) (r : ℝ)
    (j : Fin m) (hj : j ∈ boundaryClusterBlock l u) (hja : j ≠ a) (hba : b ≠ a) :
    ((D.resolvedCoordinates r).2.2 (shapeTriple a b j hja hba) : ℝ) < 1 := by
  rw [D.resolvedCoordinates_shape_ratio r j hj hja hba]
  exact unitNormRatio_lt_one _

theorem recover_shape (D : PureBoundaryClusterData i m l u a b) (r : ℝ)
    (j : Fin m) (hj : j ∈ boundaryClusterBlock l u) (hja : j ≠ a) (hba : b ≠ a) :
    recoverRelativePosition ((D.resolvedCoordinates r).2.1 (shapePair a j hja))
      ((D.resolvedCoordinates r).2.2 (shapeTriple a b j hja hba)) = (D.boundaryVelocity j : ℂ) := by
  rw [D.resolvedCoordinates_shape_direction r j hj hja,
    D.resolvedCoordinates_shape_ratio r j hj hja hba, recoverRelativePosition_phase_ratio]

theorem boundaryVelocity_eq_of_coordinates_eq {D E : PureBoundaryClusterData i m l u a b} {r s : ℝ}
    (h : D.resolvedCoordinates r = E.resolvedCoordinates s) : D.boundaryVelocity = E.boundaryVelocity := by
  funext j
  by_cases hj : j ∈ boundaryClusterBlock l u
  · by_cases hja : j = a
    · simp only [hja, D.boundaryVelocity_left, E.boundaryVelocity_left]
    · apply Complex.ofReal_injective
      rw [← D.recover_shape r j hj hja D.endpoint_lt.ne',
        ← E.recover_shape s j hj hja D.endpoint_lt.ne', h]
  · rw [D.boundaryVelocity_zero_off j hj, E.boundaryVelocity_zero_off j hj]

theorem scaledBoundary_eq_of_coordinates_eq {D E : PureBoundaryClusterData i m l u a b} {r s : ℝ}
    (h : D.resolvedCoordinates r = E.resolvedCoordinates s) (j : Fin m) :
    D.scaledBoundary r j = E.scaledBoundary s j := by
  apply Complex.ofReal_injective
  apply OnePoint.coe_injective
  simpa only [resolvedCoordinates_boundary] using
    congrArg (fun z : CompactCoordinateSpace n m => z.1 (Sum.inr j)) h

theorem center_scale_eq_of_coordinates_eq {D E : PureBoundaryClusterData i m l u a b} {r s : ℝ}
    (h : D.resolvedCoordinates r = E.resolvedCoordinates s) : D.center = E.center ∧ r = s := by
  have hleft := scaledBoundary_eq_of_coordinates_eq h a
  have hright := scaledBoundary_eq_of_coordinates_eq h b
  rw [D.scaledBoundary_left, E.scaledBoundary_left] at hleft
  rw [D.scaledBoundary_right, E.scaledBoundary_right, hleft] at hright
  exact ⟨hleft, add_left_cancel hright⟩

theorem interior_eq_of_coordinates_eq {D E : PureBoundaryClusterData i m l u a b} {r s : ℝ}
    (h : D.resolvedCoordinates r = E.resolvedCoordinates s) : D.interior = E.interior := by
  funext j
  apply UpperHalfPlane.ext
  apply OnePoint.coe_injective
  simpa only [resolvedCoordinates_interior] using
    congrArg (fun z : CompactCoordinateSpace n m => z.1 (Sum.inl j)) h

theorem boundaryBase_eq_of_coordinates_eq {D E : PureBoundaryClusterData i m l u a b} {r s : ℝ}
    (h : D.resolvedCoordinates r = E.resolvedCoordinates s) : D.boundaryBase = E.boundaryBase := by
  have hr := (center_scale_eq_of_coordinates_eq h).2
  have hv := boundaryVelocity_eq_of_coordinates_eq h
  funext j
  have he := scaledBoundary_eq_of_coordinates_eq h j
  unfold scaledBoundary at he
  rw [hr, hv] at he
  exact add_right_cancel he

/-- The zero-radius point is a genuine new boundary point: the two distinct
endpoint labels have identical finite positions. -/
theorem boundaryPoint_not_mem_range (D : PureBoundaryClusterData i m l u a b) :
    D.boundaryPoint ∉ Set.range (compactificationEmbedding i :
      Normalized i m → Compactification i m) := by
  rintro ⟨c, hc⟩
  have he (j : Fin m) : c.val.boundary j = D.scaledBoundary 0 j := by
    apply Complex.ofReal_injective
    apply OnePoint.coe_injective
    have h := congrArg (fun z : Compactification i m => z.val.1 (Sum.inr j)) hc
    simpa only [compactificationEmbedding, compactCoordinates, compactPositions, vertexPoint,
      Sum.elim_inr, boundaryPoint, compactInsertion, resolvedCoordinates_boundary] using h
  have hab : c.val.boundary a = c.val.boundary b := by
    rw [he a, he b, D.scaledBoundary_left, D.scaledBoundary_right, add_zero]
  exact D.endpoint_lt.ne (c.val.boundary_strictMono.injective hab)

end PureBoundaryClusterData

end EnvelopingIsomorphism.Deformation.Kontsevich
