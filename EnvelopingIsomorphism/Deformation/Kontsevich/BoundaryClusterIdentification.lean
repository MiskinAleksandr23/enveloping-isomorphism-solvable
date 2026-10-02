import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterPhase
import EnvelopingIsomorphism.Deformation.Kontsevich.ReferenceNormIdentification

/-! Identification of a finite real cluster from actual compact coordinates.
The normalized anchor has shape coordinate `I`; its conjugate has coordinate
`-I`. Their distance two gives a fixed reference for recovering every shape
coordinate, including every external label in the collapsing boundary block. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration ComplexConjugate

namespace BoundaryClusterData

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

def shapeTriple (a : Fin n) (v : Fin n ⊕ Fin m) : DoubledTriple n m :=
  ⟨(Sum.inr a, Sum.inl v, Sum.inl (Sum.inl a)), by simp⟩

theorem resolvedCoordinates_anchor (D : BoundaryClusterData i a m S l u) (r : ℝ) :
    (D.resolvedCoordinates r).1 (Sum.inl a) =
      (((D.center : ℂ) + (r : ℂ) * Complex.I : ℂ) : OnePoint ℂ) := by
  simp only [resolvedCoordinates, doubledBase, doubledVelocity,
    D.base_eq_center a D.anchor_mem, D.velocity_anchor]

theorem shape_pairBase (D : BoundaryClusterData i a m S l u) (v : Fin n ⊕ Fin m)
    (hbase : D.baseVertex v = (D.center : ℂ)) :
    D.pairBase (harmonicDenominatorPair a v) = 0 := by
  change D.baseVertex v - conj (D.base a) = 0
  rw [hbase, D.base_eq_center a D.anchor_mem, Complex.conj_ofReal, sub_self]

/-- The pair from the conjugate anchor retains the direction of `shape + I`, at every scale. -/
theorem resolvedCoordinates_shape_direction (D : BoundaryClusterData i a m S l u) (r : ℝ)
    (v : Fin n ⊕ Fin m) (hbase : D.baseVertex v = (D.center : ℂ)) :
    (D.resolvedCoordinates r).2.1 (harmonicDenominatorPair a v) =
      complexPhase (D.velocityVertex v + Complex.I) := by
  change (if D.pairBase _ = 0 then _ else _) = _
  rw [if_pos (D.shape_pairBase v hbase)]
  change complexPhase (D.velocityVertex v - conj (D.velocity a)) = _
  rw [D.velocity_anchor, Complex.conj_I, sub_neg_eq_add]

/-- The reference doubled-anchor distance is exactly two. -/
theorem resolvedCoordinates_shape_ratio (D : BoundaryClusterData i a m S l u) (r : ℝ)
    (v : Fin n ⊕ Fin m) (hbase : D.baseVertex v = (D.center : ℂ)) :
    ((D.resolvedCoordinates r).2.2 (shapeTriple a v) : ℝ) =
      referenceNormRatio 2 (D.velocityVertex v + Complex.I) := by
  have ha : D.baseVertex (Sum.inl a) = (D.center : ℂ) := D.base_eq_center a D.anchor_mem
  change ((if D.pairBase _ = 0 ∧ D.pairBase _ = 0 then _ else _) : Set.Icc (0 : ℝ) 1).val = _
  rw [if_pos ⟨D.shape_pairBase v hbase, D.shape_pairBase (Sum.inl a) ha⟩]
  change ‖D.velocityVertex v - conj (D.velocity a)‖ /
      (‖D.velocityVertex v - conj (D.velocity a)‖ + ‖D.velocity a - conj (D.velocity a)‖) = _
  rw [D.velocity_anchor, Complex.conj_I, sub_neg_eq_add, sub_neg_eq_add]
  have hn : ‖Complex.I + Complex.I‖ = (2 : ℝ) := by
    rw [← two_mul, norm_mul]
    norm_num
  rw [hn]
  rfl

theorem resolvedCoordinates_shape_ratio_lt_one (D : BoundaryClusterData i a m S l u) (r : ℝ)
    (v : Fin n ⊕ Fin m) (hbase : D.baseVertex v = (D.center : ℂ)) :
    ((D.resolvedCoordinates r).2.2 (shapeTriple a v) : ℝ) < 1 := by
  rw [D.resolvedCoordinates_shape_ratio r v hbase]
  exact referenceNormRatio_lt_one (by norm_num) _

/-- Uniform shape identification is valid at zero as well as at positive scale. -/
theorem recover_shape (D : BoundaryClusterData i a m S l u) (r : ℝ)
    (v : Fin n ⊕ Fin m) (hbase : D.baseVertex v = (D.center : ℂ)) :
    (2 : ℂ) * recoverRelativePosition
      ((D.resolvedCoordinates r).2.1 (harmonicDenominatorPair a v))
      ((D.resolvedCoordinates r).2.2 (shapeTriple a v)) - Complex.I = D.velocityVertex v := by
  rw [D.resolvedCoordinates_shape_direction r v hbase, D.resolvedCoordinates_shape_ratio r v hbase,
    show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_num,
    recoverRelativePosition_referenceNormRatio (by norm_num), add_sub_cancel_right]

theorem velocityVertex_eq_of_coordinates_eq {D E : BoundaryClusterData i a m S l u} {r s : ℝ}
    (h : D.resolvedCoordinates r = E.resolvedCoordinates s) (v : Fin n ⊕ Fin m)
    (hD : D.baseVertex v = (D.center : ℂ)) (hE : E.baseVertex v = (E.center : ℂ)) :
    D.velocityVertex v = E.velocityVertex v := by
  rw [← D.recover_shape r v hD, ← E.recover_shape s v hE, h]

theorem velocity_eq_of_coordinates_eq {D E : BoundaryClusterData i a m S l u} {r s : ℝ}
    (h : D.resolvedCoordinates r = E.resolvedCoordinates s) : D.velocity = E.velocity := by
  funext j
  by_cases hj : j ∈ S
  · exact velocityVertex_eq_of_coordinates_eq h (Sum.inl j)
      (D.base_eq_center j hj) (E.base_eq_center j hj)
  · rw [D.velocity_zero_off j hj, E.velocity_zero_off j hj]

theorem boundaryVelocity_eq_of_coordinates_eq {D E : BoundaryClusterData i a m S l u} {r s : ℝ}
    (h : D.resolvedCoordinates r = E.resolvedCoordinates s) : D.boundaryVelocity = E.boundaryVelocity := by
  funext j
  by_cases hj : j ∈ boundaryClusterBlock l u
  · apply Complex.ofReal_injective
    exact velocityVertex_eq_of_coordinates_eq h (Sum.inr j)
      (congrArg Complex.ofReal (D.boundaryBase_eq_center j hj))
      (congrArg Complex.ofReal (E.boundaryBase_eq_center j hj))
  · rw [D.boundaryVelocity_zero_off j hj, E.boundaryVelocity_zero_off j hj]

theorem center_scale_eq_of_coordinates_eq {D E : BoundaryClusterData i a m S l u} {r s : ℝ}
    (h : D.resolvedCoordinates r = E.resolvedCoordinates s) : D.center = E.center ∧ r = s := by
  have hz := congrArg (fun z : CompactCoordinateSpace n m => z.1 (Sum.inl a)) h
  rw [D.resolvedCoordinates_anchor, E.resolvedCoordinates_anchor] at hz
  have he := OnePoint.coe_injective hz
  constructor
  · simpa using congrArg Complex.re he
  · simpa using congrArg Complex.im he

theorem base_eq_of_coordinates_eq {D E : BoundaryClusterData i a m S l u} {r s : ℝ}
    (h : D.resolvedCoordinates r = E.resolvedCoordinates s) : D.base = E.base := by
  have hr := (center_scale_eq_of_coordinates_eq h).2
  have hv := velocity_eq_of_coordinates_eq h
  funext j
  have he := OnePoint.coe_injective
    (congrArg (fun z : CompactCoordinateSpace n m => z.1 (Sum.inl j)) h)
  change D.base j + (r : ℂ) * D.velocity j = E.base j + (s : ℂ) * E.velocity j at he
  rw [hr, hv] at he
  exact add_right_cancel he

theorem boundaryBase_eq_of_coordinates_eq {D E : BoundaryClusterData i a m S l u} {r s : ℝ}
    (h : D.resolvedCoordinates r = E.resolvedCoordinates s) : D.boundaryBase = E.boundaryBase := by
  have hr := (center_scale_eq_of_coordinates_eq h).2
  have hv := boundaryVelocity_eq_of_coordinates_eq h
  funext j
  have he := OnePoint.coe_injective
    (congrArg (fun z : CompactCoordinateSpace n m => z.1 (Sum.inr j)) h)
  change (D.boundaryBase j : ℂ) + (r : ℂ) * (D.boundaryVelocity j : ℂ) =
    (E.boundaryBase j : ℂ) + (s : ℂ) * (E.boundaryVelocity j : ℂ) at he
  rw [hr, hv] at he
  exact Complex.ofReal_injective (add_right_cancel he)

end BoundaryClusterData

end EnvelopingIsomorphism.Deformation.Kontsevich
