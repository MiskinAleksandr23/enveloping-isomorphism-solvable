import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryAnchoredInfinityInsertion
import EnvelopingIsomorphism.Deformation.Kontsevich.ReferencePhaseIdentification

/-! Actual inverse-coordinate formulas for infinity data anchored by a coarse
cluster node and one outside boundary label. Radius zero is included. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryAnchoredInfinityData

open Configuration ComplexConjugate OnePoint
open scoped Topology

variable {n m : ℕ} {a : Fin n} {l u : Fin (m + 1)} {o : Fin m}

def baseVertex (D : BoundaryAnchoredInfinityData a m l u o) (v : Fin n ⊕ Fin m) : ℂ :=
  D.doubledBase (Sum.inl v)

def velocityVertex (D : BoundaryAnchoredInfinityData a m l u o) (v : Fin n ⊕ Fin m) : ℂ :=
  D.doubledVelocity (Sum.inl v)

@[simp] theorem velocityVertex_anchor (D : BoundaryAnchoredInfinityData a m l u o) :
    D.velocityVertex (Sum.inl a) = Complex.I := by
  simp only [velocityVertex, doubledVelocity, D.shape_anchor, UpperHalfPlane.coe_I]

theorem pairBase_fromAnchor (D : BoundaryAnchoredInfinityData a m l u o)
    (v : Fin n ⊕ Fin m) :
    D.pairBase (harmonicDenominatorPair a v) = D.baseVertex v := by
  change D.doubledBase (Sum.inl v) - 0 = _
  simp only [sub_zero, baseVertex]

theorem pairVelocity_fromAnchor (D : BoundaryAnchoredInfinityData a m l u o)
    (v : Fin n ⊕ Fin m) :
    D.pairVelocity (harmonicDenominatorPair a v) = D.velocityVertex v + Complex.I := by
  change D.velocityVertex v - conj (D.shape a : ℂ) = _
  rw [D.shape_anchor]
  simp

theorem outside_activeDifference (D : BoundaryAnchoredInfinityData a m l u o)
    (r : ℝ) (j : Fin m) (hj : j ∉ boundaryClusterBlock l u) :
    D.activeDifference r (harmonicDenominatorPair a (Sum.inr j)) =
      (D.boundaryBase j : ℂ) + (r : ℂ) * Complex.I := by
  rw [activeDifference, pairBase_fromAnchor, pairVelocity_fromAnchor]
  simp only [baseVertex, velocityVertex, doubledBase, doubledVelocity,
    D.boundaryVelocity_zero_off j hj, Complex.ofReal_zero, zero_add]

theorem resolvedDR_outside_direction (D : BoundaryAnchoredInfinityData a m l u o)
    (r : ℝ) (j : Fin m) (hj : j ∉ boundaryClusterBlock l u) :
    (D.resolvedDR r).1 (harmonicDenominatorPair a (Sum.inr j)) =
      complexPhase ((D.boundaryBase j : ℂ) + (r : ℂ) * Complex.I) := by
  have hp : D.pairBase (harmonicDenominatorPair a (Sum.inr j)) ≠ 0 := by
    rw [pairBase_fromAnchor]
    exact Complex.ofReal_ne_zero.mpr (fun h ↦ hj ((D.boundaryBase_eq_zero_iff j).mp h))
  change (if D.pairBase _ = 0 then _ else _) = _
  rw [if_neg hp, outside_activeDifference D r j hj]

theorem resolvedDR_reference_direction (D : BoundaryAnchoredInfinityData a m l u o) (r : ℝ) :
    (D.resolvedDR r).1 (harmonicDenominatorPair a (Sum.inr o)) =
      complexPhase ((referenceSign l o : ℂ) + (r : ℂ) * Complex.I) := by
  rw [resolvedDR_outside_direction D r o D.outside_not_mem, D.boundaryBase_anchor]

theorem resolvedDR_reference_re_ne_zero (D : BoundaryAnchoredInfinityData a m l u o) (r : ℝ) :
    ((D.resolvedDR r).1 (harmonicDenominatorPair a (Sum.inr o)) : ℂ).re ≠ 0 := by
  rw [resolvedDR_reference_direction]
  exact complexPhase_realReference_re_ne_zero (referenceSign_ne_zero l o) r

/-- The scale is recovered from one genuine stored doubled-pair direction. -/
theorem recover_scale (D : BoundaryAnchoredInfinityData a m l u o) (r : ℝ) :
    recoverReferenceHeight (referenceSign l o)
      ((D.resolvedDR r).1 (harmonicDenominatorPair a (Sum.inr o))) = r := by
  rw [resolvedDR_reference_direction, recoverReferenceHeight_phase (referenceSign_ne_zero l o)]

theorem resolvedDR_outside_ratio (D : BoundaryAnchoredInfinityData a m l u o)
    (r : ℝ) (j : Fin m) (hj : j ∉ boundaryClusterBlock l u) :
    (D.resolvedDR r).2 (boundaryRatioTriple a j o) =
      normalizedNormRatio ((D.boundaryBase j : ℂ) + (r : ℂ) * Complex.I)
        ((referenceSign l o : ℂ) + (r : ℂ) * Complex.I) := by
  have hp : D.pairBase (harmonicDenominatorPair a (Sum.inr j)) ≠ 0 := by
    rw [pairBase_fromAnchor]
    exact Complex.ofReal_ne_zero.mpr (fun h ↦ hj ((D.boundaryBase_eq_zero_iff j).mp h))
  change (if D.pairBase (harmonicDenominatorPair a (Sum.inr j)) = 0 ∧
      D.pairBase (harmonicDenominatorPair a (Sum.inr o)) = 0 then _ else _) = _
  rw [if_neg (fun h ↦ hp h.1)]
  change normalizedNormRatio (D.activeDifference r (harmonicDenominatorPair a (Sum.inr j)))
    (D.activeDifference r (harmonicDenominatorPair a (Sum.inr o))) = _
  rw [outside_activeDifference D r j hj,
    outside_activeDifference D r o D.outside_not_mem, D.boundaryBase_anchor]

theorem resolvedDR_outside_ratio_lt_one (D : BoundaryAnchoredInfinityData a m l u o)
    (r : ℝ) (j : Fin m) (hj : j ∉ boundaryClusterBlock l u) :
    ((D.resolvedDR r).2 (boundaryRatioTriple a j o) : ℝ) < 1 := by
  rw [resolvedDR_outside_ratio D r j hj]
  exact normalizedNormRatio_lt_one_right (realReference_add_mul_I_ne_zero (referenceSign_ne_zero l o) r)

/-- Every outside coarse real coordinate is recovered with a finite, nonzero reference norm. -/
theorem recover_outside_base (D : BoundaryAnchoredInfinityData a m l u o)
    (r : ℝ) (j : Fin m) (hj : j ∉ boundaryClusterBlock l u) :
    ((‖(referenceSign l o : ℂ) + (r : ℂ) * Complex.I‖ : ℂ) *
      recoverRelativePosition
        ((D.resolvedDR r).1 (harmonicDenominatorPair a (Sum.inr j)))
        ((D.resolvedDR r).2 (boundaryRatioTriple a j o))).re = D.boundaryBase j := by
  rw [resolvedDR_outside_direction D r j hj, resolvedDR_outside_ratio D r j hj,
    recoverRelativePosition_normalizedNormRatio
      (realReference_add_mul_I_ne_zero (referenceSign_ne_zero l o) r)]
  simp

theorem resolvedDR_inside_direction (D : BoundaryAnchoredInfinityData a m l u o)
    (r : ℝ) (v : Fin n ⊕ Fin m) (hv : D.baseVertex v = 0) :
    (D.resolvedDR r).1 (harmonicDenominatorPair a v) =
      complexPhase (D.velocityVertex v + Complex.I) := by
  change (if D.pairBase _ = 0 then _ else _) = _
  rw [pairBase_fromAnchor, if_pos hv, pairVelocity_fromAnchor]

theorem resolvedDR_inside_ratio (D : BoundaryAnchoredInfinityData a m l u o)
    (r : ℝ) (v : Fin n ⊕ Fin m) (hv : D.baseVertex v = 0) :
    ((D.resolvedDR r).2 (positionIdentificationTriple a v) : ℝ) =
      referenceNormRatio 2 (D.velocityVertex v + Complex.I) := by
  have ha : D.baseVertex (Sum.inl a) = 0 := rfl
  change ((if D.pairBase (harmonicDenominatorPair a v) = 0 ∧
      D.pairBase (harmonicDenominatorPair a (Sum.inl a)) = 0 then _ else _) : Set.Icc (0 : ℝ) 1).val = _
  simp only [pairBase_fromAnchor, hv, ha, and_self, ite_true]
  change ‖D.pairVelocity (harmonicDenominatorPair a v)‖ /
    (‖D.pairVelocity (harmonicDenominatorPair a v)‖ +
      ‖D.pairVelocity (harmonicDenominatorPair a (Sum.inl a))‖) = _
  simp only [pairVelocity_fromAnchor, velocityVertex_anchor]
  have hnorm : ‖Complex.I + Complex.I‖ = (2 : ℝ) := by rw [← two_mul, norm_mul]; norm_num
  rw [hnorm]
  rfl

/-- In the actual compactification, every inside point has its finite shape position, even at zero. -/
theorem compactInsertion_position_inside (D : BoundaryAnchoredInfinityData a m l u o)
    {r : ℝ} (hr : D.AdmissibleScale r) (v : Fin n ⊕ Fin m) (hv : D.baseVertex v = 0) :
    (D.compactInsertion hr).val.1 v = (D.velocityVertex v : OnePoint ℂ) := by
  rw [← compactification_position_identification a v (D.compactInsertion hr), D.compactInsertion_projectDR]
  change onePointRadialIdentificationSub 2 Complex.I
    ((D.resolvedDR r).1 (harmonicDenominatorPair a v), (D.resolvedDR r).2 (positionIdentificationTriple a v)) = _
  rw [resolvedDR_inside_direction D r v hv]
  have ht : (D.resolvedDR r).2 (positionIdentificationTriple a v) =
      referenceNormRatioIcc (by norm_num : (0 : ℝ) < 2) (D.velocityVertex v + Complex.I) :=
    Subtype.ext (resolvedDR_inside_ratio D r v hv)
  rw [ht, onePointRadialIdentificationSub_phase_ratio]
  simp

theorem compactInsertion_shape (D : BoundaryAnchoredInfinityData a m l u o)
    {r : ℝ} (hr : D.AdmissibleScale r) (j : Fin n) :
    (D.compactInsertion hr).val.1 (Sum.inl j) = ((D.shape j : ℂ) : OnePoint ℂ) :=
  compactInsertion_position_inside D hr (Sum.inl j) rfl

theorem compactInsertion_boundary_inside (D : BoundaryAnchoredInfinityData a m l u o)
    {r : ℝ} (hr : D.AdmissibleScale r) (j : Fin m) (hj : j ∈ boundaryClusterBlock l u) :
    (D.compactInsertion hr).val.1 (Sum.inr j) = ((D.boundaryVelocity j : ℂ) : OnePoint ℂ) :=
  compactInsertion_position_inside D hr (Sum.inr j) (by
    change (D.boundaryBase j : ℂ) = 0
    rw [D.boundaryBase_zero_on j hj, Complex.ofReal_zero])

theorem resolvedDR_outside_position_ratio_zero (D : BoundaryAnchoredInfinityData a m l u o)
    (j : Fin m) (hj : j ∉ boundaryClusterBlock l u) :
    ((D.resolvedDR 0).2 (positionIdentificationTriple a (Sum.inr j)) : ℝ) = 1 := by
  have hp : D.pairBase (harmonicDenominatorPair a (Sum.inr j)) ≠ 0 := by
    rw [pairBase_fromAnchor]
    exact Complex.ofReal_ne_zero.mpr (fun h ↦ hj ((D.boundaryBase_eq_zero_iff j).mp h))
  have hq : D.pairBase (harmonicDenominatorPair a (Sum.inl a)) = 0 := by rw [pairBase_fromAnchor]; rfl
  change ((if D.pairBase (harmonicDenominatorPair a (Sum.inr j)) = 0 ∧
      D.pairBase (harmonicDenominatorPair a (Sum.inl a)) = 0 then _ else _) : Set.Icc (0 : ℝ) 1).val = 1
  rw [if_neg (fun h ↦ hp h.1)]
  change ‖D.activeDifference 0 (harmonicDenominatorPair a (Sum.inr j))‖ /
    (‖D.activeDifference 0 (harmonicDenominatorPair a (Sum.inr j))‖ +
      ‖D.activeDifference 0 (harmonicDenominatorPair a (Sum.inl a))‖) = 1
  simp [activeDifference, hq, norm_ne_zero_iff.mpr hp]

theorem compactInsertion_boundary_outside_zero (D : BoundaryAnchoredInfinityData a m l u o)
    (j : Fin m) (hj : j ∉ boundaryClusterBlock l u) :
    (D.compactInsertion D.admissibleScale_zero).val.1 (Sum.inr j) = ∞ := by
  rw [← compactification_position_identification a (Sum.inr j) _, D.compactInsertion_projectDR]
  change onePointRadialIdentificationSub 2 Complex.I
    ((D.resolvedDR 0).1 (harmonicDenominatorPair a (Sum.inr j)),
      (D.resolvedDR 0).2 (positionIdentificationTriple a (Sum.inr j))) = ∞
  have ht : (D.resolvedDR 0).2 (positionIdentificationTriple a (Sum.inr j)) =
      (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1) := Subtype.ext (resolvedDR_outside_position_ratio_zero D j hj)
  rw [ht, onePointRadialIdentificationSub_one]

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryAnchoredInfinityData
