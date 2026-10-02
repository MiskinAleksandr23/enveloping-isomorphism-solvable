import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterCompactification

/-!
# Actual phase factors at a finite real-cluster face

The whole internal harmonic phase is retained by the normalized shape. An
external edge retains its coarse harmonic phase; an edge leaving the real
cluster has phase one. All identities concern the actual compact closure.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration ComplexConjugate

namespace BoundaryClusterData

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

def boundaryPoint (D : BoundaryClusterData i a m S l u) : Compactification i m :=
  D.compactInsertion D.admissibleScale_zero

def baseVertex (D : BoundaryClusterData i a m S l u) (v : Fin n ⊕ Fin m) : ℂ :=
  D.doubledBase (Sum.inl v)

def velocityVertex (D : BoundaryClusterData i a m S l u) (v : Fin n ⊕ Fin m) : ℂ :=
  D.doubledVelocity (Sum.inl v)

theorem boundaryPoint_position (D : BoundaryClusterData i a m S l u) (v : Fin n ⊕ Fin m) :
    D.boundaryPoint.val.1 v = (D.baseVertex v : OnePoint ℂ) := by
  simp [boundaryPoint, compactInsertion, resolvedCoordinates, baseVertex]

/-- Even a one-interior-vertex cluster adds a new point: that vertex reaches the real line. -/
theorem boundaryPoint_not_mem_range (D : BoundaryClusterData i a m S l u) :
    D.boundaryPoint ∉ Set.range (compactificationEmbedding i : Normalized i m → Compactification i m) := by
  rintro ⟨c, hc⟩
  have he := congrArg (fun x : Compactification i m => x.val.1 (Sum.inl a)) hc
  have he' : (c.val.interior a : ℂ) = D.base a := by
    apply OnePoint.coe_injective
    simpa only [compactificationEmbedding, compactCoordinates, compactPositions,
      D.boundaryPoint_position, baseVertex, doubledBase, vertexPoint, Sum.elim_inl] using he
  have hpos := (c.val.interior a).im_pos
  rw [← UpperHalfPlane.coe_im, he', D.base_eq_center a D.anchor_mem, Complex.ofReal_im] at hpos
  exact lt_irrefl _ hpos

theorem baseVertex_im_nonneg (D : BoundaryClusterData i a m S l u) (v : Fin n ⊕ Fin m) :
    0 ≤ (D.baseVertex v).im := by
  cases v with
  | inl j =>
    by_cases hj : j ∈ S
    · simp [baseVertex, doubledBase, D.base_eq_center j hj]
    · exact (D.base_im_pos_off j hj).le
  | inr j => simp [baseVertex, doubledBase]

theorem velocityVertex_im_nonneg (D : BoundaryClusterData i a m S l u) (v : Fin n ⊕ Fin m) :
    0 ≤ (D.velocityVertex v).im := by
  cases v with
  | inl j =>
    by_cases hj : j ∈ S
    · exact (D.velocity_im_pos j hj).le
    · simp [velocityVertex, doubledVelocity, D.velocity_zero_off j hj]
  | inr j => simp [velocityVertex, doubledVelocity]

theorem boundaryPoint_direction (D : BoundaryClusterData i a m S l u) (p : DoubledPair n m) :
    D.boundaryPoint.val.2.1 p =
      if D.pairBase p = 0 then complexPhase (D.pairVelocity p) else complexPhase (D.pairBase p) := by
  simp [boundaryPoint, compactInsertion, resolvedCoordinates, activeDifference]

theorem base_harmonicDenominator_ne_zero (D : BoundaryClusterData i a m S l u) (j : Fin n)
    (v : Fin n ⊕ Fin m) (hbase : D.baseVertex v ≠ D.base j) :
    D.baseVertex v - conj (D.base j) ≠ 0 := by
  by_cases hj : j ∈ S
  · simpa only [D.base_eq_center j hj, Complex.conj_ofReal] using sub_ne_zero.mpr hbase
  · exact harmonicDenominator_ne_zero (D.base_im_pos_off j hj) (D.baseVertex_im_nonneg v)

/-- An edge with distinct coarse endpoints retains precisely the coarse harmonic phase. -/
theorem boundary_harmonicPhase_of_distinct_base (D : BoundaryClusterData i a m S l u)
    (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j)
    (hbase : D.baseVertex v ≠ D.base j) :
    extendedHarmonicPhase j v hv D.boundaryPoint =
      complexPhase (harmonicRatio (D.base j) (D.baseVertex v)) := by
  have hn : D.pairBase (harmonicNumeratorPair j v hv) ≠ 0 := sub_ne_zero.mpr hbase
  have hd : D.pairBase (harmonicDenominatorPair j v) ≠ 0 :=
    D.base_harmonicDenominator_ne_zero j v hbase
  rw [extendedHarmonicPhase, D.boundaryPoint_direction, D.boundaryPoint_direction,
    if_neg hn, if_neg hd]
  exact (complexPhase_harmonicRatio (sub_ne_zero.mpr hbase)
    (D.base_harmonicDenominator_ne_zero j v hbase)).symm

/-- Every internal edge retains the harmonic phase of the upper-half-plane shape. -/
theorem boundary_harmonicPhase_internal (D : BoundaryClusterData i a m S l u)
    (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j)
    (hj : j ∈ S) (hbase : D.baseVertex v = (D.center : ℂ)) :
    extendedHarmonicPhase j v hv D.boundaryPoint =
      complexPhase (harmonicRatio (D.velocity j) (D.velocityVertex v)) := by
  have hn : D.pairBase (harmonicNumeratorPair j v hv) = 0 := by
    change D.baseVertex v - D.base j = 0
    rw [hbase, D.base_eq_center j hj, sub_self]
  have hd : D.pairBase (harmonicDenominatorPair j v) = 0 := by
    change D.baseVertex v - conj (D.base j) = 0
    rw [hbase, D.base_eq_center j hj, Complex.conj_ofReal, sub_self]
  have hnum : D.velocityVertex v - D.velocity j ≠ 0 :=
    D.pairVelocity_ne_zero_of_pairBase_eq_zero (harmonicNumeratorPair j v hv) hn
  have hden : D.velocityVertex v - conj (D.velocity j) ≠ 0 :=
    harmonicDenominator_ne_zero (D.velocity_im_pos j hj) (D.velocityVertex_im_nonneg v)
  rw [extendedHarmonicPhase, D.boundaryPoint_direction, D.boundaryPoint_direction,
    if_pos hn, if_pos hd]
  exact (complexPhase_harmonicRatio hnum hden).symm

/-- An edge leaving the real cluster has constant boundary phase one. -/
theorem boundary_harmonicPhase_outgoing (D : BoundaryClusterData i a m S l u)
    (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j)
    (hj : j ∈ S) (hbase : D.baseVertex v ≠ (D.center : ℂ)) :
    extendedHarmonicPhase j v hv D.boundaryPoint = 1 := by
  have hne : D.baseVertex v ≠ D.base j := by simpa only [D.base_eq_center j hj] using hbase
  rw [D.boundary_harmonicPhase_of_distinct_base j v hv hne]
  simp only [harmonicRatio, D.base_eq_center j hj, Complex.conj_ofReal,
    div_self (sub_ne_zero.mpr hbase), complexPhase_one]

end BoundaryClusterData

end EnvelopingIsomorphism.Deformation.Kontsevich
