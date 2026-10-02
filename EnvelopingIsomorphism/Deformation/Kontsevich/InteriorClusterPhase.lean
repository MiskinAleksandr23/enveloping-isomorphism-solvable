import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterCompactification

/-!
# Internal and external phase factorization at an arbitrary interior-cluster face

The statements concern the actual continuous harmonic phase on the compact
closure. Internal edges retain their velocity direction; edges with distinct
base endpoints retain the harmonic phase of the coarse configuration.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration ComplexConjugate

namespace InteriorCollisionData

variable {n m : ℕ} {i : Fin n}

def boundaryPoint (D : InteriorCollisionData i m) : Compactification i m :=
  D.compactInsertion D.admissibleScale_zero

def baseVertex (D : InteriorCollisionData i m) (v : Fin n ⊕ Fin m) : ℂ :=
  D.doubledBase (Sum.inl v)

theorem boundaryPoint_position (D : InteriorCollisionData i m) (v : Fin n ⊕ Fin m) :
    D.boundaryPoint.val.1 v = (D.baseVertex v : OnePoint ℂ) := by
  simp [boundaryPoint, compactInsertion, resolvedCoordinates, baseVertex]

theorem boundaryPoint_not_mem_range_of_base_eq (D : InteriorCollisionData i m)
    (a b : Fin n) (hab : a ≠ b) (hbase : D.base a = D.base b) :
    D.boundaryPoint ∉ Set.range (compactificationEmbedding i : Normalized i m → Compactification i m) := by
  rintro ⟨c, hc⟩
  have hpos (v : Fin n ⊕ Fin m) : (c.val.vertexPoint v : OnePoint ℂ) = (D.baseVertex v : OnePoint ℂ) := by
    have h := congrArg (fun x : Compactification i m => x.val.1 v) hc
    simpa only [compactificationEmbedding, compactCoordinates, compactPositions, D.boundaryPoint_position] using h
  have ha : (c.val.interior a : ℂ) = (D.base a : ℂ) := OnePoint.coe_injective (hpos (Sum.inl a))
  have hb : (c.val.interior b : ℂ) = (D.base b : ℂ) := OnePoint.coe_injective (hpos (Sum.inl b))
  apply hab
  apply c.val.interior_injective
  apply UpperHalfPlane.ext
  rw [ha, hb, hbase]

theorem baseVertex_im_nonneg (D : InteriorCollisionData i m) (v : Fin n ⊕ Fin m) :
    0 ≤ (D.baseVertex v).im := by
  cases v with
  | inl a => exact (D.base a).im_pos.le
  | inr j => simp [baseVertex, doubledBase]

theorem boundaryPoint_direction (D : InteriorCollisionData i m) (p : DoubledPair n m) :
    D.boundaryPoint.val.2.1 p =
      if D.pairBase p = 0 then complexPhase (D.pairVelocity p) else complexPhase (D.pairBase p) := by
  simp [boundaryPoint, compactInsertion, resolvedCoordinates, activeDifference]

theorem base_harmonicDenominator_ne_zero (D : InteriorCollisionData i m) (a : Fin n)
    (v : Fin n ⊕ Fin m) : D.baseVertex v - conj (D.base a : ℂ) ≠ 0 :=
  harmonicDenominator_ne_zero (D.base a).im_pos (D.baseVertex_im_nonneg v)

/-- An external edge has exactly the coarse harmonic phase at the cluster face. -/
theorem boundary_harmonicPhase_of_distinct_base (D : InteriorCollisionData i m)
    (a : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl a)
    (hbase : D.baseVertex v ≠ (D.base a : ℂ)) :
    extendedHarmonicPhase a v hv D.boundaryPoint =
      complexPhase (harmonicRatio (D.base a) (D.baseVertex v)) := by
  have hn : D.pairBase (harmonicNumeratorPair a v hv) ≠ 0 := sub_ne_zero.mpr hbase
  have hd : D.pairBase (harmonicDenominatorPair a v) ≠ 0 := D.base_harmonicDenominator_ne_zero a v
  rw [extendedHarmonicPhase, D.boundaryPoint_direction, D.boundaryPoint_direction,
    if_neg hn, if_neg hd]
  exact (complexPhase_harmonicRatio (sub_ne_zero.mpr hbase) (D.base_harmonicDenominator_ne_zero a v)).symm

end InteriorCollisionData

theorem complexPhase_sub_conj_upper (c : UpperHalfPlane) :
    complexPhase ((c : ℂ) - conj (c : ℂ)) = complexPhase Complex.I := by
  have heq : (c : ℂ) - conj (c : ℂ) = ((2 * c.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    all_goals ring
  rw [heq]
  exact complexPhase_pos_real_mul (mul_pos (by norm_num) c.im_pos) Complex.I

namespace SingleInteriorCluster

variable {n m : ℕ} {i : Fin n} {S : Finset (Fin n)}

/-- A cluster with at least two labelled members gives a genuinely added compactification point. -/
theorem boundaryPoint_not_mem_range (D : SingleInteriorCluster i m S) (a b : Fin n)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    D.toInteriorCollisionData.boundaryPoint ∉
      Set.range (compactificationEmbedding i : Normalized i m → Compactification i m) :=
  D.toInteriorCollisionData.boundaryPoint_not_mem_range_of_base_eq a b hab (D.base_eq_of_mem ha hb)

/-- At the face, an internal edge has the planar cluster phase up to the fixed quarter turn. -/
theorem boundary_harmonicPhase_internal (D : SingleInteriorCluster i m S) (a b : Fin n)
    (ha : a ∈ S) (hb : b ∈ S) (hab : b ≠ a) :
    extendedHarmonicPhase a (Sum.inl b) (fun h => hab (Sum.inl.inj h))
      D.toInteriorCollisionData.boundaryPoint =
        complexPhase (D.velocity b - D.velocity a) / complexPhase Complex.I := by
  have hbase : D.base b = D.base a := D.base_eq_of_mem hb ha
  have hn : D.toInteriorCollisionData.pairBase
      (harmonicNumeratorPair a (Sum.inl b) (fun h => hab (Sum.inl.inj h))) = 0 := by
    change (D.base b : ℂ) - (D.base a : ℂ) = 0
    simp only [hbase, sub_self]
  have hd : D.toInteriorCollisionData.pairBase (harmonicDenominatorPair a (Sum.inl b)) ≠ 0 :=
    D.toInteriorCollisionData.base_harmonicDenominator_ne_zero a (Sum.inl b)
  rw [extendedHarmonicPhase, InteriorCollisionData.boundaryPoint_direction,
    InteriorCollisionData.boundaryPoint_direction, if_pos hn, if_neg hd]
  change complexPhase (D.velocity b - D.velocity a) /
    complexPhase ((D.base b : ℂ) - conj (D.base a : ℂ)) = _
  rw [hbase, complexPhase_sub_conj_upper]

/-- An edge not entirely inside the cluster has the coarse interior-to-interior phase. -/
theorem boundary_harmonicPhase_external (D : SingleInteriorCluster i m S) (a b : Fin n)
    (hab : b ≠ a) (hS : ¬ (a ∈ S ∧ b ∈ S)) :
    extendedHarmonicPhase a (Sum.inl b) (fun h => hab (Sum.inl.inj h))
      D.toInteriorCollisionData.boundaryPoint = complexPhase (harmonicRatio (D.base a) (D.base b)) := by
  apply D.toInteriorCollisionData.boundary_harmonicPhase_of_distinct_base
  intro h
  have heq : D.base a = D.base b := (UpperHalfPlane.ext h).symm
  rcases (D.base_eq_iff a b).mp heq with he | hs
  · exact hab he.symm
  · exact hS hs

/-- Boundary targets are always external to an interior cluster. -/
theorem boundary_harmonicPhase_boundary_target (D : SingleInteriorCluster i m S)
    (a : Fin n) (j : Fin m) :
    extendedHarmonicPhase a (Sum.inr j) (by simp) D.toInteriorCollisionData.boundaryPoint =
      complexPhase (harmonicRatio (D.base a) (D.boundary j)) := by
  apply D.toInteriorCollisionData.boundary_harmonicPhase_of_distinct_base
  intro h
  have him := congrArg Complex.im h
  have hp := (D.base a).im_pos
  simp only [InteriorCollisionData.baseVertex, InteriorCollisionData.doubledBase,
    Complex.ofReal_im, UpperHalfPlane.coe_im] at him
  linarith

end SingleInteriorCluster

end EnvelopingIsomorphism.Deformation.Kontsevich
