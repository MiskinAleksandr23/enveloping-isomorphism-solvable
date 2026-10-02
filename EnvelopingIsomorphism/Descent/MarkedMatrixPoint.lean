import EnvelopingIsomorphism.Descent.GenericLieMatrix

/-! Encoding and decoding marked Lie-matrix equations over arbitrary extension fields. -/

namespace EnvelopingIsomorphism.Descent.MatrixGroup

open MvPolynomial
open scoped BigOperators

noncomputable section

variable {k E n : Type*} [Field k] [Field E] [Algebra k E] [Fintype n] [DecidableEq n]

abbrev weightedMarkedEquations
    (B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (weight : n → ℕ) :=
  markedIsomorphismEquations B C (fun i => OrderDual.toDual (weight i)) 1

def IsMarkedMatrix (weight : n → ℕ) (P : Matrix n n E) : Prop :=
  ∀ i r, weight r ≤ weight i → P r i = if r = i then 1 else 0

theorem marked_matrix_blockTriangular (weight : n → ℕ) (P : Matrix n n E)
    (hP : IsMarkedMatrix weight P) : P.BlockTriangular (fun i => OrderDual.toDual (weight i)) := by
  intro r i hri
  change weight r < weight i at hri
  rw [hP i r hri.le]
  have hne : r ≠ i := fun h => Nat.lt_irrefl _ (h ▸ hri)
  simp [hne]

theorem marked_matrix_diagonalPart (weight : n → ℕ) (P : Matrix n n E)
    (hP : IsMarkedMatrix weight P) :
    diagonalPart (fun i => OrderDual.toDual (weight i)) P = 1 := by
  ext r i
  by_cases hri : weight r = weight i
  · have hd := congrArg OrderDual.toDual hri
    simp only [diagonalPart, if_pos hd]
    exact hP i r hri.le
  · have hd : OrderDual.toDual (weight r) ≠ OrderDual.toDual (weight i) := by
      intro h; exact hri (congrArg OrderDual.ofDual h)
    have hne : r ≠ i := fun h => hri (congrArg weight h)
    simp [diagonalPart, hd, Matrix.one_apply, hne]

theorem marked_matrix_det (weight : n → ℕ) (P : Matrix n n E)
    (hP : IsMarkedMatrix weight P) : P.det = 1 := by
  rw [← det_diagonalPart _ (marked_matrix_blockTriangular weight P hP),
    marked_matrix_diagonalPart weight P hP, Matrix.det_one]

def markedMatrixCoordinates (P : Matrix n n E) : Coordinate n → E
  | none => 1
  | some (r, i) => P r i

theorem marked_relation_mem
    (B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (weight : n → ℕ)
    (q : ((n × n × n) ⊕ {q : n × n //
      OrderDual.toDual (weight q.2) < OrderDual.toDual (weight q.1)}) ⊕ Coordinate n) :
    markedIsomorphismRelation B C (fun i => OrderDual.toDual (weight i)) 1 q ∈
      weightedMarkedEquations B C weight :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨q, rfl⟩)

theorem marked_point_matrix_marked
    (B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (weight : n → ℕ)
    (x : Coordinate n → E) (hx : x ∈ zeroLocus E (weightedMarkedEquations B C weight)) :
    IsMarkedMatrix weight (fun r i => x (some (r, i))) := by
  intro i r hri
  rcases lt_or_eq_of_le hri with hlt | heq
  · let q : {q : n × n // OrderDual.toDual (weight q.2) < OrderDual.toDual (weight q.1)} :=
      ⟨(r, i), hlt⟩
    have h := hx _ (marked_relation_mem B C weight (Sum.inl (Sum.inr q)))
    have hzero : x (some (r, i)) = 0 := by
      simpa only [markedIsomorphismRelation, filteredIsomorphismRelation, flagRelation, aeval_X] using h
    have hne : r ≠ i := fun h => Nat.lt_irrefl _ (h ▸ hlt)
    simp [hzero, hne]
  · have h := hx _ (marked_relation_mem B C weight (Sum.inr (some (r, i))))
    have hd := congrArg OrderDual.toDual heq
    have h' : x (some (r, i)) - algebraMap k E (if r = i then 1 else 0) = 0 := by
      simpa only [markedIsomorphismRelation, diagonalPolynomial, if_pos hd, map_sub,
        aeval_X, aeval_C, coordinates, AffinePoint.toFunction, AffinePoint.ofFunction,
        Units.val_one, Matrix.one_apply] using h
    by_cases hri : r = i <;> simpa [hri] using sub_eq_zero.mp h'

theorem marked_point_matrix_bracket
    (B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (weight : n → ℕ)
    (x : Coordinate n → E) (hx : x ∈ zeroLocus E (weightedMarkedEquations B C weight))
    (i j r : n) :
    (∑ a, ∑ b, algebraMap k E (C (Pi.single a 1) (Pi.single b 1) r) *
      (x (some (a, i)) * x (some (b, j)))) =
      ∑ d, algebraMap k E (B (Pi.single i 1) (Pi.single j 1) d) * x (some (r, d)) := by
  have h := hx _ (marked_relation_mem B C weight (Sum.inl (Sum.inl (r, i, j))))
  simp only [markedIsomorphismRelation, filteredIsomorphismRelation, isomorphismRelation,
    map_sub, map_sum, map_mul, aeval_X, aeval_C, sub_eq_zero] at h
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h.symm

/-- A marked matrix satisfying the original bracket equations gives a point
of the finite marked-isomorphism equation ideal over the base field. -/
theorem markedMatrixCoordinates_mem
    (B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (weight : n → ℕ)
    (P : Matrix n n E) (hmark : IsMarkedMatrix weight P)
    (hbracket : ∀ i j r,
      (∑ a, ∑ b, algebraMap k E (C (Pi.single a 1) (Pi.single b 1) r) * (P a i * P b j)) =
        ∑ d, algebraMap k E (B (Pi.single i 1) (Pi.single j 1) d) * P r d) :
    markedMatrixCoordinates P ∈ zeroLocus E (weightedMarkedEquations B C weight) := by
  have hdet : aeval (markedMatrixCoordinates P) (genericMatrix (k := k) (n := n)).det = P.det := by
    rw [AlgHom.map_det]
    congr 1
    ext i j
    simp [genericMatrix, markedMatrixCoordinates]
  change weightedMarkedEquations B C weight ≤ RingHom.ker (aeval (markedMatrixCoordinates P)).toRingHom
  rw [weightedMarkedEquations, markedIsomorphismEquations, subgroupEquations, sup_le_iff]
  constructor
  · rw [equations, Ideal.span_le]
    intro p hp
    rcases hp with rfl
    change aeval (markedMatrixCoordinates P) determinantRelation = 0
    simp only [determinantRelation, map_sub, map_mul, aeval_X, map_one, hdet,
      markedMatrixCoordinates, one_mul, marked_matrix_det weight P hmark, sub_self]
  · apply Ideal.span_le.mpr
    rintro p ⟨q, rfl⟩
    change aeval (markedMatrixCoordinates P)
      (markedIsomorphismRelation B C (fun i => OrderDual.toDual (weight i)) 1 q) = 0
    cases q with
    | inl q =>
      cases q with
      | inl q =>
        obtain ⟨r, i, j⟩ := q
        simp only [markedIsomorphismRelation, filteredIsomorphismRelation, isomorphismRelation,
          map_sub, map_sum, map_mul, aeval_X, aeval_C, markedMatrixCoordinates, sub_eq_zero]
        simpa only [mul_comm, mul_left_comm, mul_assoc] using (hbracket i j r).symm
      | inr q =>
        simp only [markedIsomorphismRelation, filteredIsomorphismRelation, flagRelation,
          aeval_X, markedMatrixCoordinates]
        exact marked_matrix_blockTriangular weight P hmark q.property
    | inr q =>
      cases q with
      | none => simp [markedIsomorphismRelation, diagonalPolynomial, markedMatrixCoordinates,
          coordinates, AffinePoint.toFunction, AffinePoint.ofFunction]
      | some q =>
        obtain ⟨r, i⟩ := q
        by_cases hri : weight r = weight i
        · have hd := congrArg OrderDual.toDual hri
          simp only [markedIsomorphismRelation, diagonalPolynomial, if_pos hd, map_sub,
            aeval_X, aeval_C, markedMatrixCoordinates, coordinates, AffinePoint.toFunction,
            AffinePoint.ofFunction, Units.val_one, Matrix.one_apply]
          rw [hmark i r hri.le]
          split_ifs <;> simp
        · have hd : OrderDual.toDual (weight r) ≠ OrderDual.toDual (weight i) := by
            intro h; exact hri (congrArg OrderDual.ofDual h)
          have hne : r ≠ i := fun h => hri (congrArg weight h)
          simp [markedIsomorphismRelation, diagonalPolynomial, hd, markedMatrixCoordinates,
            coordinates, AffinePoint.toFunction, AffinePoint.ofFunction, hne]

end

end EnvelopingIsomorphism.Descent.MatrixGroup
