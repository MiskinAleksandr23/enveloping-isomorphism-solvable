import EnvelopingIsomorphism.Descent.MarkedSpecialization

/-! Diagonal Laurent scaling and the regular graded-coordinate arc attached to
an invertible power-series matrix. -/

namespace EnvelopingIsomorphism.Descent.MatrixGroup

open MvPolynomial
open scoped Matrix

noncomputable section

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- A diagonal matrix of units, as a unit matrix over the coefficient ring. -/
def diagonalUnit (s : n → Rˣ) : Matrix.GeneralLinearGroup n R where
  val := Matrix.diagonal fun i => (s i : R)
  inv := Matrix.diagonal fun i => ((s i)⁻¹ : Rˣ)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp

/-- Conjugation by a diagonal matrix of units. -/
def diagonalConjugate (s : n → Rˣ) (P : Matrix.GeneralLinearGroup n R) :
    Matrix.GeneralLinearGroup n R := diagonalUnit s * P * (diagonalUnit s)⁻¹

theorem diagonalConjugate_entry (s : n → Rˣ) (P : Matrix.GeneralLinearGroup n R) (i j : n) :
    (diagonalConjugate s P).val i j = (s i : R) * P.val i j * ((s j)⁻¹ : Rˣ) := by
  simp [diagonalConjugate, diagonalUnit, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem diagonalConjugate_det (s : n → Rˣ) (P : Matrix.GeneralLinearGroup n R) :
    (diagonalConjugate s P).val.det = P.val.det := by
  change ((diagonalConjugate s P).det : R) = (P.det : R)
  simp [diagonalConjugate, map_mul, mul_comm]

/-- Coordinates including inverse determinant, defined over arbitrary commutative rings. -/
def regularCoordinates (P : Matrix.GeneralLinearGroup n R) : Coordinate n → R
  | none => (P⁻¹).val.det
  | some (i, j) => P.val i j

section Field

variable {E : Type*} [Field E]

theorem regularCoordinates_eq_coordinates (P : Matrix.GeneralLinearGroup n E) :
    regularCoordinates P = (coordinates P).toFunction := by
  funext q
  cases q with
  | none =>
    change (P⁻¹).val.det = P.val.det⁻¹
    change ((P.det)⁻¹ : Eˣ).val = (P.det : E)⁻¹
    exact Units.val_inv_eq_inv_val _
  | some ij => rfl

theorem regularCoordinates_map (f : R →+* E) (P : Matrix.GeneralLinearGroup n R) :
    (fun q => f (regularCoordinates P q)) =
      (coordinates (Matrix.GeneralLinearGroup.map f P)).toFunction := by
  rw [← regularCoordinates_eq_coordinates]
  funext q
  cases q with
  | none =>
    simp only [regularCoordinates, ← map_inv, RingHom.map_det]
    rfl
  | some ij => rfl

variable {α : Type*} [LinearOrder α]

/-- A diagonal conjugation constant on each weight block fixes the diagonal-coordinate map. -/
theorem diagonalPolynomial_conjugate (b : n → α) (s : n → Eˣ)
    (hs : ∀ i j, b i = b j → s i = s j)
    (P : Matrix.GeneralLinearGroup n E) (q : Coordinate n) :
    aeval (coordinates (diagonalConjugate s P)).toFunction (diagonalPolynomial (k := E) b q) =
      aeval (coordinates P).toFunction (diagonalPolynomial (k := E) b q) := by
  cases q with
  | none =>
    simp only [diagonalPolynomial, aeval_X]
    change (diagonalConjugate s P).val.det⁻¹ = P.val.det⁻¹
    rw [diagonalConjugate_det]
  | some ij =>
    obtain ⟨i, j⟩ := ij
    by_cases hij : b i = b j
    · simp only [diagonalPolynomial, if_pos hij, aeval_X, coordinates,
        AffinePoint.toFunction, AffinePoint.ofFunction, diagonalConjugate_entry]
      rw [hs i j hij]
      simp [mul_assoc, mul_comm]
    · simp [diagonalPolynomial, hij]

end Field

section LaurentArc

variable {E : Type*} [Field E]

/-- The Laurent unit `t^(-w_i)` used in the comparison with the original Lie algebra. -/
def weightScale (weight : n → ℕ) (i : n) : (LaurentSeries E)ˣ where
  val := HahnSeries.single (-(weight i : ℤ)) 1
  inv := HahnSeries.single (weight i : ℤ) 1
  val_inv := by simp
  inv_val := by simp

/-- The generic original matrix obtained by the correct Rees diagonal conjugation. -/
def originalGenericMatrix (weight : n → ℕ) (P : Matrix.GeneralLinearGroup n (PowerSeries E)) :
    Matrix.GeneralLinearGroup n (LaurentSeries E) :=
  diagonalConjugate (weightScale weight)
    (Matrix.GeneralLinearGroup.map (algebraMap (PowerSeries E) (LaurentSeries E)) P)

theorem originalGenericMatrix_entry (weight : n → ℕ)
    (P : Matrix.GeneralLinearGroup n (PowerSeries E)) (r i : n) :
    (originalGenericMatrix weight P).val r i =
      HahnSeries.single ((weight i : ℤ) - weight r) 1 *
        algebraMap (PowerSeries E) (LaurentSeries E) (P.val r i) := by
  rw [originalGenericMatrix, diagonalConjugate_entry]
  change (HahnSeries.single (-(weight r : ℤ)) 1 *
    algebraMap (PowerSeries E) (LaurentSeries E) (P.val r i)) *
      HahnSeries.single (weight i : ℤ) 1 = _
  rw [mul_assoc, mul_comm (algebraMap (PowerSeries E) (LaurentSeries E) (P.val r i)),
    ← mul_assoc, HahnSeries.single_mul_single]
  simp [sub_eq_add_neg, add_comm]

theorem originalGenericMatrix_entry_zero_iff (weight : n → ℕ)
    (P : Matrix.GeneralLinearGroup n (PowerSeries E)) (r i : n) :
    (originalGenericMatrix weight P).val r i = 0 ↔ P.val r i = 0 := by
  rw [originalGenericMatrix_entry]
  simp only [mul_eq_zero, HahnSeries.single_eq_zero_iff, one_ne_zero, false_or]
  rw [← (algebraMap (PowerSeries E) (LaurentSeries E)).map_zero]
  exact HahnSeries.ofPowerSeries_injective.eq_iff

/-- The regular graded coordinate arc. The inverse determinant coordinate is also regular. -/
def gradedArc (weight : n → ℕ) (P : Matrix.GeneralLinearGroup n (PowerSeries E)) :
    Coordinate n → PowerSeries E
  | none => (P⁻¹).val.det
  | some (i, j) => if weight i = weight j then P.val i j else 0

theorem gradedArc_constantCoeff (weight : n → ℕ)
    (P : Matrix.GeneralLinearGroup n (PowerSeries E))
    (hP : P.val.map PowerSeries.constantCoeff = 1) (q : Coordinate n) :
    PowerSeries.constantCoeff (gradedArc weight P q) =
      coordinates (1 : Matrix.GeneralLinearGroup n E) q := by
  have heq : Matrix.GeneralLinearGroup.map PowerSeries.constantCoeff P = 1 := Units.ext hP
  have hc := congrFun (regularCoordinates_map PowerSeries.constantCoeff P) q
  rw [heq] at hc
  cases q with
  | none => exact hc
  | some ij =>
    obtain ⟨i, j⟩ := ij
    change PowerSeries.constantCoeff (if weight i = weight j then P.val i j else 0) =
      (coordinates (1 : Matrix.GeneralLinearGroup n E)).toFunction (some (i, j))
    by_cases hij : weight i = weight j
    · simpa only [regularCoordinates, if_pos hij] using hc
    · have hne : i ≠ j := fun h => hij (h ▸ rfl)
      simp [hij, coordinates, AffinePoint.toFunction, AffinePoint.ofFunction, Matrix.one_apply, hne]

variable {k : Type*} [Field k] [Algebra k E]

/-- The regular arc's generic coordinates are the graded coordinates of the
original Laurent-scaled matrix. The reverse order matches the decreasing filtration. -/
theorem gradedArc_generic (weight : n → ℕ)
    (P : Matrix.GeneralLinearGroup n (PowerSeries E)) (q : Coordinate n) :
    algebraMap (PowerSeries E) (LaurentSeries E) (gradedArc weight P q) =
      aeval (coordinates (originalGenericMatrix weight P)).toFunction
        (diagonalPolynomial (k := k) (fun i => OrderDual.toDual (weight i)) q) := by
  cases q with
  | none =>
    simp only [diagonalPolynomial, aeval_X, gradedArc]
    change algebraMap (PowerSeries E) (LaurentSeries E) ((P⁻¹).val.det) =
      (originalGenericMatrix weight P).val.det⁻¹
    rw [originalGenericMatrix, diagonalConjugate_det]
    exact congrFun (regularCoordinates_map (algebraMap (PowerSeries E) (LaurentSeries E)) P) none
  | some ij =>
    obtain ⟨i, j⟩ := ij
    by_cases hij : weight i = weight j
    · have hd : OrderDual.toDual (weight i) = OrderDual.toDual (weight j) := congrArg _ hij
      simp only [diagonalPolynomial, gradedArc, if_pos hij, if_pos hd, aeval_X]
      change algebraMap (PowerSeries E) (LaurentSeries E) (P.val i j) =
        (originalGenericMatrix weight P).val i j
      rw [originalGenericMatrix_entry, hij, sub_self]
      simp
    · have hd : OrderDual.toDual (weight i) ≠ OrderDual.toDual (weight j) := by
        intro h
        exact hij (congrArg OrderDual.ofDual h)
      simp only [diagonalPolynomial, gradedArc, if_neg hij, if_neg hd, map_zero]

/-- H4 applied directly to the actual marked power-series matrix: the regular
arc and inverse determinant coordinate are constructed here. -/
theorem marked_isomorphism_of_originalGenericMatrix [IsAlgClosed k]
    (B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k))
    (weight : n → ℕ) (P : Matrix.GeneralLinearGroup n (PowerSeries E))
    (hP : P.val.map PowerSeries.constantCoeff = 1)
    (hgeneric : (coordinates (originalGenericMatrix weight P)).toFunction ∈
      zeroLocus (LaurentSeries E)
        (filteredIsomorphismEquations B C (fun i => OrderDual.toDual (weight i)))) :
    ∃ f : blockTriangularSubgroup (k := k) (fun i => OrderDual.toDual (weight i)),
      PreservesBilinear B C f.val ∧ diagonalHom (fun i => OrderDual.toDual (weight i)) f = 1 := by
  apply marked_isomorphism_of_regular_graded_arc B C (fun i => OrderDual.toDual (weight i))
    (coordinates (originalGenericMatrix weight P)).toFunction hgeneric
    (gradedArc weight P) 1 (gradedArc_generic weight P)
  intro q
  rw [gradedArc_constantCoeff weight P hP]
  cases q with
  | none => simp [coordinates, AffinePoint.toFunction, AffinePoint.ofFunction]
  | some ij =>
    obtain ⟨i, j⟩ := ij
    by_cases hij : i = j <;>
      simp [coordinates, AffinePoint.toFunction, AffinePoint.ofFunction, hij]

end LaurentArc

end

end EnvelopingIsomorphism.Descent.MatrixGroup
