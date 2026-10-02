import EnvelopingIsomorphism.Descent.ClosedImage.AlgebraicGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Polynomial coordinates for the general linear group

The coordinates are all matrix entries and one extra coordinate for the inverse
determinant. No product topology on the scalar field is used.
-/

namespace EnvelopingIsomorphism.Descent.MatrixGroup

open Set Topology MvPolynomial

noncomputable section

variable {k n : Type*} [Field k] [Fintype n] [DecidableEq n]

abbrev Coordinate (n : Type*) := Option (n × n)

def genericMatrix : Matrix n n (MvPolynomial (Coordinate n) k) :=
  fun i j => X (some (i, j))

def matrixOfPoint (x : AffinePoint k (Coordinate n)) : Matrix n n k :=
  fun i j => x.toFunction (some (i, j))

def coordinates (g : Matrix.GeneralLinearGroup n k) : AffinePoint k (Coordinate n) :=
  AffinePoint.ofFunction fun
    | none => (g.val.det)⁻¹
    | some (i, j) => g.val i j

theorem coordinates_injective : Function.Injective (coordinates (k := k) (n := n)) := by
  intro g h heq
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  exact congrArg (fun x : AffinePoint k (Coordinate n) => x.toFunction (some (i, j))) heq

def determinantRelation : MvPolynomial (Coordinate n) k :=
  X none * (genericMatrix (k := k) (n := n)).det - 1

def equations : Ideal (MvPolynomial (Coordinate n) k) := Ideal.span {determinantRelation}

omit [Fintype n] [DecidableEq n] in
theorem eval_genericMatrix (x : AffinePoint k (Coordinate n)) :
    (genericMatrix (k := k) (n := n)).map (aeval x.toFunction) = matrixOfPoint x := by
  ext i j
  simp [genericMatrix, matrixOfPoint]

theorem eval_determinant (x : AffinePoint k (Coordinate n)) :
    aeval x.toFunction (genericMatrix (k := k) (n := n)).det = (matrixOfPoint x).det := by
  rw [AlgHom.map_det]
  change ((genericMatrix (k := k) (n := n)).map (aeval x.toFunction)).det = _
  rw [eval_genericMatrix]

theorem mem_zeros_equations (x : AffinePoint k (Coordinate n)) :
    x ∈ AffinePoint.zeros (equations (k := k) (n := n)) ↔
      x.toFunction none * (matrixOfPoint x).det = 1 := by
  change x.toFunction ∈ zeroLocus k (Ideal.span {determinantRelation}) ↔ _
  rw [zeroLocus_span]
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq, determinantRelation,
    map_sub, map_mul, aeval_X, map_one, sub_eq_zero, eval_determinant]

theorem range_coordinates :
    Set.range (coordinates (k := k) (n := n)) = AffinePoint.zeros equations := by
  ext x
  rw [mem_zeros_equations]
  constructor
  · rintro ⟨g, rfl⟩
    change (g.val.det)⁻¹ * g.val.det = 1
    exact inv_mul_cancel₀ g.det_ne_zero
  · intro hx
    have hdet : (matrixOfPoint x).det ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at hx
      exact zero_ne_one hx
    let g := Matrix.GeneralLinearGroup.mkOfDetNeZero (matrixOfPoint x) hdet
    refine ⟨g, ?_⟩
    apply funext
    intro i
    cases i with
    | none =>
        change (matrixOfPoint x).det⁻¹ = x.toFunction none
        exact (eq_inv_of_mul_eq_one_left hx).symm
    | some ij =>
        cases ij
        rfl

/-- The Zariski topology on `GL`, induced by matrix entries and inverse determinant. -/
@[reducible] def topology : TopologicalSpace (Matrix.GeneralLinearGroup n k) :=
  TopologicalSpace.induced coordinates inferInstance

def affinePresentation :
    letI := topology (k := k) (n := n)
    AffinePresentation k (Coordinate n) (Matrix.GeneralLinearGroup n k) := by
  letI := topology (k := k) (n := n)
  exact
    { coordinates := coordinates
      isEmbedding_coordinates := ⟨⟨rfl⟩, coordinates_injective⟩
      equations := equations
      range_coordinates := range_coordinates }

def mulLeftPolynomial (g : Matrix.GeneralLinearGroup n k) :
    Coordinate n → MvPolynomial (Coordinate n) k
  | none => C (g.val.det)⁻¹ * X none
  | some (i, j) => ∑ l, C (g.val i l) * X (some (l, j))

def mulRightPolynomial (g : Matrix.GeneralLinearGroup n k) :
    Coordinate n → MvPolynomial (Coordinate n) k
  | none => X none * C (g.val.det)⁻¹
  | some (i, j) => ∑ l, X (some (i, l)) * C (g.val l j)

def invPolynomial : Coordinate n → MvPolynomial (Coordinate n) k
  | none => (genericMatrix (k := k) (n := n)).det
  | some (i, j) => X none * (genericMatrix (k := k) (n := n)).adjugate i j

theorem mulLeft_coordinates (g h : Matrix.GeneralLinearGroup n k) :
    coordinates (g * h) = AffinePoint.polynomialMap (mulLeftPolynomial g) (coordinates h) := by
  apply funext
  intro i
  cases i with
  | none =>
      change (g.val * h.val).det⁻¹ =
        aeval (coordinates h).toFunction (C g.val.det⁻¹ * X none)
      simp only [Matrix.det_mul, mul_inv, map_mul, aeval_C, aeval_X,
        Algebra.algebraMap_self_apply]
      rfl
  | some ij =>
      obtain ⟨i, j⟩ := ij
      change (g.val * h.val) i j =
        aeval (coordinates h).toFunction (∑ l, C (g.val i l) * X (some (l, j)))
      simp only [Matrix.mul_apply, map_sum, map_mul, aeval_C, aeval_X,
        Algebra.algebraMap_self_apply]
      rfl

theorem mulRight_coordinates (g h : Matrix.GeneralLinearGroup n k) :
    coordinates (h * g) = AffinePoint.polynomialMap (mulRightPolynomial g) (coordinates h) := by
  apply funext
  intro i
  cases i with
  | none =>
      change (h.val * g.val).det⁻¹ =
        aeval (coordinates h).toFunction (X none * C g.val.det⁻¹)
      simp only [Matrix.det_mul, mul_inv, map_mul, aeval_C, aeval_X,
        Algebra.algebraMap_self_apply]
      rfl
  | some ij =>
      obtain ⟨i, j⟩ := ij
      change (h.val * g.val) i j =
        aeval (coordinates h).toFunction (∑ l, X (some (i, l)) * C (g.val l j))
      simp only [Matrix.mul_apply, map_sum, map_mul, aeval_C, aeval_X,
        Algebra.algebraMap_self_apply]
      rfl

theorem eval_adjugate (x : AffinePoint k (Coordinate n)) (i j : n) :
    aeval x.toFunction ((genericMatrix (k := k) (n := n)).adjugate i j) =
      (matrixOfPoint x).adjugate i j := by
  have h := (aeval (R := k) x.toFunction).map_adjugate (genericMatrix (k := k) (n := n))
  have h' := congrArg (fun M : Matrix n n k => M i j) h
  change aeval x.toFunction ((genericMatrix (k := k) (n := n)).adjugate i j) =
    ((genericMatrix (k := k) (n := n)).map (aeval x.toFunction)).adjugate i j at h'
  rwa [eval_genericMatrix] at h'

theorem inv_coordinates (g : Matrix.GeneralLinearGroup n k) :
    coordinates g⁻¹ = AffinePoint.polynomialMap (invPolynomial (k := k) (n := n))
      (coordinates g) := by
  apply funext
  intro i
  cases i with
  | none =>
      change ((g⁻¹).val.det)⁻¹ = aeval (coordinates g).toFunction genericMatrix.det
      rw [eval_determinant]
      change ((g⁻¹).val.det)⁻¹ = g.val.det
      have hdet : (g⁻¹).val.det = g.val.det⁻¹ := by
        change ((Matrix.GeneralLinearGroup.det g⁻¹ : kˣ) : k) =
          ((Matrix.GeneralLinearGroup.det g : kˣ) : k)⁻¹
        simp
      rw [hdet, inv_inv]
  | some ij =>
      obtain ⟨i, j⟩ := ij
      change (g⁻¹).val i j =
        aeval (coordinates g).toFunction (X none * genericMatrix.adjugate i j)
      rw [map_mul, aeval_X, eval_adjugate]
      change (g⁻¹).val i j = g.val.det⁻¹ * g.val.adjugate i j
      rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def]
      simp

/-- The complete affine polynomial group presentation of `GL`. -/
def groupPresentation :
    letI := topology (k := k) (n := n)
    AffinePolynomialGroup k (Coordinate n) (Matrix.GeneralLinearGroup n k) := by
  letI := topology (k := k) (n := n)
  exact
    { affinePresentation (k := k) (n := n) with
      mulLeftPolynomial := mulLeftPolynomial
      mulLeft_coordinates := mulLeft_coordinates
      mulRightPolynomial := mulRightPolynomial
      mulRight_coordinates := mulRight_coordinates
      invPolynomial := invPolynomial
      inv_coordinates := inv_coordinates }

/-- Polynomial equations in matrix entries and inverse determinant define a
closed subset of the general linear group. -/
theorem isClosed_polynomial_constraints {ι : Type*}
    (p : ι → MvPolynomial (Coordinate n) k) :
    letI := topology (k := k) (n := n)
    IsClosed {g : Matrix.GeneralLinearGroup n k |
      ∀ i, aeval (coordinates g).toFunction (p i) = 0} := by
  letI := topology (k := k) (n := n)
  have heq : {g : Matrix.GeneralLinearGroup n k |
      ∀ i, aeval (coordinates g).toFunction (p i) = 0} =
      coordinates ⁻¹' AffinePoint.zeros (Ideal.span (Set.range p)) := by
    ext g
    simp [AffinePoint.zeros, zeroLocus_span]
  rw [heq]
  exact (AffinePoint.isClosed_zeros _).preimage
    (affinePresentation (k := k) (n := n)).isEmbedding_coordinates.continuous

theorem isClosed_subgroup_of_polynomial_constraints {ι : Type*}
    (U : Subgroup (Matrix.GeneralLinearGroup n k))
    (p : ι → MvPolynomial (Coordinate n) k)
    (hp : ∀ g, g ∈ U ↔ ∀ i, aeval (coordinates g).toFunction (p i) = 0) :
    letI := topology (k := k) (n := n)
    IsClosed (U : Set (Matrix.GeneralLinearGroup n k)) := by
  letI := topology (k := k) (n := n)
  convert isClosed_polynomial_constraints p using 1
  ext g
  exact hp g

/-- The determinant equation together with a family's additional constraints. -/
def subgroupEquations {ι : Type*} (p : ι → MvPolynomial (Coordinate n) k) :
    Ideal (MvPolynomial (Coordinate n) k) := equations ⊔ Ideal.span (Set.range p)

theorem subgroup_range_coordinates {ι : Type*}
    (U : Subgroup (Matrix.GeneralLinearGroup n k))
    (p : ι → MvPolynomial (Coordinate n) k)
    (hp : ∀ g, g ∈ U ↔ ∀ i, aeval (coordinates g).toFunction (p i) = 0) :
    Set.range (fun u : U => coordinates u.val) = AffinePoint.zeros (subgroupEquations p) := by
  rw [subgroupEquations, AffinePoint.zeros_sup]
  ext x
  change (∃ u : U, coordinates u.val = x) ↔
    (x ∈ AffinePoint.zeros equations ∧ x.toFunction ∈ zeroLocus k (Ideal.span (Set.range p)))
  rw [zeroLocus_span]
  simp only [Set.mem_setOf_eq, Set.forall_mem_range]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨range_coordinates (k := k) (n := n) ▸ Set.mem_range_self u.val,
      (hp u.val).mp u.property⟩
  · rintro ⟨hx, hpx⟩
    obtain ⟨g, rfl⟩ := (range_coordinates (k := k) (n := n)).symm ▸ hx
    exact ⟨⟨g, (hp g).mpr hpx⟩, rfl⟩

/-- A polynomial subgroup presentation retaining the explicit defining ideal,
rather than choosing an unspecified ideal from topological closedness. -/
def subgroupPresentationOfPolynomialConstraints {ι : Type*}
    (U : Subgroup (Matrix.GeneralLinearGroup n k))
    (p : ι → MvPolynomial (Coordinate n) k)
    (hp : ∀ g, g ∈ U ↔ ∀ i, aeval (coordinates g).toFunction (p i) = 0) :
    letI := topology (k := k) (n := n)
    AffinePolynomialGroup k (Coordinate n) U := by
  letI := topology (k := k) (n := n)
  exact
    { groupPresentation.closedSubgroup U (isClosed_subgroup_of_polynomial_constraints U p hp) with
      equations := subgroupEquations p
      range_coordinates := subgroup_range_coordinates U p hp }

end

end EnvelopingIsomorphism.Descent.MatrixGroup
