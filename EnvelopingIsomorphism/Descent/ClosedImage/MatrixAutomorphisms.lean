import EnvelopingIsomorphism.Descent.ClosedImage.MatrixGroup
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.BilinearMap

/-! # Polynomial equations for bilinear-algebra and filtered automorphisms -/

namespace EnvelopingIsomorphism.Descent.MatrixGroup

open Set Topology MvPolynomial
open scoped Matrix

noncomputable section

variable {k n : Type*} [Field k] [Fintype n] [DecidableEq n]

def linearEquiv : Matrix.GeneralLinearGroup n k ≃* ((n → k) ≃ₗ[k] (n → k)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv k (n → k))

@[simp] theorem linearEquiv_apply (g : Matrix.GeneralLinearGroup n k) (x : n → k) :
    linearEquiv g x = g.val *ᵥ x := rfl

/-- Automorphisms preserving a specified bilinear operation. The operation may
be a Lie bracket; no unnecessary Lie identities are needed for this construction. -/
def bilinearAutomorphisms (B : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) :
    Subgroup (Matrix.GeneralLinearGroup n k) where
  carrier := {g | ∀ x y, linearEquiv g (B x y) = B (linearEquiv g x) (linearEquiv g y)}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh x y
    change linearEquiv (g * h) (B x y) = _
    rw [map_mul]
    change linearEquiv g (linearEquiv h (B x y)) =
      B (linearEquiv g (linearEquiv h x)) (linearEquiv g (linearEquiv h y))
    rw [hh, hg]
  inv_mem' := by
    intro g hg x y
    change linearEquiv g⁻¹ (B x y) = B (linearEquiv g⁻¹ x) (linearEquiv g⁻¹ y)
    rw [map_inv]
    apply (linearEquiv g).injective
    change linearEquiv g ((linearEquiv g).symm (B x y)) =
      linearEquiv g (B ((linearEquiv g).symm x) ((linearEquiv g).symm y))
    rw [hg]
    simp

theorem mem_bilinearAutomorphisms_iff_basis
    (B : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (g : Matrix.GeneralLinearGroup n k) :
    g ∈ bilinearAutomorphisms B ↔ ∀ i j,
      linearEquiv g (B (Pi.single i 1) (Pi.single j 1)) =
        B (linearEquiv g (Pi.single i 1)) (linearEquiv g (Pi.single j 1)) := by
  constructor
  · intro h i j
    exact h _ _
  · intro h
    have heq : B.compr₂ (linearEquiv g).toLinearMap =
        B.compl₁₂ (linearEquiv g).toLinearMap (linearEquiv g).toLinearMap := by
      apply (Pi.basisFun k n).ext
      intro i
      apply (Pi.basisFun k n).ext
      intro j
      simpa only [Pi.basisFun_apply, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
        LinearEquiv.coe_coe] using h i j
    intro x y
    exact LinearMap.congr_fun (LinearMap.congr_fun heq x) y

theorem bilinear_apply_eq_sum
    (B : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (x y : n → k) (r : n) :
    B x y r = ∑ i, ∑ j, x i * y j * B (Pi.single i 1) (Pi.single j 1) r := by
  have hx : ∑ i, x i • Pi.single i (1 : k) = x := by
    ext i
    simp [Pi.smul_apply, Pi.single_apply]
  have hy : ∑ j, y j • Pi.single j (1 : k) = y := by
    ext j
    simp [Pi.smul_apply, Pi.single_apply]
  calc
    B x y r = B (∑ i, x i • Pi.single i (1 : k)) (∑ j, y j • Pi.single j (1 : k)) r := by
      rw [hx, hy]
    _ = _ := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [mul_left_comm, mul_assoc]

def bracketRelation
    (B : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (r i j : n) :
    MvPolynomial (Coordinate n) k :=
  (∑ l, X (some (r, l)) * C (B (Pi.single i 1) (Pi.single j 1) l)) -
    ∑ a, ∑ b, X (some (a, i)) * X (some (b, j)) *
      C (B (Pi.single a 1) (Pi.single b 1) r)

theorem eval_bracketRelation
    (B : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k))
    (g : Matrix.GeneralLinearGroup n k) (r i j : n) :
    aeval (coordinates g).toFunction (bracketRelation B r i j) =
      linearEquiv g (B (Pi.single i 1) (Pi.single j 1)) r -
        B (linearEquiv g (Pi.single i 1)) (linearEquiv g (Pi.single j 1)) r := by
  simp only [linearEquiv_apply, Matrix.mulVec_single_one]
  rw [bilinear_apply_eq_sum]
  simp only [bracketRelation, map_sub, map_sum, map_mul, aeval_X, aeval_C,
    Algebra.algebraMap_self_apply, Matrix.col_apply, Matrix.mulVec_apply_eq_sum]
  rfl

theorem mem_bilinearAutomorphisms_iff_equations
    (B : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (g : Matrix.GeneralLinearGroup n k) :
    g ∈ bilinearAutomorphisms B ↔ ∀ q : n × n × n,
      aeval (coordinates g).toFunction (bracketRelation B q.1 q.2.1 q.2.2) = 0 := by
  rw [mem_bilinearAutomorphisms_iff_basis]
  simp only [eval_bracketRelation, sub_eq_zero]
  constructor
  · intro h q
    exact congrFun (h q.2.1 q.2.2) q.1
  · intro h i j
    funext r
    exact h (r, i, j)

theorem isClosed_bilinearAutomorphisms
    (B : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) :
    letI := topology (k := k) (n := n)
    IsClosed (bilinearAutomorphisms B : Set (Matrix.GeneralLinearGroup n k)) :=
  isClosed_subgroup_of_polynomial_constraints (bilinearAutomorphisms B)
    (fun q : n × n × n => bracketRelation B q.1 q.2.1 q.2.2)
    (mem_bilinearAutomorphisms_iff_equations B)

variable {α : Type*} [LinearOrder α]

/-- Invertible block triangular matrices. Reverse the order on the block labels
to use the decreasing-filtration convention. -/
def blockTriangularSubgroup (b : n → α) : Subgroup (Matrix.GeneralLinearGroup n k) where
  carrier := {g | g.val.BlockTriangular b}
  one_mem' := Matrix.blockTriangular_one
  mul_mem' := fun hg hh => hg.mul hh
  inv_mem' := by
    intro g hg
    letI := g.invertible
    change (g⁻¹).val.BlockTriangular b
    rw [Matrix.GeneralLinearGroup.coe_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hg

def flagRelation (b : n → α) (q : {q : n × n // b q.2 < b q.1}) :
    MvPolynomial (Coordinate n) k := X (some q.val)

theorem mem_blockTriangularSubgroup_iff_equations (b : n → α)
    (g : Matrix.GeneralLinearGroup n k) :
    g ∈ blockTriangularSubgroup (k := k) b ↔
      ∀ q, aeval (coordinates g).toFunction (flagRelation (k := k) b q) = 0 := by
  constructor
  · intro hg q
    rw [flagRelation, aeval_X]
    exact hg q.property
  · intro hg i j hij
    have h := hg ⟨(i, j), hij⟩
    rw [flagRelation, aeval_X] at h
    exact h

theorem isClosed_blockTriangularSubgroup (b : n → α) :
    letI := topology (k := k) (n := n)
    IsClosed (blockTriangularSubgroup (k := k) b : Set (Matrix.GeneralLinearGroup n k)) :=
  isClosed_subgroup_of_polynomial_constraints (blockTriangularSubgroup (k := k) b)
    (flagRelation (k := k) b) (mem_blockTriangularSubgroup_iff_equations b)

/-- Matrix automorphisms preserving both a bilinear operation and a finite
coordinate flag. This specializes to filtered Lie automorphisms. -/
def filteredBilinearAutomorphisms
    (B : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (b : n → α) :
    Subgroup (Matrix.GeneralLinearGroup n k) :=
  bilinearAutomorphisms B ⊓ blockTriangularSubgroup b

def filteredRelation
    (B : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (b : n → α) :
    (n × n × n) ⊕ {q : n × n // b q.2 < b q.1} → MvPolynomial (Coordinate n) k
  | Sum.inl q => bracketRelation B q.1 q.2.1 q.2.2
  | Sum.inr q => flagRelation b q

theorem mem_filteredBilinearAutomorphisms_iff_equations
    (B : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (b : n → α)
    (g : Matrix.GeneralLinearGroup n k) :
    g ∈ filteredBilinearAutomorphisms B b ↔
      ∀ q, aeval (coordinates g).toFunction (filteredRelation B b q) = 0 := by
  change (g ∈ bilinearAutomorphisms B ∧ g ∈ blockTriangularSubgroup b) ↔ _
  rw [mem_bilinearAutomorphisms_iff_equations, mem_blockTriangularSubgroup_iff_equations]
  constructor
  · rintro ⟨hB, hb⟩ (q | q)
    · exact hB q
    · exact hb q
  · intro h
    exact ⟨fun q => h (Sum.inl q), fun q => h (Sum.inr q)⟩

theorem isClosed_filteredBilinearAutomorphisms
    (B : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (b : n → α) :
    letI := topology (k := k) (n := n)
    IsClosed (filteredBilinearAutomorphisms B b : Set (Matrix.GeneralLinearGroup n k)) :=
  isClosed_subgroup_of_polynomial_constraints (filteredBilinearAutomorphisms B b)
    (filteredRelation B b) (mem_filteredBilinearAutomorphisms_iff_equations B b)

def filteredAutomorphismPresentation
    (B : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (b : n → α) :
    letI := topology (k := k) (n := n)
    AffinePolynomialGroup k (Coordinate n) (filteredBilinearAutomorphisms B b) := by
  letI := topology (k := k) (n := n)
  exact subgroupPresentationOfPolynomialConstraints (filteredBilinearAutomorphisms B b)
    (filteredRelation B b) (mem_filteredBilinearAutomorphisms_iff_equations B b)

end

end EnvelopingIsomorphism.Descent.MatrixGroup
