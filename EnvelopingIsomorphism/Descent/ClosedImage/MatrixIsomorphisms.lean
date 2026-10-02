import EnvelopingIsomorphism.Descent.ClosedImage.DiagonalImage
import EnvelopingIsomorphism.Descent.ClosedImage.CosetImage

/-! # Explicit equations for filtered and marked bilinear-algebra isomorphisms

Taking the bilinear operations to be Lie brackets gives the finite equations
for the isomorphism sets used in H2 and the marked fiber used in H4.
-/

namespace EnvelopingIsomorphism.Descent.MatrixGroup

open Set Topology MvPolynomial
open scoped Matrix

noncomputable section

variable {k n α : Type*} [Field k] [Fintype n] [DecidableEq n] [LinearOrder α]

def PreservesBilinear
    (B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k))
    (g : Matrix.GeneralLinearGroup n k) : Prop :=
  ∀ x y, linearEquiv g (B x y) = C (linearEquiv g x) (linearEquiv g y)

theorem preservesBilinear_iff_basis
    (B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (g : Matrix.GeneralLinearGroup n k) :
    PreservesBilinear B C g ↔ ∀ i j,
      linearEquiv g (B (Pi.single i 1) (Pi.single j 1)) =
        C (linearEquiv g (Pi.single i 1)) (linearEquiv g (Pi.single j 1)) := by
  constructor
  · intro h i j
    exact h _ _
  · intro h
    have heq : B.compr₂ (linearEquiv g).toLinearMap =
        C.compl₁₂ (linearEquiv g).toLinearMap (linearEquiv g).toLinearMap := by
      apply (Pi.basisFun k n).ext
      intro i
      apply (Pi.basisFun k n).ext
      intro j
      simpa only [Pi.basisFun_apply, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
        LinearEquiv.coe_coe] using h i j
    intro x y
    exact LinearMap.congr_fun (LinearMap.congr_fun heq x) y

def isomorphismRelation
    (B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (r i j : n) :
    MvPolynomial (Coordinate n) k :=
  (∑ l, X (some (r, l)) * MvPolynomial.C (B (Pi.single i 1) (Pi.single j 1) l)) -
    ∑ a, ∑ b, X (some (a, i)) * X (some (b, j)) *
      MvPolynomial.C (C (Pi.single a 1) (Pi.single b 1) r)

theorem eval_isomorphismRelation
    (B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k))
    (g : Matrix.GeneralLinearGroup n k) (r i j : n) :
    aeval (coordinates g).toFunction (isomorphismRelation B C r i j) =
      linearEquiv g (B (Pi.single i 1) (Pi.single j 1)) r -
        C (linearEquiv g (Pi.single i 1)) (linearEquiv g (Pi.single j 1)) r := by
  simp only [linearEquiv_apply, Matrix.mulVec_single_one]
  rw [bilinear_apply_eq_sum]
  simp only [isomorphismRelation, map_sub, map_sum, map_mul, aeval_X, aeval_C,
    Algebra.algebraMap_self_apply, Matrix.col_apply, Matrix.mulVec_apply_eq_sum]
  rfl

theorem preservesBilinear_iff_equations
    (B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (g : Matrix.GeneralLinearGroup n k) :
    PreservesBilinear B C g ↔ ∀ q : n × n × n,
      aeval (coordinates g).toFunction (isomorphismRelation B C q.1 q.2.1 q.2.2) = 0 := by
  rw [preservesBilinear_iff_basis]
  simp only [eval_isomorphismRelation, sub_eq_zero]
  constructor
  · intro h q
    exact congrFun (h q.2.1 q.2.2) q.1
  · intro h i j
    funext r
    exact h (r, i, j)

def filteredIsomorphismRelation
    (B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (b : n → α) :
    (n × n × n) ⊕ {q : n × n // b q.2 < b q.1} → MvPolynomial (Coordinate n) k
  | Sum.inl q => isomorphismRelation B C q.1 q.2.1 q.2.2
  | Sum.inr q => flagRelation b q

def filteredIsomorphismEquations
    (B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (b : n → α) :
    Ideal (MvPolynomial (Coordinate n) k) :=
  subgroupEquations (filteredIsomorphismRelation B C b)

theorem coordinates_mem_subgroupEquations_iff {ι : Type*}
    (p : ι → MvPolynomial (Coordinate n) k) (g : Matrix.GeneralLinearGroup n k) :
    coordinates g ∈ AffinePoint.zeros (subgroupEquations p) ↔
      ∀ i, aeval (coordinates g).toFunction (p i) = 0 := by
  rw [subgroupEquations, AffinePoint.zeros_sup]
  have hg : coordinates g ∈ AffinePoint.zeros equations :=
    range_coordinates (k := k) (n := n) ▸ Set.mem_range_self g
  change (coordinates g ∈ AffinePoint.zeros equations ∧
    (coordinates g).toFunction ∈ zeroLocus k (Ideal.span (Set.range p))) ↔ _
  rw [zeroLocus_span]
  simp only [Set.mem_setOf_eq, Set.forall_mem_range, hg, true_and]

theorem coordinates_mem_filteredIsomorphismEquations_iff
    (B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (b : n → α)
    (g : Matrix.GeneralLinearGroup n k) :
    coordinates g ∈ AffinePoint.zeros (filteredIsomorphismEquations B C b) ↔
      PreservesBilinear B C g ∧ g ∈ blockTriangularSubgroup b := by
  rw [filteredIsomorphismEquations, coordinates_mem_subgroupEquations_iff,
    preservesBilinear_iff_equations, mem_blockTriangularSubgroup_iff_equations]
  constructor
  · intro h
    exact ⟨fun q => h (Sum.inl q), fun q => h (Sum.inr q)⟩
  · rintro ⟨hB, hb⟩ (q | q)
    · exact hB q
    · exact hb q

def markedIsomorphismRelation
    (B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (b : n → α)
    (ι : Matrix.GeneralLinearGroup n k) :
    ((n × n × n) ⊕ {q : n × n // b q.2 < b q.1}) ⊕ Coordinate n →
      MvPolynomial (Coordinate n) k
  | Sum.inl q => filteredIsomorphismRelation B C b q
  | Sum.inr i => diagonalPolynomial b i - MvPolynomial.C ((coordinates ι).toFunction i)

/-- Determinant, bracket, flag, and prescribed-diagonal equations for the marked
isomorphism fiber. Every indexing type here is finite. -/
def markedIsomorphismEquations
    (B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (b : n → α)
    (ι : Matrix.GeneralLinearGroup n k) : Ideal (MvPolynomial (Coordinate n) k) :=
  subgroupEquations (markedIsomorphismRelation B C b ι)

theorem coordinates_mem_markedIsomorphismEquations_iff
    (B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (b : n → α)
    (ι g : Matrix.GeneralLinearGroup n k) :
    coordinates g ∈ AffinePoint.zeros (markedIsomorphismEquations B C b ι) ↔
      PreservesBilinear B C g ∧ g ∈ blockTriangularSubgroup b ∧
        AffinePoint.polynomialMap (diagonalPolynomial b) (coordinates g) = coordinates ι := by
  rw [markedIsomorphismEquations, coordinates_mem_subgroupEquations_iff]
  constructor
  · intro h
    have hfiltered : coordinates g ∈ AffinePoint.zeros (filteredIsomorphismEquations B C b) := by
      rw [filteredIsomorphismEquations, coordinates_mem_subgroupEquations_iff]
      exact fun q => h (Sum.inl q)
    obtain ⟨hB, hb⟩ := (coordinates_mem_filteredIsomorphismEquations_iff B C b g).mp hfiltered
    refine ⟨hB, hb, ?_⟩
    apply funext
    intro i
    have hi := h (Sum.inr i)
    rw [markedIsomorphismRelation, map_sub, aeval_C, Algebra.algebraMap_self_apply] at hi
    exact sub_eq_zero.mp hi
  · rintro ⟨hB, hb, hdiag⟩ (q | i)
    · have hfiltered := (coordinates_mem_filteredIsomorphismEquations_iff B C b g).mpr ⟨hB, hb⟩
      rw [filteredIsomorphismEquations, coordinates_mem_subgroupEquations_iff] at hfiltered
      exact hfiltered q
    · rw [markedIsomorphismRelation, map_sub, aeval_C, Algebra.algebraMap_self_apply]
      apply sub_eq_zero.mpr
      exact congrArg (fun x : AffinePoint k (Coordinate n) => x.toFunction i) hdiag

end

end EnvelopingIsomorphism.Descent.MatrixGroup
