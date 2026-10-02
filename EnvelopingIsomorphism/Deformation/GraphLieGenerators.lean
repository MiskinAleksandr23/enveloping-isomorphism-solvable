import EnvelopingIsomorphism.Deformation.GraphPBWComparison
import EnvelopingIsomorphism.Deformation.Kontsevich.NormalizationOverAlgebra
import EnvelopingIsomorphism.Poisson.LinearJacobi

/-!
# Native Lie generators in the geometrically normalized graph algebra

The first graph weights are the actual normalized one-vertex integrals.
The Lie-generator relations are derived from the graph commutator theorem
and the given native Lie bracket. Only the analytical product laws remain
as hypotheses in the resulting enveloping and comparison equivalences.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.KontsevichGraph

open scoped BigOperators
open MvPolynomial

variable {R : Type*} [CommRing R] [Algebra ℝ R] {d : ℕ}
  (sHigher : (j : ℕ) → Finset (KontsevichGraph (j + 2)))
  (wHigher : (j : ℕ) → KontsevichGraph (j + 2) → R)

/-- All one-vertex graphs occur at first order; later graph sets are retained. -/
def geometricFirstSets : (j : ℕ) → Finset (KontsevichGraph (j + 1))
  | 0 => Finset.univ
  | j + 1 => sHigher j

/-- The first weights are the actual geometric integrals, mapped into the
coefficient algebra. The higher graph weights are retained unchanged. -/
def geometricFirstWeights : (j : ℕ) → KontsevichGraph (j + 1) → R
  | 0 => fun Γ ↦ algebraMap ℝ R (Kontsevich.geometricOneVertexGraphWeight Γ)
  | j + 1 => wHigher j

@[simp] theorem geometricFirstSets_zero : geometricFirstSets sHigher 0 = Finset.univ := rfl
@[simp] theorem geometricFirstSets_succ (j : ℕ) : geometricFirstSets sHigher (j + 1) = sHigher j := rfl
@[simp] theorem geometricFirstWeights_zero (Γ : KontsevichGraph 1) :
    geometricFirstWeights wHigher 0 Γ = algebraMap ℝ R (Kontsevich.geometricOneVertexGraphWeight Γ) := rfl
@[simp] theorem geometricFirstWeights_succ (j : ℕ) (Γ : KontsevichGraph (j + 2)) :
    geometricFirstWeights wHigher (j + 1) Γ = wHigher j Γ := rfl

theorem geometric_first_operator (c : Fin d → Fin d → Fin d → R) (hc : IsSkew c)
    (p q : Polynomial d R) :
    weightedOperator (geometricFirstSets sHigher 0) (geometricFirstWeights wHigher 0)
      (fun _ ↦ c) p q =
        algebraMap ℝ R (1 / 2) • EnvelopingIsomorphism.Poisson.linearBracket c p q := by
  have h := Kontsevich.weightedOperator_oneVertex_geometric_over_algebra c hc
  have h' := LinearMap.congr_fun (LinearMap.congr_fun h p) q
  simpa only [geometricFirstSets, geometricFirstWeights, LinearMap.smul_apply,
    Kontsevich.linearPoissonBinary_apply] using h'

variable [Nontrivial R]

/-- The complete polynomial graph product has the exact native linear Poisson
commutator on linear polynomials, with normalization supplied by the integrals. -/
theorem geometric_polynomialProduct_linear_commutator
    (c : Fin d → Fin d → Fin d → R) (hc : IsSkew c)
    (p q : Polynomial d R) (hp : p.totalDegree ≤ 1) (hq : q.totalDegree ≤ 1) :
    polynomialProduct (geometricFirstSets sHigher) (geometricFirstWeights wHigher) c p q -
        polynomialProduct (geometricFirstSets sHigher) (geometricFirstWeights wHigher) c q p =
      EnvelopingIsomorphism.Poisson.linearBracket c p q := by
  let N := p.totalDegree + q.totalDegree + 1
  rw [polynomialProduct_eq_finiteStarOperator _ _ _ p q N (by dsimp [N]; omega),
    polynomialProduct_eq_finiteStarOperator _ _ _ q p N (by dsimp [N]; omega)]
  simpa only [one_smul] using
    finiteStarOperator_linear_commutator_of_normalization N (by dsimp [N]; omega)
      (geometricFirstSets sHigher) (geometricFirstWeights wHigher) c hc
      (algebraMap ℝ R (1 / 2)) 1 (Kontsevich.geometric_half_add_self)
      (geometric_first_operator sHigher wHigher c hc) p q hp hq

section NativeLie

variable {L : Type*} [LieRing L] [LieAlgebra R L] (b : Module.Basis (Fin d) R L)

omit [Algebra ℝ R] [Nontrivial R] in
theorem structureCoeff_isSkew : IsSkew (EnvelopingIsomorphism.Poisson.structureCoeff b) :=
  fun i j r ↦ EnvelopingIsomorphism.Poisson.structureCoeff_skew b j i r

omit [Algebra ℝ R] in
theorem totalDegree_linearPolynomial_le (x : L) :
    (EnvelopingIsomorphism.Poisson.linearPolynomial b x).totalDegree ≤ 1 := by
  simpa only [EnvelopingIsomorphism.Poisson.linearPolynomial_apply, linearCoefficient] using
    totalDegree_linearCoefficient_le (fun i ↦ b.repr x i)

variable (laws : ProductLaws (geometricFirstSets sHigher) (geometricFirstWeights wHigher)
  (EnvelopingIsomorphism.Poisson.structureCoeff b))

/-- Native linear vectors included as coordinate-linear polynomials in the actual graph algebra. -/
def geometricGeneratorLinear : L →ₗ[R]
    ProductAlgebra (geometricFirstSets sHigher) (geometricFirstWeights wHigher)
      (EnvelopingIsomorphism.Poisson.structureCoeff b) laws :=
  (toPolynomial _ _ _ laws).symm.toLinearMap.comp (EnvelopingIsomorphism.Poisson.linearPolynomial b)

@[simp] theorem toPolynomial_geometricGeneratorLinear (x : L) :
    toPolynomial _ _ _ laws (geometricGeneratorLinear sHigher wHigher b laws x) =
      EnvelopingIsomorphism.Poisson.linearPolynomial b x :=
  LinearEquiv.apply_symm_apply _ _

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The graph Lie-generator map is constructed from the native bracket.
There is no extra commutator or Lie-homomorphism premise. -/
def geometricGeneratorLieHom : L →ₗ⁅R⁆
    ProductAlgebra (geometricFirstSets sHigher) (geometricFirstWeights wHigher)
      (EnvelopingIsomorphism.Poisson.structureCoeff b) laws where
  toLinearMap := geometricGeneratorLinear sHigher wHigher b laws
  map_lie' {x y} := by
    apply (toPolynomial _ _ _ laws).injective
    change toPolynomial _ _ _ laws (geometricGeneratorLinear sHigher wHigher b laws ⁅x, y⁆) =
      toPolynomial _ _ _ laws ⁅geometricGeneratorLinear sHigher wHigher b laws x,
        geometricGeneratorLinear sHigher wHigher b laws y⁆
    rw [toPolynomial_geometricGeneratorLinear, Ring.lie_def, map_sub,
      toPolynomial_mul, toPolynomial_mul, toPolynomial_geometricGeneratorLinear,
      toPolynomial_geometricGeneratorLinear]
    rw [geometric_polynomialProduct_linear_commutator sHigher wHigher
      (EnvelopingIsomorphism.Poisson.structureCoeff b) (structureCoeff_isSkew b)
      _ _ (totalDegree_linearPolynomial_le b x) (totalDegree_linearPolynomial_le b y),
      EnvelopingIsomorphism.Poisson.linearBracket_linearPolynomial]

@[simp] theorem toPolynomial_geometricGeneratorLieHom (x : L) :
    toPolynomial _ _ _ laws (geometricGeneratorLieHom sHigher wHigher b laws x) =
      EnvelopingIsomorphism.Poisson.linearPolynomial b x :=
  toPolynomial_geometricGeneratorLinear sHigher wHigher b laws x

@[simp] theorem geometricGeneratorLieHom_basis (i : Fin d) :
    toPolynomial _ _ _ laws (geometricGeneratorLieHom sHigher wHigher b laws (b i)) = X i := by
  rw [toPolynomial_geometricGeneratorLieHom, EnvelopingIsomorphism.Poisson.linearPolynomial_basis]

/-- The actual normalized graph target is the native enveloping algebra,
with only the analytical product laws still supplied as hypotheses. -/
def geometricEnvelopingEquiv : UniversalEnvelopingAlgebra R L ≃ₐ[R]
    ProductAlgebra (geometricFirstSets sHigher) (geometricFirstWeights wHigher)
      (EnvelopingIsomorphism.Poisson.structureCoeff b) laws :=
  envelopingEquiv _ _ _ laws b (geometricGeneratorLieHom sHigher wHigher b laws)
    (geometricGeneratorLieHom_basis sHigher wHigher b laws)

local instance : Algebra ℚ R := Algebra.restrictScalars ℚ ℝ R

/-- The actual symmetrized graph comparison with its Lie-generator premise discharged. -/
def geometricComparisonEquiv : Polynomial d R ≃ₗ[R] Polynomial d R :=
  comparisonEquiv _ _ _ laws b (geometricGeneratorLieHom sHigher wHigher b laws)
    (geometricGeneratorLieHom_basis sHigher wHigher b laws)

theorem geometricComparisonEquiv_toLinearMap :
    (geometricComparisonEquiv sHigher wHigher b laws).toLinearMap =
      comparisonMap (geometricFirstSets sHigher) (geometricFirstWeights wHigher)
        (EnvelopingIsomorphism.Poisson.structureCoeff b) :=
  comparisonEquiv_toLinearMap _ _ _ laws b (geometricGeneratorLieHom sHigher wHigher b laws)
    (geometricGeneratorLieHom_basis sHigher wHigher b laws)

@[simp] theorem geometricComparisonEquiv_X (i : Fin d) :
    geometricComparisonEquiv sHigher wHigher b laws (X i) = X i :=
  comparisonEquiv_X _ _ _ laws b (geometricGeneratorLieHom sHigher wHigher b laws)
    (geometricGeneratorLieHom_basis sHigher wHigher b laws) i

@[simp] theorem geometricComparisonEquiv_symm_X (i : Fin d) :
    (geometricComparisonEquiv sHigher wHigher b laws).symm (X i) = X i :=
  comparisonEquiv_symm_X _ _ _ laws b (geometricGeneratorLieHom sHigher wHigher b laws)
    (geometricGeneratorLieHom_basis sHigher wHigher b laws) i

include laws in
theorem geometricComparison_symProduct (p q : Polynomial d R) :
    comparisonMap (geometricFirstSets sHigher) (geometricFirstWeights wHigher)
        (EnvelopingIsomorphism.Poisson.structureCoeff b)
        (EnvelopingIsomorphism.Rees.SymmetricPBWProduct.symProduct b p q) =
      polynomialProduct (geometricFirstSets sHigher) (geometricFirstWeights wHigher)
        (EnvelopingIsomorphism.Poisson.structureCoeff b)
        (comparisonMap (geometricFirstSets sHigher) (geometricFirstWeights wHigher)
          (EnvelopingIsomorphism.Poisson.structureCoeff b) p)
        (comparisonMap (geometricFirstSets sHigher) (geometricFirstWeights wHigher)
          (EnvelopingIsomorphism.Poisson.structureCoeff b) q) :=
  comparisonMap_symProduct _ _ _ laws b (geometricGeneratorLieHom sHigher wHigher b laws)
    (geometricGeneratorLieHom_basis sHigher wHigher b laws) p q

end NativeLie

end EnvelopingIsomorphism.Deformation.KontsevichGraph
