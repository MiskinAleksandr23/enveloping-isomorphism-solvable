import EnvelopingIsomorphism.Deformation.GraphBaseChange
import EnvelopingIsomorphism.PBW.FilteredTargetEquivalence

/-!
# Polynomial-valued graph products

Degree lowering makes the complete graph expansion finite on each polynomial
pair. The resulting operation is bilinear and natural in coefficients.
Associativity and unit equations remain explicit pointwise hypotheses when
constructing an associative algebra from this operation.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.KontsevichGraph

open MvPolynomial
open scoped BigOperators

variable {R : Type*} [CommRing R] {d : ℕ}
  (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
  (w : (j : ℕ) → KontsevichGraph (j + 1) → R)
  (c : Fin d → Fin d → Fin d → R)

/-- The complete graph expansion, evaluated as an actual polynomial using
the degree cutoff. All omitted positive-order terms are proved zero below. -/
def polynomialProduct (f g : Polynomial d R) : Polynomial d R :=
  finiteStarOperator (f.totalDegree + g.totalDegree) s w c f g

variable [Nontrivial R]

/-- Any larger cutoff gives exactly the same polynomial. -/
theorem polynomialProduct_eq_finiteStarOperator (f g : Polynomial d R) (N : ℕ)
    (hN : f.totalDegree + g.totalDegree ≤ N) :
    polynomialProduct s w c f g = finiteStarOperator N s w c f g := by
  simp only [polynomialProduct, finiteStarOperator, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.mul_apply']
  congr 1
  apply Finset.sum_subset (Finset.range_mono hN)
  intro j hj hj'
  apply weightedOperator_eq_zero_of_degree_lt
  have hj' : f.totalDegree + g.totalDegree ≤ j := by simpa using hj'
  omega

theorem finiteStarOperator_cutoff_independent (f g : Polynomial d R) (N M : ℕ)
    (hN : f.totalDegree + g.totalDegree ≤ N) (hM : f.totalDegree + g.totalDegree ≤ M) :
    finiteStarOperator N s w c f g = finiteStarOperator M s w c f g :=
  (polynomialProduct_eq_finiteStarOperator s w c f g N hN).symm.trans
    (polynomialProduct_eq_finiteStarOperator s w c f g M hM)

theorem polynomialProduct_add_left (f g h : Polynomial d R) :
    polynomialProduct s w c (f + g) h =
      polynomialProduct s w c f h + polynomialProduct s w c g h := by
  let N := max f.totalDegree g.totalDegree + h.totalDegree
  rw [polynomialProduct_eq_finiteStarOperator s w c (f + g) h N
    (Nat.add_le_add_right (MvPolynomial.totalDegree_add f g) _)]
  rw [polynomialProduct_eq_finiteStarOperator s w c f h N
    (Nat.add_le_add_right (le_max_left _ _) _)]
  rw [polynomialProduct_eq_finiteStarOperator s w c g h N
    (Nat.add_le_add_right (le_max_right _ _) _)]
  simp only [map_add, LinearMap.add_apply]

theorem polynomialProduct_add_right (f g h : Polynomial d R) :
    polynomialProduct s w c f (g + h) =
      polynomialProduct s w c f g + polynomialProduct s w c f h := by
  let N := f.totalDegree + max g.totalDegree h.totalDegree
  rw [polynomialProduct_eq_finiteStarOperator s w c f (g + h) N
    (Nat.add_le_add_left (MvPolynomial.totalDegree_add g h) _)]
  rw [polynomialProduct_eq_finiteStarOperator s w c f g N
    (Nat.add_le_add_left (le_max_left _ _) _)]
  rw [polynomialProduct_eq_finiteStarOperator s w c f h N
    (Nat.add_le_add_left (le_max_right _ _) _)]
  exact map_add _ _ _

theorem polynomialProduct_smul_left (r : R) (f g : Polynomial d R) :
    polynomialProduct s w c (r • f) g = r • polynomialProduct s w c f g := by
  rw [polynomialProduct_eq_finiteStarOperator s w c (r • f) g
    (f.totalDegree + g.totalDegree)
    (Nat.add_le_add_right (MvPolynomial.totalDegree_smul_le r f) _)]
  change finiteStarOperator _ s w c (r • f) g = r • finiteStarOperator _ s w c f g
  simp only [map_smul, LinearMap.smul_apply]

theorem polynomialProduct_smul_right (r : R) (f g : Polynomial d R) :
    polynomialProduct s w c f (r • g) = r • polynomialProduct s w c f g := by
  rw [polynomialProduct_eq_finiteStarOperator s w c f (r • g)
    (f.totalDegree + g.totalDegree)
    (Nat.add_le_add_left (MvPolynomial.totalDegree_smul_le r g) _)]
  change finiteStarOperator _ s w c f (r • g) = r • finiteStarOperator _ s w c f g
  exact map_smul _ _ _

/-- The all-orders polynomial graph operation is genuinely bilinear. -/
def polynomialProductBilinear : Binary R (Polynomial d R) where
  toFun f :=
    { toFun := polynomialProduct s w c f
      map_add' := polynomialProduct_add_right s w c f
      map_smul' := fun r g ↦ polynomialProduct_smul_right s w c r f g }
  map_add' f g := LinearMap.ext (fun h ↦ polynomialProduct_add_left s w c f g h)
  map_smul' r f := LinearMap.ext (fun g ↦ polynomialProduct_smul_left s w c r f g)

@[simp] theorem polynomialProductBilinear_apply (f g : Polynomial d R) :
    polynomialProductBilinear s w c f g = polynomialProduct s w c f g := rfl

@[simp] theorem polynomialProduct_zero_left (f : Polynomial d R) :
    polynomialProduct s w c 0 f = 0 := by
  change polynomialProductBilinear s w c 0 f = 0
  simp only [map_zero, LinearMap.zero_apply]

@[simp] theorem polynomialProduct_zero_right (f : Polynomial d R) :
    polynomialProduct s w c f 0 = 0 := map_zero (polynomialProductBilinear s w c f)

/-- Positive graph orders contribute only below the ordinary product degree. -/
theorem totalDegree_polynomialProduct_sub_mul_add_one_le (f g : Polynomial d R)
    (h : polynomialProduct s w c f g - f * g ≠ 0) :
    (polynomialProduct s w c f g - f * g).totalDegree + 1 ≤ f.totalDegree + g.totalDegree :=
  totalDegree_finiteStarOperator_sub_mul_add_one_le _ s w c f g h

theorem totalDegree_polynomialProduct_le (f g : Polynomial d R) :
    (polynomialProduct s w c f g).totalDegree ≤ f.totalDegree + g.totalDegree :=
  totalDegree_finiteStarOperator_le _ s w c f g

omit [Nontrivial R] in
theorem totalDegree_map_coefficients_le {S : Type*} [CommRing S] (φ : R →+* S)
    (f : Polynomial d R) : (MvPolynomial.map φ f).totalDegree ≤ f.totalDegree := by
  classical
  exact Finset.sup_mono (MvPolynomial.support_map_subset φ f)

omit [Nontrivial R] in
/-- The entire polynomial-valued expansion commutes with coefficient maps.
A common original degree bound handles degree drops under specialization. -/
theorem map_polynomialProduct {S : Type*} [CommRing S] [Nontrivial S] (φ : R →+* S)
    (f g : Polynomial d R) :
    MvPolynomial.map φ (polynomialProduct s w c f g) =
      polynomialProduct s (fun j Γ ↦ φ (w j Γ)) (fun i j r ↦ φ (c i j r))
        (MvPolynomial.map φ f) (MvPolynomial.map φ g) := by
  rw [polynomialProduct, map_finiteStarOperator]
  exact (polynomialProduct_eq_finiteStarOperator s _ _ _ _
    (f.totalDegree + g.totalDegree)
    (Nat.add_le_add (totalDegree_map_coefficients_le φ f)
      (totalDegree_map_coefficients_le φ g))).symm

/-- The analytical obligations needed to turn the actual graph product into
an associative unital algebra. These equations are hypotheses, not conclusions
of the graph-degree calculation. -/
structure ProductLaws : Prop where
  associative : ∀ f g h, polynomialProduct s w c (polynomialProduct s w c f g) h =
    polynomialProduct s w c f (polynomialProduct s w c g h)
  one_mul : ∀ f, polynomialProduct s w c 1 f = f
  mul_one : ∀ f, polynomialProduct s w c f 1 = f

/-- The polynomial module with its graph product. The multiplication data and
the actual product laws remain visible in the type, avoiding a second competing
ring structure on the untagged native polynomial type. -/
@[nolint unusedArguments]
def ProductAlgebra (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
    (w : (j : ℕ) → KontsevichGraph (j + 1) → R)
    (c : Fin d → Fin d → Fin d → R) (_laws : ProductLaws s w c) : Type _ := Polynomial d R

variable (laws : ProductLaws s w c)

instance : AddCommGroup (ProductAlgebra s w c laws) := inferInstanceAs (AddCommGroup (Polynomial d R))
instance : Nontrivial (ProductAlgebra s w c laws) := inferInstanceAs (Nontrivial (Polynomial d R))

/-- A genuine ring instance for the graph multiplication, conditional only on
its explicitly stated pointwise associativity and unit identities. -/
instance productAlgebraRing : Ring (ProductAlgebra s w c laws) where
  __ := (inferInstance : AddCommGroup (Polynomial d R))
  __ := (inferInstance : AddGroupWithOne (Polynomial d R))
  mul := polynomialProduct s w c
  mul_assoc := laws.associative
  one_mul := laws.one_mul
  mul_one := laws.mul_one
  zero_mul := polynomialProduct_zero_left s w c
  mul_zero := polynomialProduct_zero_right s w c
  left_distrib := polynomialProduct_add_right s w c
  right_distrib := polynomialProduct_add_left s w c

instance : Module R (ProductAlgebra s w c laws) := inferInstanceAs (Module R (Polynomial d R))

instance productAlgebraAlgebra : Algebra R (ProductAlgebra s w c laws) :=
  Algebra.ofModule (R := R) (A := ProductAlgebra s w c laws)
    (fun r f g ↦ by
      change polynomialProduct s w c (r • f) g = r • polynomialProduct s w c f g
      exact polynomialProduct_smul_left s w c r f g)
    (fun r f g ↦ by
      change polynomialProduct s w c f (r • g) = r • polynomialProduct s w c f g
      exact polynomialProduct_smul_right s w c r f g)

/-- The actual graph algebra has the ordinary polynomial module as coordinates. -/
def toPolynomial : ProductAlgebra s w c laws ≃ₗ[R] Polynomial d R := LinearEquiv.refl R _

@[simp] theorem toPolynomial_mul (f g : ProductAlgebra s w c laws) :
    toPolynomial s w c laws (f * g) =
      polynomialProduct s w c (toPolynomial s w c laws f) (toPolynomial s w c laws g) := rfl

@[simp] theorem toPolynomial_one : toPolynomial s w c laws 1 = 1 := rfl

@[simp] theorem toPolynomial_algebraMap (r : R) :
    toPolynomial s w c laws (algebraMap R (ProductAlgebra s w c laws) r) = C r := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, toPolynomial_one]
  simp [MvPolynomial.smul_eq_C_mul]

/-- Coefficient specialization is a genuine ring homomorphism between graph
algebras whenever the actual product laws have been supplied at both ends. -/
def coefficientMap {S : Type*} [CommRing S] [Nontrivial S] (φ : R →+* S)
    (laws' : ProductLaws s (fun j Γ ↦ φ (w j Γ)) (fun i j r ↦ φ (c i j r))) :
    ProductAlgebra s w c laws →+*
      ProductAlgebra s (fun j Γ ↦ φ (w j Γ)) (fun i j r ↦ φ (c i j r)) laws' where
  toFun f := (toPolynomial s _ _ laws').symm (MvPolynomial.map φ (toPolynomial s w c laws f))
  map_zero' := by
    apply (toPolynomial s _ _ laws').injective
    simp only [map_zero]
  map_one' := by
    apply (toPolynomial s _ _ laws').injective
    simp only [LinearEquiv.apply_symm_apply, toPolynomial_one, map_one]
  map_add' f g := by
    apply (toPolynomial s _ _ laws').injective
    simp only [LinearEquiv.apply_symm_apply, map_add]
  map_mul' f g := by
    apply (toPolynomial s _ _ laws').injective
    simp only [LinearEquiv.apply_symm_apply, toPolynomial_mul, map_polynomialProduct]

@[simp] theorem toPolynomial_coefficientMap {S : Type*} [CommRing S] [Nontrivial S]
    (φ : R →+* S)
    (laws' : ProductLaws s (fun j Γ ↦ φ (w j Γ)) (fun i j r ↦ φ (c i j r)))
    (f : ProductAlgebra s w c laws) :
    toPolynomial s _ _ laws' (coefficientMap s w c laws φ laws' f) =
      MvPolynomial.map φ (toPolynomial s w c laws f) :=
  LinearEquiv.apply_symm_apply _ _

/-- The ordinary monomial basis of the actual graph algebra's underlying module. -/
def monomialBasis : Module.Basis (Fin d →₀ ℕ) R (ProductAlgebra s w c laws) :=
  (MvPolynomial.basisMonomials (Fin d) R).map (toPolynomial s w c laws).symm

@[simp] theorem toPolynomial_monomialBasis (m : Fin d →₀ ℕ) :
    toPolynomial s w c laws (monomialBasis s w c laws m) = monomial m 1 := by
  simp [monomialBasis]

@[simp] theorem monomialBasis_zero : monomialBasis s w c laws 0 = 1 := by
  apply (toPolynomial s w c laws).injective
  rw [toPolynomial_monomialBasis, toPolynomial_one]
  simp

@[simp] theorem monomialBasis_repr_apply (x : ProductAlgebra s w c laws) (m : Fin d →₀ ℕ) :
    (monomialBasis s w c laws).repr x m = coeff m (toPolynomial s w c laws x) := rfl

theorem polynomialProduct_generator_support (i : Fin d) (m : Fin d →₀ ℕ)
    {q : Fin d →₀ ℕ}
    (hq : q ∈ (polynomialProduct s w c (X i) (monomial m 1) - X i * monomial m 1).support) :
    q.degree < m.degree + 1 := by
  have hn : polynomialProduct s w c (X i) (monomial m 1) - X i * monomial m 1 ≠ 0 :=
    MvPolynomial.support_nonempty.mp ⟨q, hq⟩
  have hd := totalDegree_polynomialProduct_sub_mul_add_one_le s w c (X i) (monomial m 1) hn
  have hqdeg : q.degree ≤
      (polynomialProduct s w c (X i) (monomial m 1) - X i * monomial m 1).totalDegree := by
    simpa only [Finsupp.degree_apply, Finsupp.sum] using MvPolynomial.le_totalDegree hq
  have hi : (X i : Polynomial d R).totalDegree ≤ 1 := by simp
  have hm : (monomial m (1 : R)).totalDegree ≤ m.degree := by
    simpa only [Finsupp.degree_apply, Finsupp.sum, Function.id_def] using
      MvPolynomial.totalDegree_monomial_le m (1 : R)
  omega

section EnvelopingIdentification

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [LieRing L] [LieAlgebra R L]
  (b : Module.Basis (Fin d) R L) (g : L →ₗ⁅R⁆ ProductAlgebra s w c laws)
  (hgen : ∀ i, toPolynomial s w c laws (g (b i)) = X i)

include hgen

/-- The graph-degree estimate supplies the generator-triangularity input of
the enveloping equivalence; it is not a separate hypothesis. -/
theorem generatorTriangular :
    PBW.FilteredTargetEquivalence.GeneratorTriangular b (monomialBasis s w c laws) g := by
  intro i m q hq
  change q.degree < m.degree + 1
  change q ∈ ((monomialBasis s w c laws).repr (g (b i) * monomialBasis s w c laws m) -
    Finsupp.single (Finsupp.single i 1 + m) 1).support at hq
  rw [Finsupp.mem_support_iff, Finsupp.sub_apply, monomialBasis_repr_apply,
    toPolynomial_mul, hgen i, toPolynomial_monomialBasis] at hq
  apply polynomialProduct_generator_support s w c i m
  apply MvPolynomial.mem_support_iff.mpr
  convert hq using 1
  simp [coeff_sub, MvPolynomial.X, monomial_mul, Finsupp.single_apply]

/-- Once actual associativity/unit laws and exact Lie-generator relations
are supplied, the graph algebra is canonically the native enveloping algebra. -/
def envelopingEquiv : UniversalEnvelopingAlgebra R L ≃ₐ[R] ProductAlgebra s w c laws :=
  PBW.FilteredTargetEquivalence.canonicalEquiv b (monomialBasis s w c laws) g
    (monomialBasis_zero s w c laws) (generatorTriangular s w c laws b g hgen)

@[simp] theorem envelopingEquiv_ι (x : L) :
    envelopingEquiv s w c laws b g hgen (UniversalEnvelopingAlgebra.ι R x) = g x :=
  PBW.FilteredTargetEquivalence.canonicalEquiv_ι b (monomialBasis s w c laws) g _ _ x

@[simp] theorem envelopingEquiv_ι_basis (i : Fin d) :
    toPolynomial s w c laws
      (envelopingEquiv s w c laws b g hgen (UniversalEnvelopingAlgebra.ι R (b i))) = X i := by
  rw [envelopingEquiv_ι, hgen]

end EnvelopingIdentification

end EnvelopingIsomorphism.Deformation.KontsevichGraph
