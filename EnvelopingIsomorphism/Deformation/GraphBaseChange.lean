import EnvelopingIsomorphism.Deformation.GraphLinearCommutator
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Scalar naturality of the actual linear-Poisson graph operators

The coefficients may lie in a parameter ring. Applying any ring homomorphism
to them commutes with every derivative, graph sum, and formal graph coefficient.
In particular specialization uses the same graph formula throughout a family.
No associativity or formality assertion is made here.
-/

namespace EnvelopingIsomorphism.Deformation

open scoped BigOperators

variable {R S σ : Type*} [CommRing R] [CommRing S]

theorem map_iteratedPDeriv (φ : R →+* S) (is : List σ) (p : MvPolynomial σ R) :
    MvPolynomial.map φ (iteratedPDeriv is p) =
      iteratedPDeriv is (MvPolynomial.map φ p) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [iteratedPDeriv_cons, ← MvPolynomial.pderiv_map, ih]

namespace KontsevichGraph

variable {n d : ℕ}

/-- Apply a ring homomorphism to the actual structural coefficients at every vertex. -/
def mapCoefficients (φ : R →+* S) (α : Coefficients n d R) : Coefficients n d S :=
  fun v i j r ↦ φ (α v i j r)

theorem map_linearCoefficient (φ : R →+* S) (c : Fin d → R) :
    MvPolynomial.map φ (linearCoefficient c) =
      linearCoefficient (fun r ↦ φ (c r)) := by
  simp [linearCoefficient]

theorem map_vertexDerivative (φ : R →+* S) (Γ : KontsevichGraph n)
    (lab : Edge n → Fin d) (v : Vertex n) (p : Polynomial d R) :
    MvPolynomial.map φ (Γ.vertexDerivative lab v p) =
      Γ.vertexDerivative lab v (MvPolynomial.map φ p) :=
  map_iteratedPDeriv φ _ p

theorem map_vertexInput (φ : R →+* S) (α : Coefficients n d R)
    (lab : Edge n → Fin d) (f g : Polynomial d R) (v : Vertex n) :
    MvPolynomial.map φ (vertexInput α lab f g v) =
      vertexInput (mapCoefficients φ α) lab (MvPolynomial.map φ f) (MvPolynomial.map φ g) v := by
  cases v with
  | inl v => exact map_linearCoefficient φ _
  | inr j => simp only [vertexInput]; split <;> rfl

theorem map_labelledOperator (φ : R →+* S) (Γ : KontsevichGraph n)
    (α : Coefficients n d R) (lab : Edge n → Fin d) (f g : Polynomial d R) :
    MvPolynomial.map φ (Γ.labelledOperator α lab f g) =
      Γ.labelledOperator (mapCoefficients φ α) lab (MvPolynomial.map φ f) (MvPolynomial.map φ g) := by
  simp only [labelledOperator_apply, map_prod, map_vertexDerivative, map_vertexInput]

/-- Scalar naturality holds term by term, independently of the graph weights. -/
theorem map_operator (φ : R →+* S) (Γ : KontsevichGraph n)
    (α : Coefficients n d R) (f g : Polynomial d R) :
    MvPolynomial.map φ (Γ.operator α f g) =
      Γ.operator (mapCoefficients φ α) (MvPolynomial.map φ f) (MvPolynomial.map φ g) := by
  simp only [operator_apply, map_sum, map_labelledOperator]

theorem map_cochain (φ : R →+* S) (Γ : KontsevichGraph n)
    (α : Coefficients n d R) (x : Fin 2 → Polynomial d R) :
    MvPolynomial.map φ (Γ.cochain α x) =
      Γ.cochain (mapCoefficients φ α) (fun i ↦ MvPolynomial.map φ (x i)) :=
  map_operator φ Γ α _ _

/-- Both the structural coefficients and the scalar graph weights specialize. -/
theorem map_weightedOperator (φ : R →+* S)
    (s : Finset (KontsevichGraph n)) (w : KontsevichGraph n → R)
    (α : Coefficients n d R) (f g : Polynomial d R) :
    MvPolynomial.map φ (weightedOperator s w α f g) =
      weightedOperator s (fun Γ ↦ φ (w Γ)) (mapCoefficients φ α)
        (MvPolynomial.map φ f) (MvPolynomial.map φ g) := by
  simp only [weightedOperator_apply, map_sum, MvPolynomial.smul_eq_C_mul,
    map_mul, MvPolynomial.map_C, map_operator]

theorem map_finiteStarOperator (φ : R →+* S) (N : ℕ)
    (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
    (w : (j : ℕ) → KontsevichGraph (j + 1) → R)
    (c : Fin d → Fin d → Fin d → R) (f g : Polynomial d R) :
    MvPolynomial.map φ (finiteStarOperator N s w c f g) =
      finiteStarOperator N s (fun j Γ ↦ φ (w j Γ)) (fun i j r ↦ φ (c i j r))
        (MvPolynomial.map φ f) (MvPolynomial.map φ g) := by
  simp only [finiteStarOperator, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.mul_apply', map_add, map_mul, map_sum, map_weightedOperator]
  rfl

/-- The complete graph expansion specializes coefficientwise in its formal parameter. -/
theorem map_graphStarSeries (φ : R →+* S)
    (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
    (w : (j : ℕ) → KontsevichGraph (j + 1) → R)
    (c : Fin d → Fin d → Fin d → R) (f g : Polynomial d R) :
    PowerSeries.map (MvPolynomial.map φ) (graphStarSeries s w c f g) =
      graphStarSeries s (fun j Γ ↦ φ (w j Γ)) (fun i j r ↦ φ (c i j r))
        (MvPolynomial.map φ f) (MvPolynomial.map φ g) := by
  apply PowerSeries.ext
  intro r
  cases r with
  | zero => simp only [PowerSeries.coeff_map, coeff_graphStarSeries_zero, map_mul]
  | succ r =>
    simp only [PowerSeries.coeff_map, coeff_graphStarSeries_succ,
      map_weightedOperator]
    rfl

/-- A polynomial family specializes by the same universal graph weights.
The polynomial parameter in the coefficients is distinct from the power-series parameter. -/
theorem eval_parameter_graphStarSeries (a : R)
    (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
    (w : (j : ℕ) → KontsevichGraph (j + 1) → R)
    (c : Fin d → Fin d → Fin d → _root_.Polynomial R) (f g : Polynomial d R) :
    PowerSeries.map (MvPolynomial.map (_root_.Polynomial.evalRingHom a))
        (graphStarSeries s (fun j Γ ↦ _root_.Polynomial.C (w j Γ)) c
          (MvPolynomial.map _root_.Polynomial.C f) (MvPolynomial.map _root_.Polynomial.C g)) =
      graphStarSeries s w (fun i j r ↦ (c i j r).eval a) f g := by
  simpa [MvPolynomial.map_map, MvPolynomial.map_id, _root_.Polynomial.evalRingHom] using
    map_graphStarSeries (_root_.Polynomial.evalRingHom a) s
      (fun j Γ ↦ _root_.Polynomial.C (w j Γ)) c
      (MvPolynomial.map _root_.Polynomial.C f) (MvPolynomial.map _root_.Polynomial.C g)

end KontsevichGraph

end EnvelopingIsomorphism.Deformation
