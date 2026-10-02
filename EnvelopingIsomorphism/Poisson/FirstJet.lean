import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# The first jet of a linear Poisson map

The coefficient calculation in block G3 is independent of characteristic and of Jacobi.
In particular, the constant terms of the two polynomial inputs need not vanish.
The final construction uses Mathlib's `LieAlgebra`, `Basis`, and `LieHom`.
-/

noncomputable section

namespace EnvelopingIsomorphism.Poisson

open MvPolynomial Module
open scoped BigOperators

universe u v w

variable {R : Type u} [CommRing R]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- The coefficient of the coordinate `X i`. -/
def linearCoeff (i : ι) (p : MvPolynomial ι R) : R :=
  coeff (Finsupp.single i 1) p

/-- A coordinatewise linear bracket tensor. Jacobi is not needed for the jet calculation. -/
def linearBracket (c : ι → ι → ι → R)
    (p q : MvPolynomial ι R) : MvPolynomial ι R :=
  ∑ i, ∑ j, ∑ r, C (c i j r) * (X r * (pderiv i p * pderiv j q))

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem constantCoeff_pderiv (i : ι) (p : MvPolynomial ι R) :
    constantCoeff (pderiv i p) = linearCoeff i p := by
  simp [constantCoeff_eq, coeff_pderiv, linearCoeff]

omit [Fintype ι] in
@[simp] theorem linearCoeff_X_mul (i j : ι) (p : MvPolynomial ι R) :
    linearCoeff i (X j * p) = if j = i then constantCoeff p else 0 := by
  by_cases h : j = i
  · subst j
    simpa [linearCoeff, constantCoeff_eq] using coeff_X_mul (0 : ι →₀ ℕ) i p
  · simp [linearCoeff, coeff_X_mul', h]

omit [DecidableEq ι] in
@[simp] theorem constantCoeff_linearBracket (c : ι → ι → ι → R)
    (p q : MvPolynomial ι R) : constantCoeff (linearBracket c p q) = 0 := by
  simp [linearBracket]

/-- Higher polynomial degrees cannot contribute to the first jet of a linear bracket. -/
theorem linearCoeff_linearBracket (c : ι → ι → ι → R)
    (p q : MvPolynomial ι R) (r : ι) :
    linearCoeff r (linearBracket c p q) =
      ∑ i, ∑ j, c i j r * (linearCoeff i p * linearCoeff j q) := by
  simp only [linearBracket, linearCoeff, coeff_sum, coeff_C_mul]
  change (∑ i, ∑ j, ∑ a, c i j a * linearCoeff r
    (X a * (pderiv i p * pderiv j q))) = _
  simp only [linearCoeff_X_mul, map_mul, constantCoeff_pderiv]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

@[simp] theorem linearBracket_X_X (c : ι → ι → ι → R) (i j : ι) :
    linearBracket c (X i) (X j) = ∑ r, C (c i j r) * X r := by
  simp [linearBracket, pderiv_X, Pi.single_apply]

variable {κ : Type w} [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] in
/-- The exact matrix identity, allowing arbitrary constant terms of the images. -/
theorem firstJet_equation (cL : ι → ι → ι → R) (cM : κ → κ → κ → R)
    (v : ι → MvPolynomial κ R)
    (h : ∀ i j, linearBracket cM (v i) (v j) = ∑ k, C (cL i j k) * v k)
    (i j : ι) (r : κ) :
    (∑ a, ∑ b, cM a b r * (linearCoeff a (v i) * linearCoeff b (v j))) =
      ∑ k, cL i j k * linearCoeff r (v k) := by
  have he := congrArg (linearCoeff r) (h i j)
  rw [linearCoeff_linearBracket] at he
  simpa [linearCoeff, coeff_sum] using he

omit [DecidableEq ι] [DecidableEq κ] in
/-- The constant translation in a Poisson map is a character on the source bracket. -/
theorem constantCoeff_character_equation (cL : ι → ι → ι → R)
    (cM : κ → κ → κ → R) (v : ι → MvPolynomial κ R)
    (h : ∀ i j, linearBracket cM (v i) (v j) = ∑ k, C (cL i j k) * v k)
    (i j : ι) : ∑ k, cL i j k * constantCoeff (v k) = 0 := by
  have he := congrArg (constantCoeff : MvPolynomial κ R → R) (h i j)
  simpa using he.symm

section LieAlgebras

variable {L M : Type*} [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

/-- Structure coefficients in an existing Mathlib Lie algebra. -/
def structureCoeff (b : Basis ι R L) (i j r : ι) : R :=
  b.repr ⁅b i, b j⁆ r

/-- The linear map represented by an extracted first-jet matrix. -/
def firstJetLinearMap (bL : Basis ι R L) (bM : Basis κ R M)
    (P : κ → ι → R) : L →ₗ[R] M :=
  bL.constr R (fun i ↦ ∑ r, P r i • bM r)

omit [DecidableEq κ] in
@[simp] theorem firstJetLinearMap_basis (bL : Basis ι R L) (bM : Basis κ R M)
    (P : κ → ι → R) (i : ι) :
    firstJetLinearMap bL bM P (bL i) = ∑ r, P r i • bM r := by
  simp [firstJetLinearMap]

omit [DecidableEq ι] in
theorem repr_firstJetLinearMap (bL : Basis ι R L) (bM : Basis κ R M)
    (P : κ → ι → R) (x : L) (r : κ) :
    bM.repr (firstJetLinearMap bL bM P x) r =
      ∑ i, bL.repr x i * P r i := by
  simp [firstJetLinearMap, Basis.constr_apply_fintype, Basis.equivFun_apply,
    map_sum, smul_eq_mul, Finsupp.single_apply]

omit [DecidableEq ι] in
/-- Bilinearity reduces bracket preservation of a linear map to basis vectors. -/
theorem map_lie_of_basis (b : Basis ι R L) (f : L →ₗ[R] M)
    (h : ∀ i j, f ⁅b i, b j⁆ = ⁅f (b i), f (b j)⁆) (x y : L) :
    f ⁅x, y⁆ = ⁅f x, f y⁆ := by
  rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul, h]

/-- Exact structure-coefficient equations produce a bundled Lie homomorphism. -/
def lieHomOfStructureEquations (bL : Basis ι R L) (bM : Basis κ R M)
    (P : κ → ι → R)
    (h : ∀ i j r, (∑ a, ∑ b, structureCoeff bM a b r * (P a i * P b j)) =
      ∑ k, structureCoeff bL i j k * P r k) : L →ₗ⁅R⁆ M where
  toLinearMap := firstJetLinearMap bL bM P
  map_lie' {x y} := by
    apply map_lie_of_basis bL
    intro i j
    apply bM.ext_elem
    intro r
    rw [repr_firstJetLinearMap]
    rw [firstJetLinearMap_basis, firstJetLinearMap_basis]
    rw [sum_lie_sum]
    simp only [smul_lie, lie_smul, map_sum, map_smul]
    have he := h i j r
    simpa [structureCoeff, mul_comm, mul_left_comm, mul_assoc] using he.symm

/-- The first jet is a Lie homomorphism if the polynomial images respect generator brackets. -/
def firstJetLieHom (bL : Basis ι R L) (bM : Basis κ R M)
    (v : ι → MvPolynomial κ R)
    (h : ∀ i j, linearBracket (structureCoeff bM) (v i) (v j) =
      ∑ k, C (structureCoeff bL i j k) * v k) : L →ₗ⁅R⁆ M :=
  lieHomOfStructureEquations bL bM (fun r i ↦ linearCoeff r (v i))
    (firstJet_equation (structureCoeff bL) (structureCoeff bM) v h)

/-- A polynomial Poisson algebra map supplies the generator identities for `firstJetLieHom`.
No preservation of the augmentation is assumed. -/
def firstJetOfPoissonAlgHom (bL : Basis ι R L) (bM : Basis κ R M)
    (Φ : MvPolynomial ι R →ₐ[R] MvPolynomial κ R)
    (hΦ : ∀ p q, Φ (linearBracket (structureCoeff bL) p q) =
      linearBracket (structureCoeff bM) (Φ p) (Φ q)) : L →ₗ⁅R⁆ M :=
  firstJetLieHom bL bM (fun i ↦ Φ (X i)) (fun i j ↦ by
    rw [← hΦ, linearBracket_X_X]
    simp only [map_sum, map_mul]
    congr 1
    ext k
    rw [show Φ (C (structureCoeff bL i j k)) = C (structureCoeff bL i j k) from
      Φ.commutes (structureCoeff bL i j k)])

end LieAlgebras

section DifferentialAlgebra

/-! This interface applies to the genuine iterated Laurent/power-series algebra in G.
It does not assert that that algebra consists of polynomials over the scalar Laurent field.
Only a scalar-valued augmentation and coordinate derivations are used. -/

variable {A : Type*} [CommRing A] [Algebra R A]

/-- First derivative at the chosen augmentation. -/
def differentialLinearCoeff (ε : A →ₐ[R] R) (δ : ι → Derivation R A A)
    (i : ι) (p : A) : R := ε (δ i p)

/-- A linear bracket in any differential algebra with specified coordinates. -/
def differentialLinearBracket (c : ι → ι → ι → R) (x : ι → A)
    (δ : ι → Derivation R A A) (p q : A) : A :=
  ∑ i, ∑ j, ∑ r, algebraMap R A (c i j r) * (x r * (δ i p * δ j q))

/-- The differential bracket reproduces its prescribed linear bracket on coordinates. -/
theorem differentialLinearBracket_coordinates (c : ι → ι → ι → R)
    (x : ι → A) (δ : ι → Derivation R A A)
    (hδx : ∀ i j, δ i (x j) = if i = j then 1 else 0) (i j : ι) :
    differentialLinearBracket c x δ (x i) (x j) =
      ∑ r, algebraMap R A (c i j r) * x r := by
  simp [differentialLinearBracket, hδx]

omit [DecidableEq ι] in
theorem augmentation_differentialLinearBracket (ε : A →ₐ[R] R)
    (c : ι → ι → ι → R) (x : ι → A) (δ : ι → Derivation R A A)
    (hx : ∀ i, ε (x i) = 0) (p q : A) :
    ε (differentialLinearBracket c x δ p q) = 0 := by
  simp [differentialLinearBracket, hx]

/-- The first jet calculation uses the Leibniz rule and works equally in completed algebras. -/
theorem differentialLinearCoeff_bracket (ε : A →ₐ[R] R)
    (c : ι → ι → ι → R) (x : ι → A) (δ : ι → Derivation R A A)
    (hx : ∀ i, ε (x i) = 0)
    (hδx : ∀ i j, δ i (x j) = if i = j then 1 else 0)
    (p q : A) (r : ι) :
    differentialLinearCoeff ε δ r (differentialLinearBracket c x δ p q) =
      ∑ i, ∑ j, c i j r *
        (differentialLinearCoeff ε δ i p * differentialLinearCoeff ε δ j q) := by
  simp [differentialLinearCoeff, differentialLinearBracket, Derivation.leibniz,
    smul_eq_mul, hx, hδx, apply_ite, mul_comm]

omit [DecidableEq κ] in
/-- Coordinate matrix equations for the genuine completed algebra, given its Poisson images. -/
theorem differential_firstJet_equation (ε : A →ₐ[R] R)
    (cL : κ → κ → κ → R) (cM : ι → ι → ι → R)
    (x : ι → A) (δ : ι → Derivation R A A)
    (hx : ∀ i, ε (x i) = 0)
    (hδx : ∀ i j, δ i (x j) = if i = j then 1 else 0)
    (v : κ → A)
    (h : ∀ i j, differentialLinearBracket cM x δ (v i) (v j) =
      ∑ k, algebraMap R A (cL i j k) * v k)
    (i j : κ) (r : ι) :
    (∑ a, ∑ b, cM a b r *
      (differentialLinearCoeff ε δ a (v i) * differentialLinearCoeff ε δ b (v j))) =
      ∑ k, cL i j k * differentialLinearCoeff ε δ r (v k) := by
  have he := congrArg (differentialLinearCoeff ε δ r) (h i j)
  rw [differentialLinearCoeff_bracket ε cM x δ hx hδx] at he
  simpa [differentialLinearCoeff, Derivation.leibniz, smul_eq_mul] using he

variable {L M : Type*} [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

/-- The completed-algebra version of the first jet, with no polynomiality assumption on `v`.
The coordinate differential algebra is an explicit input, separately instantiated for G2. -/
def differentialFirstJetLieHom (bL : Basis κ R L) (bM : Basis ι R M)
    (ε : A →ₐ[R] R) (x : ι → A) (δ : ι → Derivation R A A)
    (hx : ∀ i, ε (x i) = 0)
    (hδx : ∀ i j, δ i (x j) = if i = j then 1 else 0)
    (v : κ → A)
    (h : ∀ i j, differentialLinearBracket (structureCoeff bM) x δ (v i) (v j) =
      ∑ k, algebraMap R A (structureCoeff bL i j k) * v k) : L →ₗ⁅R⁆ M :=
  lieHomOfStructureEquations bL bM (fun r i ↦ differentialLinearCoeff ε δ r (v i))
    (differential_firstJet_equation ε (structureCoeff bL) (structureCoeff bM)
      x δ hx hδx v h)

end DifferentialAlgebra

end EnvelopingIsomorphism.Poisson
