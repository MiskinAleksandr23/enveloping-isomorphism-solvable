import EnvelopingIsomorphism.Poisson.FirstJetEquiv
import EnvelopingIsomorphism.FormalSeries.DifferentialAlgebra
import EnvelopingIsomorphism.FormalSeries.PowerSeriesDifferential

/-!
# The first jet in the actual Laurent-polynomial power-series algebra

The function ring is `PowerSeries (LaurentSeries (MvPolynomial ι k))`.
Its scalar ring is `PowerSeries (LaurentSeries k)`. Polynomial degree need not have a
uniform bound in either formal parameter. No identification with polynomials over the
Laurent field, or with the full coordinate-adic power-series ring, is used.
-/

noncomputable section

namespace EnvelopingIsomorphism.Poisson.Completed

open Module
open EnvelopingIsomorphism.FormalSeries
open scoped LaurentAlgebra BigOperators

variable {k ι : Type*} [CommRing k]

/-- The exact function algebra in G, with the Laurent completion taken before `t`. -/
abbrev Functions (ι k : Type*) [CommRing k] :=
  PowerSeries (LaurentSeries (MvPolynomial ι k))

/-- The scalar ring of the marked Lie matrix. -/
abbrev Scalars (k : Type*) [CommRing k] := PowerSeries (LaurentSeries k)

/-- Coordinates as constant series in both formal parameters. -/
def coordinate (i : ι) : Functions ι k :=
  PowerSeries.C (HahnSeries.C (MvPolynomial.X i))

/-- Extract the coordinate constant term coefficientwise in both parameters. -/
def augmentation : Functions ι k →ₐ[Scalars k] Scalars k :=
  PowerSeriesAlgebra.augmentation
    (LaurentAlgebra.augmentation (MvPolynomial.aeval (fun _ : ι ↦ (0 : k))))

/-- Coordinate differentiation, acting coefficientwise in both parameters. -/
def partialDerivation (i : ι) : Derivation (Scalars k) (Functions ι k) (Functions ι k) :=
  PowerSeriesAlgebra.derivation (LaurentAlgebra.derivation (MvPolynomial.pderiv i))

@[simp] theorem augmentation_coordinate (i : ι) :
    augmentation (coordinate i : Functions ι k) = 0 := by
  rw [augmentation, coordinate, PowerSeriesAlgebra.augmentation_C,
    LaurentAlgebra.augmentation_C]
  simp

@[simp] theorem partialDerivation_coordinate [DecidableEq ι] (i j : ι) :
    partialDerivation i (coordinate j : Functions ι k) = if i = j then 1 else 0 := by
  rw [partialDerivation, coordinate, PowerSeriesAlgebra.derivation_C,
    LaurentAlgebra.derivation_C]
  by_cases h : i = j <;>
    simp [MvPolynomial.pderiv_X, h]

/-- Every fixed pair of parameter coefficients has the actual polynomial constant term. -/
theorem coeff_augmentation (p : Functions ι k) (t : ℕ) (h : ℤ) :
    (PowerSeries.coeff t (augmentation p)).coeff h =
      MvPolynomial.constantCoeff ((PowerSeries.coeff t p).coeff h) := by
  rw [augmentation, PowerSeriesAlgebra.coeff_augmentation, LaurentAlgebra.coeff_augmentation]
  simp

/-- The extracted first derivative is exactly the coefficient of the coordinate monomial. -/
theorem coeff_firstJet (p : Functions ι k) (i : ι) (t : ℕ) (h : ℤ) :
    (PowerSeries.coeff t (differentialLinearCoeff augmentation partialDerivation i p)).coeff h =
      linearCoeff i ((PowerSeries.coeff t p).coeff h) := by
  rw [differentialLinearCoeff, coeff_augmentation, partialDerivation,
    PowerSeriesAlgebra.coeff_derivation, LaurentAlgebra.coeff_derivation]
  exact constantCoeff_pderiv i _

variable [Fintype ι] [DecidableEq ι]

/-- A coordinatewise linear Poisson bracket on the actual completed function algebra. -/
def bracket (c : ι → ι → ι → Scalars k) (p q : Functions ι k) : Functions ι k :=
  differentialLinearBracket c coordinate partialDerivation p q

omit [DecidableEq ι] in
/-- Cancellation of the invertible Laurent parameter in a scaled Poisson comparison. -/
theorem poisson_of_unit_scaled (cL cM : ι → ι → ι → Scalars k)
    (Ψ : Functions ι k →ₐ[Scalars k] Functions ι k) (s : Scalars k) (hs : IsUnit s)
    (h : ∀ p q, Ψ (s • bracket cL p q) = s • bracket cM (Ψ p) (Ψ q)) :
    ∀ p q, Ψ (bracket cL p q) = bracket cM (Ψ p) (Ψ q) := by
  intro p q
  apply hs.smul_left_cancel.mp
  simpa using h p q

/-- The first derivative matrix over the complete scalar ring. -/
def matrix (Ψ : Functions ι k →ₐ[Scalars k] Functions ι k) : Matrix ι ι (Scalars k) :=
  fun r i ↦ differentialLinearCoeff augmentation partialDerivation r (Ψ (coordinate i))

omit [Fintype ι] [DecidableEq ι] in
/-- Every coefficient of the matrix is extracted from the genuine iterated series. -/
theorem coeff_matrix (Ψ : Functions ι k →ₐ[Scalars k] Functions ι k)
    (r i : ι) (t : ℕ) (h : ℤ) :
    (PowerSeries.coeff t (matrix Ψ r i)).coeff h =
      linearCoeff r ((PowerSeries.coeff t (Ψ (coordinate i))).coeff h) :=
  coeff_firstJet _ _ _ _

omit [Fintype ι] in
/-- A comparison reducing to the identity has identity first derivative modulo `t`. -/
theorem matrix_constantCoeff (Ψ : Functions ι k →ₐ[Scalars k] Functions ι k)
    (hmark : ∀ i, PowerSeries.constantCoeff (Ψ (coordinate i)) =
      HahnSeries.C (MvPolynomial.X i)) :
    (matrix Ψ).map PowerSeries.constantCoeff = (1 : Matrix ι ι (LaurentSeries k)) := by
  apply differentialFirstJet_constantMatrix augmentation coordinate partialDerivation
    partialDerivation_coordinate
  intro i
  apply PowerSeriesAlgebra.exists_eq_add_parameter_smul
  simpa [coordinate] using hmark i

/-- The extracted matrix is a unit over `k((h))[[t]]` itself. -/
theorem matrix_isUnit (Ψ : Functions ι k →ₐ[Scalars k] Functions ι k)
    (hmark : ∀ i, PowerSeries.constantCoeff (Ψ (coordinate i)) =
      HahnSeries.C (MvPolynomial.X i)) : IsUnit (matrix Ψ) :=
  isUnit_of_constantMatrix_eq_one _ (matrix_constantCoeff Ψ hmark)

variable {L M : Type*} [LieRing L] [LieAlgebra (Scalars k) L]
    [LieRing M] [LieAlgebra (Scalars k) M]

/-- The exact Lie-matrix equations, before using the marking to prove invertibility. -/
theorem matrix_equation (bL : Basis ι (Scalars k) L) (bM : Basis ι (Scalars k) M)
    (Ψ : Functions ι k →ₐ[Scalars k] Functions ι k)
    (hΨ : ∀ p q, Ψ (bracket (structureCoeff bL) p q) =
      bracket (structureCoeff bM) (Ψ p) (Ψ q)) (i j r : ι) :
    (∑ a, ∑ b, structureCoeff bM a b r * (matrix Ψ a i * matrix Ψ b j)) =
      ∑ d, structureCoeff bL i j d * matrix Ψ r d := by
  apply differential_firstJet_equation augmentation (structureCoeff bL) (structureCoeff bM)
    coordinate partialDerivation augmentation_coordinate partialDerivation_coordinate
    (fun i ↦ Ψ (coordinate i))
  intro i j
  change bracket (structureCoeff bM) (Ψ (coordinate i)) (Ψ (coordinate j)) = _
  rw [← hΨ, bracket, differentialLinearBracket_coordinates _ _ _ partialDerivation_coordinate]
  simp only [map_sum, map_mul, AlgHom.commutes]

/-- G3 on the genuine completed function algebra: a marked Poisson comparison yields a
single Lie equivalence over `k((h))[[t]]`, with no augmentation-preservation assumption. -/
def lieEquiv (bL : Basis ι (Scalars k) L) (bM : Basis ι (Scalars k) M)
    (Ψ : Functions ι k →ₐ[Scalars k] Functions ι k)
    (hΨ : ∀ p q, Ψ (bracket (structureCoeff bL) p q) =
      bracket (structureCoeff bM) (Ψ p) (Ψ q))
    (hmark : ∀ i, PowerSeries.constantCoeff (Ψ (coordinate i)) =
      HahnSeries.C (MvPolynomial.X i)) : L ≃ₗ⁅Scalars k⁆ M :=
  markedPoissonFirstJetLieEquiv bL bM augmentation coordinate partialDerivation
    augmentation_coordinate partialDerivation_coordinate Ψ hΨ
    (fun i ↦ PowerSeriesAlgebra.exists_eq_add_parameter_smul _ _
      (by simpa [coordinate] using hmark i))

/-- The output Lie equivalence retains exactly the extracted matrix, coefficient by coefficient. -/
theorem repr_lieEquiv_basis (bL : Basis ι (Scalars k) L) (bM : Basis ι (Scalars k) M)
    (Ψ : Functions ι k →ₐ[Scalars k] Functions ι k)
    (hΨ : ∀ p q, Ψ (bracket (structureCoeff bL) p q) =
      bracket (structureCoeff bM) (Ψ p) (Ψ q))
    (hmark : ∀ i, PowerSeries.constantCoeff (Ψ (coordinate i)) =
      HahnSeries.C (MvPolynomial.X i)) (i r : ι) :
    bM.repr (lieEquiv bL bM Ψ hΨ hmark (bL i)) r = matrix Ψ r i := by
  change bM.repr (firstJetLinearMap bL bM (matrix Ψ) (bL i)) r = matrix Ψ r i
  simp [Finsupp.single_apply]

/-- The actual Lie equivalence specializes to the prescribed identity matrix. -/
theorem lieEquiv_constantCoeff (bL : Basis ι (Scalars k) L) (bM : Basis ι (Scalars k) M)
    (Ψ : Functions ι k →ₐ[Scalars k] Functions ι k)
    (hΨ : ∀ p q, Ψ (bracket (structureCoeff bL) p q) =
      bracket (structureCoeff bM) (Ψ p) (Ψ q))
    (hmark : ∀ i, PowerSeries.constantCoeff (Ψ (coordinate i)) =
      HahnSeries.C (MvPolynomial.X i)) (i r : ι) :
    PowerSeries.constantCoeff (bM.repr (lieEquiv bL bM Ψ hΨ hmark (bL i)) r) =
      (1 : Matrix ι ι (LaurentSeries k)) r i := by
  rw [repr_lieEquiv_basis]
  exact congrFun (congrFun (matrix_constantCoeff Ψ hmark) r) i

end EnvelopingIsomorphism.Poisson.Completed
