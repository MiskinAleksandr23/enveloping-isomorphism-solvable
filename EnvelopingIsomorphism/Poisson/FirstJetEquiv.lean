import EnvelopingIsomorphism.Poisson.FirstJet
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Invertibility of the marked first jet

A square power-series matrix whose constant matrix is the identity has unit determinant.
Consequently the actual first-jet matrix defines a Lie equivalence, preserving the prescribed
specialization. The coefficient ring may be any commutative ring, including the Laurent field.
-/

noncomputable section

namespace EnvelopingIsomorphism.Poisson

open Module
open scoped BigOperators

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Being the identity modulo the power-series parameter makes the determinant a unit. -/
theorem isUnit_det_of_constantMatrix_eq_one (P : Matrix ι ι (PowerSeries R))
    (hP : P.map PowerSeries.constantCoeff = 1) : IsUnit P.det := by
  rw [PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
  change IsUnit (P.map PowerSeries.constantCoeff).det
  rw [hP, Matrix.det_one]
  exact isUnit_one

/-- The exact matrix, not only its specialization, is invertible. -/
theorem isUnit_of_constantMatrix_eq_one (P : Matrix ι ι (PowerSeries R))
    (hP : P.map PowerSeries.constantCoeff = 1) : IsUnit P :=
  (Matrix.isUnit_iff_isUnit_det P).mpr (isUnit_det_of_constantMatrix_eq_one P hP)

section LieAlgebras

variable {L M : Type*} [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

theorem firstJetLinearMap_eq_toLin (bL : Basis ι R L) (bM : Basis ι R M)
    (P : Matrix ι ι R) : firstJetLinearMap bL bM P = Matrix.toLin bL bM P := by
  apply bL.ext
  intro i
  rw [firstJetLinearMap_basis, Matrix.toLin_self]

/-- Unit determinant upgrades the first jet to an equivalence of the original Lie modules. -/
def lieEquivOfStructureEquations (bL : Basis ι R L) (bM : Basis ι R M)
    (P : Matrix ι ι R) (hP : IsUnit P.det)
    (h : ∀ i j r, (∑ a, ∑ b, structureCoeff bM a b r * (P a i * P b j)) =
      ∑ k, structureCoeff bL i j k * P r k) : L ≃ₗ⁅R⁆ M :=
  LieEquiv.ofBijective (lieHomOfStructureEquations bL bM P h) (by
    change Function.Bijective (firstJetLinearMap bL bM P)
    rw [firstJetLinearMap_eq_toLin]
    exact (Matrix.toLinOfInv bL bM (P.mul_nonsing_inv hP)
      (P.nonsing_inv_mul hP)).bijective)

@[simp] theorem lieEquivOfStructureEquations_apply (bL : Basis ι R L) (bM : Basis ι R M)
    (P : Matrix ι ι R) (hP : IsUnit P.det)
    (h : ∀ i j r, (∑ a, ∑ b, structureCoeff bM a b r * (P a i * P b j)) =
      ∑ k, structureCoeff bL i j k * P r k) (x : L) :
    lieEquivOfStructureEquations bL bM P hP h x = firstJetLinearMap bL bM P x := rfl

end LieAlgebras

section PowerSeries

variable {L M : Type*} [LieRing L] [LieAlgebra (PowerSeries R) L]
    [LieRing M] [LieAlgebra (PowerSeries R) M]

/-- The marked output in G3: a Lie equivalence over the complete coefficient ring itself. -/
def markedFirstJetLieEquiv (bL : Basis ι (PowerSeries R) L)
    (bM : Basis ι (PowerSeries R) M) (P : Matrix ι ι (PowerSeries R))
    (hP : P.map PowerSeries.constantCoeff = 1)
    (h : ∀ i j r, (∑ a, ∑ b, structureCoeff bM a b r * (P a i * P b j)) =
      ∑ k, structureCoeff bL i j k * P r k) : L ≃ₗ⁅PowerSeries R⁆ M :=
  lieEquivOfStructureEquations bL bM P (isUnit_det_of_constantMatrix_eq_one P hP) h

/-- The resulting equivalence has exactly the supplied matrix. -/
theorem repr_markedFirstJetLieEquiv_basis (bL : Basis ι (PowerSeries R) L)
    (bM : Basis ι (PowerSeries R) M) (P : Matrix ι ι (PowerSeries R))
    (hP : P.map PowerSeries.constantCoeff = 1)
    (h : ∀ i j r, (∑ a, ∑ b, structureCoeff bM a b r * (P a i * P b j)) =
      ∑ k, structureCoeff bL i j k * P r k) (i r : ι) :
    bM.repr (markedFirstJetLieEquiv bL bM P hP h (bL i)) r = P r i := by
  change bM.repr (firstJetLinearMap bL bM P (bL i)) r = P r i
  simp [Finsupp.single_apply]

/-- The prescribed identity specialization is retained, rather than forgotten by existence. -/
theorem markedFirstJetLieEquiv_constantCoeff (bL : Basis ι (PowerSeries R) L)
    (bM : Basis ι (PowerSeries R) M) (P : Matrix ι ι (PowerSeries R))
    (hP : P.map PowerSeries.constantCoeff = 1)
    (h : ∀ i j r, (∑ a, ∑ b, structureCoeff bM a b r * (P a i * P b j)) =
      ∑ k, structureCoeff bL i j k * P r k) (i r : ι) :
    PowerSeries.constantCoeff
      (bM.repr (markedFirstJetLieEquiv bL bM P hP h (bL i)) r) =
        (1 : Matrix ι ι R) r i := by
  rw [repr_markedFirstJetLieEquiv_basis]
  exact congrFun (congrFun hP r) i

end PowerSeries

section DifferentialAlgebra

variable {A : Type*} [CommRing A] [Algebra (PowerSeries R) A]

omit [Fintype ι] in
/-- Images equal to the coordinates modulo the parameter have identity first-jet matrix
modulo that parameter, even when their constant terms in the coordinates are nonzero. -/
theorem differentialFirstJet_constantMatrix (ε : A →ₐ[PowerSeries R] PowerSeries R)
    (x : ι → A) (δ : ι → Derivation (PowerSeries R) A A)
    (hδx : ∀ i j, δ i (x j) = if i = j then 1 else 0)
    (v : ι → A) (hv : ∀ i, ∃ w : A, v i = x i + (PowerSeries.X : PowerSeries R) • w) :
    Matrix.map (fun r i ↦ differentialLinearCoeff ε δ r (v i)) PowerSeries.constantCoeff =
      (1 : Matrix ι ι R) := by
  ext r i
  obtain ⟨w, hw⟩ := hv i
  by_cases hri : r = i <;>
    simp [Matrix.map_apply, Matrix.one_apply, differentialLinearCoeff, hw, hδx,
      hri, smul_eq_mul]

variable {L M : Type*} [LieRing L] [LieAlgebra (PowerSeries R) L]
    [LieRing M] [LieAlgebra (PowerSeries R) M]

/-- A Poisson comparison equal to the identity modulo the parameter yields a marked Lie
equivalence over the complete scalar ring. This theorem applies to the genuine function
algebra once its augmentation and coordinate derivations have been constructed. -/
def markedDifferentialFirstJetLieEquiv (bL : Basis ι (PowerSeries R) L)
    (bM : Basis ι (PowerSeries R) M)
    (ε : A →ₐ[PowerSeries R] PowerSeries R) (x : ι → A)
    (δ : ι → Derivation (PowerSeries R) A A)
    (hx : ∀ i, ε (x i) = 0)
    (hδx : ∀ i j, δ i (x j) = if i = j then 1 else 0)
    (v : ι → A) (hv : ∀ i, ∃ w : A, v i = x i + (PowerSeries.X : PowerSeries R) • w)
    (h : ∀ i j, differentialLinearBracket (structureCoeff bM) x δ (v i) (v j) =
      ∑ k, algebraMap (PowerSeries R) A (structureCoeff bL i j k) * v k) :
    L ≃ₗ⁅PowerSeries R⁆ M :=
  markedFirstJetLieEquiv bL bM (fun r i ↦ differentialLinearCoeff ε δ r (v i))
    (differentialFirstJet_constantMatrix ε x δ hδx v hv)
    (differential_firstJet_equation ε (structureCoeff bL) (structureCoeff bM)
      x δ hx hδx v h)

/-- The equivalence retains the actual first derivative of each generator image. -/
theorem repr_markedDifferentialFirstJetLieEquiv_basis (bL : Basis ι (PowerSeries R) L)
    (bM : Basis ι (PowerSeries R) M)
    (ε : A →ₐ[PowerSeries R] PowerSeries R) (x : ι → A)
    (δ : ι → Derivation (PowerSeries R) A A)
    (hx : ∀ i, ε (x i) = 0)
    (hδx : ∀ i j, δ i (x j) = if i = j then 1 else 0)
    (v : ι → A) (hv : ∀ i, ∃ w : A, v i = x i + (PowerSeries.X : PowerSeries R) • w)
    (h : ∀ i j, differentialLinearBracket (structureCoeff bM) x δ (v i) (v j) =
      ∑ k, algebraMap (PowerSeries R) A (structureCoeff bL i j k) * v k) (i r : ι) :
    bM.repr (markedDifferentialFirstJetLieEquiv bL bM ε x δ hx hδx v hv h (bL i)) r =
      differentialLinearCoeff ε δ r (v i) :=
  repr_markedFirstJetLieEquiv_basis _ _ _ _ _ _ _

/-- Apply the marked first-jet construction directly to a Poisson algebra homomorphism.
The scalar-linearity and Poisson property are the only properties of the map used. -/
def markedPoissonFirstJetLieEquiv (bL : Basis ι (PowerSeries R) L)
    (bM : Basis ι (PowerSeries R) M)
    (ε : A →ₐ[PowerSeries R] PowerSeries R) (x : ι → A)
    (δ : ι → Derivation (PowerSeries R) A A)
    (hx : ∀ i, ε (x i) = 0)
    (hδx : ∀ i j, δ i (x j) = if i = j then 1 else 0)
    (Ψ : A →ₐ[PowerSeries R] A)
    (hΨ : ∀ p q, Ψ (differentialLinearBracket (structureCoeff bL) x δ p q) =
      differentialLinearBracket (structureCoeff bM) x δ (Ψ p) (Ψ q))
    (hmark : ∀ i, ∃ w : A, Ψ (x i) = x i + (PowerSeries.X : PowerSeries R) • w) :
    L ≃ₗ⁅PowerSeries R⁆ M :=
  markedDifferentialFirstJetLieEquiv bL bM ε x δ hx hδx (fun i ↦ Ψ (x i)) hmark
    (fun i j ↦ by
      rw [← hΨ, differentialLinearBracket_coordinates _ x δ hδx]
      simp only [map_sum, map_mul, AlgHom.commutes])

end DifferentialAlgebra

end EnvelopingIsomorphism.Poisson
