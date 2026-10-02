import EnvelopingIsomorphism.Poisson.LinearJacobi
import EnvelopingIsomorphism.Deformation.Polyvectors
import EnvelopingIsomorphism.Deformation.Kontsevich.OneVertexGraphOperators
import EnvelopingIsomorphism.Deformation.SchoutenJacobi
import Mathlib.Tactic.FinCases

/-! The actual native linear Poisson tensor as an unnormalized polynomial
multiderivation, and its genuine Schouten Maurer–Cartan equation. -/

namespace EnvelopingIsomorphism.Deformation

open MvPolynomial Module

noncomputable section

section Construction

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] {d : ℕ}

/-- Skew diagonal-zero coefficient tables give linear bivectors without any Jacobi assumption.
This constructor is suitable for individual coefficients of a Poisson family. -/
def linearBivectorOfCoefficients (c : Fin d → Fin d → Fin d → R)
    (hskew : ∀ i j r, c i j r = -c j i r) (hdiag : ∀ i r, c i i r = 0) :
    Multiderivation R (MvPolynomial (Fin d) R) 2 :=
  ⟨{ toMultilinearMap := (cochainTwoEquiv R (MvPolynomial (Fin d) R)).symm
        (Kontsevich.linearPoissonBinary c)
     map_eq_zero_of_eq' := by
       intro a i j h hne
       change Poisson.linearBracket c (a 0) (a 1) = 0
       fin_cases i <;> fin_cases j
       · exact (hne rfl).elim
       · change a 0 = a 1 at h
         rw [h]
         exact Poisson.linearBracket_self_of_coefficients c hskew hdiag _
       · change a 1 = a 0 at h
         rw [← h]
         exact Poisson.linearBracket_self_of_coefficients c hskew hdiag _
       · exact (hne rfl).elim }, by
    intro i a p q
    change Poisson.linearBracket c ((Function.update a i (p * q)) 0)
      ((Function.update a i (p * q)) 1) =
      p * Poisson.linearBracket c ((Function.update a i q) 0) ((Function.update a i q) 1) +
        q * Poisson.linearBracket c ((Function.update a i p) 0) ((Function.update a i p) 1)
    fin_cases i
    · simpa using Poisson.linearBracket_mul_left c p q (a 1)
    · simpa using Poisson.linearBracket_mul_right c (a 0) p q⟩

@[simp] theorem linearBivectorOfCoefficients_apply (c : Fin d → Fin d → Fin d → R)
    (hskew : ∀ i j r, c i j r = -c j i r) (hdiag : ∀ i r, c i i r = 0)
    (a : Fin 2 → MvPolynomial (Fin d) R) :
    linearBivectorOfCoefficients c hskew hdiag a = Poisson.linearBracket c (a 0) (a 1) := rfl

theorem linearBivectorOfCoefficients_toBinary (c : Fin d → Fin d → Fin d → R)
    (hskew : ∀ i j r, c i j r = -c j i r) (hdiag : ∀ i r, c i i r = 0) :
    cochainTwoEquiv R (MvPolynomial (Fin d) R)
      (linearBivectorOfCoefficients c hskew hdiag).val.toMultilinearMap =
        Kontsevich.linearPoissonBinary c :=
  (cochainTwoEquiv R (MvPolynomial (Fin d) R)).apply_symm_apply _

/-- Uncurrying the actual linear Poisson binary map gives an alternating bilinear map. -/
def linearBivectorAlternating (b : Basis (Fin d) R L) :
    MvPolynomial (Fin d) R [⋀^Fin 2]→ₗ[R] MvPolynomial (Fin d) R where
  toMultilinearMap := (cochainTwoEquiv R (MvPolynomial (Fin d) R)).symm
    (Kontsevich.linearPoissonBinary (Poisson.structureCoeff b))
  map_eq_zero_of_eq' a i j h hne := by
    change Poisson.linearBracket (Poisson.structureCoeff b) (a 0) (a 1) = 0
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · change a 0 = a 1 at h
      rw [h]
      exact Poisson.linearBracket_self b _
    · change a 1 = a 0 at h
      rw [← h]
      exact Poisson.linearBracket_self b _
    · exact (hne rfl).elim

@[simp] theorem linearBivectorAlternating_apply (b : Basis (Fin d) R L)
    (a : Fin 2 → MvPolynomial (Fin d) R) :
    linearBivectorAlternating b a = Poisson.linearBracket (Poisson.structureCoeff b) (a 0) (a 1) := rfl

/-- The genuine linear Poisson bivector. There is no factorial normalization in this definition. -/
def linearBivector (b : Basis (Fin d) R L) :
    Multiderivation R (MvPolynomial (Fin d) R) 2 :=
  ⟨linearBivectorAlternating b, by
    intro i a p q
    fin_cases i
    · simpa using Poisson.linearBracket_mul_left (Poisson.structureCoeff b) p q (a 1)
    · simpa using Poisson.linearBracket_mul_right (Poisson.structureCoeff b) (a 0) p q⟩

@[simp] theorem linearBivector_apply (b : Basis (Fin d) R L)
    (a : Fin 2 → MvPolynomial (Fin d) R) :
    linearBivector b a = Poisson.linearBracket (Poisson.structureCoeff b) (a 0) (a 1) := rfl

/-- Returning to the existing binary-cochain representation recovers its exact raw bracket. -/
theorem linearBivector_toBinary (b : Basis (Fin d) R L) :
    cochainTwoEquiv R (MvPolynomial (Fin d) R) (linearBivector b).val.toMultilinearMap =
      Kontsevich.linearPoissonBinary (Poisson.structureCoeff b) :=
  (cochainTwoEquiv R (MvPolynomial (Fin d) R)).apply_symm_apply _

end Construction

section Schouten

variable {K : Type*} [Field K] [CharZero K]
variable {L : Type*} [LieRing L] [LieAlgebra K L] {d : ℕ}

omit [CharZero K] in
theorem rawBivector_linearBivector (b : Basis (Fin d) K L) :
    rawBivector (linearBivector b) = Kontsevich.linearPoissonBinary (Poisson.structureCoeff b) :=
  linearBivector_toBinary b

omit [CharZero K] in
@[simp] theorem rawBivector_linearBivector_apply (b : Basis (Fin d) K L)
    (p q : PolynomialFunctions K d) :
    rawBivector (linearBivector b) p q = Poisson.linearBracket (Poisson.structureCoeff b) p q := by
  rw [rawBivector_linearBivector]
  rfl

omit [CharZero K] in
/-- Native Lie Jacobi gives the all-polynomial Jacobi insertion required by the source DGLA. -/
theorem linearBivector_jacobiInsert (b : Basis (Fin d) K L) (p q r : PolynomialFunctions K d) :
    jacobiInsert (rawBivector (linearBivector b)) (rawBivector (linearBivector b)) p q r = 0 := by
  simp only [jacobiInsert_apply, rawBivector_linearBivector_apply]
  rw [Poisson.linearBracket_skew b (Poisson.linearBracket (Poisson.structureCoeff b) p q) r,
    Poisson.linearBracket_skew b (Poisson.linearBracket (Poisson.structureCoeff b) q r) p,
    Poisson.linearBracket_skew b (Poisson.linearBracket (Poisson.structureCoeff b) r p) q]
  simpa only [neg_add, neg_zero, add_assoc, add_comm, add_left_comm] using
    congrArg (fun f => -f) (Poisson.linearBracket_lie_jacobi b p q r)

/-- The genuine Schouten square of the linear Poisson tensor is zero. -/
theorem linearBivector_schouten_self (b : Basis (Fin d) K L) :
    (show Multiderivation K (PolynomialFunctions K d) 3 from
      schoutenBracket K d 1 1 (linearBivector b) (linearBivector b)) = 0 :=
  (schoutenBivector_self_eq_zero_iff (linearBivector b)).mpr (linearBivector_jacobiInsert b)

/-- The actual linear bivector is Maurer–Cartan in the constructed polynomial Schouten DGLA. -/
theorem linearBivector_isMaurerCartan (b : Basis (Fin d) K L) :
    (polynomialSchoutenDGLA K d).IsMaurerCartan (linearBivector b) :=
  (polynomialSchouten_MC_iff_Jacobi (linearBivector b)).mpr (linearBivector_jacobiInsert b)

end Schouten

end

end EnvelopingIsomorphism.Deformation
