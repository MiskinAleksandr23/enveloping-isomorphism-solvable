import EnvelopingIsomorphism.Poisson.FirstJet
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.Ring

/-! The genuine linear Poisson bracket associated to a native Lie algebra.
All identities hold on the entire polynomial algebra over an arbitrary commutative ring. -/

namespace EnvelopingIsomorphism.Poisson

open MvPolynomial Module
open scoped BigOperators

noncomputable section

variable {R ι : Type*} [CommRing R] [Fintype ι]

@[simp] theorem linearBracket_C_left (c : ι → ι → ι → R) (a : R) (p : MvPolynomial ι R) :
    linearBracket c (C a) p = 0 := by simp [linearBracket]

@[simp] theorem linearBracket_C_right (c : ι → ι → ι → R) (p : MvPolynomial ι R) (a : R) :
    linearBracket c p (C a) = 0 := by simp [linearBracket]

@[simp] theorem linearBracket_zero_left (c : ι → ι → ι → R) (p : MvPolynomial ι R) :
    linearBracket c 0 p = 0 := by simp [linearBracket]

@[simp] theorem linearBracket_zero_right (c : ι → ι → ι → R) (p : MvPolynomial ι R) :
    linearBracket c p 0 = 0 := by simp [linearBracket]

theorem linearBracket_add_left (c : ι → ι → ι → R) (p q r : MvPolynomial ι R) :
    linearBracket c (p + q) r = linearBracket c p r + linearBracket c q r := by
  simp [linearBracket, add_mul, mul_add, Finset.sum_add_distrib]

theorem linearBracket_add_right (c : ι → ι → ι → R) (p q r : MvPolynomial ι R) :
    linearBracket c p (q + r) = linearBracket c p q + linearBracket c p r := by
  simp [linearBracket, mul_add, Finset.sum_add_distrib]

theorem linearBracket_smul_left (c : ι → ι → ι → R) (a : R) (p q : MvPolynomial ι R) :
    linearBracket c (a • p) q = a • linearBracket c p q := by
  simp only [linearBracket, Derivation.map_smul, smul_mul_assoc, mul_smul_comm, Finset.smul_sum]

theorem linearBracket_smul_right (c : ι → ι → ι → R) (a : R) (p q : MvPolynomial ι R) :
    linearBracket c p (a • q) = a • linearBracket c p q := by
  simp only [linearBracket, Derivation.map_smul, mul_smul_comm, Finset.smul_sum]

/-- The actual bracket is bilinear, with no Jacobi hypothesis on its coefficients. -/
def linearBracketBilinear (c : ι → ι → ι → R) :
    MvPolynomial ι R →ₗ[R] MvPolynomial ι R →ₗ[R] MvPolynomial ι R where
  toFun p :=
    { toFun := linearBracket c p
      map_add' := linearBracket_add_right c p
      map_smul' a q := linearBracket_smul_right c a p q }
  map_add' p q := by apply LinearMap.ext; intro r; exact linearBracket_add_left c p q r
  map_smul' a p := by apply LinearMap.ext; intro q; exact linearBracket_smul_left c a p q

@[simp] theorem linearBracketBilinear_apply (c : ι → ι → ι → R) (p q : MvPolynomial ι R) :
    linearBracketBilinear c p q = linearBracket c p q := rfl

@[simp] theorem linearBracket_neg_left (c : ι → ι → ι → R) (p q : MvPolynomial ι R) :
    linearBracket c (-p) q = -linearBracket c p q := by
  simpa only [linearBracketBilinear_apply, LinearMap.neg_apply] using
    congrArg (fun T : MvPolynomial ι R →ₗ[R] MvPolynomial ι R => T q)
      ((linearBracketBilinear c).map_neg p)

@[simp] theorem linearBracket_neg_right (c : ι → ι → ι → R) (p q : MvPolynomial ι R) :
    linearBracket c p (-q) = -linearBracket c p q := (linearBracketBilinear c p).map_neg q

theorem linearBracket_mul_left (c : ι → ι → ι → R) (p q r : MvPolynomial ι R) :
    linearBracket c (p * q) r = p * linearBracket c q r + q * linearBracket c p r := by
  simp [linearBracket, Derivation.leibniz, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm, mul_comm]

theorem linearBracket_mul_right (c : ι → ι → ι → R) (p q r : MvPolynomial ι R) :
    linearBracket c p (q * r) = q * linearBracket c p r + r * linearBracket c p q := by
  simp [linearBracket, Derivation.leibniz, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm]

/-- Holding the first polynomial fixed gives a genuine derivation. -/
def linearBracketDerivation (c : ι → ι → ι → R) (p : MvPolynomial ι R) :
    Derivation R (MvPolynomial ι R) (MvPolynomial ι R) where
  toLinearMap := linearBracketBilinear c p
  map_one_eq_zero' := by change linearBracket c p 1 = 0; simp [linearBracket]
  leibniz' q r := by
    change linearBracket c p (q * r) = q * linearBracket c p r + r * linearBracket c p q
    exact linearBracket_mul_right c p q r

theorem linearBracket_skew_of_coefficients (c : ι → ι → ι → R)
    (hc : ∀ i j r, c i j r = -c j i r) (p q : MvPolynomial ι R) :
    linearBracket c p q = -linearBracket c q p := by
  simp only [linearBracket, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro r hr
  rw [hc j i r]
  simp [mul_comm, mul_left_comm]

theorem linearBracket_self_of_coefficients (c : ι → ι → ι → R)
    (hc : ∀ i j r, c i j r = -c j i r) (hdiag : ∀ i r, c i i r = 0)
    (p : MvPolynomial ι R) : linearBracket c p p = 0 := by
  classical
  have hX : ∀ i, linearBracket c (X i) (X i) = 0 := by
    intro i
    simp [linearBracket_X_X, hdiag]
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [linearBracket_add_left, linearBracket_add_right, hp, hq]
    rw [linearBracket_skew_of_coefficients c hc q p]
    ring
  | mul_X p i hp =>
    simp only [linearBracket_mul_left, linearBracket_mul_right, hp, hX]
    rw [linearBracket_skew_of_coefficients c hc (X i) p]
    ring

/-- The cyclic Jacobi expression for the actual polynomial bracket. -/
def linearJacobiator (c : ι → ι → ι → R) (p q r : MvPolynomial ι R) : MvPolynomial ι R :=
  linearBracket c p (linearBracket c q r) +
    linearBracket c q (linearBracket c r p) +
    linearBracket c r (linearBracket c p q)

theorem linearJacobiator_rotate (c : ι → ι → ι → R) (p q r : MvPolynomial ι R) :
    linearJacobiator c q r p = linearJacobiator c p q r := by
  unfold linearJacobiator
  abel

@[simp] theorem linearJacobiator_C_first (c : ι → ι → ι → R) (a : R)
    (p q : MvPolynomial ι R) : linearJacobiator c (C a) p q = 0 := by simp [linearJacobiator]

@[simp] theorem linearJacobiator_C_second (c : ι → ι → ι → R) (a : R)
    (p q : MvPolynomial ι R) : linearJacobiator c p (C a) q = 0 := by simp [linearJacobiator]

@[simp] theorem linearJacobiator_C_third (c : ι → ι → ι → R) (a : R)
    (p q : MvPolynomial ι R) : linearJacobiator c p q (C a) = 0 := by simp [linearJacobiator]

theorem linearJacobiator_add_first (c : ι → ι → ι → R) (p p' q r : MvPolynomial ι R) :
    linearJacobiator c (p + p') q r = linearJacobiator c p q r + linearJacobiator c p' q r := by
  simp only [linearJacobiator, linearBracket_add_left, linearBracket_add_right]
  abel

theorem linearJacobiator_add_second (c : ι → ι → ι → R) (p q q' r : MvPolynomial ι R) :
    linearJacobiator c p (q + q') r = linearJacobiator c p q r + linearJacobiator c p q' r := by
  simp only [linearJacobiator, linearBracket_add_left, linearBracket_add_right]
  abel

theorem linearJacobiator_add_third (c : ι → ι → ι → R) (p q r r' : MvPolynomial ι R) :
    linearJacobiator c p q (r + r') = linearJacobiator c p q r + linearJacobiator c p q r' := by
  simp only [linearJacobiator, linearBracket_add_left, linearBracket_add_right]
  abel

/-- For a skew biderivation, the Jacobi expression is a derivation in its first slot. -/
theorem linearJacobiator_mul_first (c : ι → ι → ι → R)
    (hc : ∀ i j r, c i j r = -c j i r) (p p' q r : MvPolynomial ι R) :
    linearJacobiator c (p * p') q r =
      p * linearJacobiator c p' q r + p' * linearJacobiator c p q r := by
  simp only [linearJacobiator, linearBracket_mul_left, linearBracket_mul_right,
    linearBracket_add_right]
  simp only [linearBracket_skew_of_coefficients c hc p q,
    linearBracket_skew_of_coefficients c hc p' q]
  ring

theorem linearJacobiator_mul_second (c : ι → ι → ι → R)
    (hc : ∀ i j r, c i j r = -c j i r) (p q q' r : MvPolynomial ι R) :
    linearJacobiator c p (q * q') r =
      q * linearJacobiator c p q' r + q' * linearJacobiator c p q r := by
  rw [← linearJacobiator_rotate c p (q * q') r, linearJacobiator_mul_first c hc,
    linearJacobiator_rotate c p q' r, linearJacobiator_rotate c p q r]

theorem linearJacobiator_mul_third (c : ι → ι → ι → R)
    (hc : ∀ i j r, c i j r = -c j i r) (p q r r' : MvPolynomial ι R) :
    linearJacobiator c p q (r * r') =
      r * linearJacobiator c p q r' + r' * linearJacobiator c p q r := by
  rw [linearJacobiator_rotate c (r * r') p q, linearJacobiator_mul_first c hc,
    ← linearJacobiator_rotate c r' p q, ← linearJacobiator_rotate c r p q]

/-- Skewness and generator Jacobi extend Jacobi to all polynomials. -/
theorem linearJacobiator_eq_zero_of_generators (c : ι → ι → ι → R)
    (hc : ∀ i j r, c i j r = -c j i r)
    (hgen : ∀ i j k, linearJacobiator c (X i) (X j) (X k) = 0)
    (p q r : MvPolynomial ι R) : linearJacobiator c p q r = 0 := by
  have hXX : ∀ i j (r : MvPolynomial ι R), linearJacobiator c (X i) (X j) r = 0 := by
    intro i j r
    induction r using MvPolynomial.induction_on with
    | C a => simp
    | add r s hr hs => rw [linearJacobiator_add_third, hr, hs, add_zero]
    | mul_X r k hr =>
      rw [linearJacobiator_mul_third c hc, hgen, hr]
      simp
  have hX : ∀ i (q r : MvPolynomial ι R), linearJacobiator c (X i) q r = 0 := by
    intro i q r
    induction q using MvPolynomial.induction_on with
    | C a => simp
    | add q s hq hs => rw [linearJacobiator_add_second, hq, hs, add_zero]
    | mul_X q j hq =>
      rw [linearJacobiator_mul_second c hc, hXX, hq]
      simp
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p s hp hs => rw [linearJacobiator_add_first, hp, hs, add_zero]
  | mul_X p i hp =>
    rw [linearJacobiator_mul_first c hc, hX, hp]
    simp

section NativeLie

variable {L : Type*} [LieRing L] [LieAlgebra R L]

/-- The native Lie space identified with the linear coordinate polynomials. -/
def linearPolynomial (b : Basis ι R L) : L →ₗ[R] MvPolynomial ι R :=
  b.constr R X

@[simp] theorem linearPolynomial_basis (b : Basis ι R L) (i : ι) :
    linearPolynomial b (b i) = X i := by classical simp [linearPolynomial]

theorem linearPolynomial_apply (b : Basis ι R L) (x : L) :
    linearPolynomial b x = ∑ i, C (b.repr x i) * X i := by
  simp [linearPolynomial, Basis.constr_apply_fintype, Basis.equivFun_apply, Algebra.smul_def]

omit [Fintype ι] in
theorem structureCoeff_skew (b : Basis ι R L) (i j r : ι) :
    structureCoeff b i j r = -structureCoeff b j i r := by
  have h := congrArg (fun x => b.repr x r) (lie_skew (b i) (b j)).symm
  simpa only [structureCoeff, map_neg, Finsupp.neg_apply] using h

omit [Fintype ι] in
@[simp] theorem structureCoeff_self (b : Basis ι R L) (i r : ι) :
    structureCoeff b i i r = 0 := by simp [structureCoeff]

/-- The polynomial bracket restricts exactly to the given native Lie bracket. -/
theorem linearBracket_linearPolynomial (b : Basis ι R L) (x y : L) :
    linearBracket (structureCoeff b) (linearPolynomial b x) (linearPolynomial b y) =
      linearPolynomial b ⁅x, y⁆ := by
  classical
  letI : LieRing (Module.End R L) := LieRing.ofAssociativeRing
  have h : (linearBracketBilinear (structureCoeff b)).compl₁₂
      (linearPolynomial b) (linearPolynomial b) =
        (LieModule.toEnd R L L).toLinearMap.compr₂ (linearPolynomial b) := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    change linearBracket (structureCoeff b) (linearPolynomial b (b i))
      (linearPolynomial b (b j)) = linearPolynomial b ⁅b i, b j⁆
    rw [linearPolynomial_basis, linearPolynomial_basis, linearBracket_X_X, linearPolynomial_apply]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

theorem linearJacobiator_X_X_X (b : Basis ι R L) (i j k : ι) :
    linearJacobiator (structureCoeff b) (X i) (X j) (X k) = 0 := by
  unfold linearJacobiator
  simp only [← linearPolynomial_basis b, linearBracket_linearPolynomial]
  simpa only [map_add, map_zero] using
    congrArg (linearPolynomial b) (lie_jacobi (b i) (b j) (b k))

/-- Skewness of the actual linear Poisson bracket on all polynomials. -/
theorem linearBracket_skew (b : Basis ι R L) (p q : MvPolynomial ι R) :
    linearBracket (structureCoeff b) p q = -linearBracket (structureCoeff b) q p :=
  linearBracket_skew_of_coefficients (structureCoeff b) (structureCoeff_skew b) p q

/-- Alternation holds over every commutative coefficient ring, including characteristic two. -/
@[simp] theorem linearBracket_self (b : Basis ι R L) (p : MvPolynomial ι R) :
    linearBracket (structureCoeff b) p p = 0 :=
  linearBracket_self_of_coefficients (structureCoeff b) (structureCoeff_skew b)
    (structureCoeff_self b) p

/-- The full cyclic Jacobi identity for the actual polynomial bracket. -/
theorem linearBracket_lie_jacobi (b : Basis ι R L) (p q r : MvPolynomial ι R) :
    linearBracket (structureCoeff b) p (linearBracket (structureCoeff b) q r) +
      linearBracket (structureCoeff b) q (linearBracket (structureCoeff b) r p) +
      linearBracket (structureCoeff b) r (linearBracket (structureCoeff b) p q) = 0 :=
  linearJacobiator_eq_zero_of_generators (structureCoeff b) (structureCoeff_skew b)
    (linearJacobiator_X_X_X b) p q r

/-- Jacobi in the Leibniz form used by native `LieRing` and Schouten constructions. -/
theorem linearBracket_leibniz_lie (b : Basis ι R L) (p q r : MvPolynomial ι R) :
    linearBracket (structureCoeff b) p (linearBracket (structureCoeff b) q r) =
      linearBracket (structureCoeff b) (linearBracket (structureCoeff b) p q) r +
      linearBracket (structureCoeff b) q (linearBracket (structureCoeff b) p r) := by
  have h := linearBracket_lie_jacobi b p q r
  rw [linearBracket_skew b r p, linearBracket_neg_right,
    linearBracket_skew b r (linearBracket (structureCoeff b) p q)] at h
  apply sub_eq_zero.mp
  convert h using 1
  abel

/-- The linear Poisson bracket gives an actual Lie-ring structure on the existing polynomial space.
This is a definition rather than a global instance, to avoid conflicting brackets on polynomials. -/
abbrev linearPoissonLieRing (b : Basis ι R L) : LieRing (MvPolynomial ι R) where
  bracket := linearBracket (structureCoeff b)
  add_lie := linearBracket_add_left (structureCoeff b)
  lie_add := linearBracket_add_right (structureCoeff b)
  lie_self := linearBracket_self b
  leibniz_lie := linearBracket_leibniz_lie b

/-- Scalar compatibility for the same actual Lie-ring structure. -/
abbrev linearPoissonLieAlgebra (b : Basis ι R L) :
    letI := linearPoissonLieRing b
    LieAlgebra R (MvPolynomial ι R) := by
  letI := linearPoissonLieRing b
  exact { (inferInstance : Module R (MvPolynomial ι R)) with
    lie_smul := fun a p q => linearBracket_smul_right (structureCoeff b) a p q }

end NativeLie

end

end EnvelopingIsomorphism.Poisson
