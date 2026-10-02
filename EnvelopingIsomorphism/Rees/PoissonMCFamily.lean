import EnvelopingIsomorphism.Rees.Family
import EnvelopingIsomorphism.Deformation.LinearBivector
import EnvelopingIsomorphism.Deformation.SignedDGLASeries
import EnvelopingIsomorphism.Deformation.Twist
import EnvelopingIsomorphism.Deformation.Gauge.CurvatureLeading

/-! The full Rees Poisson family, coefficientwise as bivectors.
Individual coefficients are only alternating biderivations and are not assumed Poisson. -/

namespace EnvelopingIsomorphism.Rees.PoissonMCFamily

set_option backward.isDefEq.respectTransparency false

open Module MvPolynomial
open EnvelopingIsomorphism.Deformation EnvelopingIsomorphism.FormalSeries
open scoped BigOperators

noncomputable section

section PolynomialIdentities

variable {R : Type*} [CommRing R] {d : ℕ}

def coefficientJacobi (c e : Fin d → Fin d → Fin d → R) (i j k r : Fin d) : R :=
  ∑ a, (c a k r * e i j a + c a i r * e j k a + c a j r * e k i a)

theorem bracket_sum_left {α : Type*} (c : Fin d → Fin d → Fin d → R)
    (s : Finset α) (f : α → MvPolynomial (Fin d) R) (q : MvPolynomial (Fin d) R) :
    Poisson.linearBracket c (∑ i ∈ s, f i) q = ∑ i ∈ s, Poisson.linearBracket c (f i) q := by
  change Poisson.linearBracketBilinear c (∑ i ∈ s, f i) q = _
  rw [map_sum, LinearMap.sum_apply]
  rfl

theorem bracket_C_mul_left (c : Fin d → Fin d → Fin d → R)
    (a : R) (p q : MvPolynomial (Fin d) R) :
    Poisson.linearBracket c (C a * p) q = C a * Poisson.linearBracket c p q := by
  rw [Poisson.linearBracket_mul_left, Poisson.linearBracket_C_left]
  simp

theorem nested_bracket_generators (c e : Fin d → Fin d → Fin d → R) (i j k : Fin d) :
    Poisson.linearBracket c (Poisson.linearBracket e (X i) (X j)) (X k) =
      ∑ r, C (∑ a, c a k r * e i j a) * X r := by
  rw [Poisson.linearBracket_X_X, bracket_sum_left]
  simp only [bracket_C_mul_left, Poisson.linearBracket_X_X, Finset.mul_sum,
    ← mul_assoc, ← map_mul]
  rw [Finset.sum_comm]
  simp [map_sum, Finset.mul_sum, mul_comm]

theorem jacobiInsert_generators (c e : Fin d → Fin d → Fin d → R) (i j k : Fin d) :
    jacobiInsert (Kontsevich.linearPoissonBinary c) (Kontsevich.linearPoissonBinary e)
      (X i) (X j) (X k) = ∑ r, C (coefficientJacobi c e i j k r) * X r := by
  simp only [jacobiInsert_apply, Kontsevich.linearPoissonBinary_apply, nested_bracket_generators,
    coefficientJacobi, Finset.sum_add_distrib, map_add, add_mul]

theorem coefficientJacobi_coeff (c e : Fin d → Fin d → Fin d → Polynomial R)
    (n : ℕ) (i j k r : Fin d) :
    (coefficientJacobi c e i j k r).coeff n =
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n,
        coefficientJacobi (fun i j r => (c i j r).coeff ab.1)
          (fun i j r => (e i j r).coeff ab.2) i j k r := by
  simp only [coefficientJacobi, Polynomial.finsetSum_coeff, Polynomial.coeff_add,
    Polynomial.coeff_mul, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]

variable {L : Type*} [LieRing L] [LieAlgebra R L]

/-- These coefficient equations follow from the full polynomial Poisson Jacobi theorem. -/
theorem native_coefficientJacobi (b : Basis (Fin d) R L) (i j k r : Fin d) :
    coefficientJacobi (Poisson.structureCoeff b) (Poisson.structureCoeff b) i j k r = 0 := by
  have hright := Poisson.linearBracket_lie_jacobi b (X i) (X j) (X k)
  have hleft : jacobiInsert (Kontsevich.linearPoissonBinary (Poisson.structureCoeff b))
      (Kontsevich.linearPoissonBinary (Poisson.structureCoeff b)) (X i) (X j) (X k) = 0 := by
    simp only [jacobiInsert_apply, Kontsevich.linearPoissonBinary_apply]
    rw [Poisson.linearBracket_skew b (Poisson.linearBracket (Poisson.structureCoeff b) (X i) (X j)) (X k),
      Poisson.linearBracket_skew b (Poisson.linearBracket (Poisson.structureCoeff b) (X j) (X k)) (X i),
      Poisson.linearBracket_skew b (Poisson.linearBracket (Poisson.structureCoeff b) (X k) (X i)) (X j)]
    simpa only [neg_add, neg_zero, add_assoc, add_comm, add_left_comm] using
      congrArg (fun f => -f) hright
  rw [jacobiInsert_generators] at hleft
  have h := congrArg (Poisson.linearCoeff r) hleft
  simpa [Poisson.linearCoeff, coeff_sum, coeff_C_mul, coeff_X, Finsupp.single_left_inj] using h

end PolynomialIdentities

section QuadraticTranslation

variable {K V W : Type*} [Field K] [CharZero K]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

omit [CharZero K] in
theorem applyBilinear_constant_left (B : V →ₗ[K] V →ₗ[K] W) (v : V)
    (p : PowerSeriesModule K V) :
    PowerSeriesModule.applyBilinear B (PowerSeriesModule.single 0 v) p =
      PowerSeriesModule.map (B v) p := by
  apply PowerSeriesModule.ext
  intro n
  rw [PowerSeriesModule.coeffV_applyBilinear, PowerSeriesModule.coeffV_map]
  rw [Finset.sum_eq_single (0, n)]
  · simp
  · intro ij hij hne
    have hi : ij.1 ≠ 0 := by
      intro hzero
      apply hne
      have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      exact Prod.ext hzero (by omega)
    simp [hi]
  · simp [Finset.HasAntidiagonal.mem_antidiagonal]

omit [CharZero K] in
theorem applyBilinear_symmetric (B : V →ₗ[K] V →ₗ[K] W)
    (hB : ∀ v w, B v w = B w v) (p q : PowerSeriesModule K V) :
    PowerSeriesModule.applyBilinear B p q = PowerSeriesModule.applyBilinear B q p := by
  rw [PowerSeriesModule.applyBilinear_flip]
  have hflip : B.flip = B := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    exact hB w v
  rw [hflip]

omit [CharZero K] in
theorem applyBilinear_scalar (B : V →ₗ[K] V →ₗ[K] W) (a : K)
    (p q : PowerSeriesModule K V) :
    PowerSeriesModule.applyBilinear (a • B) p q =
      a • PowerSeriesModule.applyBilinear B p q := by
  apply PowerSeriesModule.ext
  intro n
  simp [PowerSeriesModule.coeffV_applyBilinear, Finset.smul_sum]

/-- Translate a zero-differential quadratic MC equation by its constant solution. -/
theorem quadratic_translation (B : V →ₗ[K] V →ₗ[K] W)
    (hB : ∀ v w, B v w = B w v) (v : V) (hv : B v v = 0)
    (p : PowerSeriesModule K V)
    (hp : PowerSeriesModule.applyBilinear B
      (PowerSeriesModule.single 0 v + p) (PowerSeriesModule.single 0 v + p) = 0) :
    Gauge.quadraticCurvature (B v) ((2 : K)⁻¹ • B) p = 0 := by
  have h := hp
  change PowerSeriesModule.extendBilinear B
    (PowerSeriesModule.single 0 v + p) (PowerSeriesModule.single 0 v + p) = 0 at h
  simp only [map_add, LinearMap.add_apply, PowerSeriesModule.extendBilinear_apply] at h
  rw [applyBilinear_constant_left, applyBilinear_constant_left,
    PowerSeriesModule.map_single, hv] at h
  rw [applyBilinear_symmetric B hB p (PowerSeriesModule.single 0 v),
    applyBilinear_constant_left] at h
  have htwo : (2 : K) • PowerSeriesModule.map (B v) p +
      PowerSeriesModule.applyBilinear B p p = 0 := by
    simpa only [two_smul, PowerSeriesModule.single, HahnSeries.single_eq_zero,
      HahnModule.of_zero, zero_add, add_assoc] using h
  have hhalf := congrArg (fun q : PowerSeriesModule K W => (2 : K)⁻¹ • q) htwo
  simp only [smul_add, smul_smul, inv_mul_cancel₀ (show (2 : K) ≠ 0 from two_ne_zero),
    one_smul, smul_zero] at hhalf
  simpa only [Gauge.quadraticCurvature, applyBilinear_scalar] using hhalf

end QuadraticTranslation

section ReesCoefficients

variable {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L] {d : ℕ}
variable {b : Basis (Fin d) k L} (D : WeightData b)

theorem family_structureCoeff (i j r : Fin d) :
    Poisson.structureCoeff (Family.basis D) i j r = D.coeff i j r := by
  rw [Poisson.structureCoeff, Family.basis_bracket]
  simp [Finsupp.single_apply]

def coeffTable (n : ℕ) (i j r : Fin d) : k := (D.coeff i j r).coeff n

theorem coeffTable_skew (n : ℕ) (i j r : Fin d) :
    coeffTable D n i j r = -coeffTable D n j i r := by
  have h := Poisson.structureCoeff_skew (Family.basis D) i j r
  rw [family_structureCoeff, family_structureCoeff] at h
  have hn := congrArg (fun p : Polynomial k => p.coeff n) h
  simpa only [coeffTable, Polynomial.coeff_neg] using hn

theorem coeffTable_self (n : ℕ) (i r : Fin d) : coeffTable D n i i r = 0 := by
  have h := Poisson.structureCoeff_self (Family.basis D) i r
  rw [family_structureCoeff] at h
  simp [coeffTable, h]

/-- A coefficient of the full Rees tensor. No Jacobi premise is imposed on this coefficient. -/
def bivectorCoefficient (n : ℕ) : Multiderivation k (MvPolynomial (Fin d) k) 2 :=
  linearBivectorOfCoefficients (coeffTable D n) (coeffTable_skew D n) (coeffTable_self D n)

/-- The actual outer-parameter family of polynomial bivectors. -/
def poissonSeries : PowerSeriesModule k (Multiderivation k (MvPolynomial (Fin d) k) 2) :=
  PowerSeriesModule.mk (bivectorCoefficient D)

@[simp] theorem poissonSeries_coeff (n : ℕ) :
    PowerSeriesModule.coeffV n (poissonSeries D) = bivectorCoefficient D n := rfl

theorem raw_bivectorCoefficient (n : ℕ) :
    rawBivector (bivectorCoefficient D n) = Kontsevich.linearPoissonBinary (coeffTable D n) :=
  linearBivectorOfCoefficients_toBinary _ _ _

/-- The full polynomial Rees table satisfies Jacobi before any coefficient is extracted. -/
theorem rees_coefficientJacobi (i j k r : Fin d) :
    coefficientJacobi D.coeff D.coeff i j k r = 0 := by
  simpa only [coefficientJacobi, family_structureCoeff] using
    native_coefficientJacobi (Family.basis D) i j k r

/-- Each coefficient of the full quadratic Jacobi expression is a finite Cauchy sum. -/
theorem coeffTable_jacobi_convolution (n : ℕ) (i j l r : Fin d) :
    (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n,
      coefficientJacobi (coeffTable D ab.1) (coeffTable D ab.2) i j l r) = 0 := by
  have h := congrArg (fun p : Polynomial k => p.coeff n) (rees_coefficientJacobi D i j l r)
  rw [coefficientJacobi_coeff, Polynomial.coeff_zero] at h
  exact h

theorem jacobiInsert_generators_convolution (n : ℕ) (i j k : Fin d) :
    (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n,
      jacobiInsert (Kontsevich.linearPoissonBinary (coeffTable D ab.1))
        (Kontsevich.linearPoissonBinary (coeffTable D ab.2)) (X i) (X j) (X k)) = 0 := by
  simp only [jacobiInsert_generators]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro r hr
  rw [← Finset.sum_mul, ← map_sum, coeffTable_jacobi_convolution, map_zero, zero_mul]

variable [CharZero k]

local instance laurentCharZero : CharZero (LaurentSeries k) :=
  Algebra.charZero_of_charZero k (LaurentSeries k)

/-- The actual Schouten bracket in the bivector-to-trivector degrees. -/
def bivectorBracket : Multiderivation k (PolynomialFunctions k d) 2 →ₗ[k]
    Multiderivation k (PolynomialFunctions k d) 2 →ₗ[k]
      Multiderivation k (PolynomialFunctions k d) 3 :=
  schoutenBracket k d 1 1

theorem bivectorBracket_apply
    (F G : Multiderivation k (PolynomialFunctions k d) 2) (p q r : PolynomialFunctions k d) :
    bivectorBracket F G ![p, q, r] =
      jacobiInsert (rawBivector F) (rawBivector G) p q r +
        jacobiInsert (rawBivector G) (rawBivector F) p q r :=
  schoutenBivectors_apply F G p q r

/-- The entire Rees bivector series has zero Schouten square.
This is proved from the full polynomial family, not by assuming its coefficients Poisson. -/
theorem poissonSeries_square :
    PowerSeriesModule.applyBilinear (k := k)
      (V := Multiderivation k (PolynomialFunctions k d) 2)
      (W := Multiderivation k (PolynomialFunctions k d) 2)
      (X := Multiderivation k (PolynomialFunctions k d) 3)
      (bivectorBracket (k := k) (d := d))
      (poissonSeries D) (poissonSeries D) = 0 := by
  apply PowerSeriesModule.ext
  intro n
  change (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n,
    bivectorBracket (bivectorCoefficient D ab.1) (bivectorCoefficient D ab.2)) =
      (0 : Multiderivation k (PolynomialFunctions k d) 3)
  apply Multiderivation.ext_coordinates 3
  intro u
  have hu : (fun i : Fin 3 => X (u i) : Fin 3 → PolynomialFunctions k d) =
      ![X (u 0), X (u 1), X (u 2)] := by
    funext i
    fin_cases i <;> rfl
  rw [hu]
  change (Multiderivation.evaluation ![X (u 0), X (u 1), X (u 2)])
    (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n,
      bivectorBracket (bivectorCoefficient D ab.1) (bivectorCoefficient D ab.2)) = 0
  rw [map_sum]
  simp only [Multiderivation.evaluation_apply, bivectorBracket_apply,
    raw_bivectorCoefficient, Finset.sum_add_distrib]
  rw [jacobiInsert_generators_convolution]
  simp only [zero_add]
  have hswap := Finset.Nat.sum_antidiagonal_swap (n := n)
    (f := fun ab => jacobiInsert (Kontsevich.linearPoissonBinary (coeffTable D ab.1))
      (Kontsevich.linearPoissonBinary (coeffTable D ab.2)) (X (u 0)) (X (u 1)) (X (u 2)))
  exact hswap.trans (jacobiInsert_generators_convolution D n (u 0) (u 1) (u 2))

def constantBivector : Multiderivation k (PolynomialFunctions k d) 2 := bivectorCoefficient D 0

theorem constantBivector_square :
    bivectorBracket (constantBivector D) (constantBivector D) = 0 := by
  have h := congrArg (PowerSeriesModule.coeffV 0) (poissonSeries_square D)
  change (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal 0,
    bivectorBracket (bivectorCoefficient D ab.1) (bivectorCoefficient D ab.2)) =
      (0 : Multiderivation k (PolynomialFunctions k d) 3) at h
  simpa only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, constantBivector] using h

theorem constantBivector_isMaurerCartan :
    (polynomialSchoutenDGLA k d).IsMaurerCartan (constantBivector D) := by
  change (0 : Multiderivation k (PolynomialFunctions k d) 3) +
    (2 : k)⁻¹ • bivectorBracket (constantBivector D) (constantBivector D) = 0
  rw [constantBivector_square]
  simp

/-- The genuine Laurent coefficient extension of the polynomial Schouten source. -/
abbrev laurentSource := (polynomialSchoutenDGLA k d).laurent

def laurentBivectorBracket : (laurentSource (k := k) (d := d)).Obj 1 →ₗ[LaurentSeries k]
    (laurentSource (k := k) (d := d)).Obj 1 →ₗ[LaurentSeries k]
      (laurentSource (k := k) (d := d)).Obj 2 :=
  (laurentSource (k := k) (d := d)).bracket 1 1

theorem laurentBivectorBracket_single (e f : ℤ)
    (x y : Multiderivation k (PolynomialFunctions k d) 2) :
    laurentBivectorBracket (LaurentModule.single (k := k) e x) (LaurentModule.single (k := k) f y) =
      LaurentModule.single (k := k) (e + f) (bivectorBracket x y) :=
  (polynomialSchoutenDGLA k d).laurentBracket_single 1 1 e f x y

omit [CharZero k] in
theorem laurent_single_sum {α : Type*} (s : Finset α) (e : ℤ)
    (f : α → Multiderivation k (PolynomialFunctions k d) 3) :
    (∑ a ∈ s, LaurentModule.single (k := k) e (f a)) =
      LaurentModule.single (k := k) e (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, LaurentModule.single_add]

/-- The actual total family `h * π(t)` in Laurent-completed source coefficients. -/
def totalLaurentSeries : PowerSeriesModule (LaurentSeries k) ((laurentSource (k := k) (d := d)).Obj 1) :=
  PowerSeriesModule.mk (k := LaurentSeries k)
    (fun n => LaurentModule.single (k := k) 1 (bivectorCoefficient D n))

@[simp] theorem totalLaurentSeries_coeff (n : ℕ) :
    PowerSeriesModule.coeffV (k := LaurentSeries k) n (totalLaurentSeries D) =
      LaurentModule.single (k := k) 1 (bivectorCoefficient D n) := rfl

theorem totalLaurentSeries_square :
    PowerSeriesModule.applyBilinear (k := LaurentSeries k)
      (V := (laurentSource (k := k) (d := d)).Obj 1)
      (W := (laurentSource (k := k) (d := d)).Obj 1)
      (X := (laurentSource (k := k) (d := d)).Obj 2)
      (laurentBivectorBracket (k := k) (d := d)) (totalLaurentSeries D) (totalLaurentSeries D) = 0 := by
  apply PowerSeriesModule.ext (k := LaurentSeries k)
  intro n
  change (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n,
    laurentBivectorBracket (LaurentModule.single (k := k) 1 (bivectorCoefficient D ab.1))
      (LaurentModule.single (k := k) 1 (bivectorCoefficient D ab.2))) = 0
  simp only [laurentBivectorBracket_single]
  rw [laurent_single_sum]
  have h := congrArg (PowerSeriesModule.coeffV (k := k) n) (poissonSeries_square D)
  change (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n,
    bivectorBracket (bivectorCoefficient D ab.1) (bivectorCoefficient D ab.2)) =
      (0 : Multiderivation k (PolynomialFunctions k d) 3) at h
  rw [h, LaurentModule.single_zero]

/-- The constant Laurent Maurer–Cartan element `h * π(0)`. -/
def baseLaurentBivector : (laurentSource (k := k) (d := d)).Obj 1 :=
  LaurentModule.single (k := k) 1 (constantBivector D)

theorem baseLaurentBivector_square :
    laurentBivectorBracket (baseLaurentBivector D) (baseLaurentBivector D) = 0 := by
  rw [baseLaurentBivector, laurentBivectorBracket_single, constantBivector_square,
    LaurentModule.single_zero]

theorem laurentSource_d_one (x : (laurentSource (k := k) (d := d)).Obj 1) :
    (laurentSource (k := k) (d := d)).d 1 x = 0 := by
  apply LaurentModule.ext (k := k)
  intro e
  rfl

theorem baseLaurentBivector_isMaurerCartan :
    (laurentSource (k := k) (d := d)).IsMaurerCartan (baseLaurentBivector D) := by
  have hs : (laurentSource (k := k) (d := d)).bracket 1 1
      (baseLaurentBivector D) (baseLaurentBivector D) = 0 := baseLaurentBivector_square D
  unfold SignedDGLA.IsMaurerCartan SignedDGLA.curvature
  rw [laurentSource_d_one, hs]
  simp

/-- The actual source DGLA twisted at `h * π(0)`. -/
def twistedSource := (laurentSource (k := k) (d := d)).twist
  (baseLaurentBivector D) (baseLaurentBivector_isMaurerCartan D)

/-- The positive perturbation `h * (π(t) - π(0))`, with Laurent completion taken first. -/
def perturbationSeries : PowerSeriesModule (LaurentSeries k) ((laurentSource (k := k) (d := d)).Obj 1) :=
  totalLaurentSeries D - PowerSeriesModule.single (k := LaurentSeries k) 0 (baseLaurentBivector D)

theorem perturbationSeries_positive :
    PowerSeriesModule.coeffV (k := LaurentSeries k) 0 (perturbationSeries D) = 0 := by
  simp [perturbationSeries, PowerSeriesModule.coeffV_sub,
    PowerSeriesModule.coeffV_single, totalLaurentSeries_coeff, baseLaurentBivector, constantBivector]

/-- Every coefficient has exactly one factor of the inner Laurent parameter. -/
theorem perturbationSeries_coeff (n : ℕ) :
    PowerSeriesModule.coeffV (k := LaurentSeries k) n (perturbationSeries D) =
      LaurentModule.single (k := k) 1
        (bivectorCoefficient D n - if n = 0 then constantBivector D else 0) := by
  by_cases hn : n = 0
  · subst n
    rw [perturbationSeries_positive]
    simp only [constantBivector]
    exact ((congrArg (LaurentModule.single (k := k) 1)
      (sub_self (bivectorCoefficient D 0))).trans (LaurentModule.single_zero 1)).symm
  · simp only [perturbationSeries, PowerSeriesModule.coeffV_sub,
      PowerSeriesModule.coeffV_single, totalLaurentSeries_coeff, hn]
    exact (sub_zero (LaurentModule.single (k := k) 1 (bivectorCoefficient D n) :
      (laurentSource (k := k) (d := d)).Obj 1)).trans
      (congrArg (LaurentModule.single (k := k) 1) (sub_zero (bivectorCoefficient D n)).symm)

/-- One half of the actual source bracket, with its cohomological target degree explicitly transported. -/
def sourceQuadratic : (laurentSource (k := k) (d := d)).Obj 1 →ₗ[LaurentSeries k]
    (laurentSource (k := k) (d := d)).Obj 1 →ₗ[LaurentSeries k]
      (laurentSource (k := k) (d := d)).Obj 2 :=
  (((2 : LaurentSeries k)⁻¹) • (laurentSource (k := k) (d := d)).bracket 1 1).compr₂
    (gradedModuleCongr (LaurentSeries k) (laurentSource (k := k) (d := d)).complex.X
      (by decide : (1 : ℤ) + 1 = 2)).toLinearMap

theorem sourceQuadratic_eq : sourceQuadratic (k := k) (d := d) =
    (2 : LaurentSeries k)⁻¹ • laurentBivectorBracket (k := k) (d := d) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rfl

theorem laurent_twistedD_one_apply (x : (laurentSource (k := k) (d := d)).Obj 1) :
    (laurentSource (k := k) (d := d)).twistedD (baseLaurentBivector D) 1 x =
      laurentBivectorBracket (baseLaurentBivector D) x := by
  rw [SignedDGLA.twistedD_apply, laurentSource_d_one,
    SignedDGLA.oddAdjoint_apply]
  exact zero_add _

theorem twistedSource_d_one : ((twistedSource D).complex.d 1 2).hom =
    laurentBivectorBracket (baseLaurentBivector D) := by
  exact ((laurentSource (k := k) (d := d)).twist_d
    (baseLaurentBivector D) (baseLaurentBivector_isMaurerCartan D) 1).trans
      (LinearMap.ext (laurent_twistedD_one_apply D))

/-- The positive Rees perturbation satisfies the actual twisted source MC equation. -/
theorem perturbationSeries_curvature :
    Gauge.quadraticCurvature ((twistedSource D).complex.d 1 2).hom
      (sourceQuadratic (k := k) (d := d)) (perturbationSeries D) = 0 := by
  rw [twistedSource_d_one, sourceQuadratic_eq]
  apply quadratic_translation (K := LaurentSeries k)
    (laurentBivectorBracket (k := k) (d := d))
    (fun x y => (laurentSource (k := k) (d := d)).bracket_one_symmetric x y)
    (baseLaurentBivector D) (baseLaurentBivector_square D) (perturbationSeries D)
  have hsum : PowerSeriesModule.single (k := LaurentSeries k) 0 (baseLaurentBivector D) +
      perturbationSeries D = totalLaurentSeries D := by
    unfold perturbationSeries
    abel
  rw [hsum]
  exact totalLaurentSeries_square D

/-- The concrete F11 source Maurer–Cartan series, with no MC hypothesis supplied by the caller. -/
def sourceMCSeries : Gauge.MCSeries ((twistedSource D).complex.d 1 2).hom
    (sourceQuadratic (k := k) (d := d)) :=
  ⟨perturbationSeries D, perturbationSeries_positive D, perturbationSeries_curvature D⟩

variable {M : Type*} [LieRing M] [LieAlgebra k M]
variable {c : Basis (Fin d) k M} (E : WeightData c)

omit [CharZero k] in
/-- Identical zero-fiber tables produce the same base bivector in the common coordinate space. -/
theorem constantBivector_eq_of_zero
    (hzero : ∀ i j r, Polynomial.eval 0 (D.coeff i j r) = Polynomial.eval 0 (E.coeff i j r)) :
    constantBivector D = constantBivector E := by
  have hc : coeffTable D 0 = coeffTable E 0 := by
    funext i j r
    simpa only [coeffTable, Polynomial.coeff_zero_eq_eval_zero] using hzero i j r
  apply rawBivector_injective
  change rawBivector (bivectorCoefficient D 0) = rawBivector (bivectorCoefficient E 0)
  rw [raw_bivectorCoefficient, raw_bivectorCoefficient, hc]

theorem baseLaurentBivector_eq_of_zero
    (hzero : ∀ i j r, Polynomial.eval 0 (D.coeff i j r) = Polynomial.eval 0 (E.coeff i j r)) :
    baseLaurentBivector D = baseLaurentBivector E :=
  congrArg (LaurentModule.single (k := k) 1) (constantBivector_eq_of_zero D E hzero)

end ReesCoefficients

end

end EnvelopingIsomorphism.Rees.PoissonMCFamily
