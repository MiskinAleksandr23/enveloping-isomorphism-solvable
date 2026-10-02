import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Prod
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Polynomial.Module.TensorProduct
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.Tactic.Abel

/-!
# An explicit contraction of the polynomial Koszul complex

The construction uses the recursive tensor presentation of a Koszul complex.
If `C` is the total module for the old variables, adjoining one variable gives
`C[X] ⊕ C[X]`, with differential `(a,b) ↦ (da + Xb, -db)`.
Here module-valued polynomials are finitely supported coefficient sequences.
No regular-sequence or exactness hypothesis is used: division by the new
variable gives a contraction, recursively, over every commutative ring.
-/

namespace EnvelopingIsomorphism.Deformation.Koszul

noncomputable section

universe u

variable {R : Type u} [CommRing R]

section PolynomialModule

variable {M N : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Multiplication by the polynomial variable on module-valued polynomials. -/
def mulX : (ℕ →₀ M) →ₗ[R] (ℕ →₀ M) := Finsupp.lmapDomain M R Nat.succ

/-- Remove the constant coefficient and divide by the polynomial variable. -/
def divX : (ℕ →₀ M) →ₗ[R] (ℕ →₀ M) :=
  Finsupp.lcomapDomain Nat.succ Nat.succ_injective

@[simp] theorem divX_apply (p : ℕ →₀ M) (i : ℕ) :
    divX (R := R) p i = p (i + 1) := rfl

@[simp] theorem mulX_apply_zero (p : ℕ →₀ M) : mulX (R := R) p 0 = 0 := by
  simp [mulX, Finsupp.mapDomain_notin_range]

@[simp] theorem mulX_apply_succ (p : ℕ →₀ M) (i : ℕ) :
    mulX (R := R) p (i + 1) = p i := by
  exact Finsupp.mapDomain_apply Nat.succ_injective p i

@[simp] theorem divX_mulX (p : ℕ →₀ M) : divX (R := R) (mulX (R := R) p) = p := by
  ext i
  simp

theorem mulX_divX (p : ℕ →₀ M) :
    mulX (R := R) (divX (R := R) p) = p - Finsupp.single 0 (p 0) := by
  ext i
  cases i <;> simp

@[simp] theorem map_mulX (f : M →ₗ[R] N) (p : ℕ →₀ M) :
    Finsupp.mapRange.linearMap f (mulX (R := R) p) =
      mulX (R := R) (Finsupp.mapRange.linearMap f p) := by
  ext i
  cases i <;> simp

@[simp] theorem map_divX (f : M →ₗ[R] N) (p : ℕ →₀ M) :
    Finsupp.mapRange.linearMap f (divX (R := R) p) =
      divX (R := R) (Finsupp.mapRange.linearMap f p) := by
  ext i
  rfl

end PolynomialModule

/-- A differential module with an explicit contraction onto its augmentation.
This is construction data, not an assumed resolution: `polynomial` below
constructs all fields and identities from the ground ring. -/
structure AugmentedContraction (R : Type u) [CommRing R] where
  C : ModuleCat.{u} R
  d : C →ₗ[R] C
  h : C →ₗ[R] C
  ε : C →ₗ[R] R
  η : R →ₗ[R] C
  d_sq : ∀ x, d (d x) = 0
  ε_d : ∀ x, ε (d x) = 0
  d_η : ∀ r, d (η r) = 0
  ε_η : ∀ r, ε (η r) = r
  contraction : ∀ x, d (h x) + h (d x) = x - η (ε x)

namespace AugmentedContraction

variable (K : AugmentedContraction R)

/-- Tensor with the two-term complex `R[X] --X--> R[X]`. -/
abbrev stepModule : ModuleCat.{u} R := ModuleCat.of R ((ℕ →₀ K.C) × (ℕ →₀ K.C))

def stepD : K.stepModule →ₗ[R] K.stepModule :=
  ((Finsupp.mapRange.linearMap K.d).comp (LinearMap.fst R _ _) +
    mulX.comp (LinearMap.snd R _ _)).prod
    (-((Finsupp.mapRange.linearMap K.d).comp (LinearMap.snd R _ _)))

def stepH : K.stepModule →ₗ[R] K.stepModule :=
  ((Finsupp.lsingle 0).comp (K.h.comp ((Finsupp.lapply 0).comp
    (LinearMap.fst R _ _)))).prod
    (divX.comp (LinearMap.fst R _ _))

def stepε : K.stepModule →ₗ[R] R :=
  K.ε.comp ((Finsupp.lapply 0).comp (LinearMap.fst R _ _))

def stepη : R →ₗ[R] K.stepModule := ((Finsupp.lsingle 0).comp K.η).prod 0

@[simp] theorem stepD_apply (a b : ℕ →₀ K.C) :
    K.stepD (a, b) =
      (Finsupp.mapRange.linearMap K.d a + mulX (R := R) b,
        -Finsupp.mapRange.linearMap K.d b) := rfl

@[simp] theorem stepH_apply (a b : ℕ →₀ K.C) :
    K.stepH (a, b) = (Finsupp.single 0 (K.h (a 0)), divX (R := R) a) := rfl

@[simp] theorem stepε_apply (a b : ℕ →₀ K.C) : K.stepε (a, b) = K.ε (a 0) := rfl

@[simp] theorem stepη_apply (r : R) : K.stepη r = (Finsupp.single 0 (K.η r), 0) := rfl

theorem stepD_sq (x : K.stepModule) : K.stepD (K.stepD x) = 0 := by
  rcases x with ⟨a, b⟩
  apply Prod.ext
  · ext i
    cases i <;> simp [stepD, K.d_sq]
  · ext i
    simp [stepD, K.d_sq]

theorem stepε_d (x : K.stepModule) : K.stepε (K.stepD x) = 0 := by
  rcases x with ⟨a, b⟩
  simp [stepD, stepε, K.ε_d]

theorem stepD_η (r : R) : K.stepD (K.stepη r) = 0 := by
  apply Prod.ext
  · ext i
    by_cases hi : i = 0 <;> simp [stepD, stepη, hi, K.d_η]
  · simp [stepD, stepη]

theorem stepε_η (r : R) : K.stepε (K.stepη r) = r := by
  simp [stepε, stepη, K.ε_η]

theorem step_contraction (x : K.stepModule) :
    K.stepD (K.stepH x) + K.stepH (K.stepD x) = x - K.stepη (K.stepε x) := by
  rcases x with ⟨a, b⟩
  apply Prod.ext
  · ext i
    cases i with
    | zero => simpa [stepD, stepH, stepη, stepε] using K.contraction (a 0)
    | succ i => simp [stepD, stepH, stepη, stepε]
  · ext i
    simp [stepD, stepH, stepη, stepε]

/-- Adjoining a polynomial variable preserves the explicit augmented contraction. -/
def step : AugmentedContraction R where
  C := K.stepModule
  d := K.stepD
  h := K.stepH
  ε := K.stepε
  η := K.stepη
  d_sq := K.stepD_sq
  ε_d := K.stepε_d
  d_η := K.stepD_η
  ε_η := K.stepε_η
  contraction := K.step_contraction

/-- Every augmented cycle has the explicit preimage supplied by the contraction. -/
theorem exact (x : K.C) (hd : K.d x = 0) (hε : K.ε x = 0) : K.d (K.h x) = x := by
  simpa [hd, hε] using K.contraction x

theorem mem_range_d_iff (x : K.C) :
    x ∈ LinearMap.range K.d ↔ K.d x = 0 ∧ K.ε x = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨K.d_sq y, K.ε_d y⟩
  · rintro ⟨hd, hε⟩
    exact ⟨K.h x, K.exact x hd hε⟩

end AugmentedContraction

/-- The zero-variable Koszul complex is the base ring in degree zero. -/
def ground (R : Type u) [CommRing R] : AugmentedContraction R where
  C := ModuleCat.of R R
  d := 0
  h := 0
  ε := LinearMap.id
  η := LinearMap.id
  d_sq _ := rfl
  ε_d _ := rfl
  d_η _ := rfl
  ε_η _ := rfl
  contraction _ := by simp

/-- The explicit Koszul contraction for `n` independent polynomial variables. -/
def polynomial (R : Type u) [CommRing R] : ℕ → AugmentedContraction R
  | 0 => ground R
  | n + 1 => (polynomial R n).step

/-- Polynomial Koszul exactness, with no hypothesis on regular sequences.
The displayed preimage is explicit and works over any commutative base ring. -/
theorem polynomial_exact (n : ℕ) (x : (polynomial R n).C)
    (hd : (polynomial R n).d x = 0) (hε : (polynomial R n).ε x = 0) :
    (polynomial R n).d ((polynomial R n).h x) = x :=
  (polynomial R n).exact x hd hε

theorem polynomial_range_d (n : ℕ) :
    LinearMap.range (polynomial R n).d =
      LinearMap.ker (polynomial R n).d ⊓ LinearMap.ker (polynomial R n).ε := by
  ext x
  exact (polynomial R n).mem_range_d_iff x

/-- Exterior degree in the recursive tensor presentation. Polynomial exponents
do not contribute to this degree. -/
def Homogeneous : (n p : ℕ) → (polynomial R n).C → Prop
  | 0, 0, _ => True
  | 0, _ + 1, x => x = 0
  | n + 1, 0, x => (∀ i, Homogeneous n 0 (x.1 i)) ∧ x.2 = 0
  | n + 1, p + 1, x =>
      (∀ i, Homogeneous n (p + 1) (x.1 i)) ∧ ∀ i, Homogeneous n p (x.2 i)

theorem homogeneous_zero (n p : ℕ) : Homogeneous (R := R) n p 0 := by
  induction n generalizing p with
  | zero => cases p <;> simp [Homogeneous]
  | succ n ih =>
    cases p with
    | zero => exact ⟨fun _ => ih 0, rfl⟩
    | succ p => exact ⟨fun _ => ih (p + 1), fun _ => ih p⟩

theorem homogeneous_add (n p : ℕ) (x y : (polynomial R n).C)
    (hx : Homogeneous n p x) (hy : Homogeneous n p y) : Homogeneous n p (x + y) := by
  induction n generalizing p with
  | zero => cases p <;> simp_all [Homogeneous]
  | succ n ih =>
    cases p with
    | zero =>
      refine ⟨fun i => ih 0 _ _ (hx.1 i) (hy.1 i), ?_⟩
      change x.2 + y.2 = 0
      rw [hx.2, hy.2, add_zero]
    | succ p =>
      exact ⟨fun i => ih (p + 1) _ _ (hx.1 i) (hy.1 i),
        fun i => ih p _ _ (hx.2 i) (hy.2 i)⟩

theorem homogeneous_smul (n p : ℕ) (r : R) (x : (polynomial R n).C)
    (hx : Homogeneous n p x) : Homogeneous n p (r • x) := by
  induction n generalizing p with
  | zero => cases p <;> simp_all [Homogeneous]
  | succ n ih =>
    cases p with
    | zero =>
      refine ⟨fun i => ih 0 _ (hx.1 i), ?_⟩
      change r • x.2 = 0
      rw [hx.2, smul_zero]
    | succ p => exact ⟨fun i => ih (p + 1) _ (hx.1 i), fun i => ih p _ (hx.2 i)⟩

theorem homogeneous_neg (n p : ℕ) (x : (polynomial R n).C)
    (hx : Homogeneous n p x) : Homogeneous n p (-x) := by
  simpa using homogeneous_smul n p (-1 : R) x hx

/-- The degree-`p` module of the polynomial Koszul complex. -/
def term (R : Type u) [CommRing R] (n p : ℕ) : Submodule R (polynomial R n).C where
  carrier := {x | Homogeneous n p x}
  zero_mem' := homogeneous_zero n p
  add_mem' := fun hx hy => homogeneous_add n p _ _ hx hy
  smul_mem' := homogeneous_smul n p

theorem d_degree_zero (n : ℕ) (x : (polynomial R n).C)
    (hx : Homogeneous n 0 x) : (polynomial R n).d x = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨a, b⟩
    rcases hx with ⟨ha, hb⟩
    change b = 0 at hb
    subst b
    apply Prod.ext
    · ext i
      change (polynomial R n).d (a i) +
        mulX (R := R) (0 : ℕ →₀ (polynomial R n).C) i = 0
      simpa using ih (a i) (ha i)
    · change -Finsupp.mapRange.linearMap (polynomial R n).d 0 = 0
      simp

theorem d_homogeneous (n p : ℕ) (x : (polynomial R n).C)
    (hx : Homogeneous n (p + 1) x) :
    Homogeneous n p ((polynomial R n).d x) := by
  induction n generalizing p with
  | zero =>
    have hx' : x = 0 := hx
    subst x
    simpa using homogeneous_zero (R := R) 0 p
  | succ n ih =>
    rcases x with ⟨a, b⟩
    rcases hx with ⟨ha, hb⟩
    have hfirst (i : ℕ) : Homogeneous n p
        ((Finsupp.mapRange.linearMap (polynomial R n).d a + mulX (R := R) b) i) := by
      apply homogeneous_add
      · exact ih p (a i) (ha i)
      · cases i with
        | zero => simpa using homogeneous_zero (R := R) n p
        | succ i => simpa using hb i
    cases p with
    | zero =>
      refine ⟨hfirst, ?_⟩
      ext i
      change -(polynomial R n).d (b i) = 0
      rw [d_degree_zero n (b i) (hb i), neg_zero]
    | succ p =>
      refine ⟨hfirst, fun i => ?_⟩
      exact homogeneous_neg n p _ (ih p (b i) (hb i))

theorem h_homogeneous (n p : ℕ) (x : (polynomial R n).C)
    (hx : Homogeneous n p x) :
    Homogeneous n (p + 1) ((polynomial R n).h x) := by
  induction n generalizing p with
  | zero => exact homogeneous_zero 0 (p + 1)
  | succ n ih =>
    rcases x with ⟨a, b⟩
    have ha : ∀ i, Homogeneous n p (a i) := by
      cases p <;> exact hx.1
    refine ⟨fun i => ?_, fun i => ha (i + 1)⟩
    change Homogeneous n (p + 1) (Finsupp.single 0 ((polynomial R n).h (a 0)) i)
    by_cases hi : i = 0
    · simpa [hi] using ih p (a 0) (ha 0)
    · simpa [hi] using homogeneous_zero (R := R) n (p + 1)

theorem ε_positive_degree (n p : ℕ) (x : (polynomial R n).C)
    (hx : Homogeneous n (p + 1) x) : (polynomial R n).ε x = 0 := by
  induction n with
  | zero => exact hx
  | succ n ih => exact ih (x.1 0) (hx.1 0)

/-- Exactness in every positive exterior degree, with a homogeneous preimage. -/
theorem polynomial_exact_positive (n p : ℕ) (x : (polynomial R n).C)
    (hx : Homogeneous n (p + 1) x) (hd : (polynomial R n).d x = 0) :
    ∃ y : (polynomial R n).C,
      Homogeneous n (p + 2) y ∧ (polynomial R n).d y = x :=
  ⟨(polynomial R n).h x, h_homogeneous n (p + 1) x hx,
    polynomial_exact n x hd (ε_positive_degree n p x hx)⟩

/-- The Koszul differential between consecutive exterior degrees. -/
def termD (n p : ℕ) : term R n (p + 1) →ₗ[R] term R n p where
  toFun x := ⟨(polynomial R n).d x, d_homogeneous (R := R) n p x.val x.property⟩
  map_add' x y := Subtype.ext ((polynomial R n).d.map_add x y)
  map_smul' r x := Subtype.ext ((polynomial R n).d.map_smul r x)

/-- The explicit contraction raises exterior degree by one. It is linear over
the coefficient ring, but not over the polynomial ring. -/
def termH (n p : ℕ) : term R n p →ₗ[R] term R n (p + 1) where
  toFun x := ⟨(polynomial R n).h x, h_homogeneous (R := R) n p x.val x.property⟩
  map_add' x y := Subtype.ext ((polynomial R n).h.map_add x y)
  map_smul' r x := Subtype.ext ((polynomial R n).h.map_smul r x)

@[simp] theorem termD_coe (n p : ℕ) (x : term R n (p + 1)) :
    (termD n p x : (polynomial R n).C) = (polynomial R n).d x := rfl

@[simp] theorem termH_coe (n p : ℕ) (x : term R n p) :
    (termH n p x : (polynomial R n).C) = (polynomial R n).h x := rfl

theorem termD_sq (n p : ℕ) :
    (termD (R := R) n p).comp (termD n (p + 1)) = 0 := by
  ext x
  exact (polynomial R n).d_sq x

/-- The (unaugmented) polynomial Koszul chain complex. -/
def complex (R : Type u) [CommRing R] (n : ℕ) : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun p => ModuleCat.of R (term R n p))
    (fun p => ModuleCat.ofHom (termD n p)) (fun p => by
      apply ModuleCat.hom_ext
      exact termD_sq n p)

theorem term_range_eq_ker (n p : ℕ) :
    LinearMap.range (termD (R := R) n (p + 1)) = LinearMap.ker (termD n p) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    exact (polynomial R n).d_sq y
  · intro hx
    have hd : (polynomial R n).d x = 0 := congrArg Subtype.val hx
    refine ⟨termH n (p + 1) x, ?_⟩
    apply Subtype.ext
    exact polynomial_exact (R := R) n x.val hd
      (ε_positive_degree (R := R) n p x.val x.property)

theorem η_degree_zero (n : ℕ) (r : R) :
    Homogeneous n 0 ((polynomial R n).η r) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨fun i => ?_, rfl⟩
    change Homogeneous n 0 (Finsupp.single 0 ((polynomial R n).η r) i)
    by_cases hi : i = 0
    · simpa [hi] using ih
    · simpa [hi] using homogeneous_zero (R := R) n 0

/-- Augmentation of the polynomial Koszul complex. -/
def augmentation (n : ℕ) : term R n 0 →ₗ[R] R :=
  (polynomial R n).ε.comp (term R n 0).subtype

/-- Constant polynomials, as a section of the augmentation. -/
def augmentationSection (n : ℕ) : R →ₗ[R] term R n 0 where
  toFun r := ⟨(polynomial R n).η r, η_degree_zero n r⟩
  map_add' r s := Subtype.ext ((polynomial R n).η.map_add r s)
  map_smul' r s := Subtype.ext ((polynomial R n).η.map_smul r s)

@[simp] theorem augmentation_section (n : ℕ) (r : R) :
    augmentation n (augmentationSection n r) = r := (polynomial R n).ε_η r

theorem augmentation_surjective (n : ℕ) : Function.Surjective (augmentation (R := R) n) :=
  fun r => ⟨augmentationSection n r, augmentation_section n r⟩

/-- Exactness at degree zero of the augmented polynomial Koszul complex. -/
theorem augmentation_exact (n : ℕ) :
    LinearMap.range (termD (R := R) n 0) = LinearMap.ker (augmentation n) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (polynomial R n).ε_d y
  · intro hx
    refine ⟨termH n 0 x, ?_⟩
    apply Subtype.ext
    exact polynomial_exact (R := R) n x.val
      (d_degree_zero (R := R) n x.val x.property) hx

/-- The polynomial coefficient ring, in the same recursive coordinate order as
the Koszul complex. The newest variable is the outer polynomial variable. -/
structure CoefficientRing where
  carrier : Type u
  [commRing : CommRing carrier]

instance : CoeSort CoefficientRing.{u} (Type u) := ⟨CoefficientRing.carrier⟩
instance (S : CoefficientRing) : CommRing S := S.commRing

@[reducible] def coefficientRing (R : Type u) [CommRing R] : ℕ → CoefficientRing.{u}
  | 0 => ⟨R⟩
  | n + 1 => ⟨Polynomial (coefficientRing R n)⟩

instance coefficientAlgebra : (n : ℕ) → Algebra R (coefficientRing R n)
  | 0 => inferInstanceAs (Algebra R R)
  | n + 1 =>
    letI := coefficientAlgebra n
    inferInstanceAs (Algebra R (Polynomial (coefficientRing R n)))

/-- Polynomial convolution on finitely supported module coefficients. -/
abbrev coefficientModule (S M : Type u) [CommRing S] [AddCommGroup M] [Module S M] :
    Module (Polynomial S) (ℕ →₀ M) :=
  (PolynomialModule.coeffAddEquiv (R := S) (M := M)).symm.module (Polynomial S)

section CoefficientMaps

variable {S M N : Type u} [CommRing S] [AddCommGroup M] [Module S M]
  [AddCommGroup N] [Module S N]

/-- Coefficient representation as a polynomial-linear equivalence. -/
def coefficientEquiv (S M : Type u) [CommRing S] [AddCommGroup M] [Module S M] :
    letI := coefficientModule S M
    (ℕ →₀ M) ≃ₗ[Polynomial S] PolynomialModule S M :=
  letI := coefficientModule S M
  { toAddEquiv := (PolynomialModule.coeffAddEquiv (R := S) (M := M)).symm
    map_smul' _ _ := rfl }

/-- Applying a linear map to each coefficient is polynomial-linear. -/
def coefficientMap (f : M →ₗ[S] N) :
    letI := coefficientModule S M
    letI := coefficientModule S N
    (ℕ →₀ M) →ₗ[Polynomial S] (ℕ →₀ N) := by
  letI := coefficientModule S M
  letI := coefficientModule S N
  refine
    { toFun := Finsupp.mapRange.linearMap f
      map_add' := (Finsupp.mapRange.linearMap f).map_add
      map_smul' := ?_ }
  intro p x
  change (PolynomialModule.map S f (p • PolynomialModule.ofCoeff S x)).coeff =
    (p • PolynomialModule.map S f (PolynomialModule.ofCoeff S x)).coeff
  rw [PolynomialModule.map_smul]
  simp

theorem coefficient_mulX (x : ℕ →₀ M) :
    letI := coefficientModule S M
    mulX (R := S) x = (Polynomial.X : Polynomial S) • x := by
  letI := coefficientModule S M
  ext i
  change mulX (R := S) x i =
    (PolynomialModule.coeff (Polynomial.X • PolynomialModule.ofCoeff S x)) i
  rw [show (Polynomial.X : Polynomial S) = Polynomial.monomial 1 (1 : S) by
    simpa only [pow_one] using (Polynomial.monomial_one_right_eq_X_pow (R := S) 1).symm]
  cases i <;> simp [PolynomialModule.monomial_smul_apply]

theorem coefficient_mulX_smul (f : Polynomial S) (x : ℕ →₀ M) :
    letI := coefficientModule S M
    mulX (R := S) (f • x) = f • mulX (R := S) x := by
  letI := coefficientModule S M
  rw [coefficient_mulX, coefficient_mulX, smul_comm]

theorem coefficient_C_smul (r : S) (x : ℕ →₀ M) :
    letI := coefficientModule S M
    (Polynomial.C r : Polynomial S) • x = r • x := by
  letI := coefficientModule S M
  ext i
  change (PolynomialModule.coeff (Polynomial.C r • PolynomialModule.ofCoeff S x)) i = r • x i
  change (PolynomialModule.coeff (Polynomial.monomial 0 r • PolynomialModule.ofCoeff S x)) i = _
  simpa only [Nat.zero_le, ite_true, Nat.sub_zero] using
    (PolynomialModule.monomial_smul_apply 0 r (PolynomialModule.ofCoeff S x) i)

end CoefficientMaps

/-- Polynomial scalar multiplication on the total Koszul module. -/
instance scalarModule : (n : ℕ) → Module (coefficientRing R n) (polynomial R n).C
  | 0 => inferInstanceAs (Module R R)
  | n + 1 =>
    letI := scalarModule n
    letI := coefficientModule (coefficientRing R n) (polynomial R n).C
    inferInstanceAs (Module (Polynomial (coefficientRing R n))
      ((ℕ →₀ (polynomial R n).C) × (ℕ →₀ (polynomial R n).C)))

theorem polynomial_smul_fst (n : ℕ) (f : coefficientRing R (n + 1))
    (x : (polynomial R (n + 1)).C) (i : ℕ) :
    letI := scalarModule (R := R) (n + 1)
    (f • x : (polynomial R (n + 1)).C).1 i =
      (PolynomialModule.coeff ((f : Polynomial (coefficientRing R n)) •
        PolynomialModule.ofCoeff (coefficientRing R n) x.1)) i :=
  rfl

theorem polynomial_smul_snd (n : ℕ) (f : coefficientRing R (n + 1))
    (x : (polynomial R (n + 1)).C) (i : ℕ) :
    letI := scalarModule (R := R) (n + 1)
    (f • x : (polynomial R (n + 1)).C).2 i =
      (PolynomialModule.coeff ((f : Polynomial (coefficientRing R n)) •
        PolynomialModule.ofCoeff (coefficientRing R n) x.2)) i :=
  rfl

/-- The Koszul differential as a linear map over the polynomial coefficient ring. -/
def polynomialD : (n : ℕ) →
    (polynomial R n).C →ₗ[coefficientRing R n] (polynomial R n).C
  | 0 => 0
  | n + 1 =>
    letI := scalarModule (R := R) n
    letI := coefficientModule (coefficientRing R n) (polynomial R n).C
    let D := coefficientMap (polynomialD n)
    let X := LinearMap.lsmul (Polynomial (coefficientRing R n))
      (ℕ →₀ (polynomial R n).C) Polynomial.X
    (D.comp (LinearMap.fst _ _ _) + X.comp (LinearMap.snd _ _ _)).prod
      (-D.comp (LinearMap.snd _ _ _))

theorem polynomialD_eq (n : ℕ) (x : (polynomial R n).C) :
    polynomialD n x = (polynomial R n).d x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    letI := scalarModule (R := R) n
    letI := coefficientModule (coefficientRing R n) (polynomial R n).C
    rcases x with ⟨a, b⟩
    apply Prod.ext
    · ext i
      change polynomialD n (a i) + ((Polynomial.X : Polynomial (coefficientRing R n)) • b) i =
        (polynomial R n).d (a i) + mulX (R := R) b i
      rw [ih, ← coefficient_mulX]
      rfl
    · ext i
      change -polynomialD n (b i) = -(polynomial R n).d (b i)
      rw [ih]

/-- The independent polynomial coordinates, ordered by the tensor recursion. -/
def coordinate : (n : ℕ) → Fin n → coefficientRing R n
  | 0 => Fin.elim0
  | n + 1 => Fin.cases Polynomial.X (fun i => Polynomial.C (coordinate n i))

/-- Contraction with one exterior basis covector. The Koszul differential is
the sum of these contractions multiplied by their polynomial coordinates. -/
def interior : (n : ℕ) → Fin n →
    (polynomial R n).C →ₗ[coefficientRing R n] (polynomial R n).C
  | 0 => Fin.elim0
  | n + 1 =>
    letI := scalarModule (R := R) n
    letI := coefficientModule (coefficientRing R n) (polynomial R n).C
    Fin.cases ((LinearMap.snd _ _ _).prod 0)
      (fun i => (coefficientMap (interior n i)).prodMap (-coefficientMap (interior n i)))

theorem polynomialD_sum_interior (n : ℕ) (x : (polynomial R n).C) :
    polynomialD n x = ∑ i : Fin n, coordinate (R := R) n i • interior (R := R) n i x := by
  induction n with
  | zero => simp [polynomialD]
  | succ n ih =>
    letI := scalarModule (R := R) (n + 1)
    letI := scalarModule (R := R) n
    letI := coefficientModule (coefficientRing R n) (polynomial R n).C
    rcases x with ⟨a, b⟩
    apply Prod.ext
    · ext j
      let L : (polynomial R (n + 1)).C →ₗ[R] (polynomial R n).C :=
        (Finsupp.lapply j).comp (LinearMap.fst R _ _)
      change L (polynomialD (n + 1) (a, b)) =
        L (∑ i : Fin (n + 1), coordinate (R := R) (n + 1) i • interior (n + 1) i (a, b))
      rw [map_sum, Fin.sum_univ_succ]
      change polynomialD n (a j) + ((Polynomial.X : Polynomial (coefficientRing R n)) • b) j =
        ((Polynomial.X : Polynomial (coefficientRing R n)) • b) j +
          ∑ i : Fin n, (Polynomial.C (coordinate (R := R) n i) • coefficientMap (interior n i) a) j
      simp only [coefficient_C_smul, Finsupp.smul_apply]
      change polynomialD n (a j) + ((Polynomial.X : Polynomial (coefficientRing R n)) • b) j =
        ((Polynomial.X : Polynomial (coefficientRing R n)) • b) j +
          ∑ i : Fin n, coordinate (R := R) n i • interior n i (a j)
      rw [ih, add_comm]
    · ext j
      let L : (polynomial R (n + 1)).C →ₗ[R] (polynomial R n).C :=
        (Finsupp.lapply j).comp (LinearMap.snd R _ _)
      change L (polynomialD (n + 1) (a, b)) =
        L (∑ i : Fin (n + 1), coordinate (R := R) (n + 1) i • interior (n + 1) i (a, b))
      rw [map_sum, Fin.sum_univ_succ]
      change -polynomialD n (b j) =
        ((Polynomial.X : Polynomial (coefficientRing R n)) • (0 : ℕ →₀ (polynomial R n).C)) j +
          ∑ i : Fin n, (Polynomial.C (coordinate (R := R) n i) • -coefficientMap (interior n i) b) j
      simp only [smul_zero, Finsupp.zero_apply, zero_add, coefficient_C_smul, Finsupp.smul_apply,
        Finsupp.neg_apply, smul_neg, Finset.sum_neg_distrib]
      change -polynomialD n (b j) = -(∑ i : Fin n, coordinate (R := R) n i • interior n i (b j))
      rw [ih]

theorem interior_degree_zero (n : ℕ) (i : Fin n) (x : (polynomial R n).C)
    (hx : Homogeneous n 0 x) : interior n i x = 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rcases x with ⟨a, b⟩
    have hb : b = 0 := hx.2
    subst b
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · apply Prod.ext
      · ext j
        exact ih i (a j) (hx.1 j)
      · change -Finsupp.mapRange.linearMap (interior n i) 0 = 0
        simp

theorem interior_homogeneous (n p : ℕ) (i : Fin n) (x : (polynomial R n).C)
    (hx : Homogeneous n (p + 1) x) : Homogeneous n p (interior n i x) := by
  induction n generalizing p with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rcases x with ⟨a, b⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · cases p with
      | zero => exact ⟨hx.2, rfl⟩
      | succ p => exact ⟨hx.2, fun _ => homogeneous_zero n p⟩
    · cases p with
      | zero =>
        refine ⟨fun j => ih 0 i (a j) (hx.1 j), ?_⟩
        ext j
        change -interior n i (b j) = 0
        rw [interior_degree_zero n i (b j) (hx.2 j), neg_zero]
      | succ p =>
        exact ⟨fun j => ih (p + 1) i (a j) (hx.1 j),
          fun j => homogeneous_neg n p _ (ih p i (b j) (hx.2 j))⟩

theorem homogeneous_polynomial_smul (n p : ℕ) (f : coefficientRing R n)
    (x : (polynomial R n).C) (hx : Homogeneous n p x) :
    Homogeneous n p (f • x : (polynomial R n).C) := by
  induction n generalizing p with
  | zero => cases p <;> simp_all [Homogeneous]
  | succ n ih =>
    letI := scalarModule (R := R) n
    letI := coefficientModule (coefficientRing R n) (polynomial R n).C
    rcases x with ⟨a, b⟩
    have coeff_mem (q : ℕ →₀ (polynomial R n).C) (p : ℕ)
        (hq : ∀ i, Homogeneous n p (q i)) (i : ℕ) :
        Homogeneous n p
          (PolynomialModule.coeff ((f : Polynomial (coefficientRing R n)) •
            PolynomialModule.ofCoeff (coefficientRing R n) q) i) := by
      rw [PolynomialModule.smul_apply]
      exact (term R n p).sum_mem fun z _ => ih p (f.coeff z.1) (q z.2) (hq z.2)
    cases p with
    | zero =>
      refine ⟨fun i => coeff_mem a 0 hx.1 i, ?_⟩
      change PolynomialModule.coeff
        ((f : Polynomial (coefficientRing R n)) •
          PolynomialModule.ofCoeff (coefficientRing R n) b) = 0
      have hb : b = 0 := hx.2
      rw [hb]
      simp
    | succ p =>
      exact ⟨fun i => coeff_mem a (p + 1) hx.1 i, fun i => coeff_mem b p hx.2 i⟩

/-- The degree-`p` term, now as a module over the full polynomial ring. -/
def polynomialTerm (R : Type u) [CommRing R] (n p : ℕ) :
    Submodule (coefficientRing R n) (polynomial R n).C where
  carrier := {x | Homogeneous n p x}
  zero_mem' := homogeneous_zero n p
  add_mem' := fun hx hy => homogeneous_add n p _ _ hx hy
  smul_mem' := fun f _ hx => homogeneous_polynomial_smul n p f _ hx

def polynomialTermD (n p : ℕ) :
    polynomialTerm R n (p + 1) →ₗ[coefficientRing R n] polynomialTerm R n p where
  toFun x := ⟨polynomialD n x.val, by
    rw [polynomialD_eq]
    exact d_homogeneous (R := R) n p x.val x.property⟩
  map_add' x y := Subtype.ext ((polynomialD n).map_add x.val y.val)
  map_smul' r x := Subtype.ext ((polynomialD n).map_smul r x.val)

/-- Interior multiplication restricted to consecutive exterior degrees. -/
def termInterior (n p : ℕ) (i : Fin n) :
    polynomialTerm R n (p + 1) →ₗ[coefficientRing R n] polynomialTerm R n p where
  toFun x := ⟨interior n i x.val, interior_homogeneous (R := R) n p i x.val x.property⟩
  map_add' x y := Subtype.ext ((interior n i).map_add x.val y.val)
  map_smul' r x := Subtype.ext ((interior n i).map_smul r x.val)

theorem polynomialTermD_sum_interior (n p : ℕ) (x : polynomialTerm R n (p + 1)) :
    polynomialTermD n p x = ∑ i : Fin n, coordinate (R := R) n i • termInterior n p i x := by
  apply Subtype.ext
  change polynomialD n x.val = (polynomialTerm R n p).subtype
    (∑ i : Fin n, coordinate (R := R) n i • termInterior n p i x)
  rw [map_sum]
  simp only [map_smul]
  exact polynomialD_sum_interior n x.val

theorem polynomialTermD_sq (n p : ℕ) :
    (polynomialTermD (R := R) n p).comp (polynomialTermD n (p + 1)) = 0 := by
  ext x
  change polynomialD n (polynomialD n x.val) = 0
  rw [polynomialD_eq, polynomialD_eq]
  exact (polynomial R n).d_sq x

/-- The Koszul chain complex over the polynomial ring itself. -/
def polynomialComplex (R : Type u) [CommRing R] (n : ℕ) :
    ChainComplex (ModuleCat.{u} (coefficientRing R n)) ℕ :=
  ChainComplex.of (fun p => ModuleCat.of _ (polynomialTerm R n p))
    (fun p => ModuleCat.ofHom (polynomialTermD n p)) (fun p => by
      apply ModuleCat.hom_ext
      exact polynomialTermD_sq n p)

theorem polynomialTerm_range_eq_ker (n p : ℕ) :
    LinearMap.range (polynomialTermD (R := R) n (p + 1)) =
      LinearMap.ker (polynomialTermD n p) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    change polynomialD n (polynomialD n y.val) = 0
    rw [polynomialD_eq, polynomialD_eq]
    exact (polynomial R n).d_sq y
  · intro hx
    have hd : (polynomial R n).d x.val = 0 := by
      have h := congrArg Subtype.val hx
      change polynomialD n x.val = 0 at h
      rwa [polynomialD_eq] at h
    refine ⟨⟨(polynomial R n).h x.val,
      h_homogeneous (R := R) n (p + 1) x.val x.property⟩, ?_⟩
    apply Subtype.ext
    change polynomialD n ((polynomial R n).h x.val) = x.val
    rw [polynomialD_eq]
    exact polynomial_exact (R := R) n x.val hd
      (ε_positive_degree (R := R) n p x.val x.property)

section Freeness

/-- Coefficients in a submodule can be regarded as submodule-valued coefficients. -/
def subtypeCoefficients {S M : Type u} [CommRing S] [AddCommGroup M] [Module S M]
    (U : Submodule S M) (q : ℕ →₀ M) (hq : ∀ i, q i ∈ U) : ℕ →₀ U :=
  ⟨q.support, fun i => ⟨q i, hq i⟩, fun i => by
    simp only [ne_eq, Subtype.ext_iff, Submodule.coe_zero]
    exact Finsupp.mem_support_iff⟩

@[simp] theorem subtypeCoefficients_apply {S M : Type u} [CommRing S]
    [AddCommGroup M] [Module S M] (U : Submodule S M) (q : ℕ →₀ M)
    (hq : ∀ i, q i ∈ U) (i : ℕ) :
    (subtypeCoefficients U q hq i : M) = q i := rfl

instance polynomialModuleFree (S M : Type u) [CommRing S] [AddCommGroup M]
    [Module S M] [Module.Free S M] : Module.Free (Polynomial S) (PolynomialModule S M) :=
  .of_equiv (PolynomialModule.polynomialTensorProductLEquivPolynomialModule S M)

/-- Forget the condition on each coefficient, without changing the polynomial action. -/
def includeCoefficients (n p : ℕ) :
    letI := coefficientModule (coefficientRing R n) (polynomial R n).C
    PolynomialModule (coefficientRing R n) (polynomialTerm R n p) →ₗ[
      Polynomial (coefficientRing R n)] (ℕ →₀ (polynomial R n).C) := by
  letI := coefficientModule (coefficientRing R n) (polynomial R n).C
  letI := coefficientModule (coefficientRing R n) (polynomialTerm R n p)
  exact (coefficientMap (polynomialTerm R n p).subtype).comp
    (coefficientEquiv (coefficientRing R n) (polynomialTerm R n p)).symm.toLinearMap

@[simp] theorem includeCoefficients_apply (n p : ℕ)
    (q : PolynomialModule (coefficientRing R n) (polynomialTerm R n p)) (i : ℕ) :
    includeCoefficients n p q i = (q.coeff i : (polynomial R n).C) := rfl

def termZeroStepMap (n : ℕ) :
    PolynomialModule (coefficientRing R n) (polynomialTerm R n 0) →ₗ[
      coefficientRing R (n + 1)] polynomialTerm R (n + 1) 0 := by
  letI := scalarModule (R := R) (n + 1)
  letI := coefficientModule (coefficientRing R n) (polynomial R n).C
  exact ((includeCoefficients n 0).prod 0).codRestrict
    (polynomialTerm R (n + 1) 0) (fun q => ⟨fun i => (q.coeff i).property, rfl⟩)

theorem termZeroStepMap_bijective (n : ℕ) :
    Function.Bijective (termZeroStepMap (R := R) n) := by
  constructor
  · intro x y h
    apply PolynomialModule.ext
    ext i
    exact congrArg (fun q : polynomialTerm R (n + 1) 0 => q.val.1 i) h
  · intro x
    refine ⟨PolynomialModule.ofCoeff (coefficientRing R n)
      (subtypeCoefficients (polynomialTerm R n 0) x.val.1 x.property.1), ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · ext i; rfl
    · exact x.property.2.symm

/-- The degree-zero tensor step has a single polynomial-module summand. -/
def termZeroStepEquiv (n : ℕ) :
    PolynomialModule (coefficientRing R n) (polynomialTerm R n 0) ≃ₗ[
      coefficientRing R (n + 1)] polynomialTerm R (n + 1) 0 :=
  LinearEquiv.ofBijective (termZeroStepMap n) (termZeroStepMap_bijective n)

def termSuccStepMap (n p : ℕ) :
    (PolynomialModule (coefficientRing R n) (polynomialTerm R n (p + 1)) ×
      PolynomialModule (coefficientRing R n) (polynomialTerm R n p)) →ₗ[
      coefficientRing R (n + 1)] polynomialTerm R (n + 1) (p + 1) := by
  letI := scalarModule (R := R) (n + 1)
  letI := coefficientModule (coefficientRing R n) (polynomial R n).C
  exact ((includeCoefficients n (p + 1)).prodMap (includeCoefficients n p)).codRestrict
    (polynomialTerm R (n + 1) (p + 1))
    (fun q => ⟨fun i => (q.1.coeff i).property, fun i => (q.2.coeff i).property⟩)

theorem termSuccStepMap_bijective (n p : ℕ) :
    Function.Bijective (termSuccStepMap (R := R) n p) := by
  constructor
  · intro x y h
    apply Prod.ext
    · apply PolynomialModule.ext
      ext i
      exact congrArg (fun q : polynomialTerm R (n + 1) (p + 1) => q.val.1 i) h
    · apply PolynomialModule.ext
      ext i
      exact congrArg (fun q : polynomialTerm R (n + 1) (p + 1) => q.val.2 i) h
  · intro x
    refine ⟨(PolynomialModule.ofCoeff (coefficientRing R n)
      (subtypeCoefficients (polynomialTerm R n (p + 1)) x.val.1 x.property.1),
      PolynomialModule.ofCoeff (coefficientRing R n)
        (subtypeCoefficients (polynomialTerm R n p) x.val.2 x.property.2)), ?_⟩
    apply Subtype.ext
    apply Prod.ext <;> ext i <;> rfl

/-- Splitting exterior degree according to whether the newest generator occurs. -/
def termSuccStepEquiv (n p : ℕ) :
    (PolynomialModule (coefficientRing R n) (polynomialTerm R n (p + 1)) ×
      PolynomialModule (coefficientRing R n) (polynomialTerm R n p)) ≃ₗ[
      coefficientRing R (n + 1)] polynomialTerm R (n + 1) (p + 1) :=
  LinearEquiv.ofBijective (termSuccStepMap n p) (termSuccStepMap_bijective n p)

/-- Every term of the polynomial Koszul complex is free over its polynomial ring. -/
instance polynomialTermFree (n p : ℕ) :
    Module.Free (coefficientRing R n) (polynomialTerm R n p) := by
  induction n generalizing p with
  | zero =>
    cases p with
    | zero =>
      let e : polynomialTerm R 0 0 ≃ₗ[R] R :=
        LinearEquiv.ofBijective (polynomialTerm R 0 0).subtype
          ⟨Subtype.val_injective, fun r => ⟨⟨r, trivial⟩, rfl⟩⟩
      exact Module.Free.of_equiv e.symm
    | succ p =>
      haveI : Subsingleton (polynomialTerm R 0 (p + 1)) :=
        ⟨fun x y => Subtype.ext (x.property.trans y.property.symm)⟩
      infer_instance
  | succ n ih =>
    haveI (q : ℕ) : Module.Free (coefficientRing R n) (polynomialTerm R n q) := ih q
    cases p with
    | zero => exact Module.Free.of_equiv (termZeroStepEquiv (R := R) n)
    | succ p => exact Module.Free.of_equiv (termSuccStepEquiv (R := R) n p)

end Freeness

/-- Indices of exterior monomials, recursively split according to the newest generator. -/
def ExteriorIndex : ℕ → ℕ → Type
  | 0, 0 => PUnit
  | 0, _ + 1 => Empty
  | n + 1, 0 => ExteriorIndex n 0
  | n + 1, p + 1 => ExteriorIndex n (p + 1) ⊕ ExteriorIndex n p

instance exteriorIndexFintype (n p : ℕ) : Fintype (ExteriorIndex n p) := by
  induction n generalizing p with
  | zero => cases p <;> dsimp [ExteriorIndex] <;> infer_instance
  | succ n ih =>
    cases p with
    | zero => exact ih 0
    | succ p =>
      letI := ih p
      letI := ih (p + 1)
      exact inferInstanceAs (Fintype (ExteriorIndex n (p + 1) ⊕ ExteriorIndex n p))

theorem exteriorIndex_card (n p : ℕ) : Fintype.card (ExteriorIndex n p) = n.choose p := by
  induction n generalizing p with
  | zero => cases p <;> simp [ExteriorIndex]
  | succ n ih =>
    cases p with
    | zero => simpa [ExteriorIndex] using ih 0
    | succ p =>
      change Fintype.card (ExteriorIndex n (p + 1) ⊕ ExteriorIndex n p) = (n + 1).choose (p + 1)
      simp only [Fintype.card_sum, ih, Nat.choose_succ_succ]
      exact Nat.add_comm _ _

/-- Extend a module basis to polynomial coefficients. -/
def polynomialModuleBasis {S M : Type u} [CommRing S] [AddCommGroup M] [Module S M]
    {ι : Type*} (b : Module.Basis ι S M) :
    Module.Basis ι (Polynomial S) (PolynomialModule S M) :=
  (Algebra.TensorProduct.basis (Polynomial S) b).map
    (PolynomialModule.polynomialTensorProductLEquivPolynomialModule S M)

/-- The canonical exterior-monomial basis of each polynomial Koszul term. -/
def termBasis : (n p : ℕ) →
    Module.Basis (ExteriorIndex n p) (coefficientRing R n) (polynomialTerm R n p)
  | 0, 0 =>
    let e : polynomialTerm R 0 0 ≃ₗ[R] R :=
      LinearEquiv.ofBijective (polynomialTerm R 0 0).subtype
        ⟨Subtype.val_injective, fun r => ⟨⟨r, trivial⟩, rfl⟩⟩
    (Module.Basis.singleton PUnit R).map e.symm
  | 0, p + 1 =>
    haveI : Subsingleton (polynomialTerm R 0 (p + 1)) :=
      ⟨fun x y => Subtype.ext (x.property.trans y.property.symm)⟩
    haveI : IsEmpty (ExteriorIndex 0 (p + 1)) := inferInstanceAs (IsEmpty Empty)
    Module.Basis.empty _
  | n + 1, 0 => (polynomialModuleBasis (termBasis n 0)).map (termZeroStepEquiv n)
  | n + 1, p + 1 =>
    ((polynomialModuleBasis (termBasis n (p + 1))).prod
      (polynomialModuleBasis (termBasis n p))).map (termSuccStepEquiv n p)

/-- Evaluate all Koszul polynomial variables at zero. -/
def coefficientEval : (n : ℕ) → coefficientRing R n →+* R
  | 0 => RingHom.id R
  | n + 1 => (coefficientEval n).comp Polynomial.constantCoeff

@[simp] theorem coefficientEval_algebraMap (n : ℕ) (r : R) :
    coefficientEval n (algebraMap R (coefficientRing R n) r) = r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change coefficientEval n (Polynomial.constantCoeff
      (Polynomial.C (algebraMap R (coefficientRing R n) r))) = r
    simpa using ih

@[simp] theorem coefficientEval_coordinate (n : ℕ) (i : Fin n) :
    coefficientEval n (coordinate (R := R) n i) = 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [coordinate, coefficientEval]
    · simpa [coordinate, coefficientEval] using ih j

/-- The coefficient ring as a module on which all Koszul variables act by zero. -/
def diagonal (R : Type u) [CommRing R] (n : ℕ) : ModuleCat.{u} (coefficientRing R n) :=
  letI := Module.compHom R (coefficientEval (R := R) n)
  ModuleCat.of (coefficientRing R n) R

instance diagonalBaseModule (n : ℕ) : Module R (diagonal R n) := inferInstanceAs (Module R R)

instance diagonalBaseFree (n : ℕ) : Module.Free R (diagonal R n) :=
  inferInstanceAs (Module.Free R R)

instance diagonalBaseFinite (n : ℕ) : Module.Finite R (diagonal R n) :=
  inferInstanceAs (Module.Finite R R)

instance diagonalScalarTower (n : ℕ) : IsScalarTower R (coefficientRing R n) (diagonal R n) where
  smul_assoc r f x := by
    change R at x
    change coefficientEval n (r • f) * x =
      r * (coefficientEval n f * x)
    rw [Algebra.smul_def, map_mul, coefficientEval_algebraMap, mul_assoc]

instance diagonalSMulCommClass (n : ℕ) : SMulCommClass (coefficientRing R n) R (diagonal R n) where
  smul_comm f r x := by
    change R at x
    change coefficientEval n f * (r * x) = r * (coefficientEval n f * x)
    exact mul_left_comm _ _ _

@[simp] theorem coordinate_smul_diagonal (n : ℕ) (i : Fin n) (x : diagonal R n) :
    coordinate (R := R) n i • x = 0 := by
  change R at x
  change coefficientEval n (coordinate (R := R) n i) * (x : R) = 0
  rw [coefficientEval_coordinate, zero_mul]

/-- Applying `Hom(-, diagonal)` to the Koszul resolution gives zero differentials. -/
theorem hom_comp_d_eq_zero (n p : ℕ)
    (f : polynomialTerm R n p →ₗ[coefficientRing R n] diagonal R n) :
    f.comp (polynomialTermD n p) = 0 := by
  ext x
  change f (polynomialTermD n p x) = 0
  rw [polynomialTermD_sum_interior, map_sum]
  simp only [map_smul, coordinate_smul_diagonal, Finset.sum_const_zero]

theorem ε_polynomial_smul (n : ℕ) (f : coefficientRing R n)
    (x : (polynomial R n).C) :
    (polynomial R n).ε (f • x : (polynomial R n).C) =
      coefficientEval n f * (polynomial R n).ε x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    letI := scalarModule (R := R) n
    rcases x with ⟨a, b⟩
    change (polynomial R n).ε
      (PolynomialModule.coeff ((f : Polynomial (coefficientRing R n)) •
        PolynomialModule.ofCoeff (coefficientRing R n) a) 0) =
      coefficientEval n (f.coeff 0) * (polynomial R n).ε (a 0)
    rw [PolynomialModule.smul_apply]
    simpa using ih (f.coeff 0) (a 0)

/-- The polynomial-linear augmentation onto the diagonal module. -/
def polynomialAugmentation (n : ℕ) :
    polynomialTerm R n 0 →ₗ[coefficientRing R n] diagonal R n where
  toFun x := (polynomial R n).ε x.val
  map_add' x y := (polynomial R n).ε.map_add x.val y.val
  map_smul' f x := ε_polynomial_smul n f x.val

theorem polynomialAugmentation_surjective (n : ℕ) :
    Function.Surjective (polynomialAugmentation (R := R) n) :=
  fun r => ⟨⟨(polynomial R n).η r, η_degree_zero (R := R) n (r : R)⟩,
    (polynomial R n).ε_η r⟩

theorem polynomialAugmentation_exact (n : ℕ) :
    LinearMap.range (polynomialTermD (R := R) n 0) =
      LinearMap.ker (polynomialAugmentation n) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change (polynomial R n).ε (polynomialD n y.val) = 0
    rw [polynomialD_eq]
    exact (polynomial R n).ε_d y
  · intro hx
    refine ⟨⟨(polynomial R n).h x.val,
      h_homogeneous (R := R) n 0 x.val x.property⟩, ?_⟩
    apply Subtype.ext
    change polynomialD n ((polynomial R n).h x.val) = x.val
    rw [polynomialD_eq]
    exact polynomial_exact (R := R) n x.val
      (d_degree_zero (R := R) n x.val x.property) hx

theorem polynomialAugmentation_comp_d (n : ℕ) :
    (polynomialAugmentation (R := R) n).comp (polynomialTermD n 0) = 0 := by
  apply LinearMap.range_le_ker_iff.mp
  exact (polynomialAugmentation_exact n).le

set_option backward.isDefEq.respectTransparency false in
theorem polynomialComplex_exactAt_succ (n p : ℕ) :
    (polynomialComplex R n).ExactAt (p + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (p + 2) (p + 1) p (by simp) (by simp),
    CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker]
  simpa [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', polynomialComplex,
    ChainComplex.of.d] using
    polynomialTerm_range_eq_ker (R := R) n p

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory in
/-- Augmentation as a morphism from the Koszul complex to the diagonal in degree zero. -/
def augmentationChainMap (n : ℕ) :
    polynomialComplex R n ⟶ (ChainComplex.single₀ _).obj (diagonal R n) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (X := polynomialTerm R n 0) (Y := diagonal R n)
      (polynomialAugmentation (R := R) n), by
    apply ModuleCat.hom_ext
    simpa [polynomialComplex, ChainComplex.of.d] using polynomialAugmentation_comp_d (R := R) n⟩

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem augmentationChainMap_f_zero (n : ℕ) :
    (augmentationChainMap (R := R) n).f 0 =
      ModuleCat.ofHom (X := polynomialTerm R n 0) (Y := diagonal R n)
        (polynomialAugmentation n) := by
  unfold augmentationChainMap
  apply ChainComplex.toSingle₀Equiv_symm_apply_f_zero

open CategoryTheory in
instance polynomialAugmentation_epi (n : ℕ) :
    Epi (ModuleCat.ofHom (polynomialAugmentation (R := R) n)) :=
  (ModuleCat.epi_iff_surjective _).mpr (polynomialAugmentation_surjective n)

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory in
instance augmentationChainMap_quasiIso (n : ℕ) :
    QuasiIso (augmentationChainMap (R := R) n) := by
  constructor
  intro p
  cases p with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · constructor
      · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
        change LinearMap.range ((polynomialComplex R n).d 1 0).hom =
          LinearMap.ker ((augmentationChainMap (R := R) n).f 0).hom
        rw [augmentationChainMap_f_zero]
        simpa [polynomialComplex, ChainComplex.of.d] using polynomialAugmentation_exact (R := R) n
      · simpa [augmentationChainMap, HomologicalComplex.shortComplexFunctor'] using
          polynomialAugmentation_epi (R := R) n
    all_goals rfl
  | succ p =>
    rw [quasiIsoAt_iff_exactAt']
    · exact polynomialComplex_exactAt_succ n p
    · apply ChainComplex.exactAt_succ_single_obj

open CategoryTheory in
/-- The polynomial Koszul resolution, with proved freeness and exactness. -/
def resolution (R : Type u) [CommRing R] (n : ℕ) : ProjectiveResolution (diagonal R n) where
  complex := polynomialComplex R n
  projective p := by
    change Projective (ModuleCat.of (coefficientRing R n) (polynomialTerm R n p))
    infer_instance
  π := augmentationChainMap n

/-- The recursive polynomial coefficient ring is the usual multivariate polynomial ring. -/
def coefficientRingEquivMvPolynomial : (n : ℕ) →
    coefficientRing R n ≃+* MvPolynomial (Fin n) R
  | 0 => (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).symm.toRingEquiv
  | n + 1 => (Polynomial.mapEquiv (coefficientRingEquivMvPolynomial n)).trans
      (MvPolynomial.finSuccEquiv R n).symm.toRingEquiv

theorem coefficientRingEquiv_algebraMap (n : ℕ) (r : R) :
    coefficientRingEquivMvPolynomial n (algebraMap R (coefficientRing R n) r) =
      MvPolynomial.C r := by
  induction n with
  | zero => simp [coefficientRingEquivMvPolynomial]
  | succ n ih =>
    change (MvPolynomial.finSuccEquiv R n).symm
      (Polynomial.map (coefficientRingEquivMvPolynomial n).toRingHom
        (Polynomial.C (algebraMap R (coefficientRing R n) r))) = MvPolynomial.C r
    rw [Polynomial.map_C]
    change (MvPolynomial.finSuccEquiv R n).symm
      (Polynomial.C (coefficientRingEquivMvPolynomial n
        (algebraMap R (coefficientRing R n) r))) = MvPolynomial.C r
    rw [ih]
    exact (MvPolynomial.finSuccEquiv R n).symm.commutes r

open CategoryTheory in
/-- The same projective resolution over Mathlib's `MvPolynomial` ring. -/
def mvPolynomialResolution (R : Type u) [CommRing R] (n : ℕ) :
    ProjectiveResolution
      ((ModuleCat.restrictScalars (coefficientRingEquivMvPolynomial (R := R) n).symm.toRingHom).obj
        (diagonal R n)) :=
  (ModuleCat.restrictScalars (coefficientRingEquivMvPolynomial (R := R) n).symm.toRingHom).mapProjectiveResolution
    (resolution R n)

/-- The invertible polynomial change of coordinates `uᵢ = xᵢ - yᵢ`, `vᵢ = yᵢ`.
It works for arbitrary variable types over any commutative coefficient ring. -/
def differenceCoordinates (R : Type u) [CommRing R] (σ : Type*) :
    MvPolynomial (σ ⊕ σ) R ≃ₐ[R] MvPolynomial (σ ⊕ σ) R := by
  let f : MvPolynomial (σ ⊕ σ) R →ₐ[R] MvPolynomial (σ ⊕ σ) R :=
    MvPolynomial.aeval (Sum.elim
      (fun i => MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr i))
      (fun i => MvPolynomial.X (Sum.inr i)))
  let g : MvPolynomial (σ ⊕ σ) R →ₐ[R] MvPolynomial (σ ⊕ σ) R :=
    MvPolynomial.aeval (Sum.elim
      (fun i => MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr i))
      (fun i => MvPolynomial.X (Sum.inr i)))
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · ext i
    cases i <;> simp [f, g]
  · ext i
    cases i <;> simp [f, g]

@[simp] theorem differenceCoordinates_X_left (σ : Type*) (i : σ) :
    differenceCoordinates R σ (MvPolynomial.X (Sum.inl i)) =
      MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr i) := by
  simp [differenceCoordinates, AlgEquiv.ofAlgHom]

@[simp] theorem differenceCoordinates_X_right (σ : Type*) (i : σ) :
    differenceCoordinates R σ (MvPolynomial.X (Sum.inr i)) = MvPolynomial.X (Sum.inr i) := by
  simp [differenceCoordinates, AlgEquiv.ofAlgHom]

/-- Identify the Koszul coefficient ring in the difference variables with the
polynomial ring on the two copies of the original variables. -/
def differenceCoefficientEquiv (R : Type u) [CommRing R] (n : ℕ) :
    coefficientRing (MvPolynomial (Fin n) R) n ≃+* MvPolynomial (Fin n ⊕ Fin n) R :=
  (coefficientRingEquivMvPolynomial (R := MvPolynomial (Fin n) R) n).trans
    ((MvPolynomial.sumAlgEquiv R (Fin n) (Fin n)).symm.toRingEquiv.trans
      (differenceCoordinates R (Fin n)).toRingEquiv)

theorem differenceCoefficientEquiv_algebraMap (R : Type u) [CommRing R] (n : ℕ)
    (a : MvPolynomial (Fin n) R) :
    differenceCoefficientEquiv R n
      (algebraMap (MvPolynomial (Fin n) R) (coefficientRing (MvPolynomial (Fin n) R) n) a) =
      MvPolynomial.rename Sum.inr a := by
  change differenceCoordinates R (Fin n)
    ((MvPolynomial.sumAlgEquiv R (Fin n) (Fin n)).symm
      (coefficientRingEquivMvPolynomial n
        (algebraMap (MvPolynomial (Fin n) R) (coefficientRing (MvPolynomial (Fin n) R) n) a))) = _
  rw [coefficientRingEquiv_algebraMap]
  induction a using MvPolynomial.induction_on with
  | C r => simp [differenceCoordinates, AlgEquiv.ofAlgHom]
  | add a b ha hb => simp [ha, hb]
  | mul_X a i ha => simp [ha]

open CategoryTheory in
/-- The proved projective Koszul resolution after replacing independent
variables by `xᵢ-yᵢ`. Its coefficient module is the transported diagonal. -/
def differenceResolution (R : Type u) [CommRing R] (n : ℕ) :
    ProjectiveResolution
      ((ModuleCat.restrictScalars (differenceCoefficientEquiv R n).symm.toRingHom).obj
        (diagonal (MvPolynomial (Fin n) R) n)) :=
  (ModuleCat.restrictScalars (differenceCoefficientEquiv R n).symm.toRingHom).mapProjectiveResolution
    (resolution (MvPolynomial (Fin n) R) n)

set_option backward.isDefEq.respectTransparency false in
theorem coefficientEval_eq_constantCoeff (n : ℕ) (x : coefficientRing R n) :
    coefficientEval n x = MvPolynomial.constantCoeff (coefficientRingEquivMvPolynomial n x) := by
  induction n with
  | zero => simp [coefficientEval, coefficientRingEquivMvPolynomial]
  | succ n ih =>
    change coefficientEval n (x.coeff 0) =
      MvPolynomial.constantCoeff ((MvPolynomial.finSuccEquiv R n).symm
        (Polynomial.map (coefficientRingEquivMvPolynomial n).toRingHom x))
    rw [ih]
    have h := MvPolynomial.finSuccEquiv_coeff_coeff (0 : Fin n →₀ ℕ)
      ((MvPolynomial.finSuccEquiv R n).symm
        (Polynomial.map (coefficientRingEquivMvPolynomial n).toRingHom x)) 0
    have hz : (0 : Fin n →₀ ℕ).cons 0 = 0 := by
      ext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [AlgEquiv.apply_symm_apply, Polynomial.coeff_map, hz] at h
    exact h

theorem coefficientEval_equiv_symm (n : ℕ) (p : MvPolynomial (Fin n) R) :
    coefficientEval n ((coefficientRingEquivMvPolynomial (R := R) n).symm p) =
      MvPolynomial.constantCoeff p := by
  rw [coefficientEval_eq_constantCoeff, RingEquiv.apply_symm_apply]

/-- Restriction to the diagonal in the polynomial ring on two copies of the variables. -/
def diagonalSubstitution (R : Type u) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin n ⊕ Fin n) R →+* MvPolynomial (Fin n) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Sum.elim MvPolynomial.X MvPolynomial.X)

theorem differenceCoordinates_symm_X_left (σ : Type*) (i : σ) :
    (differenceCoordinates R σ).symm (MvPolynomial.X (Sum.inl i)) =
      MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr i) := by
  simp [differenceCoordinates, AlgEquiv.ofAlgHom]

theorem differenceCoordinates_symm_X_right (σ : Type*) (i : σ) :
    (differenceCoordinates R σ).symm (MvPolynomial.X (Sum.inr i)) =
      MvPolynomial.X (Sum.inr i) := by
  simp [differenceCoordinates, AlgEquiv.ofAlgHom]

/-- The transported augmentation is exactly diagonal substitution, not a different
module with an abstractly isomorphic carrier. -/
theorem difference_augmentation (n : ℕ) :
    (coefficientEval (R := MvPolynomial (Fin n) R) n).comp
      (differenceCoefficientEquiv R n).symm.toRingHom = diagonalSubstitution R n := by
  have h : (coefficientEval (R := MvPolynomial (Fin n) R) n).comp
      (coefficientRingEquivMvPolynomial (R := MvPolynomial (Fin n) R) n).symm.toRingHom =
      MvPolynomial.constantCoeff := by
    apply RingHom.ext
    intro p
    exact coefficientEval_equiv_symm (R := MvPolynomial (Fin n) R) n p
  change (coefficientEval (R := MvPolynomial (Fin n) R) n).comp
    ((coefficientRingEquivMvPolynomial (R := MvPolynomial (Fin n) R) n).symm.toRingHom.comp
      ((MvPolynomial.sumAlgEquiv R (Fin n) (Fin n)).toRingHom.comp
        (differenceCoordinates R (Fin n)).symm.toRingHom)) = _
  rw [← RingHom.comp_assoc, h]
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [diagonalSubstitution, differenceCoordinates, AlgEquiv.ofAlgHom]
  · intro i
    cases i with
    | inl i => simp [diagonalSubstitution, differenceCoordinates_symm_X_left]
    | inr i => simp [diagonalSubstitution, differenceCoordinates_symm_X_right]

section StandardDiagonal

open CategoryTheory
open scoped TensorProduct

/-- Transport the target of a projective resolution through a proved module isomorphism. -/
def resolutionChangeTarget {S : Type u} [CommRing S] {X Y : ModuleCat.{u} S}
    (P : ProjectiveResolution X) (e : X ≅ Y) : ProjectiveResolution Y where
  complex := P.complex
  projective := P.projective
  π := P.π ≫ (ChainComplex.single₀ _).map e.hom

/-- The conventional diagonal module for the polynomial ring in two variable sets. -/
def standardDiagonal (R : Type u) [CommRing R] (n : ℕ) :
    ModuleCat.{u} (MvPolynomial (Fin n ⊕ Fin n) R) :=
  (ModuleCat.restrictScalars (diagonalSubstitution R n)).obj
    (ModuleCat.of (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R))

def differenceDiagonalIso (R : Type u) [CommRing R] (n : ℕ) :
    ((ModuleCat.restrictScalars (differenceCoefficientEquiv R n).symm.toRingHom).obj
      (diagonal (MvPolynomial (Fin n) R) n)) ≅ standardDiagonal R n :=
  (ModuleCat.restrictScalarsComp'App (differenceCoefficientEquiv R n).symm.toRingHom
    (coefficientEval (R := MvPolynomial (Fin n) R) n) (diagonalSubstitution R n)
    (difference_augmentation n).symm
    (ModuleCat.of (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R))).symm

/-- The difference-variable Koszul resolution of the conventional diagonal module. -/
def standardDifferenceResolution (R : Type u) [CommRing R] (n : ℕ) :
    ProjectiveResolution (standardDiagonal R n) :=
  resolutionChangeTarget (differenceResolution R n) (differenceDiagonalIso R n)

/-- The coordinate identification of the polynomial enveloping algebra. -/
def polynomialTensorEquiv (R : Type u) [CommRing R] (n : ℕ) :
    (MvPolynomial (Fin n) R ⊗[R] MvPolynomial (Fin n) R) ≃ₐ[R]
      MvPolynomial (Fin n ⊕ Fin n) R :=
  MvPolynomial.tensorEquivSum R (Fin n) (Fin n) R

theorem polynomialTensorEquiv_one_tmul (R : Type u) [CommRing R] (n : ℕ)
    (a : MvPolynomial (Fin n) R) :
    polynomialTensorEquiv R n (1 ⊗ₜ[R] a) = MvPolynomial.rename Sum.inr a := by
  have h : (polynomialTensorEquiv R n).toAlgHom.comp Algebra.TensorProduct.includeRight =
      MvPolynomial.rename Sum.inr := by
    ext i
    simp [polynomialTensorEquiv]
  exact AlgHom.congr_fun h a

/-- One ring equivalence from independent difference coordinates to `A ⊗ A`. -/
def coefficientEnvelopingEquiv (R : Type u) [CommRing R] (n : ℕ) :
    coefficientRing (MvPolynomial (Fin n) R) n ≃+*
      (MvPolynomial (Fin n) R ⊗[R] MvPolynomial (Fin n) R) :=
  (differenceCoefficientEquiv R n).trans (polynomialTensorEquiv R n).symm.toRingEquiv

theorem coefficientEnvelopingEquiv_algebraMap (R : Type u) [CommRing R] (n : ℕ)
    (a : MvPolynomial (Fin n) R) :
    coefficientEnvelopingEquiv R n
      (algebraMap (MvPolynomial (Fin n) R) (coefficientRing (MvPolynomial (Fin n) R) n) a) =
      1 ⊗ₜ[R] a := by
  apply (polynomialTensorEquiv R n).injective
  change polynomialTensorEquiv R n ((polynomialTensorEquiv R n).symm
    (differenceCoefficientEquiv R n
      (algebraMap (MvPolynomial (Fin n) R) (coefficientRing (MvPolynomial (Fin n) R) n) a))) = _
  rw [AlgEquiv.apply_symm_apply, differenceCoefficientEquiv_algebraMap, polynomialTensorEquiv_one_tmul]

/-- The coefficient equivalence is linear over `A`, using the right copy of `A` in `A ⊗ A`. -/
def coefficientEnvelopingAlgEquiv (R : Type u) [CommRing R] (n : ℕ) :
    letI : Algebra (MvPolynomial (Fin n) R)
      (MvPolynomial (Fin n) R ⊗[R] MvPolynomial (Fin n) R) := Algebra.TensorProduct.rightAlgebra
    coefficientRing (MvPolynomial (Fin n) R) n ≃ₐ[MvPolynomial (Fin n) R]
      (MvPolynomial (Fin n) R ⊗[R] MvPolynomial (Fin n) R) :=
  letI : Algebra (MvPolynomial (Fin n) R)
    (MvPolynomial (Fin n) R ⊗[R] MvPolynomial (Fin n) R) := Algebra.TensorProduct.rightAlgebra
  { coefficientEnvelopingEquiv R n with
    commutes' := coefficientEnvelopingEquiv_algebraMap R n }

theorem tensor_diagonal_augmentation (R : Type u) [CommRing R] (n : ℕ) :
    (diagonalSubstitution R n).comp (polynomialTensorEquiv R n).toRingHom =
      (Algebra.TensorProduct.lmul' R :
        MvPolynomial (Fin n) R ⊗[R] MvPolynomial (Fin n) R →ₐ[R]
          MvPolynomial (Fin n) R).toRingHom := by
  have h : (MvPolynomial.aeval (Sum.elim MvPolynomial.X MvPolynomial.X)).comp
      (polynomialTensorEquiv R n).toAlgHom =
      (Algebra.TensorProduct.lmul' R :
        MvPolynomial (Fin n) R ⊗[R] MvPolynomial (Fin n) R →ₐ[R]
          MvPolynomial (Fin n) R) := by
    apply Algebra.TensorProduct.ext
    · ext i
      simp [polynomialTensorEquiv]
    · ext i
      simp [polynomialTensorEquiv]
  exact congrArg AlgHom.toRingHom h

/-- The usual diagonal module for `A ⊗[R] A`, where `A` is a polynomial algebra. -/
def envelopingDiagonal (R : Type u) [CommRing R] (n : ℕ) :
    ModuleCat.{u} (MvPolynomial (Fin n) R ⊗[R] MvPolynomial (Fin n) R) :=
  (ModuleCat.restrictScalars (Algebra.TensorProduct.lmul' R :
    MvPolynomial (Fin n) R ⊗[R] MvPolynomial (Fin n) R →ₐ[R]
      MvPolynomial (Fin n) R).toRingHom).obj
    (ModuleCat.of (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R))

def envelopingDiagonalIso (R : Type u) [CommRing R] (n : ℕ) :
    ((ModuleCat.restrictScalars (polynomialTensorEquiv R n).toRingHom).obj
      (standardDiagonal R n)) ≅ envelopingDiagonal R n :=
  (ModuleCat.restrictScalarsComp'App (polynomialTensorEquiv R n).toRingHom
    (diagonalSubstitution R n) (Algebra.TensorProduct.lmul' R).toRingHom
    (tensor_diagonal_augmentation R n).symm
    (ModuleCat.of (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R))).symm

/-- The proved polynomial Koszul projective resolution of `A` over `A ⊗[R] A`. -/
def envelopingResolution (R : Type u) [CommRing R] (n : ℕ) :
    ProjectiveResolution (envelopingDiagonal R n) :=
  resolutionChangeTarget
    ((ModuleCat.restrictScalars (polynomialTensorEquiv R n).toRingHom).mapProjectiveResolution
      (standardDifferenceResolution R n)) (envelopingDiagonalIso R n)

theorem coefficientEnveloping_augmentation (R : Type u) [CommRing R] (n : ℕ) :
    (coefficientEval (R := MvPolynomial (Fin n) R) n).comp
      (coefficientEnvelopingEquiv R n).symm.toRingHom =
      (Algebra.TensorProduct.lmul' R :
        MvPolynomial (Fin n) R ⊗[R] MvPolynomial (Fin n) R →ₐ[R]
          MvPolynomial (Fin n) R).toRingHom := by
  change (coefficientEval (R := MvPolynomial (Fin n) R) n).comp
    ((differenceCoefficientEquiv R n).symm.toRingHom.comp
      (polynomialTensorEquiv R n).toRingHom) = _
  rw [← RingHom.comp_assoc, difference_augmentation, tensor_diagonal_augmentation]

def directEnvelopingDiagonalIso (R : Type u) [CommRing R] (n : ℕ) :
    ((ModuleCat.restrictScalars (coefficientEnvelopingEquiv R n).symm.toRingHom).obj
      (diagonal (MvPolynomial (Fin n) R) n)) ≅ envelopingDiagonal R n :=
  (ModuleCat.restrictScalarsComp'App (coefficientEnvelopingEquiv R n).symm.toRingHom
    (coefficientEval (R := MvPolynomial (Fin n) R) n)
    (Algebra.TensorProduct.lmul' R).toRingHom
    (coefficientEnveloping_augmentation R n).symm
    (ModuleCat.of (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R))).symm

/-- A one-step transport of the Koszul resolution, useful for coefficient-linear comparisons. -/
def directEnvelopingResolution (R : Type u) [CommRing R] (n : ℕ) :
    ProjectiveResolution (envelopingDiagonal R n) :=
  resolutionChangeTarget
    ((ModuleCat.restrictScalars (coefficientEnvelopingEquiv R n).symm.toRingHom).mapProjectiveResolution
      (resolution (MvPolynomial (Fin n) R) n)) (directEnvelopingDiagonalIso R n)

end StandardDiagonal

end

end EnvelopingIsomorphism.Deformation.Koszul
