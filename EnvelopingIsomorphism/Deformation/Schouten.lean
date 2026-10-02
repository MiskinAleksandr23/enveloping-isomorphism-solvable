import EnvelopingIsomorphism.Deformation.Polyvectors
import EnvelopingIsomorphism.Deformation.ZeroDifferentialTransfer
import EnvelopingIsomorphism.Deformation.HochschildDGLA
import Mathlib.RingTheory.Derivation.Lie

/-!
# The signed Schouten algebra of polynomial multiderivations

The inclusion and projection are actual factorial-normalized cochains and
coordinate antisymmetric evaluations. Full integer degrees retain functions
in degree -1 and put the zero module below them.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation

set_option backward.isDefEq.respectTransparency false

universe u
variable (K : Type u) [Field K] [CharZero K] (d : ℕ)

abbrev PolynomialFunctions := MvPolynomial (Fin d) K

/-- Polynomial multiderivations in their shifted cohomological degrees. -/
@[reducible] def fullPolyvectorObj : ℤ → ModuleCat.{u} K
  | .ofNat n => ModuleCat.of K (Multiderivation K (PolynomialFunctions K d) (n + 1))
  | .negSucc 0 => ModuleCat.of K (PolynomialFunctions K d)
  | .negSucc (_ + 1) => ModuleCat.of K PUnit

abbrev FullPolyvector (p : ℤ) : Type u := fullPolyvectorObj K d p

/-- Actual normalized HKR on each shifted component, including functions. -/
def fullPolyvectorInclusion : (p : ℤ) → FullPolyvector K d p →ₗ[K]
    FullCochain K (PolynomialFunctions K d) p
  | .ofNat n => (cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1)).toLinearMap.comp
      (Multiderivation.toCochain.restrictScalars K)
  | .negSucc 0 => LinearMap.id
  | .negSucc (_ + 1) => LinearMap.id

/-- Actual alternating coordinate projection on every shifted component. -/
def fullPolyvectorProjection : (p : ℤ) → FullCochain K (PolynomialFunctions K d) p →ₗ[K]
    FullPolyvector K d p
  | .ofNat n => (Multiderivation.fromCochain.restrictScalars K).comp
      (cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1)).symm.toLinearMap
  | .negSucc 0 => LinearMap.id
  | .negSucc (_ + 1) => LinearMap.id

@[simp] theorem fullPolyvectorProjection_inclusion (p : ℤ) (F : FullPolyvector K d p) :
    fullPolyvectorProjection K d p (fullPolyvectorInclusion K d p F) = F := by
  cases p with
  | ofNat n =>
    change Multiderivation.fromCochain
      ((cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1)).symm
        ((cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1))
          (Multiderivation.toCochain F))) = F
    rw [LinearEquiv.symm_apply_apply, Multiderivation.fromCochain_toCochain]
  | negSucc n => cases n <;> rfl

variable {K d}

omit [CharZero K] in
theorem uncurried_curriedDifferential (n : ℕ)
    (f : Curried K (PolynomialFunctions K d) (n + 1)) :
    (cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1 + 1)).symm
      (curriedDifferential (LinearMap.mul K (PolynomialFunctions K d)) n f) =
      (-1 : K) ^ (n + 1 + 1) •
        barDifferential (LinearMap.mul K (PolynomialFunctions K d)) (n + 1)
          ((cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1)).symm f) := by
  simp only [curriedDifferential, LinearMap.smul_apply, map_smul,
    barDifferential_apply, LinearEquiv.apply_symm_apply]

omit [CharZero K] in
theorem fullDifferential_commutative_neg_one (f : PolynomialFunctions K d) :
    fullDifferential (LinearMap.mul K (PolynomialFunctions K d)) (-1) f = 0 := by
  apply LinearMap.ext
  intro g
  change f * g - g * f = 0
  rw [mul_comm, sub_self]

theorem fullPolyvectorInclusion_closed (p : ℤ) (F : FullPolyvector K d p) :
    fullDifferential (LinearMap.mul K (PolynomialFunctions K d)) p
      (fullPolyvectorInclusion K d p F) = 0 := by
  cases p with
  | ofNat n =>
    apply (cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1 + 1)).symm.injective
    rw [map_zero]
    change (cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1 + 1)).symm
      (curriedDifferential (LinearMap.mul K (PolynomialFunctions K d)) n
        ((cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1))
          (Multiderivation.toCochain F))) = 0
    rw [uncurried_curriedDifferential, LinearEquiv.symm_apply_apply,
      Multiderivation.barDifferential_toCochain, smul_zero]
  | negSucc n =>
    cases n with
    | zero => exact fullDifferential_commutative_neg_one _
    | succ n => rfl

theorem fullPolyvectorProjection_boundary (p : ℤ)
    (f : FullCochain K (PolynomialFunctions K d) p) :
    fullPolyvectorProjection K d (p + 1)
      (fullDifferential (LinearMap.mul K (PolynomialFunctions K d)) p f) = 0 := by
  cases p with
  | ofNat n =>
    change (Multiderivation.fromCochain.restrictScalars K)
      ((cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1 + 1)).symm
        (curriedDifferential (LinearMap.mul K (PolynomialFunctions K d)) n f)) = 0
    rw [uncurried_curriedDifferential, map_smul]
    change (-1 : K) ^ (n + 1 + 1) • Multiderivation.fromCochain _ = 0
    rw [Multiderivation.fromCochain_barDifferential, smul_zero]
  | negSucc n =>
    cases n with
    | zero =>
      change fullPolyvectorProjection K d 0
        (fullDifferential (LinearMap.mul K (PolynomialFunctions K d)) (-1) f) = 0
      rw [fullDifferential_commutative_neg_one (K := K) (d := d), map_zero]
    | succ n =>
      change fullPolyvectorProjection K d _ 0 = 0
      exact map_zero _

private theorem bar_closed_of_full_closed (n : ℕ)
    (f : FullCochain K (PolynomialFunctions K d) (n : ℤ))
    (hf : fullDifferential (LinearMap.mul K (PolynomialFunctions K d)) n f = 0) :
    barDifferential (LinearMap.mul K (PolynomialFunctions K d)) (n + 1)
      ((cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1)).symm f) = 0 := by
  have h := congrArg (cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1 + 1)).symm hf
  change (cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1 + 1)).symm
    (curriedDifferential (LinearMap.mul K (PolynomialFunctions K d)) n f) = _ at h
  rw [uncurried_curriedDifferential, map_zero] at h
  exact (smul_eq_zero.mp h).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

omit [CharZero K] in
private theorem barDifferential_commutative_zero (f : Cochain K (PolynomialFunctions K d) 0) :
    barDifferential (LinearMap.mul K (PolynomialFunctions K d)) 0 f = 0 := by
  have h := barDifferential_derivationProduct (k := K) 0
    (cochainZeroEquiv K (PolynomialFunctions K d) f) (fun i : Fin 0 => Fin.elim0 i)
  rw [derivationProduct_zero, LinearEquiv.symm_apply_apply] at h
  exact h

private theorem full_cycle_correction_zero
    (f : FullCochain K (PolynomialFunctions K d) 0)
    (hf : fullDifferential (LinearMap.mul K (PolynomialFunctions K d)) 0 f = 0) :
    f - fullPolyvectorInclusion K d 0 (fullPolyvectorProjection K d 0 f) = 0 := by
  obtain ⟨b, hb⟩ := Multiderivation.cocycle_correction _ (bar_closed_of_full_closed 0 f hf)
  rw [barDifferential_commutative_zero] at hb
  have he := sub_eq_zero.mp hb.symm
  apply sub_eq_zero.mpr
  change f = (cochainCurriedEquiv K (PolynomialFunctions K d) 1)
    (Multiderivation.toCochain (Multiderivation.fromCochain
      ((cochainCurriedEquiv K (PolynomialFunctions K d) 1).symm f)))
  have h := congrArg (cochainCurriedEquiv K (PolynomialFunctions K d) 1) he
  simpa only [LinearEquiv.apply_symm_apply] using h

private theorem full_cycle_correction_succ (n : ℕ)
    (f : Curried K (PolynomialFunctions K d) (n + 1 + 1))
    (hf : curriedDifferential (LinearMap.mul K (PolynomialFunctions K d)) (n + 1) f = 0) :
    ∃ b : Curried K (PolynomialFunctions K d) (n + 1),
      curriedDifferential (LinearMap.mul K (PolynomialFunctions K d)) n b =
        f - (cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1 + 1))
          (Multiderivation.toCochain (Multiderivation.fromCochain
            ((cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1 + 1)).symm f))) := by
  obtain ⟨b, hb⟩ := Multiderivation.cocycle_correction _ (bar_closed_of_full_closed (n + 1) f hf)
  refine ⟨(-1 : K) ^ (n + 1 + 1) •
    (cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1)) b, ?_⟩
  apply (cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1 + 1)).symm.injective
  change (cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1 + 1)).symm
    (curriedDifferential (LinearMap.mul K (PolynomialFunctions K d)) n
      ((-1 : K) ^ (n + 1 + 1) •
        (cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1)) b)) = _
  rw [uncurried_curriedDifferential, map_smul, LinearEquiv.symm_apply_apply,
    map_smul, smul_smul, insertionSign_square, one_smul, hb]
  simp only [map_sub, LinearEquiv.symm_apply_apply]

omit [CharZero K] in
private theorem fullDifferential_congr {p q : ℤ} (h : p = q)
    (f : FullCochain K (PolynomialFunctions K d) p) :
    fullDifferential (LinearMap.mul K (PolynomialFunctions K d)) q
        (gradedModuleCongr K (fullCochainObj K (PolynomialFunctions K d)) h f) =
      gradedModuleCongr K (fullCochainObj K (PolynomialFunctions K d)) (congrArg (· + 1) h)
        (fullDifferential (LinearMap.mul K (PolynomialFunctions K d)) p f) := by
  subst q
  rfl

/-- In every integer degree, a closed cochain differs from its chosen representative by a boundary. -/
theorem fullPolyvector_cycle_correction (p : ℤ)
    (f : FullCochain K (PolynomialFunctions K d) p)
    (hf : fullDifferential (LinearMap.mul K (PolynomialFunctions K d)) p f = 0) :
    ∃ b : FullCochain K (PolynomialFunctions K d) (p - 1),
      f - fullPolyvectorInclusion K d p (fullPolyvectorProjection K d p f) =
        gradedModuleCongr K (fullCochainObj K (PolynomialFunctions K d))
          (by omega : (p - 1) + 1 = p)
          (fullDifferential (LinearMap.mul K (PolynomialFunctions K d)) (p - 1) b) := by
  cases p with
  | ofNat n =>
    cases n with
    | zero =>
      refine ⟨0, ?_⟩
      change f - fullPolyvectorInclusion K d 0 (fullPolyvectorProjection K d 0 f) = _
      rw [full_cycle_correction_zero (K := K) (d := d) f hf]
      simp only [map_zero]
    | succ n =>
      have hidx : (Int.ofNat (n + 1) - 1) = (n : ℤ) := by
        change (((n + 1 : ℕ) : ℤ) - 1) = (n : ℤ)
        simp
      obtain ⟨b, hb⟩ := full_cycle_correction_succ n f hf
      refine ⟨gradedModuleCongr K (fullCochainObj K (PolynomialFunctions K d)) hidx.symm b, ?_⟩
      rw [fullDifferential_congr, gradedModuleCongr_trans]
      change _ = curriedDifferential (LinearMap.mul K (PolynomialFunctions K d)) n b
      exact hb.symm
  | negSucc n =>
    refine ⟨0, ?_⟩
    cases n <;>
      simp only [fullPolyvectorInclusion, fullPolyvectorProjection, LinearMap.id_apply,
        sub_self, map_zero]

variable (K d)

/-- The concrete projected model, with correction supplied by the proved polynomial HKR theorem. -/
def fullPolyvectorModel :
    (hochschildDGLA (LinearMap.mul K (PolynomialFunctions K d)) mul_assoc).ProjectedModel :=
  SignedDGLA.projectedModelOfCycleCorrection _ (fullPolyvectorObj K d)
    (fullPolyvectorInclusion K d) (fullPolyvectorProjection K d)
    (by
      intro p f
      change ((fullComplex (LinearMap.mul K (PolynomialFunctions K d)) mul_assoc).d p (p + 1)).hom
        (fullPolyvectorInclusion K d p f) = 0
      rw [fullComplex_d]
      exact fullPolyvectorInclusion_closed p f)
    (by
      intro p f
      change fullPolyvectorProjection K d (p + 1)
        (((fullComplex (LinearMap.mul K (PolynomialFunctions K d)) mul_assoc).d p (p + 1)).hom f) = 0
      rw [fullComplex_d]
      exact fullPolyvectorProjection_boundary p f)
    (by
      intro p f hf
      change ((fullComplex (LinearMap.mul K (PolynomialFunctions K d)) mul_assoc).d p (p + 1)).hom f = 0 at hf
      rw [fullComplex_d] at hf
      obtain ⟨b, hb⟩ := fullPolyvector_cycle_correction p f hf
      refine ⟨b, ?_⟩
      change _ = gradedModuleCongr K (fullCochainObj K (PolynomialFunctions K d)) _
        (((fullComplex (LinearMap.mul K (PolynomialFunctions K d)) mul_assoc).d
          (p - 1) ((p - 1) + 1)).hom b)
      rw [fullComplex_d]
      exact hb)

/-- The actual signed DGLA of polynomial polyvectors, with zero differential. -/
def polynomialSchoutenDGLA : SignedDGLA.{u, u} K :=
  (fullPolyvectorModel K d).toSignedDGLA

def schoutenBracket (p q : ℤ) : FullPolyvector K d p →ₗ[K] FullPolyvector K d q →ₗ[K]
    FullPolyvector K d (p + q) := (fullPolyvectorModel K d).bracket p q

theorem schoutenBracket_apply (p q : ℤ) (F : FullPolyvector K d p) (G : FullPolyvector K d q) :
    schoutenBracket K d p q F G = fullPolyvectorProjection K d (p + q)
      (fullBracket p q (fullPolyvectorInclusion K d p F) (fullPolyvectorInclusion K d q G)) := rfl

theorem schoutenBracket_skew (p q : ℤ) (F : FullPolyvector K d p) (G : FullPolyvector K d q) :
    HEq (schoutenBracket K d p q F G)
      (-((p * q).negOnePow : K) • schoutenBracket K d q p G F) :=
  (fullPolyvectorModel K d).skew p q F G

theorem schoutenBracket_jacobi (p q r : ℤ)
    (F : FullPolyvector K d p) (G : FullPolyvector K d q) (H : FullPolyvector K d r) :
    gradedModuleCongr K (fullPolyvectorObj K d) (add_assoc p q r).symm
        (schoutenBracket K d p (q + r) F (schoutenBracket K d q r G H)) =
      schoutenBracket K d (p + q) r (schoutenBracket K d p q F G) H +
        ((p * q).negOnePow : K) • gradedModuleCongr K (fullPolyvectorObj K d)
          (by omega : q + (p + r) = (p + q) + r)
          (schoutenBracket K d q (p + r) G (schoutenBracket K d p r F H)) :=
  (fullPolyvectorModel K d).jacobi p q r F G H

@[simp] theorem polynomialSchoutenDGLA_d (p q : ℤ) :
    (polynomialSchoutenDGLA K d).complex.d p q = 0 :=
  (fullPolyvectorModel K d).complex_d p q

variable {K d}

private theorem cochainBracket_toCochain_closed (m n : ℕ)
    (F : Multiderivation K (PolynomialFunctions K d) (m + 1))
    (G : Multiderivation K (PolynomialFunctions K d) (n + 1)) :
    barDifferential (LinearMap.mul K (PolynomialFunctions K d)) (m + (n + 1))
      (cochainBracketPositive m n (Multiderivation.toCochain F) (Multiderivation.toCochain G)) = 0 := by
  have h := fullDifferential_bracket (LinearMap.mul K (PolynomialFunctions K d)) (m : ℤ) (n : ℤ)
    (fullPolyvectorInclusion K d m F) (fullPolyvectorInclusion K d n G)
  rw [fullPolyvectorInclusion_closed, fullPolyvectorInclusion_closed] at h
  simp only [map_zero, LinearMap.zero_apply, smul_zero, add_zero] at h
  change curriedDifferential (LinearMap.mul K (PolynomialFunctions K d)) (m + n)
    (curriedBracket m n
      ((cochainCurriedEquiv K (PolynomialFunctions K d) (m + 1)) (Multiderivation.toCochain F))
      ((cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1)) (Multiderivation.toCochain G))) = 0 at h
  exact bar_closed_of_full_closed (m + n) _ h

/-- In positive arities the bracket is the actual full antisymmetrization of normalized
Gerstenhaber insertion. This also proves that this insertion expression is a multiderivation. -/
theorem schoutenBracket_nat_val (m n : ℕ)
    (F : Multiderivation K (PolynomialFunctions K d) (m + 1))
    (G : Multiderivation K (PolynomialFunctions K d) (n + 1)) :
    (show Multiderivation K (PolynomialFunctions K d) (m + (n + 1)) from
      schoutenBracket K d m n F G).val =
      MultilinearMap.alternatization
        (cochainBracketPositive m n (Multiderivation.toCochain F) (Multiderivation.toCochain G)) := by
  change (Multiderivation.fromCochain
    (cochainBracketPositive m n (Multiderivation.toCochain F) (Multiderivation.toCochain G))).val = _
  exact Multiderivation.fromCochain_val_of_closed _ (cochainBracket_toCochain_closed m n F G)

/-- Explicit permutation-sum evaluation of the positive-arity Schouten bracket. -/
theorem schoutenBracket_nat_apply (m n : ℕ)
    (F : Multiderivation K (PolynomialFunctions K d) (m + 1))
    (G : Multiderivation K (PolynomialFunctions K d) (n + 1))
    (a : Fin (m + (n + 1)) → PolynomialFunctions K d) :
    (show Multiderivation K (PolynomialFunctions K d) (m + (n + 1)) from
      schoutenBracket K d m n F G) a =
      ∑ σ : Equiv.Perm (Fin (m + (n + 1))), Equiv.Perm.sign σ •
        cochainBracketPositive m n (Multiderivation.toCochain F) (Multiderivation.toCochain G)
          (fun i => a (σ i)) := by
  rw [schoutenBracket_nat_val]
  exact alternatingEvaluation_apply _ _

/-- The bracket of two functions is zero in degree -2. -/
theorem schoutenBracket_functions (f g : PolynomialFunctions K d) :
    schoutenBracket K d (-1) (-1) f g = 0 := by
  rw [schoutenBracket_apply, fullBracket_constants, map_zero]

/-- Bracketing a vector field with a function is its ordinary derivation action. -/
theorem schoutenBracket_vector_function (F : Multiderivation K (PolynomialFunctions K d) 1)
    (f : PolynomialFunctions K d) :
    schoutenBracket K d 0 (-1) F f = (Multiderivation.oneEquiv F) f := by
  change ((cochainCurriedEquiv K (PolynomialFunctions K d) 1) (Multiderivation.toCochain F)) f = _
  rw [cochainCurriedEquiv_one]
  change Multiderivation.toCochain F (fun _ => f) = _
  rw [Multiderivation.toCochain_apply]
  simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
  change F (fun _ => f) = F (Function.update (fun _ => 0) 0 f)
  congr 1
  funext i
  rw [Fin.eq_zero i, Function.update_self]

theorem schoutenBracket_function_vector (f : PolynomialFunctions K d)
    (F : Multiderivation K (PolynomialFunctions K d) 1) :
    schoutenBracket K d (-1) 0 f F = -(Multiderivation.oneEquiv F) f := by
  change -(schoutenBracket K d 0 (-1) F f) = _
  rw [schoutenBracket_vector_function]

omit [CharZero K] in
private theorem alternating_curryLeft_comm (n : ℕ)
    (F : PolynomialFunctions K d [⋀^Fin (n + 1 + 1)]→ₗ[K] PolynomialFunctions K d)
    (a b : PolynomialFunctions K d) :
    (F.curryLeft a).curryLeft b = -(F.curryLeft b).curryLeft a := by
  have h := F.curryLeft_same (a + b)
  simp only [map_add, AlternatingMap.curryLeft_add, LinearMap.add_apply,
    AlternatingMap.curryLeft_same, zero_add, add_zero] at h
  rw [add_comm] at h
  exact eq_neg_of_add_eq_zero_left h

omit [CharZero K] in
/-- For a raw alternating cochain all signed constant insertions coincide. -/
private theorem curriedPreLie_constant_alternating (n : ℕ)
    (F : PolynomialFunctions K d [⋀^Fin (n + 1)]→ₗ[K] PolynomialFunctions K d)
    (a : PolynomialFunctions K d) :
    curriedPreLie 0 n
      (cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1) F.toMultilinearMap) a =
      (n + 1) • cochainCurriedEquiv K (PolynomialFunctions K d) n
        (F.curryLeft a).toMultilinearMap := by
  induction n with
  | zero =>
    change (cochainCurriedEquiv K (PolynomialFunctions K d) 0) (F.curryLeft a).toMultilinearMap =
      (1 : ℕ) • (cochainCurriedEquiv K (PolynomialFunctions K d) 0) (F.curryLeft a).toMultilinearMap
    rw [one_nsmul]
  | succ n ih =>
    apply LinearMap.ext
    intro b
    change (cochainCurriedEquiv K (PolynomialFunctions K d) n)
        ((F.curryLeft a).curryLeft b).toMultilinearMap +
      (-1 : K) ^ 1 • curriedPreLie 0 n
        ((cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1))
          (F.curryLeft b).toMultilinearMap) a =
        (n + 1 + 1) • (cochainCurriedEquiv K (PolynomialFunctions K d) n)
          ((F.curryLeft a).curryLeft b).toMultilinearMap
    rw [pow_one, neg_one_smul, ← sub_eq_add_neg]
    rw [ih, alternating_curryLeft_comm, AlternatingMap.coe_neg, map_neg, smul_neg]
    simp only [add_nsmul, one_nsmul]
    abel

/-- Constant insertion of normalized alternating cochains is normalized contraction. -/
theorem constantInsertion_toCochain (n : ℕ)
    (F : Multiderivation K (PolynomialFunctions K d) (n + 1)) (a : PolynomialFunctions K d) :
    (cochainCurriedEquiv K (PolynomialFunctions K d) n).symm
      (curriedBracketConstant n
        (cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1) (Multiderivation.toCochain F)) a) =
      Multiderivation.toCochain (F.contract a) := by
  apply (cochainCurriedEquiv K (PolynomialFunctions K d) n).injective
  rw [LinearEquiv.apply_symm_apply]
  change curriedPreLie 0 n
    ((cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1))
      (((n + 1).factorial : K)⁻¹ • F.val.toMultilinearMap)) a =
    (cochainCurriedEquiv K (PolynomialFunctions K d) n)
      ((n.factorial : K)⁻¹ • (F.val.curryLeft a).toMultilinearMap)
  rw [map_smul, map_smul, LinearMap.smul_apply, map_smul,
    curriedPreLie_constant_alternating, ← Nat.cast_smul_eq_nsmul K, smul_smul]
  congr 1
  have hn : (n + 1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_inv_rev]
  rw [mul_assoc, inv_mul_cancel₀ hn, mul_one]

/-- All higher brackets with a function are ordinary contraction, with the degree transport explicit. -/
theorem schoutenBracket_higher_function (n : ℕ)
    (F : Multiderivation K (PolynomialFunctions K d) (n + 1 + 1)) (a : PolynomialFunctions K d) :
    HEq (schoutenBracket K d (Int.ofNat (n + 1)) (-1) F a) (F.contract a) := by
  have ht := fullBracket_nat_constant (n + 1)
    (fullPolyvectorInclusion K d (Int.ofNat (n + 1)) F) a
  have hdeg : Int.ofNat (n + 1) + (-1) = (n : ℤ) := by
    change (((n + 1 : ℕ) : ℤ) + (-1)) = (n : ℤ)
    simp
  have hp := (fullPolyvectorModel K d).projection_heq hdeg ht
  change HEq (schoutenBracket K d (Int.ofNat (n + 1)) (-1) F a)
    (Multiderivation.fromCochain
      ((cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1)).symm
        (curriedBracketConstant (n + 1)
          (cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1 + 1)
            (Multiderivation.toCochain F)) a))) at hp
  rw [constantInsertion_toCochain (n + 1) F a, Multiderivation.fromCochain_toCochain] at hp
  exact hp

/-- Normalized inclusion in degree zero is the usual linear map underlying the vector field. -/
theorem fullPolyvectorInclusion_zero (F : Multiderivation K (PolynomialFunctions K d) 1) :
    fullPolyvectorInclusion K d 0 F = (Multiderivation.oneEquiv F).toLinearMap := by
  apply LinearMap.ext
  intro a
  exact schoutenBracket_vector_function F a

/-- The Schouten bracket of vector fields is their actual derivation commutator. -/
theorem schoutenBracket_vectors (F G : Multiderivation K (PolynomialFunctions K d) 1) :
    schoutenBracket K d 0 0 F G =
      Multiderivation.ofDerivation ⁅Multiderivation.oneEquiv F, Multiderivation.oneEquiv G⁆ := by
  have hc : cochainBracketPositive 0 0 (Multiderivation.toCochain F) (Multiderivation.toCochain G) =
      Multiderivation.toCochain
        (Multiderivation.ofDerivation ⁅Multiderivation.oneEquiv F, Multiderivation.oneEquiv G⁆) := by
    apply (cochainCurriedEquiv K (PolynomialFunctions K d) 1).injective
    rw [cochainBracketPositive_apply, LinearEquiv.apply_symm_apply]
    change curriedBracket 0 0 (fullPolyvectorInclusion K d 0 F) (fullPolyvectorInclusion K d 0 G) =
      fullPolyvectorInclusion K d 0
        (Multiderivation.ofDerivation ⁅Multiderivation.oneEquiv F, Multiderivation.oneEquiv G⁆)
    rw [fullPolyvectorInclusion_zero, fullPolyvectorInclusion_zero,
      fullPolyvectorInclusion_zero, Multiderivation.oneEquiv_ofDerivation, curriedBracket_unary_unary]
    rfl
  change Multiderivation.fromCochain
    (cochainBracketPositive 0 0 (Multiderivation.toCochain F) (Multiderivation.toCochain G)) = _
  rw [hc, Multiderivation.fromCochain_toCochain]

end EnvelopingIsomorphism.Deformation
