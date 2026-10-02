import EnvelopingIsomorphism.Deformation.Hochschild
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Order.Hom.PowersetCard

/-!
# HKR cochains and their normalization

Products of derivations are cocycles in the project's full Hochschild complex.
Alternatization and factorial normalization give the HKR cocycles, including
arity zero. Coordinate evaluation is expressed by an actual determinant.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation

open scoped BigOperators

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- A coefficient times a product of derivations, as a full Hochschild cochain. -/
def derivationProduct {n : ℕ} (f : A) (D : Fin n → Derivation k A A) : Cochain k A n :=
  f • (MultilinearMap.mkPiAlgebra k (Fin n) A).compLinearMap (fun i => (D i).toLinearMap)

@[simp] theorem derivationProduct_apply {n : ℕ} (f : A) (D : Fin n → Derivation k A A)
    (a : Fin n → A) : derivationProduct f D a = f * ∏ i, D i (a i) := rfl

theorem derivationProduct_zero (f : A) (D : Fin 0 → Derivation k A A) :
    derivationProduct f D = (cochainZeroEquiv k A).symm f := by
  ext a
  simp

theorem derivationProduct_cons {n : ℕ} (f : A) (D : Fin (n + 1) → Derivation k A A)
    (a : A) (x : Fin n → A) :
    derivationProduct f D (Fin.cons a x) =
      derivationProduct (f * D 0 a) (fun i => D i.succ) x := by
  simp [derivationProduct_apply, Fin.prod_univ_succ, mul_assoc]

theorem derivationProduct_curryLeft {n : ℕ} (f : A) (D : Fin (n + 1) → Derivation k A A)
    (a : A) : (derivationProduct f D).curryLeft a =
      derivationProduct (f * D 0 a) (fun i => D i.succ) := by
  ext x
  exact derivationProduct_cons f D a x

/-- The cocycle identity for a product of derivations, in every arity. -/
theorem barDifferential_derivationProduct (n : ℕ) (f : A) (D : Fin n → Derivation k A A) :
    barDifferential (LinearMap.mul k A) n (derivationProduct f D) = 0 := by
  induction n generalizing f with
  | zero =>
    rw [derivationProduct_zero]
    apply (cochainOneEquiv k A).injective
    rw [barDifferential_zero, map_zero]
    ext a
    change -(f * a - a * f) = 0
    rw [mul_comm f a, sub_self, neg_zero]
  | succ n ih =>
    ext x
    rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail (Fin.tail x)]
    rw [barDifferential_cons_cons, derivationProduct_curryLeft, ih]
    simp only [zero_apply, derivationProduct_apply, Fin.prod_univ_succ, Fin.cons_zero,
      Fin.cons_succ, LinearMap.mul_apply', Derivation.leibniz, smul_eq_mul]
    ring

/-- Permuting inputs simply permutes the factors, with the inverse convention. -/
theorem derivationProduct_domDomCongr {n : ℕ} (f : A) (D : Fin n → Derivation k A A)
    (σ : Equiv.Perm (Fin n)) :
    (derivationProduct f D).domDomCongr σ =
      derivationProduct f (fun i => D (σ.symm i)) := by
  ext a
  simp only [MultilinearMap.domDomCongr_apply, derivationProduct_apply]
  congr 1
  simpa using (Equiv.prod_comp σ (fun i => D (σ.symm i) (a i)))

/-- Unnormalized antisymmetric evaluation, as in the Koszul-to-bar comparison. -/
def alternatingEvaluation {n : ℕ} (F : Cochain k A n) (a : Fin n → A) : A :=
  MultilinearMap.alternatization F a

theorem alternatingEvaluation_apply {n : ℕ} (F : Cochain k A n) (a : Fin n → A) :
    alternatingEvaluation F a =
      ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • F (fun i => a (σ i)) := by
  simp only [alternatingEvaluation, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply]

/-- Antisymmetric evaluation is linear in the full Hochschild cochain. -/
def alternatingEvaluationLinearMap {n : ℕ} (a : Fin n → A) : Cochain k A n →ₗ[k] A where
  toFun F := alternatingEvaluation F a
  map_add' F G := by simp [alternatingEvaluation, map_add]
  map_smul' c F := by
    simp only [alternatingEvaluation_apply, smul_apply, RingHom.id_apply,
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    exact smul_comm (Equiv.Perm.sign σ) c _

@[simp] theorem alternatingEvaluationLinearMap_apply {n : ℕ} (a : Fin n → A)
    (F : Cochain k A n) : alternatingEvaluationLinearMap a F = alternatingEvaluation F a := rfl

/-- Alternating products of derivations are still full Hochschild cocycles. -/
theorem barDifferential_alternatization_derivationProduct (n : ℕ) (f : A)
    (D : Fin n → Derivation k A A) :
    barDifferential (LinearMap.mul k A) n
      (MultilinearMap.alternatization (derivationProduct f D)).toMultilinearMap = 0 := by
  rw [MultilinearMap.alternatization_coe, map_sum]
  apply Finset.sum_eq_zero
  intro σ hσ
  rw [Units.smul_def, map_zsmul, derivationProduct_domDomCongr,
    barDifferential_derivationProduct, smul_zero]

/-- Alternating evaluation of a product of derivations is its evaluation determinant. -/
theorem alternatingEvaluation_derivationProduct {n : ℕ} (f : A)
    (D : Fin n → Derivation k A A) (a : Fin n → A) :
    alternatingEvaluation (derivationProduct f D) a =
      f * Matrix.det (fun i j => D j (a i)) := by
  rw [alternatingEvaluation_apply, Matrix.det_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  simp [derivationProduct_apply, Units.smul_def, zsmul_eq_mul, mul_left_comm]

/-- Antisymmetric evaluation vanishes if a fixed pair of slots is symmetric. -/
theorem alternatingEvaluation_eq_zero_of_swap {n : ℕ} (F : Cochain k A n)
    (i j : Fin n) (hij : i ≠ j)
    (hF : ∀ a, F (fun q => a (Equiv.swap i j q)) = F a) (a : Fin n → A) :
    alternatingEvaluation F a = 0 := by
  rw [alternatingEvaluation_apply]
  refine Finset.sum_involution (fun σ _ => σ * Equiv.swap i j) ?_ ?_
    (fun _ _ => Finset.mem_univ _) (fun σ _ => Equiv.mul_swap_involutive i j σ)
  · intro σ hσ
    have he : F (fun q => a ((σ * Equiv.swap i j) q)) = F (fun q => a (σ q)) :=
      hF (fun q => a (σ q))
    rw [he, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij, mul_smul]
    simp [Units.smul_def]
  · intro σ hσ hn he
    exact hij (Equiv.mul_swap_eq_iff.mp he)

/-- A permutation splits into its first value and a permutation of the remaining slots. -/
theorem alternatingEvaluation_eq_zero_of_curryLeft {n : ℕ} (F : Cochain k A (n + 1))
    (hF : ∀ b x, alternatingEvaluation (F.curryLeft b) x = 0) (a : Fin (n + 1) → A) :
    alternatingEvaluation F a = 0 := by
  rw [alternatingEvaluation_apply, Finset.univ_perm_fin_succ, Finset.sum_map]
  change (∑ pe : Fin (n + 1) × Equiv.Perm (Fin n),
    Equiv.Perm.sign (Equiv.Perm.decomposeFin.symm pe) •
      F (fun i => a (Equiv.Perm.decomposeFin.symm pe i))) = 0
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro p hp
  calc
    _ = (if p = 0 then (1 : ℤˣ) else -1) •
        alternatingEvaluation (F.curryLeft (a p))
          (fun j => a (Equiv.swap 0 p j.succ)) := by
      rw [alternatingEvaluation_apply, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro τ hτ
      rw [Equiv.Perm.decomposeFin.symm_sign, mul_smul]
      congr 2
      rw [MultilinearMap.curryLeft_apply]
      congr 1
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    _ = 0 := by rw [hF, smul_zero]

private def barTail {n : ℕ} (F : Cochain k A (n + 1)) : Cochain k A (n + 1 + 1) :=
  ((barDifferential (LinearMap.mul k A) n).comp F.curryLeft).uncurryLeft

/-- Antisymmetric evaluation kills every full Hochschild boundary over a commutative algebra. -/
theorem alternatingEvaluation_barDifferential (n : ℕ) (F : Cochain k A n)
    (a : Fin (n + 1) → A) :
    alternatingEvaluation (barDifferential (LinearMap.mul k A) n F) a = 0 := by
  induction n with
  | zero =>
    have h0 := barDifferential_derivationProduct (k := k) 0 (cochainZeroEquiv k A F)
      (fun i : Fin 0 => Fin.elim0 i)
    rw [derivationProduct_zero, LinearEquiv.symm_apply_apply] at h0
    simp [h0, alternatingEvaluation]
  | succ n ih =>
    let H := barDifferential (LinearMap.mul k A) (n + 1) F + barTail F
    have htail : alternatingEvaluation (barTail F) a = 0 := by
      apply alternatingEvaluation_eq_zero_of_curryLeft
      intro b x
      change alternatingEvaluation
        (barDifferential (LinearMap.mul k A) n (F.curryLeft b)) x = 0
      exact ih _ _
    have heval (b c : A) (x : Fin n → A) :
        H (Fin.cons b (Fin.cons c x)) = b * F (Fin.cons c x) -
          F (Fin.cons (b * c) x) + c * F (Fin.cons b x) := by
      change barDifferential (LinearMap.mul k A) (n + 1) F (Fin.cons b (Fin.cons c x)) +
        barDifferential (LinearMap.mul k A) n (F.curryLeft b) (Fin.cons c x) = _
      rw [barDifferential_cons_cons]
      simp only [LinearMap.mul_apply']
      abel
    have hH : alternatingEvaluation H a = 0 := by
      apply alternatingEvaluation_eq_zero_of_swap H 0 1 (by simp)
      intro x
      have hswap : (fun i => x (Equiv.swap (0 : Fin (n + 1 + 1)) 1 i)) =
          Fin.cons (Fin.tail x 0) (Fin.cons (x 0) (Fin.tail (Fin.tail x))) := by
        funext i
        refine Fin.cases (by simp [Fin.tail]) (fun j => ?_) i
        refine Fin.cases (by simp [Fin.tail]) (fun l => ?_) j
        have h0 : l.succ.succ ≠ (0 : Fin (n + 1 + 1)) := by simp
        have h1 : l.succ.succ ≠ (1 : Fin (n + 1 + 1)) := by
          intro he
          have hv := congrArg Fin.val he
          simp only [Fin.val_succ, Fin.val_one] at hv
          omega
        simp [Equiv.swap_apply_of_ne_of_ne h0 h1, Fin.tail]
      rw [hswap, heval]
      conv_rhs => rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail (Fin.tail x), heval]
      rw [mul_comm (Fin.tail x 0) (x 0)]
      abel
    have hadd : alternatingEvaluation H a =
        alternatingEvaluation (barDifferential (LinearMap.mul k A) (n + 1) F) a +
          alternatingEvaluation (barTail F) a := by
      simp [H, alternatingEvaluation, map_add]
    rw [hadd, htail, add_zero] at hH
    exact hH

/-- Bundled form: antisymmetric evaluation vanishes on the image of the bar differential. -/
theorem alternatingEvaluationLinearMap_comp_barDifferential (n : ℕ) (a : Fin (n + 1) → A) :
    (alternatingEvaluationLinearMap a).comp (barDifferential (LinearMap.mul k A) n) = 0 := by
  ext F
  exact alternatingEvaluation_barDifferential n F a

section Normalized

variable {K : Type*} [Field K] [Algebra K A]

/-- The normalized alternating HKR map associated to a coefficient and derivations. -/
def hkrAlternating {n : ℕ} (f : A) (D : Fin n → Derivation K A A) :
    A [⋀^Fin n]→ₗ[K] A :=
  (n.factorial : K)⁻¹ • MultilinearMap.alternatization (derivationProduct f D)

/-- HKR viewed as an element of the full Hochschild cochain space. -/
def hkrCochain {n : ℕ} (f : A) (D : Fin n → Derivation K A A) : Cochain K A n :=
  (hkrAlternating f D).toMultilinearMap

/-- Factorial normalization does not affect the cocycle identity. -/
theorem barDifferential_hkrCochain (n : ℕ) (f : A) (D : Fin n → Derivation K A A) :
    barDifferential (LinearMap.mul K A) n (hkrCochain f D) = 0 := by
  change barDifferential (LinearMap.mul K A) n
    ((n.factorial : K)⁻¹ •
      (MultilinearMap.alternatization (derivationProduct f D)).toMultilinearMap) = 0
  rw [map_smul, barDifferential_alternatization_derivationProduct, smul_zero]

/-- Evaluating HKR itself retains the factor `1/n!`. -/
theorem hkrCochain_apply {n : ℕ} (f : A) (D : Fin n → Derivation K A A) (a : Fin n → A) :
    hkrCochain f D a =
      (n.factorial : K)⁻¹ • (f * Matrix.det (fun i j => D j (a i))) := by
  change (n.factorial : K)⁻¹ • alternatingEvaluation (derivationProduct f D) a = _
  rw [alternatingEvaluation_derivationProduct]

/-- HKR is linear in its polynomial or algebra coefficient. -/
def hkrCochainLinearMap {n : ℕ} (D : Fin n → Derivation K A A) : A →ₗ[K] Cochain K A n where
  toFun f := hkrCochain f D
  map_add' f g := by ext a; simp [hkrCochain_apply, add_mul, smul_add]
  map_smul' c f := by
    ext a
    simp only [hkrCochain_apply, smul_apply, RingHom.id_apply, smul_mul_assoc]
    exact smul_comm _ _ _

@[simp] theorem hkrCochainLinearMap_apply {n : ℕ} (D : Fin n → Derivation K A A) (f : A) :
    hkrCochainLinearMap D f = hkrCochain f D := rfl

/-- Antisymmetric evaluation cancels the HKR normalization exactly once. -/
theorem alternatingEvaluation_hkrCochain [CharZero K] {n : ℕ} (f : A)
    (D : Fin n → Derivation K A A) (a : Fin n → A) :
    alternatingEvaluation (hkrCochain f D) a =
      f * Matrix.det (fun i j => D j (a i)) := by
  change MultilinearMap.alternatization (hkrAlternating f D).toMultilinearMap a = _
  rw [AlternatingMap.coe_alternatization]
  change (Fintype.card (Fin n)).factorial •
    ((n.factorial : K)⁻¹ • alternatingEvaluation (derivationProduct f D) a) = _
  rw [Fintype.card_fin, ← Nat.cast_smul_eq_nsmul K, smul_smul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_smul,
    alternatingEvaluation_derivationProduct]

/-- At arity zero HKR is exactly the coefficient, with `0! = 1`. -/
theorem hkrCochain_zero (f : A) (D : Fin 0 → Derivation K A A) :
    hkrCochain f D = (cochainZeroEquiv K A).symm f := by
  ext a
  simp [hkrCochain_apply, Matrix.det_isEmpty]

end Normalized

section Polynomial

open MvPolynomial

variable {K : Type*} [Field K] {d n : ℕ}

/-- HKR on an ordered tuple of coordinate partial derivatives. -/
def coordinateHKR (f : MvPolynomial (Fin d) K) (u : Fin n → Fin d) :
    Cochain K (MvPolynomial (Fin d) K) n :=
  hkrCochain f (fun i => pderiv (u i))

/-- Coordinate HKR bundled as a linear map on polynomial coefficients. -/
def coordinateHKRLinearMap (u : Fin n → Fin d) :
    MvPolynomial (Fin d) K →ₗ[K] Cochain K (MvPolynomial (Fin d) K) n :=
  hkrCochainLinearMap (fun i => pderiv (u i))

@[simp] theorem coordinateHKRLinearMap_apply (u : Fin n → Fin d) (f : MvPolynomial (Fin d) K) :
    coordinateHKRLinearMap u f = coordinateHKR f u := rfl

/-- A single coordinate evaluation has the factorial denominator. -/
theorem coordinateHKR_apply (f : MvPolynomial (Fin d) K) (u v : Fin n → Fin d) :
    coordinateHKR f u (fun i => X (v i)) =
      (n.factorial : K)⁻¹ •
        (f * Matrix.det (fun i j => if v i = u j then (1 : MvPolynomial (Fin d) K) else 0)) := by
  simpa [coordinateHKR, MvPolynomial.pderiv_X, Pi.single_apply, eq_comm] using
    hkrCochain_apply f (fun i => pderiv (u i)) (fun i => X (v i))

/-- Koszul-to-bar antisymmetric coordinate evaluation gives the full Kronecker determinant. -/
theorem alternatingEvaluation_coordinateHKR [CharZero K]
    (f : MvPolynomial (Fin d) K) (u v : Fin n → Fin d) :
    alternatingEvaluation (coordinateHKR f u) (fun i => X (v i)) =
      f * Matrix.det (fun i j => if v i = u j then (1 : MvPolynomial (Fin d) K) else 0) := by
  simpa [coordinateHKR, MvPolynomial.pderiv_X, Pi.single_apply, eq_comm] using
    alternatingEvaluation_hkrCochain f (fun i => pderiv (u i)) (fun i => X (v i))

/-- An injective coordinate tuple evaluates its own normalized HKR cochain to `f/n!`. -/
theorem coordinateHKR_apply_self (f : MvPolynomial (Fin d) K) (u : Fin n → Fin d)
    (hu : Function.Injective u) :
    coordinateHKR f u (fun i => X (u i)) = (n.factorial : K)⁻¹ • f := by
  rw [coordinateHKR_apply]
  have hmat : (fun i j : Fin n => if u i = u j then (1 : MvPolynomial (Fin d) K) else 0) =
      (1 : Matrix (Fin n) (Fin n) (MvPolynomial (Fin d) K)) := by
    ext i j
    simp [hu.eq_iff, Matrix.one_apply]
  rw [hmat, Matrix.det_one, mul_one]

/-- The full antisymmetrized evaluation is the identity on an injective coordinate tuple. -/
theorem alternatingEvaluation_coordinateHKR_self [CharZero K]
    (f : MvPolynomial (Fin d) K) (u : Fin n → Fin d) (hu : Function.Injective u) :
    alternatingEvaluation (coordinateHKR f u) (fun i => X (u i)) = f := by
  rw [alternatingEvaluation_coordinateHKR]
  have hmat : (fun i j : Fin n => if u i = u j then (1 : MvPolynomial (Fin d) K) else 0) =
      (1 : Matrix (Fin n) (Fin n) (MvPolynomial (Fin d) K)) := by
    ext i j
    simp [hu.eq_iff, Matrix.one_apply]
  rw [hmat, Matrix.det_one, mul_one]

/-- The normalized coordinate HKR and unnormalized alternating evaluation form a retraction. -/
theorem alternatingEvaluationLinearMap_comp_coordinateHKRLinearMap [CharZero K]
    (u : Fin n → Fin d) (hu : Function.Injective u) :
    (alternatingEvaluationLinearMap (fun i => (X (u i) : MvPolynomial (Fin d) K))).comp
      (coordinateHKRLinearMap u) = LinearMap.id := by
  apply LinearMap.ext
  intro f
  exact alternatingEvaluation_coordinateHKR_self f u hu

/-- Distinct sorted exterior-coordinate subsets have zero HKR pairing. -/
theorem alternatingEvaluation_coordinateHKR_powersetCard_ne [CharZero K]
    (f : MvPolynomial (Fin d) K) (s t : Set.powersetCard (Fin d) n) (hst : s ≠ t) :
    alternatingEvaluation
      (coordinateHKR f (Set.powersetCard.ofFinEmbEquiv.symm s))
      (fun i => X (Set.powersetCard.ofFinEmbEquiv.symm t i)) = 0 := by
  classical
  have hns : ¬ t.val ⊆ s.val := by
    intro hsub
    apply hst
    apply Subtype.ext
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [s.prop, t.prop])).symm
  obtain ⟨x, hxt, hxs⟩ := Finset.not_subset.mp hns
  have hxrange : x ∈ Set.range (Set.powersetCard.ofFinEmbEquiv.symm t) :=
    (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t x).mpr hxt
  obtain ⟨i, hi⟩ := hxrange
  have hne (j : Fin n) : Set.powersetCard.ofFinEmbEquiv.symm t i ≠
      Set.powersetCard.ofFinEmbEquiv.symm s j := by
    intro he
    apply hxs
    apply (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s x).mp
    exact ⟨j, he.symm.trans hi⟩
  rw [alternatingEvaluation_coordinateHKR,
    Matrix.det_eq_zero_of_row_eq_zero i (fun j => if_neg (hne j)), mul_zero]

/-- Coordinate HKR lies in the kernel of the existing full Hochschild differential. -/
theorem barDifferential_coordinateHKR (f : MvPolynomial (Fin d) K) (u : Fin n → Fin d) :
    barDifferential (LinearMap.mul K (MvPolynomial (Fin d) K)) n (coordinateHKR f u) = 0 :=
  barDifferential_hkrCochain n f (fun i => pderiv (u i))

end Polynomial

end EnvelopingIsomorphism.Deformation
