import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! Weighted leading terms of finite polynomial differences. -/

noncomputable section

namespace EnvelopingIsomorphism.Identification.PolynomialDifference

open MvPolynomial
open scoped BigOperators

variable {R α : Type*} [CommRing R] [Fintype α] [DecidableEq α]

/-- Literal translation of polynomial coordinates. -/
def translation (η : α → R) : MvPolynomial α R →ₐ[R] MvPolynomial α R :=
  MvPolynomial.aeval (fun i ↦ X i + C (η i))

omit [Fintype α] [DecidableEq α] in
@[simp] theorem translation_X (η : α → R) (i : α) :
    translation η (X i) = X i + C (η i) := MvPolynomial.aeval_X _ _

omit [Fintype α] [DecidableEq α] in
@[simp] theorem translation_C (η : α → R) (r : R) :
    translation η (C r) = C r := (translation η).commutes r

/-- The constant vector field giving the first-order translation term. -/
def directionalDerivative (η : α → R) : Derivation R (MvPolynomial α R) (MvPolynomial α R) :=
  ∑ i, η i • pderiv i

omit [DecidableEq α] in
theorem directionalDerivative_apply (η : α → R) (p : MvPolynomial α R) :
    directionalDerivative η p = ∑ i, η i • pderiv i p := by
  change Derivation.coeFnAddMonoidHom (∑ i, η i • pderiv i) p = _
  rw [map_sum]
  simp only [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply]

@[simp] theorem directionalDerivative_X (η : α → R) (j : α) :
    directionalDerivative η (X j) = C (η j) := by
  rw [directionalDerivative_apply]
  simp [pderiv_X, Pi.single_apply, ← C_mul']

/-- Finite difference as a linear map. -/
def difference (η : α → R) : Module.End R (MvPolynomial α R) :=
  (translation η).toLinearMap - LinearMap.id

/-- The remainder after removing the directional derivative. -/
def remainder (η : α → R) : Module.End R (MvPolynomial α R) :=
  difference η - (directionalDerivative η).toLinearMap

omit [Fintype α] [DecidableEq α] in
@[simp] theorem difference_apply (η : α → R) (p : MvPolynomial α R) :
    difference η p = translation η p - p := rfl

omit [DecidableEq α] in
@[simp] theorem remainder_apply (η : α → R) (p : MvPolynomial α R) :
    remainder η p = difference η p - directionalDerivative η p := rfl

omit [Fintype α] [DecidableEq α] in
theorem translation_mul_X (η : α → R) (p : MvPolynomial α R) (i : α) :
    translation η (p * X i) = translation η p * X i + η i • translation η p := by
  rw [map_mul, translation_X, mul_add]
  rw [mul_comm _ (C _), C_mul']

omit [Fintype α] [DecidableEq α] in
theorem difference_mul_X (η : α → R) (p : MvPolynomial α R) (i : α) :
    difference η (p * X i) = difference η p * X i + η i • translation η p := by
  simp only [difference_apply, translation_mul_X]
  ring

theorem remainder_mul_X (η : α → R) (p : MvPolynomial α R) (i : α) :
    remainder η (p * X i) = remainder η p * X i + η i • difference η p := by
  simp only [remainder_apply, difference_apply, translation_mul_X, Derivation.leibniz,
    directionalDerivative_X, smul_eq_mul, ← C_mul']
  ring

/-- A support bound with an explicit degree drop. It is a submodule of the
native polynomial algebra, including when weights vanish. -/
def bounded (ω : α → ℕ) (drop degree : ℕ) : Submodule R (MvPolynomial α R) :=
  (Finsupp.supported R R {a | Finsupp.weight ω a + drop ≤ degree}).comap
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

omit [Fintype α] [DecidableEq α] in
theorem mem_bounded (ω : α → ℕ) (drop degree : ℕ) (p : MvPolynomial α R) :
    p ∈ bounded ω drop degree ↔
      ∀ a ∈ p.support, Finsupp.weight ω a + drop ≤ degree := Iff.rfl

omit [Fintype α] [DecidableEq α] in
theorem bounded_mono (ω : α → ℕ) (drop : ℕ) {d e : ℕ} (h : d ≤ e) :
    bounded (R := R) ω drop d ≤ bounded ω drop e :=
  fun _ hp _ ha ↦ (hp ha).trans h

omit [Fintype α] [DecidableEq α] in
theorem bounded_mul_X (ω : α → ℕ) {p : MvPolynomial α R} {drop d : ℕ}
    (hp : p ∈ bounded ω drop d) (i : α) :
    p * X i ∈ bounded ω drop (d + ω i) := by
  rw [mem_bounded] at hp ⊢
  intro a ha
  rw [support_mul_X] at ha
  obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp ha
  have h := hp v hv
  simp only [addRightEmbedding_apply, map_add, Finsupp.weight_single, one_smul]
  omega

omit [Fintype α] [DecidableEq α] in
theorem bounded_smul_shift (ω : α → ℕ) (η : α → R)
    (hω : ∀ i, ω i = 0 ∨ ω i = 1) (hη : ∀ i, ω i = 0 → η i = 0)
    {p : MvPolynomial α R} {drop d : ℕ} (hp : p ∈ bounded ω drop d) (i : α) :
    η i • p ∈ bounded ω (drop + 1) (d + ω i) := by
  rcases hω i with hi | hi
  · rw [hη i hi, zero_smul]
    exact zero_mem _
  · have h := (bounded ω drop d).smul_mem (η i) hp
    rw [mem_bounded] at h ⊢
    intro a ha
    have ha' := h a ha
    rw [hi]
    omega

/-- Simultaneous bounds for translation, first difference and second-order remainder. -/
structure Bounds (ω : α → ℕ) (η : α → R) (p : MvPolynomial α R) (degree : ℕ) : Prop where
  translated : translation η p ∈ bounded ω 0 degree
  difference : difference η p ∈ bounded ω 1 degree
  remainder : remainder η p ∈ bounded ω 2 degree

omit [DecidableEq α] in
theorem bounds_C (ω : α → ℕ) (η : α → R) (r : R) : Bounds ω η (C r) 0 := by
  constructor
  · rw [translation_C]
    rw [mem_bounded]
    intro a ha
    have ha' : a = 0 := Finset.mem_singleton.mp (support_monomial_subset ha)
    simp [ha']
  · simp only [difference_apply, translation_C, sub_self]
    exact zero_mem _
  · simp only [remainder_apply, difference_apply, translation_C, sub_self,
      show directionalDerivative η (C r) = 0 from (directionalDerivative η).map_algebraMap r]
    exact zero_mem _

theorem Bounds.mul_X {ω : α → ℕ} {η : α → R}
    (hω : ∀ i, ω i = 0 ∨ ω i = 1) (hη : ∀ i, ω i = 0 → η i = 0)
    {p : MvPolynomial α R} {d : ℕ} (hp : Bounds ω η p d) (i : α) :
    Bounds ω η (p * X i) (d + ω i) := by
  constructor
  · rw [translation_mul_X]
    apply add_mem (bounded_mul_X ω hp.translated i)
    apply (bounded ω 0 (d + ω i)).smul_mem
    exact bounded_mono ω 0 (Nat.le_add_right d (ω i)) hp.translated
  · rw [difference_mul_X]
    exact add_mem (bounded_mul_X ω hp.difference i)
      (bounded_smul_shift ω η hω hη hp.translated i)
  · rw [remainder_mul_X]
    exact add_mem (bounded_mul_X ω hp.remainder i)
      (bounded_smul_shift ω η hω hη hp.difference i)

theorem monomial_bounds (ω : α → ℕ) (η : α → R)
    (hω : ∀ i, ω i = 0 ∨ ω i = 1) (hη : ∀ i, ω i = 0 → η i = 0)
    (a : α →₀ ℕ) (r : R) : Bounds ω η (monomial a r) (Finsupp.weight ω a) := by
  induction a using Finsupp.induction with
  | zero => simpa using bounds_C ω η r
  | single_add i n a hi hn ih =>
      have hp (n : ℕ) : Bounds ω η (monomial a r * X i ^ n)
          (Finsupp.weight ω a + n * ω i) := by
        induction n with
        | zero => simpa using ih
        | succ n ihn =>
            have h := ihn.mul_X hω hη i
            simpa only [pow_succ, ← mul_assoc, Nat.succ_mul, Nat.add_assoc] using h
      rw [add_comm (Finsupp.single i n) a, monomial_add_single, map_add,
        Finsupp.weight_single, nsmul_eq_mul]
      exact hp n

omit [Fintype α] [DecidableEq α] in
theorem linear_mem_bounded (ω : α → ℕ) (drop : ℕ)
    (F : Module.End R (MvPolynomial α R))
    (hF : ∀ a r, F (monomial a r) ∈ bounded ω drop (Finsupp.weight ω a))
    {p : MvPolynomial α R} {m : ℕ}
    (hp : ∀ a ∈ p.support, Finsupp.weight ω a ≤ m) : F p ∈ bounded ω drop m := by
  rw [p.as_sum, map_sum]
  apply Submodule.sum_mem
  intro a ha
  exact bounded_mono ω drop (hp a ha) (hF a (coeff a p))

/-- The support bound on the input is essential: it controls all three
translation estimates, including the second-order remainder. -/
theorem bounds_of_support_le (ω : α → ℕ) (η : α → R)
    (hω : ∀ i, ω i = 0 ∨ ω i = 1) (hη : ∀ i, ω i = 0 → η i = 0)
    {p : MvPolynomial α R} {m : ℕ}
    (hp : ∀ a ∈ p.support, Finsupp.weight ω a ≤ m) : Bounds ω η p m := by
  constructor
  · exact linear_mem_bounded ω 0 (translation η).toLinearMap
      (fun a r ↦ (monomial_bounds ω η hω hη a r).translated) hp
  · exact linear_mem_bounded ω 1 (difference η)
      (fun a r ↦ (monomial_bounds ω η hω hη a r).difference) hp
  · exact linear_mem_bounded ω 2 (remainder η)
      (fun a r ↦ (monomial_bounds ω η hω hη a r).remainder) hp

/-- Finite differences lower complementary weight by at least one. -/
theorem difference_support_lt (ω : α → ℕ) (η : α → R)
    (hω : ∀ i, ω i = 0 ∨ ω i = 1) (hη : ∀ i, ω i = 0 → η i = 0)
    {p : MvPolynomial α R} {m : ℕ}
    (hp : ∀ a ∈ p.support, Finsupp.weight ω a ≤ m)
    {a : α →₀ ℕ} (ha : a ∈ (translation η p - p).support) :
    Finsupp.weight ω a < m := by
  have h := (mem_bounded ω 1 m _).mp (bounds_of_support_le ω η hω hη hp).difference a ha
  omega

/-- After subtracting the directional derivative, two weights are lost. -/
theorem remainder_support (ω : α → ℕ) (η : α → R)
    (hω : ∀ i, ω i = 0 ∨ ω i = 1) (hη : ∀ i, ω i = 0 → η i = 0)
    {p : MvPolynomial α R} {m : ℕ}
    (hp : ∀ a ∈ p.support, Finsupp.weight ω a ≤ m)
    {a : α →₀ ℕ} (ha : a ∈ (translation η p - p - directionalDerivative η p).support) :
    Finsupp.weight ω a + 2 ≤ m :=
  (mem_bounded ω 2 m _).mp (bounds_of_support_le ω η hω hη hp).remainder a ha

omit [DecidableEq α] in
/-- A constant vector field in weight-one coordinates shifts homogeneous
components down by one. -/
theorem directionalDerivative_component (ω : α → ℕ) (η : α → R)
    (hω : ∀ i, ω i = 0 ∨ ω i = 1) (hη : ∀ i, ω i = 0 → η i = 0)
    {m : ℕ} (hm : 0 < m) (p : MvPolynomial α R) :
    weightedHomogeneousComponent ω (m - 1) (directionalDerivative η p) =
      directionalDerivative η (weightedHomogeneousComponent ω m p) := by
  rw [directionalDerivative_apply, map_sum, directionalDerivative_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  rcases hω i with hi | hi
  · simp only [hη i hi, zero_smul]
  · ext a
    simp only [coeff_smul, coeff_weightedHomogeneousComponent, coeff_pderiv,
      map_add, Finsupp.weight_single, one_smul, hi]
    have hiff : Finsupp.weight ω a = m - 1 ↔ Finsupp.weight ω a + 1 = m := by omega
    simp only [hiff, ite_mul, zero_mul]

/-- Exact leading finite-difference formula. The input support bound rules
out contamination of degree `m - 1` by higher input degrees. -/
theorem component_translation_sub (ω : α → ℕ) (η : α → R)
    (hω : ∀ i, ω i = 0 ∨ ω i = 1) (hη : ∀ i, ω i = 0 → η i = 0)
    {p : MvPolynomial α R} {m : ℕ} (hm : 0 < m)
    (hp : ∀ a ∈ p.support, Finsupp.weight ω a ≤ m) :
    weightedHomogeneousComponent ω (m - 1)
        ((MvPolynomial.aeval (fun i ↦ X i + C (η i))) p - p) =
      ∑ i, η i • pderiv i (weightedHomogeneousComponent ω m p) := by
  have hr : weightedHomogeneousComponent ω (m - 1) (remainder η p) = 0 := by
    apply weightedHomogeneousComponent_eq_zero'
    intro a ha heq
    have h := (mem_bounded ω 2 m _).mp (bounds_of_support_le ω η hω hη hp).remainder a ha
    omega
  change weightedHomogeneousComponent ω (m - 1)
    (difference η p - directionalDerivative η p) = 0 at hr
  rw [map_sub, sub_eq_zero] at hr
  change weightedHomogeneousComponent ω (m - 1) (difference η p) = _
  rw [hr, directionalDerivative_component ω η hω hη hm, directionalDerivative_apply]

end EnvelopingIsomorphism.Identification.PolynomialDifference
