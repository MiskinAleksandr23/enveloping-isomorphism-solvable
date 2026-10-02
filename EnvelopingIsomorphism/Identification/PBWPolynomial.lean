import EnvelopingIsomorphism.Identification.LeadingProduct
import EnvelopingIsomorphism.PBW.Leading
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Actual PBW coordinates as a filtered product on the standard polynomial ring. -/

noncomputable section
namespace EnvelopingIsomorphism.Identification

variable {R L α : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LinearOrder α] (b : Module.Basis α R L)

open UniversalEnvelopingAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing

/-- Ordered PBW coordinates identify the underlying module with a polynomial ring. -/
def pbwPolynomialEquiv : UniversalEnvelopingAlgebra R L ≃ₗ[R] MvPolynomial α R :=
  (EnvelopingIsomorphism.PBW.pbwBasis b).repr.trans (MvPolynomial.basisMonomials α R).repr.symm

@[simp] theorem coeff_pbwPolynomialEquiv (x : UniversalEnvelopingAlgebra R L) (m : α →₀ ℕ) :
    MvPolynomial.coeff m (pbwPolynomialEquiv b x) =
      (EnvelopingIsomorphism.PBW.pbwBasis b).repr x m := rfl

@[simp] theorem pbwPolynomialEquiv_basis (m : α →₀ ℕ) :
    pbwPolynomialEquiv b (EnvelopingIsomorphism.PBW.pbwBasis b m) = MvPolynomial.monomial m 1 := by
  apply (MvPolynomial.basisMonomials α R).repr.injective
  change (MvPolynomial.basisMonomials α R).repr
      ((MvPolynomial.basisMonomials α R).repr.symm
        ((EnvelopingIsomorphism.PBW.pbwBasis b).repr (EnvelopingIsomorphism.PBW.pbwBasis b m))) = _
  rw [LinearEquiv.apply_symm_apply]
  change (EnvelopingIsomorphism.PBW.pbwBasis b).repr (EnvelopingIsomorphism.PBW.pbwBasis b m) =
    (MvPolynomial.basisMonomials α R).repr ((MvPolynomial.basisMonomials α R) m)
  rw [Module.Basis.repr_self, Module.Basis.repr_self]

@[simp] theorem pbwPolynomialEquiv_symm_monomial (m : α →₀ ℕ) :
    (pbwPolynomialEquiv b).symm (MvPolynomial.monomial m 1) =
      EnvelopingIsomorphism.PBW.pbwBasis b m := by
  apply (pbwPolynomialEquiv b).injective
  rw [LinearEquiv.apply_symm_apply, pbwPolynomialEquiv_basis]

/-- The actual native enveloping multiplication transported to polynomial coordinates. -/
def pbwStar : MvPolynomial α R →ₗ[R] MvPolynomial α R →ₗ[R] MvPolynomial α R where
  toFun p :=
    { toFun q := pbwPolynomialEquiv b
        ((pbwPolynomialEquiv b).symm p * (pbwPolynomialEquiv b).symm q)
      map_add' q r := by simp [mul_add]
      map_smul' r q := by simp [Algebra.mul_smul_comm] }
  map_add' p q := by ext r; simp [add_mul]
  map_smul' r p := by ext q; simp

@[simp] theorem pbwStar_apply (p q : MvPolynomial α R) :
    pbwStar b p q = pbwPolynomialEquiv b
      ((pbwPolynomialEquiv b).symm p * (pbwPolynomialEquiv b).symm q) := rfl

/-- The error between transported PBW multiplication and ordinary polynomial multiplication. -/
def pbwStarError : MvPolynomial α R →ₗ[R] MvPolynomial α R →ₗ[R] MvPolynomial α R where
  toFun p :=
    { toFun q := pbwStar b p q - p * q
      map_add' q r := by simp [mul_add]; abel
      map_smul' r q := by simp [Algebra.mul_smul_comm, smul_sub] }
  map_add' p q := by
    apply LinearMap.ext
    intro r
    change pbwStar b (p + q) r - (p + q) * r =
      (pbwStar b p r - p * r) + (pbwStar b q r - q * r)
    rw [map_add, LinearMap.add_apply, add_mul]
    abel
  map_smul' r p := by ext q; simp [smul_sub]

@[simp] theorem pbwStarError_apply (p q : MvPolynomial α R) :
    pbwStarError b p q = pbwStar b p q - p * q := rfl

omit [LinearOrder α] in
theorem polynomial_basis_mul_homogeneous (ω : α → ℕ) (m n : α →₀ ℕ) :
    (MvPolynomial.basisMonomials α R) m * (MvPolynomial.basisMonomials α R) n ∈
      basisHomogeneous (MvPolynomial.basisMonomials α R) (Finsupp.weight ω)
        (Finsupp.weight ω m + Finsupp.weight ω n) := by
  have hm : MvPolynomial.monomial m (1 : R) * MvPolynomial.monomial n 1 =
      MvPolynomial.monomial (m + n) 1 := by simp [MvPolynomial.monomial_mul]
  rw [MvPolynomial.coe_basisMonomials, hm]
  exact basis_mem_basisSupport (MvPolynomial.basisMonomials α R) (map_add _ _ _)

theorem pbwStarError_basis_mem_strict (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω a < ω i + ω j)
    (m n : α →₀ ℕ) :
    pbwStarError b ((MvPolynomial.basisMonomials α R) m)
      ((MvPolynomial.basisMonomials α R) n) ∈
      basisStrict (MvPolynomial.basisMonomials α R) (Finsupp.weight ω)
        (Finsupp.weight ω m + Finsupp.weight ω n) := by
  classical
  let w := EnvelopingIsomorphism.PBW.orderedWord m ++ EnvelopingIsomorphism.PBW.orderedWord n
  have hw : EnvelopingIsomorphism.PBW.pbwBasis b m * EnvelopingIsomorphism.PBW.pbwBasis b n =
      EnvelopingIsomorphism.PBW.wordEval b (Finsupp.single w 1) := by
    simp only [EnvelopingIsomorphism.PBW.wordEval_single_one, w, List.map_append, List.prod_append,
      EnvelopingIsomorphism.PBW.pbwBasis_apply]
  have hidx : EnvelopingIsomorphism.PBW.wordIndex w = m + n := by
    simp [w]
  apply (mem_basisSupport (MvPolynomial.basisMonomials α R) _ _).mpr
  intro t ht
  have hcoeff := Finsupp.mem_support_iff.mp ht
  change MvPolynomial.coeff t
    (pbwStarError b (MvPolynomial.monomial m 1) (MvPolynomial.monomial n 1)) ≠ 0 at hcoeff
  simp only [pbwStarError_apply, pbwStar_apply, pbwPolynomialEquiv_symm_monomial, hw,
    MvPolynomial.monomial_mul, mul_one, MvPolynomial.coeff_sub, coeff_pbwPolynomialEquiv,
    MvPolynomial.coeff_monomial] at hcoeff
  have ht' : t ∈ ((EnvelopingIsomorphism.PBW.pbwBasis b).repr
      (EnvelopingIsomorphism.PBW.wordEval b (Finsupp.single w 1)) -
      Finsupp.single (EnvelopingIsomorphism.PBW.wordIndex w) 1).support := by
    apply Finsupp.mem_support_iff.mpr
    simpa only [Finsupp.sub_apply, Finsupp.single_apply, hidx] using hcoeff
  have h := EnvelopingIsomorphism.PBW.pbwBasis_repr_wordEval_sub_single_weight_lt b ω hc w ht'
  change Finsupp.weight ω t < Finsupp.weight ω m + Finsupp.weight ω n
  simpa only [EnvelopingIsomorphism.PBW.wordWeight, hidx, map_add] using h

/-- PBW multiplication agrees with the commutative product modulo strictly
lower weight, for all filtered inputs and not only individual monomials. -/
theorem pbwStar_sub_mul_mem_strict (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω a < ω i + ω j)
    (d e : ℕ) (p : MvPolynomial α R)
    (hp : p ∈ basisUpper (MvPolynomial.basisMonomials α R) (Finsupp.weight ω) d)
    (q : MvPolynomial α R)
    (hq : q ∈ basisUpper (MvPolynomial.basisMonomials α R) (Finsupp.weight ω) e) :
    pbwStar b p q - p * q ∈
      basisStrict (MvPolynomial.basisMonomials α R) (Finsupp.weight ω) (d + e) := by
  apply bilinear_mem_basisSupport (MvPolynomial.basisMonomials α R) (pbwStarError b) _ hp hq
  intro m hm n hn
  apply basisSupport_mono (MvPolynomial.basisMonomials α R) _
    (pbwStarError_basis_mem_strict b ω hc m n)
  intro t ht
  change Finsupp.weight ω t < d + e
  exact lt_of_lt_of_le ht (Nat.add_le_add hm hn)

/-- An inner derivation, transported through actual PBW coordinates. -/
def pbwInner (a : UniversalEnvelopingAlgebra R L) : Module.End R (MvPolynomial α R) :=
  (pbwPolynomialEquiv b).toLinearMap.comp
    ((LieAlgebra.ad R _ a).comp (pbwPolynomialEquiv b).symm.toLinearMap)

@[simp] theorem pbwInner_apply (a : UniversalEnvelopingAlgebra R L) (p : MvPolynomial α R) :
    pbwInner b a p = pbwPolynomialEquiv b ⁅a, (pbwPolynomialEquiv b).symm p⁆ := rfl

theorem pbwInner_leibniz (a : UniversalEnvelopingAlgebra R L) (p q : MvPolynomial α R) :
    pbwInner b a (pbwStar b p q) =
      pbwStar b (pbwInner b a p) q + pbwStar b p (pbwInner b a q) := by
  simp only [pbwInner_apply, pbwStar_apply, LinearEquiv.symm_apply_apply, ← map_add]
  congr 1
  simp only [Ring.lie_def, mul_sub, sub_mul, mul_assoc]
  abel

theorem pbwInner_isLocallyFinite {a : UniversalEnvelopingAlgebra R L}
    (ha : a ∈ LF R (UniversalEnvelopingAlgebra R L)) : IsLocallyFinite (pbwInner b a) := by
  apply locallyFinite_of_surjective_intertwiner _ _ (pbwPolynomialEquiv b).toLinearMap _
    (pbwPolynomialEquiv b).surjective ha
  intro x
  simp [pbwInner_apply]

theorem pbwPolynomialEquiv_mem_upper_iff (ω : α → ℕ) (d : ℕ)
    (x : UniversalEnvelopingAlgebra R L) :
    pbwPolynomialEquiv b x ∈ basisUpper (MvPolynomial.basisMonomials α R) (Finsupp.weight ω) d ↔
      x ∈ EnvelopingIsomorphism.PBW.weightedUpper b ω d := by
  rw [basisUpper, mem_basisSupport, EnvelopingIsomorphism.PBW.mem_weightedUpper_iff]
  rfl

theorem pbwInner_mem_strict (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω a < ω i + ω j)
    {a : UniversalEnvelopingAlgebra R L} {m d : ℕ}
    (ha : a ∈ EnvelopingIsomorphism.PBW.weightedUpper b ω m)
    {p : MvPolynomial α R}
    (hp : p ∈ basisUpper (MvPolynomial.basisMonomials α R) (Finsupp.weight ω) d) :
    pbwInner b a p ∈ basisStrict (MvPolynomial.basisMonomials α R)
      (Finsupp.weight ω) (m + d) := by
  have ha' := (pbwPolynomialEquiv_mem_upper_iff b ω m a).mpr ha
  have h₁ := pbwStar_sub_mul_mem_strict b ω hc m d _ ha' p hp
  have h₂ : pbwStar b p (pbwPolynomialEquiv b a) - p * pbwPolynomialEquiv b a ∈
      basisStrict (MvPolynomial.basisMonomials α R) (Finsupp.weight ω) (m + d) := by
    simpa only [Nat.add_comm] using pbwStar_sub_mul_mem_strict b ω hc d m p hp _ ha'
  have h := (basisStrict (MvPolynomial.basisMonomials α R)
    (Finsupp.weight ω) (m + d)).sub_mem h₁ h₂
  convert h using 1
  simp only [pbwInner_apply, Ring.lie_def, map_sub, pbwStar_apply,
    LinearEquiv.symm_apply_apply]
  rw [mul_comm p (pbwPolynomialEquiv b a)]
  abel

/-- The commutator shift follows from the actual filtered PBW product;
it is not an additional hypothesis of the homogeneous leading construction. -/
theorem inner_pbwBasis_mem_upper_pred (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω a < ω i + ω j)
    {a : UniversalEnvelopingAlgebra R L} {m : ℕ} (hm : 0 < m)
    (ha : a ∈ EnvelopingIsomorphism.PBW.weightedUpper b ω m) (n : α →₀ ℕ) :
    ⁅a, EnvelopingIsomorphism.PBW.pbwBasis b n⁆ ∈
      EnvelopingIsomorphism.PBW.weightedUpper b ω (Finsupp.weight ω n + (m - 1)) := by
  apply (pbwPolynomialEquiv_mem_upper_iff b ω _ _).mp
  have hn := (pbwPolynomialEquiv_mem_upper_iff b ω _ _).mpr
    (EnvelopingIsomorphism.PBW.pbwBasis_mem_weightedUpper b ω (m := n) le_rfl)
  have h := pbwInner_mem_strict b ω hc ha hn
  simp only [pbwInner_apply, LinearEquiv.symm_apply_apply] at h
  apply basisSupport_mono (MvPolynomial.basisMonomials α R) _ h
  intro t ht
  change Finsupp.weight ω t ≤ Finsupp.weight ω n + (m - 1)
  change Finsupp.weight ω t < m + Finsupp.weight ω n at ht
  omega

theorem pbwInner_basis_upper (ω : α → ℕ) (a : UniversalEnvelopingAlgebra R L) (r : ℕ)
    (hshift : ∀ m, ⁅a, EnvelopingIsomorphism.PBW.pbwBasis b m⁆ ∈
      EnvelopingIsomorphism.PBW.weightedUpper b ω (Finsupp.weight ω m + r)) (m : α →₀ ℕ) :
    pbwInner b a ((MvPolynomial.basisMonomials α R) m) ∈
      basisUpper (MvPolynomial.basisMonomials α R) (Finsupp.weight ω) (Finsupp.weight ω m + r) := by
  change pbwInner b a (MvPolynomial.monomial m 1) ∈ _
  rw [pbwInner_apply, pbwPolynomialEquiv_symm_monomial, pbwPolynomialEquiv_mem_upper_iff]
  exact hshift m

/-- The actual homogeneous leading inner derivation in PBW polynomial coordinates.
Strict decrease of bracket weights ensures the graded product is commutative. -/
def pbwLeadingDerivation (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω a < ω i + ω j)
    (a : UniversalEnvelopingAlgebra R L) (r : ℕ)
    (hshift : ∀ m, ⁅a, EnvelopingIsomorphism.PBW.pbwBasis b m⁆ ∈
      EnvelopingIsomorphism.PBW.weightedUpper b ω (Finsupp.weight ω m + r)) :
    Derivation R (MvPolynomial α R) (MvPolynomial α R) :=
  leadingDerivationOfFilteredProduct (MvPolynomial.basisMonomials α R) (Finsupp.weight ω)
    (polynomial_basis_mul_homogeneous ω) (pbwStar b) (pbwStar_sub_mul_mem_strict b ω hc)
    (pbwInner b a) r (pbwInner_basis_upper b ω a r hshift) (pbwInner_leibniz b a)

/-- The canonical polynomial leading derivation of a locally finite inner
derivation is locally nilpotent when its shift is positive. -/
theorem pbwLeadingDerivation_isLocallyNilpotent (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω a < ω i + ω j)
    (a : UniversalEnvelopingAlgebra R L) (r : ℕ) (hr : 0 < r)
    (hshift : ∀ m, ⁅a, EnvelopingIsomorphism.PBW.pbwBasis b m⁆ ∈
      EnvelopingIsomorphism.PBW.weightedUpper b ω (Finsupp.weight ω m + r))
    (ha : a ∈ LF R (UniversalEnvelopingAlgebra R L)) :
    IsLocallyNilpotent (pbwLeadingDerivation b ω hc a r hshift).toLinearMap :=
  leadingOperator_isLocallyNilpotent (MvPolynomial.basisMonomials α R) (Finsupp.weight ω)
    (pbwInner b a) r hr (pbwInner_isLocallyFinite b ha) (pbwInner_basis_upper b ω a r hshift)

/-- The leading derivation associated to an actual upper bound for a. -/
def pbwLeadingDerivationOfUpper (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω a < ω i + ω j)
    (a : UniversalEnvelopingAlgebra R L) (m : ℕ) (hm : 0 < m)
    (ha : a ∈ EnvelopingIsomorphism.PBW.weightedUpper b ω m) :
    Derivation R (MvPolynomial α R) (MvPolynomial α R) :=
  pbwLeadingDerivation b ω hc a (m - 1) (inner_pbwBasis_mem_upper_pred b ω hc hm ha)

theorem pbwLeadingDerivationOfUpper_isLocallyNilpotent (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω a < ω i + ω j)
    (a : UniversalEnvelopingAlgebra R L) (m : ℕ) (hm : 1 < m)
    (ha : a ∈ EnvelopingIsomorphism.PBW.weightedUpper b ω m)
    (hLF : a ∈ LF R (UniversalEnvelopingAlgebra R L)) :
    IsLocallyNilpotent
      (pbwLeadingDerivationOfUpper b ω hc a m (Nat.zero_lt_of_lt hm) ha).toLinearMap :=
  pbwLeadingDerivation_isLocallyNilpotent b ω hc a (m - 1) (by omega)
    (inner_pbwBasis_mem_upper_pred b ω hc (Nat.zero_lt_of_lt hm) ha) hLF

end EnvelopingIsomorphism.Identification
