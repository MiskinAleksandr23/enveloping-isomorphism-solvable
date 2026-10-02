import EnvelopingIsomorphism.Identification.PolynomialLeading
import EnvelopingIsomorphism.Identification.Metabelian

/-! The second HQ2 filtration: polynomial coefficients of a locally finite
vector field become constant under the separating eigenweight condition. -/

noncomputable section
namespace EnvelopingIsomorphism.Identification

open MvPolynomial

variable {k Q β J σ : Type*} [Field k] [CharZero k]
  [AddCommGroup Q] [Module k Q] [Fintype β]

omit [CharZero k] in
theorem leading_eigenweight_coefficients
    (ω : σ → ℕ) (bQ : Module.Basis β k Q) (χ : J → Q →ₗ[k] k)
    (D : Derivation k (MvPolynomial σ k) (MvPolynomial σ k)) (e : ℕ)
    (hshift : ∀ m, D ((basisMonomials σ k) m) ∈
      basisUpper (basisMonomials σ k) (Finsupp.weight ω) (Finsupp.weight ω m + e))
    (w : J → MvPolynomial σ k) (hw : ∀ j, (w j).IsWeightedHomogeneous ω 1)
    (a : β → MvPolynomial σ k)
    (ha : ∀ i, a i ∈ basisUpper (basisMonomials σ k) (Finsupp.weight ω) e)
    (heigen : ∀ j, D (w j) = w j * (∑ i, χ j (bQ i) • a i)) (j : J) :
    polynomialLeadingDerivation ω D e hshift (w j) =
      w j * (∑ i, χ j (bQ i) • weightedHomogeneousComponent ω e (a i)) := by
  let top := fun i => weightedHomogeneousComponent ω e (a i)
  have hsumHom : (∑ i, χ j (bQ i) • top i) ∈
      basisHomogeneous (basisMonomials σ k) (Finsupp.weight ω) e := by
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (weightedComponent_mem_homogeneous ω e (a i))
  have hwHom := (polynomial_homogeneous_iff_basis ω 1 (w j)).mp (hw j)
  have hprodHom := homogeneous_mul_mem (basisMonomials σ k) (Finsupp.weight ω)
    (polynomial_basis_mul_homogeneous ω) hwHom hsumHom
  have hsumRem : ((∑ i, χ j (bQ i) • a i) - ∑ i, χ j (bQ i) • top i) ∈
      basisStrict (basisMonomials σ k) (Finsupp.weight ω) e := by
    rw [← Finset.sum_sub_distrib]
    apply Submodule.sum_mem
    intro i _
    simpa only [← smul_sub] using Submodule.smul_mem
      (basisStrict (basisMonomials σ k) (Finsupp.weight ω) e)
      (χ j (bQ i)) (weightedComponent_remainder_strict ω e (ha i))
  have hrem : D (w j) - w j * (∑ i, χ j (bQ i) • top i) ∈
      basisStrict (basisMonomials σ k) (Finsupp.weight ω) (1 + e) := by
    rw [heigen j, ← mul_sub]
    have h := strict_mul_upper_mem (basisMonomials σ k) (Finsupp.weight ω)
      (polynomial_basis_mul_homogeneous ω) hsumRem
      (homogeneous_mem_upper (basisMonomials σ k) (Finsupp.weight ω) hwHom)
    simpa only [mul_comm, Nat.add_comm] using h
  change leadingOperator (basisMonomials σ k) (Finsupp.weight ω) D.toLinearMap e (w j) = _
  rw [leadingOperator_polynomial_homogeneous ω D.toLinearMap e (hw j)]
  exact weightedComponent_eq_of_homogeneous_remainder ω (1 + e) hprodHom hrem

/-- All highest coefficients vanish at every positive common coefficient bound. -/
theorem top_coefficients_eq_zero_of_locallyFinite
    (ω : σ → ℕ) (bQ : Module.Basis β k Q) (χ : J → Q →ₗ[k] k)
    (hχ : ∀ q, (∀ j, χ j q = 0) → q = 0)
    (D : Derivation k (MvPolynomial σ k) (MvPolynomial σ k)) (e : ℕ) (he : 0 < e)
    (hLF : IsLocallyFinite D.toLinearMap)
    (hshift : ∀ m, D ((basisMonomials σ k) m) ∈
      basisUpper (basisMonomials σ k) (Finsupp.weight ω) (Finsupp.weight ω m + e))
    (w : J → MvPolynomial σ k) (hw0 : ∀ j, w j ≠ 0)
    (hw : ∀ j, (w j).IsWeightedHomogeneous ω 1)
    (a : β → MvPolynomial σ k)
    (ha : ∀ i, a i ∈ basisUpper (basisMonomials σ k) (Finsupp.weight ω) e)
    (heigen : ∀ j, D (w j) = w j * (∑ i, χ j (bQ i) • a i)) :
    ∀ i, weightedHomogeneousComponent ω e (a i) = 0 := by
  apply polynomial_coefficients_eq_zero_of_locallyNilpotent bQ χ hχ
    (polynomialLeadingDerivation ω D e hshift)
    (polynomialLeadingDerivation_isLocallyNilpotent ω D e he hshift hLF) w hw0
  exact leading_eigenweight_coefficients ω bQ χ D e hshift w hw a ha heigen

theorem coefficients_upper_zero_of_locallyFinite
    (ω : σ → ℕ) (bQ : Module.Basis β k Q) (χ : J → Q →ₗ[k] k)
    (hχ : ∀ q, (∀ j, χ j q = 0) → q = 0)
    (D : Derivation k (MvPolynomial σ k) (MvPolynomial σ k))
    (hLF : IsLocallyFinite D.toLinearMap)
    (w : J → MvPolynomial σ k) (hw0 : ∀ j, w j ≠ 0)
    (hw : ∀ j, (w j).IsWeightedHomogeneous ω 1)
    (a : β → MvPolynomial σ k)
    (hlinear : ∀ e, (∀ i, a i ∈ basisUpper (basisMonomials σ k) (Finsupp.weight ω) e) →
      ∀ m, D ((basisMonomials σ k) m) ∈
        basisUpper (basisMonomials σ k) (Finsupp.weight ω) (Finsupp.weight ω m + e))
    (heigen : ∀ j, D (w j) = w j * (∑ i, χ j (bQ i) • a i)) :
    ∀ i, a i ∈ basisUpper (basisMonomials σ k) (Finsupp.weight ω) 0 := by
  classical
  choose bounds hbounds using fun i => exists_mem_basisUpper (basisMonomials σ k)
    (Finsupp.weight ω) (a i)
  have hbound : ∀ i, a i ∈ basisUpper (basisMonomials σ k) (Finsupp.weight ω)
      (Finset.univ.sup bounds) := fun i =>
    basisUpper_mono (basisMonomials σ k) (Finsupp.weight ω)
      (Finset.le_sup (Finset.mem_univ i)) (hbounds i)
  suffices h : ∀ e, (∀ i, a i ∈ basisUpper (basisMonomials σ k) (Finsupp.weight ω) e) →
      ∀ i, a i ∈ basisUpper (basisMonomials σ k) (Finsupp.weight ω) 0 from h _ hbound
  intro e
  induction e with
  | zero => exact id
  | succ e ih =>
    intro ha
    have htop := top_coefficients_eq_zero_of_locallyFinite ω bQ χ hχ D (e + 1)
      (Nat.zero_lt_succ e) hLF (hlinear _ ha) w hw0 hw a ha heigen
    apply ih
    intro i
    have hrem := weightedComponent_remainder_strict ω (e + 1) (ha i)
    rw [htop i, sub_zero] at hrem
    apply basisSupport_mono (basisMonomials σ k) _ hrem
    intro m hm
    exact Nat.le_of_lt_succ hm

/-- With ordinary degree, the recovered coefficients are actual constants. -/
theorem coefficients_constant_of_locallyFinite
    (bQ : Module.Basis β k Q) (χ : J → Q →ₗ[k] k)
    (hχ : ∀ q, (∀ j, χ j q = 0) → q = 0)
    (D : Derivation k (MvPolynomial σ k) (MvPolynomial σ k))
    (hLF : IsLocallyFinite D.toLinearMap)
    (w : J → MvPolynomial σ k) (hw0 : ∀ j, w j ≠ 0)
    (hw : ∀ j, (w j).IsWeightedHomogeneous (fun _ => 1) 1)
    (a : β → MvPolynomial σ k)
    (hlinear : ∀ e, (∀ i, a i ∈ basisUpper (basisMonomials σ k)
      (Finsupp.weight (fun _ => 1)) e) →
      ∀ m, D ((basisMonomials σ k) m) ∈ basisUpper (basisMonomials σ k)
        (Finsupp.weight (fun _ => 1)) (Finsupp.weight (fun _ => 1) m + e))
    (heigen : ∀ j, D (w j) = w j * (∑ i, χ j (bQ i) • a i)) :
    ∀ i, a i = C (coeff 0 (a i)) := by
  have hupper := coefficients_upper_zero_of_locallyFinite (fun _ => 1)
    bQ χ hχ D hLF w hw0 hw a hlinear heigen
  intro i
  have hhom : (a i).IsWeightedHomogeneous (fun _ => 1) 0 := by
    intro m hm
    exact Nat.eq_zero_of_le_zero ((mem_basisSupport (basisMonomials σ k) _ _).mp
      (hupper i) m (Finsupp.mem_support_iff.mpr hm))
  calc
    a i = weightedHomogeneousComponent (fun _ => 1) 0 (a i) :=
      hhom.weightedHomogeneousComponent_same.symm
    _ = C (coeff 0 (a i)) := weightedHomogeneousComponent_zero (a i) (fun _ => one_ne_zero)

section LinearFields

variable [LinearOrder σ]

omit [CharZero k] in
theorem polynomial_word_eq_monomial (w : List σ) :
    (w.map (X : σ → MvPolynomial σ k)).prod = monomial (EnvelopingIsomorphism.PBW.wordIndex w) 1 := by
  induction w with
  | nil => simp
  | cons i w ih =>
    simp only [List.map_cons, List.prod_cons, ih, EnvelopingIsomorphism.PBW.wordIndex_cons,
      X, monomial_mul, one_mul]

omit [CharZero k] in
theorem polynomial_word_mem_ordinaryUpper (w : List σ) :
    (w.map (X : σ → MvPolynomial σ k)).prod ∈
      basisUpper (basisMonomials σ k) (Finsupp.weight (fun _ => 1)) w.length := by
  rw [polynomial_word_eq_monomial]
  apply basis_mem_basisSupport (basisMonomials σ k)
  exact le_of_eq (EnvelopingIsomorphism.PBW.wordWeight_one w)

omit [CharZero k] in
theorem linear_derivation_word_bound
    (D : Derivation k (MvPolynomial σ k) (MvPolynomial σ k))
    (hD : ∀ i, D (X i) ∈ basisUpper (basisMonomials σ k) (Finsupp.weight (fun _ => 1)) 1)
    (w : List σ) :
    D ((w.map X).prod) ∈
      basisUpper (basisMonomials σ k) (Finsupp.weight (fun _ => 1)) w.length := by
  induction w with
  | nil => simp
  | cons i w ih =>
    have hXi : (X i : MvPolynomial σ k) ∈
        basisUpper (basisMonomials σ k) (Finsupp.weight (fun _ => 1)) 1 := by
      simpa using polynomial_word_mem_ordinaryUpper (k := k) [i]
    have h₁ := upper_mul_upper_mem (basisMonomials σ k) (Finsupp.weight (fun _ => 1))
      (polynomial_basis_mul_homogeneous (fun _ => 1)) hXi ih
    have h₂ := upper_mul_upper_mem (basisMonomials σ k) (Finsupp.weight (fun _ => 1))
      (polynomial_basis_mul_homogeneous (fun _ => 1)) (polynomial_word_mem_ordinaryUpper w) (hD i)
    rw [Nat.add_comm w.length 1] at h₂
    simpa only [List.map_cons, List.prod_cons, List.length_cons, Derivation.leibniz,
      smul_eq_mul, Nat.add_comm] using add_mem h₁ h₂

omit [CharZero k] in
/-- A polynomial derivation with affine-linear values on variables preserves
ordinary upper degree. Its action on all monomials is derived by Leibniz. -/
theorem linear_derivation_monomial_bound
    (D : Derivation k (MvPolynomial σ k) (MvPolynomial σ k))
    (hD : ∀ i, D (X i) ∈ basisUpper (basisMonomials σ k) (Finsupp.weight (fun _ => 1)) 1)
    (m : σ →₀ ℕ) :
    D ((basisMonomials σ k) m) ∈ basisUpper (basisMonomials σ k)
      (Finsupp.weight (fun _ => 1)) (Finsupp.weight (fun _ => 1) m) := by
  have h := linear_derivation_word_bound D hD (EnvelopingIsomorphism.PBW.orderedWord m)
  rw [polynomial_word_eq_monomial, EnvelopingIsomorphism.PBW.wordIndex_orderedWord] at h
  have hlen : (EnvelopingIsomorphism.PBW.orderedWord m).length = Finsupp.weight (fun _ => 1) m := by
    rw [← EnvelopingIsomorphism.PBW.wordWeight_one, EnvelopingIsomorphism.PBW.wordWeight,
      EnvelopingIsomorphism.PBW.wordIndex_orderedWord]
  simpa only [hlen, coe_basisMonomials] using h

end LinearFields

def polynomialVectorField (a : β → MvPolynomial σ k)
    (δ : β → Derivation k (MvPolynomial σ k) (MvPolynomial σ k)) :
    Derivation k (MvPolynomial σ k) (MvPolynomial σ k) := ∑ i, a i • δ i

omit [CharZero k] in
theorem polynomialVectorField_apply (a : β → MvPolynomial σ k)
    (δ : β → Derivation k (MvPolynomial σ k) (MvPolynomial σ k)) (p : MvPolynomial σ k) :
    polynomialVectorField a δ p = ∑ i, a i * δ i p := by
  change Derivation.coeFnAddMonoidHom (∑ i, a i • δ i) p = _
  rw [map_sum]
  simp [Finset.sum_apply, Derivation.coeFnAddMonoidHom, smul_eq_mul]

omit [CharZero k] in
theorem polynomialVectorField_degree_bound [LinearOrder σ]
    (a : β → MvPolynomial σ k)
    (δ : β → Derivation k (MvPolynomial σ k) (MvPolynomial σ k))
    (hδ : ∀ i j, δ i (X j) ∈
      basisUpper (basisMonomials σ k) (Finsupp.weight (fun _ => 1)) 1)
    (e : ℕ) (ha : ∀ i, a i ∈ basisUpper (basisMonomials σ k) (Finsupp.weight (fun _ => 1)) e)
    (m : σ →₀ ℕ) :
    polynomialVectorField a δ ((basisMonomials σ k) m) ∈
      basisUpper (basisMonomials σ k) (Finsupp.weight (fun _ => 1))
        (Finsupp.weight (fun _ => 1) m + e) := by
  rw [polynomialVectorField_apply]
  apply Submodule.sum_mem
  intro i _
  have h := upper_mul_upper_mem (basisMonomials σ k) (Finsupp.weight (fun _ => 1))
    (polynomial_basis_mul_homogeneous (fun _ => 1)) (ha i)
    (linear_derivation_monomial_bound (δ i) (hδ i) m)
  simpa only [Nat.add_comm] using h

/-- The complete polynomial vector-field step of HQ2: local finiteness,
linear generator images, and separating eigenweights force scalar coefficients.
The needed degree bound is proved from the variable images and Leibniz. -/
theorem linear_vectorField_coefficients_constant [LinearOrder σ]
    (bQ : Module.Basis β k Q) (χ : J → Q →ₗ[k] k)
    (hχ : ∀ q, (∀ j, χ j q = 0) → q = 0)
    (a : β → MvPolynomial σ k)
    (δ : β → Derivation k (MvPolynomial σ k) (MvPolynomial σ k))
    (hδ : ∀ i j, δ i (X j) ∈
      basisUpper (basisMonomials σ k) (Finsupp.weight (fun _ => 1)) 1)
    (hLF : IsLocallyFinite (polynomialVectorField a δ).toLinearMap)
    (w : J → MvPolynomial σ k) (hw0 : ∀ j, w j ≠ 0)
    (hw : ∀ j, (w j).IsWeightedHomogeneous (fun _ => 1) 1)
    (heigen : ∀ i j, δ i (w j) = χ j (bQ i) • w j) :
    ∀ i, a i = C (coeff 0 (a i)) := by
  apply coefficients_constant_of_locallyFinite bQ χ hχ (polynomialVectorField a δ) hLF
    w hw0 hw a (polynomialVectorField_degree_bound a δ hδ)
  intro j
  rw [polynomialVectorField_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [heigen, Algebra.mul_smul_comm, mul_comm]

end EnvelopingIsomorphism.Identification
