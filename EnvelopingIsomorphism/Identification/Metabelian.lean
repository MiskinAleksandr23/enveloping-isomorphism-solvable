import EnvelopingIsomorphism.Identification.MetabelianBasic
import EnvelopingIsomorphism.Identification.LeadingDerivation
import EnvelopingIsomorphism.PBW.Weighted
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! Coefficient and leading-operator arguments for HQ2. -/

noncomputable section
namespace EnvelopingIsomorphism.Identification

section Eigenweights

variable {k Q β J σ : Type*} [Field k]
variable [AddCommGroup Q] [Module k Q] [Fintype β]

/-- A separating family of linear forms remains separating for polynomial
coefficients. The proof takes coefficients, avoiding additional scalar-extension APIs. -/
theorem polynomial_coefficients_eq_zero_of_separating_weights
    (bQ : Module.Basis β k Q) (χ : J → Q →ₗ[k] k)
    (hχ : ∀ q, (∀ j, χ j q = 0) → q = 0)
    (p : β → MvPolynomial σ k)
    (hp : ∀ j, ∑ i, χ j (bQ i) • p i = 0) : ∀ i, p i = 0 := by
  classical
  intro i
  ext m
  have hq : (∑ i, MvPolynomial.coeff m (p i) • bQ i) = 0 := by
    apply hχ
    intro j
    have hcoeff := congrArg (MvPolynomial.coeff m) (hp j)
    simpa only [map_sum, map_smul, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_zero, smul_eq_mul, mul_comm] using hcoeff
  have hcoord := congrArg (fun q => bQ.repr q i) hq
  simpa [Finsupp.single_apply] using hcoord

/-- The divisibility obstruction and spanning eigenweights annihilate every
polynomial coefficient in the leading-vector-field argument of HQ2. -/
theorem polynomial_coefficients_eq_zero_of_locallyNilpotent
    [CharZero k] (bQ : Module.Basis β k Q) (χ : J → Q →ₗ[k] k)
    (hχ : ∀ q, (∀ j, χ j q = 0) → q = 0)
    (D : Derivation k (MvPolynomial σ k) (MvPolynomial σ k))
    (hD : IsLocallyNilpotent D.toLinearMap)
    (w : J → MvPolynomial σ k) (hw : ∀ j, w j ≠ 0)
    (p : β → MvPolynomial σ k)
    (heigen : ∀ j, D (w j) = w j * (∑ i, χ j (bQ i) • p i)) :
    ∀ i, p i = 0 := by
  apply polynomial_coefficients_eq_zero_of_separating_weights bQ χ hχ p
  intro j
  have hz := locallyNilpotent_eq_zero_of_eq_mul D hD (heigen j)
  rw [heigen j] at hz
  exact (mul_eq_zero.mp hz).resolve_left (hw j)

end Eigenweights

section WeightedEuler

variable {k σ : Type*} [Field k] [CharZero k] [Fintype σ]

/-- A positive-weight homogeneous polynomial with all positive-weight
partials zero vanishes, by the existing weighted Euler identity. -/
theorem homogeneous_eq_zero_of_positive_weight_partials
    (ω : σ → ℕ) {p : MvPolynomial σ k} {d : ℕ} (hd : d ≠ 0)
    (hp : p.IsWeightedHomogeneous ω d)
    (hderiv : ∀ i, ω i ≠ 0 → MvPolynomial.pderiv i p = 0) : p = 0 := by
  have heuler := hp.sum_weight_X_mul_pderiv
  have hsum : (∑ i : σ, ω i • (MvPolynomial.X i * MvPolynomial.pderiv i p)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : ω i = 0
    · simp [hi]
    · simp [hderiv i hi]
  rw [hsum, nsmul_eq_mul] at heuler
  exact (mul_eq_zero.mp heuler.symm).resolve_left (Nat.cast_ne_zero.mpr hd)

variable {Q β J : Type*} [AddCommGroup Q] [Module k Q] [Fintype β]

/-- The polynomial contradiction used in the first HQ2 filtration. The
leading inner operator will supply D and the displayed eigenvector formula. -/
theorem homogeneous_eq_zero_of_locallyNilpotent_weight_formula
    (bQ : Module.Basis β k Q) (χ : J → Q →ₗ[k] k)
    (hχ : ∀ q, (∀ j, χ j q = 0) → q = 0)
    (ω : σ → ℕ) (τ : β → σ)
    (hτ : ∀ i, ω i ≠ 0 → ∃ j, τ j = i)
    (D : Derivation k (MvPolynomial σ k) (MvPolynomial σ k))
    (hD : IsLocallyNilpotent D.toLinearMap)
    (w : J → MvPolynomial σ k) (hw : ∀ j, w j ≠ 0)
    {p : MvPolynomial σ k} {d : ℕ} (hd : d ≠ 0)
    (hp : p.IsWeightedHomogeneous ω d)
    (heigen : ∀ j, D (w j) =
      w j * (∑ i, χ j (bQ i) • MvPolynomial.pderiv (τ i) p)) : p = 0 := by
  have hpartials := polynomial_coefficients_eq_zero_of_locallyNilpotent bQ χ hχ D hD
    w hw (fun i => MvPolynomial.pderiv (τ i) p) heigen
  apply homogeneous_eq_zero_of_positive_weight_partials ω hd hp
  intro i hi
  obtain ⟨j, rfl⟩ := hτ i hi
  exact hpartials j

end WeightedEuler

section EigenvectorObstruction

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem not_locallyNilpotent_of_eigenvector (D : Module.End k V)
    {x : V} (hx : x ≠ 0) {c : k} (hc : c ≠ 0) (he : D x = c • x) :
    ¬ IsLocallyNilpotent D := by
  have hpow (n : ℕ) : (D ^ n) x = c ^ n • x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, he, smul_smul, pow_succ]
  intro hD
  obtain ⟨n, hn⟩ := hD x
  rw [hpow] at hn
  exact smul_ne_zero (pow_ne_zero n hc) hx hn

end EigenvectorObstruction

section AffineObstruction

variable {k L Q α J : Type*} [Field k]
variable [LieRing L] [LieAlgebra k L] [AddCommGroup Q] [Module k Q]
variable [LinearOrder α] (b : Module.Basis α k L)

attribute [local instance 100] LieRing.ofAssociativeRing
open UniversalEnvelopingAlgebra

include b in
/-- A nonzero quotient component prevents local nilpotence. This includes
the last step of HQ2 and allows an arbitrary linear, non-Lie section. -/
theorem not_mem_LN_of_nonzero_affine_quotient
    (H : LieIdeal k L) [IsLieAbelian H] (s : Q →ₗ[k] L)
    (χ : J → Q →ₗ[k] k) (w : J → H)
    (hw : ∀ j, w j ≠ 0)
    (hχ : Function.Injective (fun q j => χ j q))
    (he : ∀ j q, ⁅s q, (w j : L)⁆ = χ j q • (w j : L))
    {q : Q} (hq : q ≠ 0) {p : UniversalEnvelopingAlgebra k L}
    (hp : p ∈ idealPolynomialPart H) :
    ι k (s q) + p ∉ LN k (UniversalEnvelopingAlgebra k L) := by
  classical
  have hex : ∃ j, χ j q ≠ 0 := by
    by_contra! h
    apply hq
    apply hχ
    funext j
    simp [h j]
  obtain ⟨j, hj⟩ := hex
  have hwL : (w j : L) ≠ 0 := by
    intro h
    apply hw j
    exact Subtype.ext h
  have hιw : ι k (w j : L) ≠ 0 := by
    intro h
    apply hwL
    exact EnvelopingIsomorphism.PBW.ι_injective_of_basis b (h.trans (map_zero (ι k)).symm)
  apply not_locallyNilpotent_of_eigenvector _ hιw hj
  change ⁅ι k (s q) + p, ι k (w j : L)⁆ = χ j q • ι k (w j : L)
  rw [add_lie, lie_eq_zero_of_mem_idealPolynomialPart H hp
    (ι_mem_idealPolynomialPart H (w j).property), add_zero, ← LieHom.map_lie, he, map_smul]

end AffineObstruction

section FiniteFiltration

variable {R L α : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable [LinearOrder α] (b : Module.Basis α R L) (ω : α → ℕ)
attribute [local instance 100] LieRing.ofAssociativeRing
open UniversalEnvelopingAlgebra

theorem lie_word_mem_weightedUpper
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω a ≤ ω i + ω j)
    (a : UniversalEnvelopingAlgebra R L)
    (ha : ∀ i, ⁅a, ι R (b i)⁆ ∈ EnvelopingIsomorphism.PBW.weightedUpper b ω (ω i))
    (w : List α) :
    ⁅a, (w.map (ι R ∘ b)).prod⁆ ∈
      EnvelopingIsomorphism.PBW.weightedUpper b ω (EnvelopingIsomorphism.PBW.wordWeight ω w) := by
  induction w with
  | nil => simp [Ring.lie_def]
  | cons i w ih =>
    have hword := EnvelopingIsomorphism.PBW.word_mem_weightedUpper b ω hc w
    have hgen : ι R (b i) ∈ EnvelopingIsomorphism.PBW.weightedUpper b ω (ω i) := by
      rw [← EnvelopingIsomorphism.PBW.pbwBasis_single b i]
      apply EnvelopingIsomorphism.PBW.pbwBasis_mem_weightedUpper
      simp [Finsupp.weight_single]
    simp only [List.map_cons, List.prod_cons, Function.comp_apply, inner_mul,
      EnvelopingIsomorphism.PBW.wordWeight_cons]
    exact add_mem
      (EnvelopingIsomorphism.PBW.weightedUpper_mul_le b ω hc _ _
        (Submodule.mul_mem_mul (ha i) hword))
      (EnvelopingIsomorphism.PBW.weightedUpper_mul_le b ω hc _ _
        (Submodule.mul_mem_mul hgen ih))

theorem lie_mem_weightedUpper_of_generator_bound
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω a ≤ ω i + ω j)
    (a : UniversalEnvelopingAlgebra R L)
    (ha : ∀ i, ⁅a, ι R (b i)⁆ ∈ EnvelopingIsomorphism.PBW.weightedUpper b ω (ω i))
    {d : ℕ} {p : UniversalEnvelopingAlgebra R L}
    (hp : p ∈ EnvelopingIsomorphism.PBW.weightedUpper b ω d) :
    ⁅a, p⁆ ∈ EnvelopingIsomorphism.PBW.weightedUpper b ω d := by
  apply mapsTo_basisSupport (EnvelopingIsomorphism.PBW.pbwBasis b) (LieAlgebra.ad R _ a) _ p hp
  intro m hm
  apply EnvelopingIsomorphism.PBW.weightedUpper_mono b ω hm
  change ⁅a, EnvelopingIsomorphism.PBW.pbwBasis b m⁆ ∈
    EnvelopingIsomorphism.PBW.weightedUpper b ω (Finsupp.weight ω m)
  rw [EnvelopingIsomorphism.PBW.pbwBasis_apply]
  simpa only [EnvelopingIsomorphism.PBW.wordWeight, EnvelopingIsomorphism.PBW.wordIndex_orderedWord] using
    lie_word_mem_weightedUpper b ω hc a ha (EnvelopingIsomorphism.PBW.orderedWord m)

/-- Positive finite PBW weights give a native-U criterion for local finiteness
of an inner derivation from its action on the original Lie generators. -/
theorem mem_LF_of_weighted_generator_bound [Finite α] [IsNoetherianRing R]
    (hω : ∀ i, ω i ≠ 0)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω a ≤ ω i + ω j)
    (a : UniversalEnvelopingAlgebra R L)
    (ha : ∀ i, ⁅a, ι R (b i)⁆ ∈ EnvelopingIsomorphism.PBW.weightedUpper b ω (ω i)) :
    a ∈ LF R (UniversalEnvelopingAlgebra R L) := by
  apply locallyFinite_of_preserves_finite_basisUpper
    (EnvelopingIsomorphism.PBW.pbwBasis b) (Finsupp.weight ω)
    (LieAlgebra.ad R _ a) (Finsupp.finite_of_nat_weight_le ω hω)
  intro m
  change ⁅a, EnvelopingIsomorphism.PBW.pbwBasis b m⁆ ∈
    EnvelopingIsomorphism.PBW.weightedUpper b ω (Finsupp.weight ω m)
  rw [EnvelopingIsomorphism.PBW.pbwBasis_apply]
  simpa only [EnvelopingIsomorphism.PBW.wordWeight, EnvelopingIsomorphism.PBW.wordIndex_orderedWord] using
    lie_word_mem_weightedUpper b ω hc a ha (EnvelopingIsomorphism.PBW.orderedWord m)

/-- Every linear Lie generator has ordinary PBW degree at most one. -/
theorem ι_mem_ordinaryUpper_one (x : L) :
    ι R x ∈ EnvelopingIsomorphism.PBW.weightedUpper b (fun _ => 1) 1 := by
  have hspan : Submodule.span R (Set.range b) ≤
      (EnvelopingIsomorphism.PBW.weightedUpper b (fun _ => 1) 1).comap (ι R).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change ι R (b i) ∈ EnvelopingIsomorphism.PBW.weightedUpper b (fun _ => 1) 1
    rw [← EnvelopingIsomorphism.PBW.pbwBasis_single b i]
    apply EnvelopingIsomorphism.PBW.pbwBasis_mem_weightedUpper
    simp [Finsupp.weight_single]
  rw [b.span_eq] at hspan
  exact hspan (Submodule.mem_top : x ∈ (⊤ : Submodule R L))

include b in
/-- Inner derivations of linear generators are locally finite for a finite
free Lie algebra over a noetherian base ring. -/
theorem ι_mem_LF [Finite α] [IsNoetherianRing R] (x : L) :
    ι R x ∈ LF R (UniversalEnvelopingAlgebra R L) := by
  apply mem_LF_of_weighted_generator_bound b (fun _ => 1) (by simp)
    (by intros; omega) (ι R x)
  intro i
  rw [← LieHom.map_lie]
  exact ι_mem_ordinaryUpper_one b ⁅x, b i⁆

end FiniteFiltration

end EnvelopingIsomorphism.Identification
