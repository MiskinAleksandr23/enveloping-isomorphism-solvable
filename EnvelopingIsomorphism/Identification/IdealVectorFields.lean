import EnvelopingIsomorphism.Identification.MetabelianAffine
import EnvelopingIsomorphism.Identification.PolynomialInner

/-! Actual polynomial vector fields induced by the action on an abelian ideal. -/

noncomputable section
namespace EnvelopingIsomorphism.Identification

open UniversalEnvelopingAlgebra MvPolynomial
attribute [local instance 100] LieRing.ofAssociativeRing

variable {k L α β : Type*} [Field k] [LieRing L] [LieAlgebra k L]
  [Fintype α] [Fintype β] [LinearOrder (α ⊕ β)]
  (b : Module.Basis (α ⊕ β) k L) (H : LieIdeal k L)
  (hH : (H : Submodule k L) = Submodule.span k (Set.range (fun i : α => b (.inl i))))

/-- The linear polynomial recording the ideal-block coordinates. -/
def idealCoordinatePolynomial : L →ₗ[k] MvPolynomial α k :=
  ∑ i, (b.coord (.inl i)).smulRight (X i)

theorem idealCoordinatePolynomial_apply (x : L) :
    idealCoordinatePolynomial b x = ∑ i : α, b.repr x (.inl i) • (X i : MvPolynomial α k) := by
  simp [idealCoordinatePolynomial, Module.Basis.coord_apply]

theorem idealCoordinatePolynomial_homogeneous (x : L) :
    (idealCoordinatePolynomial b x).IsWeightedHomogeneous (fun _ => 1) 1 := by
  apply (polynomial_homogeneous_iff_basis (fun _ => 1) 1 _).mpr
  rw [idealCoordinatePolynomial_apply]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  change (basisMonomials α k) (Finsupp.single i 1) ∈ _
  apply basis_mem_basisSupport
  simp [Finsupp.weight_single]

theorem idealCoordinatePolynomial_mem_upper_one (x : L) :
    idealCoordinatePolynomial b x ∈ basisUpper (basisMonomials α k)
      (Finsupp.weight (fun _ => 1)) 1 :=
  homogeneous_mem_upper (basisMonomials α k) (Finsupp.weight (fun _ => 1))
    ((polynomial_homogeneous_iff_basis (fun _ => 1) 1 _).mp (idealCoordinatePolynomial_homogeneous b x))

variable (φ : MvPolynomial α k →ₐ[k] UniversalEnvelopingAlgebra k L)
  (hφX : ∀ i, φ (X i) = ι k (b (.inl i)))

include hH hφX in
theorem eval_idealCoordinatePolynomial {x : L} (hx : x ∈ H) :
    φ (idealCoordinatePolynomial b x) = ι k x := by
  rw [idealCoordinatePolynomial_apply, map_sum]
  simp only [map_smul, hφX]
  have h := congrArg (ι k) (b.sum_repr x)
  rw [map_sum, Fintype.sum_sum_type] at h
  have hz (j : β) : b.repr x (.inr j) = 0 := coeff_eq_zero_on_complement b H hH hx j
  simpa only [map_smul, hz, zero_smul, map_zero, Finset.sum_const_zero, add_zero] using h

/-- The polynomial derivation determined by the true brackets with ideal generators. -/
def idealPolynomialAction (x : L) : Derivation k (MvPolynomial α k) (MvPolynomial α k) :=
  MvPolynomial.mkDerivation k (fun i => idealCoordinatePolynomial b ⁅x, b (.inl i)⁆)

@[simp] theorem idealPolynomialAction_X (x : L) (i : α) :
    idealPolynomialAction b x (X i) = idealCoordinatePolynomial b ⁅x, b (.inl i)⁆ :=
  MvPolynomial.mkDerivation_X _ _ _

theorem idealPolynomialAction_X_upper (x : L) (i : α) :
    idealPolynomialAction b x (X i) ∈ basisUpper (basisMonomials α k)
      (Finsupp.weight (fun _ => 1)) 1 := by
  rw [idealPolynomialAction_X]
  exact idealCoordinatePolynomial_mem_upper_one b _

include hH hφX in
theorem idealPolynomialAction_intertwines (x : L) (p : MvPolynomial α k) :
    φ (idealPolynomialAction b x p) = ⁅ι k x, φ p⁆ := by
  apply algHom_intertwines_polynomial_derivation_inner φ (idealPolynomialAction b x) (ι k x) _ p
  intro i
  rw [idealPolynomialAction_X,
    eval_idealCoordinatePolynomial b H hH φ hφX (H.lie_mem (ideal_basis_mem b H hH i)),
    hφX, LieHom.map_lie]

include hH hφX in
theorem idealPolynomialAction_eigenvector (hφ : Function.Injective φ)
    (x w : L) (hw : w ∈ H) (c : k) (he : ⁅x, w⁆ = c • w) :
    idealPolynomialAction b x (idealCoordinatePolynomial b w) =
      c • idealCoordinatePolynomial b w := by
  apply hφ
  rw [idealPolynomialAction_intertwines b H hH φ hφX,
    eval_idealCoordinatePolynomial b H hH φ hφX hw, ← LieHom.map_lie,
    he, map_smul, map_smul, eval_idealCoordinatePolynomial b H hH φ hφX hw]

include hH hφX in
theorem idealCoordinatePolynomial_ne_zero {w : L} (hw : w ∈ H) (hw0 : w ≠ 0) :
    idealCoordinatePolynomial b w ≠ 0 := by
  intro h
  apply hw0
  apply EnvelopingIsomorphism.PBW.ι_injective_of_basis b
  rw [← eval_idealCoordinatePolynomial b H hH φ hφX hw, h, map_zero, map_zero]

section CoefficientIdentification

variable [CharZero k] [LinearOrder α]
variable {Q J : Type*} [AddCommGroup Q] [Module k Q]

include hH hφX in
/-- The second hard HQ2 step for an actual affine polynomial expression in
the native UEA. All polynomial vector fields and their degree estimates are
constructed from the true Lie brackets; no filtered-action hypotheses remain. -/
theorem affine_coefficients_constant_of_locallyFinite
    (hφ : Function.Injective φ) (bQ : Module.Basis β k Q) (ψ : J → Q →ₗ[k] k)
    (hψ : ∀ q, (∀ j, ψ j q = 0) → q = 0)
    (w : J → L) (hwH : ∀ j, w j ∈ H) (hw0 : ∀ j, w j ≠ 0)
    (he : ∀ i j, ⁅b (.inr i), w j⁆ = ψ j (bQ i) • w j)
    (p : β → MvPolynomial α k) (p₀ : MvPolynomial α k)
    (hLF : φ p₀ + ∑ i, φ (p i) * ι k (b (.inr i)) ∈
      LF k (UniversalEnvelopingAlgebra k L)) :
    ∀ i, p i = C (coeff 0 (p i)) := by
  let δ := fun i : β => idealPolynomialAction b (b (.inr i))
  have hδeval := fun i x => idealPolynomialAction_intertwines b H hH φ hφX (b (.inr i)) x
  have hLFpoly := polynomialVectorField_isLocallyFinite_of_inner φ hφ p p₀
    (fun i => ι k (b (.inr i))) δ hδeval hLF
  apply linear_vectorField_coefficients_constant bQ ψ hψ p δ
    (fun i j => idealPolynomialAction_X_upper b (b (.inr i)) j) hLFpoly
    (fun j => idealCoordinatePolynomial b (w j))
    (fun j => idealCoordinatePolynomial_ne_zero b H hH φ hφX (hwH j) (hw0 j))
    (fun j => idealCoordinatePolynomial_homogeneous b (w j))
  intro i j
  exact idealPolynomialAction_eigenvector b H hH φ hφX hφ (b (.inr i)) (w j) (hwH j)
    (ψ j (bQ i)) (he i j)

end CoefficientIdentification
end EnvelopingIsomorphism.Identification
