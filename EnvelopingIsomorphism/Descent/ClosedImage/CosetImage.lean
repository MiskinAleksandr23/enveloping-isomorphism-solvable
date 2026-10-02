import EnvelopingIsomorphism.Descent.ClosedImage.AlgebraicGroup

/-! # Closed cosets and their generic extension-field containment -/

namespace EnvelopingIsomorphism.Descent

open Set Topology MvPolynomial

noncomputable section

namespace AffinePoint

variable {k σ τ υ : Type*} [Field k]

theorem polynomialMap_comp (F : τ → MvPolynomial σ k) (E : υ → MvPolynomial τ k)
    (x : AffinePoint k σ) :
    polynomialMap E (polynomialMap F x) =
      polynomialMap (fun i => aeval F (E i)) x := by
  apply funext
  intro i
  change aeval (fun j => aeval x.toFunction (F j)) (E i) =
    aeval x.toFunction (aeval F (E i))
  rw [comp_aeval_apply]

end AffinePoint

namespace AffinePolynomialGroup

variable {k σ τ G H : Type*} [Field k] [IsAlgClosed k] [Finite σ] [Finite τ]
  [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

/-- The right coset of the image of a polynomial group homomorphism is closed. -/
theorem isClosed_coset_range (P : AffinePresentation k σ G)
    (Q : AffinePolynomialGroup k τ H) (f : G →* H) (F : τ → MvPolynomial σ k)
    (hF : ∀ g, Q.coordinates (f g) = AffinePoint.polynomialMap F (P.coordinates g))
    (h : H) : IsClosed (Set.range (fun g => f g * h)) := by
  letI := Q.separatelyContinuousMul
  change IsClosed (Set.range ((fun x => x * h) ∘ f))
  rw [Set.range_comp]
  exact isClosedMap_mul_right h _ (isClosed_range P Q f F hF)

/-- Polynomial equations for the closed coset also hold at every image point
over an extension field. -/
theorem closed_coset_with_generic_containment
    {K : Type*} [Field K] [Algebra k K]
    (P : AffinePresentation k σ G) (Q : AffinePolynomialGroup k τ H)
    (f : G →* H) (F : τ → MvPolynomial σ k)
    (hF : ∀ g, Q.coordinates (f g) = AffinePoint.polynomialMap F (P.coordinates g))
    (h : H) :
    ∃ J : Ideal (MvPolynomial τ k),
      Q.coordinates '' Set.range (fun g => f g * h) = AffinePoint.zeros J ∧
      ∀ x : σ → K, x ∈ zeroLocus K P.equations →
        (fun i => aeval x (aeval F (Q.mulRightPolynomial h i))) ∈ zeroLocus K J := by
  let E : τ → MvPolynomial σ k := fun i => aeval F (Q.mulRightPolynomial h i)
  have hE : ∀ g, Q.coordinates (f g * h) = AffinePoint.polynomialMap E (P.coordinates g) := by
    intro g
    rw [Q.mulRight_coordinates, hF, AffinePoint.polynomialMap_comp]
  have hclosed := Q.toAffinePresentation.isClosedEmbedding_coordinates.isClosedMap _
    (isClosed_coset_range P Q f F hF h)
  obtain ⟨J, hJ⟩ := (AffinePoint.isClosed_iff_zeros _).mp hclosed
  refine ⟨J, hJ, ?_⟩
  have hJE : AffinePoint.polynomialMap E '' AffinePoint.zeros P.equations = AffinePoint.zeros J :=
    (P.coordinate_range_eq_polynomial_image Q.toAffinePresentation
      (fun g => f g * h) E hE).symm.trans hJ
  intro x hx q hq
  apply polynomial_image_relation_baseChange P.equations E q _ x hx
  intro y hy
  have hmem : AffinePoint.polynomialMap E (AffinePoint.ofFunction y) ∈ AffinePoint.zeros J := by
    rw [← hJE]
    exact ⟨AffinePoint.ofFunction y, hy, rfl⟩
  exact hmem q hq

end AffinePolynomialGroup

end

end EnvelopingIsomorphism.Descent
