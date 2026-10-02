import EnvelopingIsomorphism.Descent.ClosedImage.PolynomialImage

/-! # Closed images of affine polynomial groups

An affine presentation consists of an embedding into finite affine space whose
image is cut out by polynomial equations. For groups we additionally record
polynomial formulas for translations and inversion. This is a coordinate
contract, suitable in particular for matrix groups using an extra inverse
determinant coordinate. Closedness of a homomorphism's image is a theorem below,
not a field of the contract.
-/

namespace EnvelopingIsomorphism.Descent

open Set Topology TopologicalSpace MvPolynomial

noncomputable section

/-- Coordinates and equations presenting a topological space as an affine
algebraic set with its Zariski topology. -/
structure AffinePresentation (k σ X : Type*) [Field k] [TopologicalSpace X] where
  coordinates : X → AffinePoint k σ
  isEmbedding_coordinates : IsEmbedding coordinates
  equations : Ideal (MvPolynomial σ k)
  range_coordinates : Set.range coordinates = AffinePoint.zeros equations

namespace AffinePresentation

variable {k σ τ X Y : Type*} [Field k] [TopologicalSpace X] [TopologicalSpace Y]

theorem isClosedEmbedding_coordinates (P : AffinePresentation k σ X) :
    IsClosedEmbedding P.coordinates :=
  ⟨P.isEmbedding_coordinates, P.range_coordinates ▸ AffinePoint.isClosed_zeros P.equations⟩

theorem noetherianSpace [Finite σ] (P : AffinePresentation k σ X) : NoetherianSpace X :=
  P.isEmbedding_coordinates.isInducing.noetherianSpace

/-- A map with polynomial coordinate formulas is continuous for the Zariski
topologies supplied by the presentations. -/
theorem continuous_of_polynomial (P : AffinePresentation k σ X)
    (Q : AffinePresentation k τ Y) (f : X → Y) (F : τ → MvPolynomial σ k)
    (hF : ∀ x, Q.coordinates (f x) = AffinePoint.polynomialMap F (P.coordinates x)) :
    Continuous f := by
  apply Q.isEmbedding_coordinates.isInducing.continuous_iff.mpr
  have heq : Q.coordinates ∘ f = AffinePoint.polynomialMap F ∘ P.coordinates :=
    funext hF
  rw [heq]
  exact (AffinePoint.continuous_polynomialMap F).comp P.isEmbedding_coordinates.continuous

theorem coordinate_range_eq_polynomial_image (P : AffinePresentation k σ X)
    (Q : AffinePresentation k τ Y) (f : X → Y) (F : τ → MvPolynomial σ k)
    (hF : ∀ x, Q.coordinates (f x) = AffinePoint.polynomialMap F (P.coordinates x)) :
    Q.coordinates '' Set.range f = AffinePoint.polynomialMap F '' AffinePoint.zeros P.equations := by
  rw [← P.range_coordinates]
  ext y
  constructor
  · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
    exact ⟨P.coordinates x, ⟨x, rfl⟩, (hF x).symm⟩
  · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
    exact ⟨f x, ⟨x, rfl⟩, hF x⟩

theorem range_eq_preimage_polynomial_image (P : AffinePresentation k σ X)
    (Q : AffinePresentation k τ Y) (f : X → Y) (F : τ → MvPolynomial σ k)
    (hF : ∀ x, Q.coordinates (f x) = AffinePoint.polynomialMap F (P.coordinates x)) :
    Set.range f = Q.coordinates ⁻¹'
      (AffinePoint.polynomialMap F '' AffinePoint.zeros P.equations) := by
  rw [← coordinate_range_eq_polynomial_image P Q f F hF]
  exact (Set.preimage_image_eq _ Q.isEmbedding_coordinates.injective).symm

theorem isConstructible_range [IsAlgClosed k] [Finite σ] [Finite τ]
    (P : AffinePresentation k σ X) (Q : AffinePresentation k τ Y)
    (f : X → Y) (F : τ → MvPolynomial σ k)
    (hF : ∀ x, Q.coordinates (f x) = AffinePoint.polynomialMap F (P.coordinates x)) :
    IsConstructible (Set.range f) := by
  letI := Q.noetherianSpace
  rw [range_eq_preimage_polynomial_image P Q f F hF]
  apply IsConstructible.preimage Q.isEmbedding_coordinates.continuous
  · intro U hU hUc V hVc hV
    exact NoetherianSpace.isCompact _
  · exact AffinePoint.isConstructible_polynomialMap_image_zeros P.equations F

end AffinePresentation

/-- An affine group presentation with polynomial formulas for the operations
needed by the closed-subgroup theorem. -/
structure AffinePolynomialGroup (k σ G : Type*) [Field k] [Group G] [TopologicalSpace G]
    extends AffinePresentation k σ G where
  mulLeftPolynomial : G → σ → MvPolynomial σ k
  mulLeft_coordinates : ∀ g h, coordinates (g * h) =
    AffinePoint.polynomialMap (mulLeftPolynomial g) (coordinates h)
  mulRightPolynomial : G → σ → MvPolynomial σ k
  mulRight_coordinates : ∀ g h, coordinates (h * g) =
    AffinePoint.polynomialMap (mulRightPolynomial g) (coordinates h)
  invPolynomial : σ → MvPolynomial σ k
  inv_coordinates : ∀ g, coordinates g⁻¹ = AffinePoint.polynomialMap invPolynomial (coordinates g)

namespace AffinePolynomialGroup

variable {k σ τ G H : Type*} [Field k] [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]

theorem separatelyContinuousMul (Q : AffinePolynomialGroup k τ H) : SeparatelyContinuousMul H where
  continuous_const_mul {g} := Q.toAffinePresentation.continuous_of_polynomial
    Q.toAffinePresentation (fun h => g * h) (Q.mulLeftPolynomial g) (Q.mulLeft_coordinates g)
  continuous_mul_const {g} := Q.toAffinePresentation.continuous_of_polynomial
    Q.toAffinePresentation (fun h => h * g) (Q.mulRightPolynomial g) (Q.mulRight_coordinates g)

theorem continuousInv (Q : AffinePolynomialGroup k τ H) : ContinuousInv H where
  continuous_inv := Q.toAffinePresentation.continuous_of_polynomial
    Q.toAffinePresentation Inv.inv Q.invPolynomial Q.inv_coordinates

/-- A closed subgroup of an affine polynomial group inherits an affine polynomial
presentation. Its equations exist because the ambient coordinates are a closed
embedding; the group operation formulas restrict directly. -/
def closedSubgroup (Q : AffinePolynomialGroup k τ H) (U : Subgroup H)
    (hU : IsClosed (U : Set H)) : AffinePolynomialGroup k τ U := by
  have hex : ∃ J : Ideal (MvPolynomial τ k),
      Q.coordinates '' (U : Set H) = AffinePoint.zeros J :=
    (AffinePoint.isClosed_iff_zeros _).mp
      (Q.toAffinePresentation.isClosedEmbedding_coordinates.isClosedMap _ hU)
  choose J hJ using hex
  exact
    { coordinates := fun u => Q.coordinates u.val
      isEmbedding_coordinates := Q.isEmbedding_coordinates.comp
        ⟨Topology.IsInducing.subtypeVal, Subtype.val_injective⟩
      equations := J
      range_coordinates := by
        rw [← hJ]
        ext x
        constructor
        · rintro ⟨u, rfl⟩
          exact ⟨u.val, u.property, rfl⟩
        · rintro ⟨u, hu, rfl⟩
          exact ⟨⟨u, hu⟩, rfl⟩
      mulLeftPolynomial := fun u => Q.mulLeftPolynomial u.val
      mulLeft_coordinates := fun u v => Q.mulLeft_coordinates u.val v.val
      mulRightPolynomial := fun u => Q.mulRightPolynomial u.val
      mulRight_coordinates := fun u v => Q.mulRight_coordinates u.val v.val
      invPolynomial := Q.invPolynomial
      inv_coordinates := fun u => Q.inv_coordinates u.val }

/-- The image of a homomorphism of affine polynomial groups over an algebraically
closed field is closed. The source only needs an affine presentation. -/
theorem isClosed_range [IsAlgClosed k] [Finite σ] [Finite τ]
    (P : AffinePresentation k σ G) (Q : AffinePolynomialGroup k τ H)
    (f : G →* H) (F : τ → MvPolynomial σ k)
    (hF : ∀ g, Q.coordinates (f g) = AffinePoint.polynomialMap F (P.coordinates g)) :
    IsClosed (Set.range f) := by
  letI := Q.separatelyContinuousMul
  letI := Q.continuousInv
  exact subgroup_isClosed_of_isConstructible f.range
    (P.isConstructible_range Q.toAffinePresentation f F hF)

/-- The coordinate image has polynomial equations. This is stronger than merely
being closed inside the target group's point space. -/
theorem exists_image_equations [IsAlgClosed k] [Finite σ] [Finite τ]
    (P : AffinePresentation k σ G) (Q : AffinePolynomialGroup k τ H)
    (f : G →* H) (F : τ → MvPolynomial σ k)
    (hF : ∀ g, Q.coordinates (f g) = AffinePoint.polynomialMap F (P.coordinates g)) :
    ∃ J : Ideal (MvPolynomial τ k),
      AffinePoint.polynomialMap F '' AffinePoint.zeros P.equations = AffinePoint.zeros J := by
  apply (AffinePoint.isClosed_iff_zeros _).mp
  rw [← P.coordinate_range_eq_polynomial_image Q.toAffinePresentation f F hF]
  exact Q.toAffinePresentation.isClosedEmbedding_coordinates.isClosedMap _
    (isClosed_range P Q f F hF)

/-- The closed image is cut out by equations that also contain every generic
image point over every specified extension field. The transfer uses
Nullstellensatz rather than an unsupported rational-point surjectivity claim. -/
theorem closed_image_with_generic_containment [IsAlgClosed k] [Finite σ] [Finite τ]
    {K : Type*} [Field K] [Algebra k K]
    (P : AffinePresentation k σ G) (Q : AffinePolynomialGroup k τ H)
    (f : G →* H) (F : τ → MvPolynomial σ k)
    (hF : ∀ g, Q.coordinates (f g) = AffinePoint.polynomialMap F (P.coordinates g)) :
    ∃ J : Ideal (MvPolynomial τ k),
      AffinePoint.polynomialMap F '' AffinePoint.zeros P.equations = AffinePoint.zeros J ∧
      ∀ x : σ → K, x ∈ zeroLocus K P.equations →
        (fun i => aeval x (F i)) ∈ zeroLocus K J := by
  obtain ⟨J, hJ⟩ := exists_image_equations P Q f F hF
  refine ⟨J, hJ, ?_⟩
  intro x hx q hq
  apply polynomial_image_relation_baseChange P.equations F q _ x hx
  intro y hy
  have hmem : AffinePoint.polynomialMap F (AffinePoint.ofFunction y) ∈ AffinePoint.zeros J := by
    rw [← hJ]
    exact ⟨AffinePoint.ofFunction y, hy, rfl⟩
  exact hmem q hq

end AffinePolynomialGroup

end

end EnvelopingIsomorphism.Descent
