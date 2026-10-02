import EnvelopingIsomorphism.Descent.ClosedImage.MatrixIsomorphisms

/-! # Closed graded image of the filtered isomorphism set

This is the finite-coordinate H3 statement, including the coset and the
extension-field generic containment required by H4.
-/

namespace EnvelopingIsomorphism.Descent.MatrixGroup

open Set Topology MvPolynomial

noncomputable section

variable {k n α : Type*} [Field k] [Fintype n] [DecidableEq n] [LinearOrder α]

theorem PreservesBilinear.mul
    {A B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)}
    {g h : Matrix.GeneralLinearGroup n k}
    (hg : PreservesBilinear B C g) (hh : PreservesBilinear A B h) :
    PreservesBilinear A C (g * h) := by
  intro x y
  rw [map_mul]
  change linearEquiv g (linearEquiv h (A x y)) =
    C (linearEquiv g (linearEquiv h x)) (linearEquiv g (linearEquiv h y))
  rw [hh, hg]

theorem PreservesBilinear.inv
    {B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)}
    {g : Matrix.GeneralLinearGroup n k} (hg : PreservesBilinear B C g) :
    PreservesBilinear C B g⁻¹ := by
  intro x y
  rw [map_inv]
  apply (linearEquiv g).injective
  change linearEquiv g ((linearEquiv g).symm (C x y)) =
    linearEquiv g (B ((linearEquiv g).symm x) ((linearEquiv g).symm y))
  rw [hg]
  simp

/-- The filtered isomorphism set, as a subset of the block triangular group. -/
def filteredIsomorphisms
    (B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (b : n → α) :
    Set (blockTriangularSubgroup (k := k) b) :=
  {g | PreservesBilinear B C g.val}

theorem filteredIsomorphism_diagonal_image_eq_coset
    (B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (b : n → α)
    (f₀ : blockTriangularSubgroup (k := k) b) (hf₀ : PreservesBilinear B C f₀.val) :
    diagonalHom b '' filteredIsomorphisms B C b =
      (fun h => h * diagonalHom b f₀) '' Set.range (filteredDiagonalHom C b) := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    let a := g * f₀⁻¹
    have ha : a.val ∈ filteredBilinearAutomorphisms C b :=
      ⟨(show PreservesBilinear B C g.val from hg).mul hf₀.inv, a.property⟩
    let u : filteredBilinearAutomorphisms C b := ⟨a.val, ha⟩
    refine ⟨filteredDiagonalHom C b u, ⟨u, rfl⟩, ?_⟩
    change diagonalHom b a * diagonalHom b f₀ = diagonalHom b g
    rw [← map_mul]
    simp [a]
  · rintro ⟨h, ⟨u, rfl⟩, rfl⟩
    let a : blockTriangularSubgroup (k := k) b := Subgroup.inclusion inf_le_right u
    refine ⟨a * f₀, ?_, ?_⟩
    · exact (show PreservesBilinear C C u.val from u.property.1).mul hf₀
    · exact map_mul (diagonalHom b) a f₀

theorem isClosed_filteredIsomorphism_diagonal_image [IsAlgClosed k]
    (B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (b : n → α)
    (f₀ : blockTriangularSubgroup (k := k) b) (hf₀ : PreservesBilinear B C f₀.val) :
    letI := topology (k := k) (n := n)
    IsClosed (diagonalHom b '' filteredIsomorphisms B C b) := by
  letI := topology (k := k) (n := n)
  letI := (groupPresentation (k := k) (n := n)).separatelyContinuousMul
  rw [filteredIsomorphism_diagonal_image_eq_coset B C b f₀ hf₀]
  exact isClosedMap_mul_right (diagonalHom b f₀) _ (isClosed_filteredDiagonalHom_range C b)

theorem filteredIsomorphism_polynomial_image_eq
    (B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (b : n → α) :
    AffinePoint.polynomialMap (diagonalPolynomial b) ''
      AffinePoint.zeros (filteredIsomorphismEquations B C b) =
        coordinates '' (diagonalHom b '' filteredIsomorphisms B C b) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxdet : x ∈ AffinePoint.zeros (equations (k := k) (n := n)) := by
      rw [filteredIsomorphismEquations, subgroupEquations, AffinePoint.zeros_sup] at hx
      exact hx.1
    obtain ⟨g, rfl⟩ := (range_coordinates (k := k) (n := n)).symm ▸ hxdet
    obtain ⟨hg, hb⟩ := (coordinates_mem_filteredIsomorphismEquations_iff B C b g).mp hx
    refine ⟨diagonalHom b ⟨g, hb⟩, ⟨⟨g, hb⟩, hg, rfl⟩, ?_⟩
    exact diagonalHom_coordinates b ⟨g, hb⟩
  · rintro ⟨z, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨coordinates g.val, ?_, (diagonalHom_coordinates b g).symm⟩
    exact (coordinates_mem_filteredIsomorphismEquations_iff B C b g.val).mpr ⟨hg, g.property⟩

/-- H3 in explicit finite matrix coordinates: the graded image is a closed coset
cut out by an ideal, and all extension-field generic image points satisfy that
same ideal. No scheme-theoretic image or smoothness premise is used. -/
theorem filteredIsomorphism_closed_image_with_generic_containment [IsAlgClosed k]
    {K : Type*} [Field K] [Algebra k K]
    (B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (b : n → α)
    (f₀ : blockTriangularSubgroup (k := k) b) (hf₀ : PreservesBilinear B C f₀.val) :
    ∃ J : Ideal (MvPolynomial (Coordinate n) k),
      coordinates '' (diagonalHom b '' filteredIsomorphisms B C b) = AffinePoint.zeros J ∧
      ∀ x : Coordinate n → K, x ∈ zeroLocus K (filteredIsomorphismEquations B C b) →
        (fun i => aeval x (diagonalPolynomial (k := k) b i)) ∈ zeroLocus K J := by
  letI := topology (k := k) (n := n)
  have hclosed := (affinePresentation (k := k) (n := n)).isClosedEmbedding_coordinates.isClosedMap _
    (isClosed_filteredIsomorphism_diagonal_image B C b f₀ hf₀)
  obtain ⟨J, hJ⟩ := (AffinePoint.isClosed_iff_zeros _).mp hclosed
  refine ⟨J, hJ, ?_⟩
  have himage : AffinePoint.polynomialMap (diagonalPolynomial b) ''
      AffinePoint.zeros (filteredIsomorphismEquations B C b) = AffinePoint.zeros J :=
    (filteredIsomorphism_polynomial_image_eq B C b).trans hJ
  intro x hx q hq
  apply polynomial_image_relation_baseChange (filteredIsomorphismEquations B C b)
    (diagonalPolynomial b) q _ x hx
  intro z hz
  have hmem : AffinePoint.polynomialMap (diagonalPolynomial b) (AffinePoint.ofFunction z) ∈
      AffinePoint.zeros J := by
    rw [← himage]
    exact ⟨AffinePoint.ofFunction z, hz, rfl⟩
  exact hmem q hq

/-- H3 starting only with an extension-field filtered isomorphism. A base-field
isomorphism needed to identify the coset is obtained by Nullstellensatz. -/
theorem filteredIsomorphism_closed_image_of_extension_point [IsAlgClosed k]
    {K : Type*} [Field K] [Algebra k K]
    (B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (b : n → α)
    (x : Coordinate n → K) (hx : x ∈ zeroLocus K (filteredIsomorphismEquations B C b)) :
    ∃ J : Ideal (MvPolynomial (Coordinate n) k),
      coordinates '' (diagonalHom b '' filteredIsomorphisms B C b) = AffinePoint.zeros J ∧
      ∀ y : Coordinate n → K, y ∈ zeroLocus K (filteredIsomorphismEquations B C b) →
        (fun i => aeval y (diagonalPolynomial (k := k) b i)) ∈ zeroLocus K J := by
  obtain ⟨z, hz⟩ := zeroLocus_nonempty_of_extensionPoint
    (filteredIsomorphismEquations B C b) x hx
  have hz' : AffinePoint.ofFunction z ∈ AffinePoint.zeros (filteredIsomorphismEquations B C b) := hz
  have hzdet : AffinePoint.ofFunction z ∈ AffinePoint.zeros (equations (k := k) (n := n)) := by
    rw [filteredIsomorphismEquations, subgroupEquations, AffinePoint.zeros_sup] at hz'
    exact hz'.1
  obtain ⟨g, hg⟩ := (range_coordinates (k := k) (n := n)).symm ▸ hzdet
  have hg' : coordinates g ∈ AffinePoint.zeros (filteredIsomorphismEquations B C b) := by
    rwa [hg]
  obtain ⟨hbracket, hflag⟩ := (coordinates_mem_filteredIsomorphismEquations_iff B C b g).mp hg'
  exact filteredIsomorphism_closed_image_with_generic_containment B C b ⟨g, hflag⟩ hbracket

end

end EnvelopingIsomorphism.Descent.MatrixGroup
