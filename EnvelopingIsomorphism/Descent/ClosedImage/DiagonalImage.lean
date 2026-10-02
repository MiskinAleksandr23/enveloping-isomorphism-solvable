import EnvelopingIsomorphism.Descent.ClosedImage.MatrixAutomorphisms

/-! # The closed image of the diagonal-block homomorphism -/

namespace EnvelopingIsomorphism.Descent.MatrixGroup

open Set Topology MvPolynomial

noncomputable section

variable {k n α : Type*} [Field k] [Fintype n] [DecidableEq n] [LinearOrder α]

def diagonalPart (b : n → α) (M : Matrix n n k) : Matrix n n k :=
  fun i j => if b i = b j then M i j else 0

omit [Fintype n] in
theorem diagonalPart_one (b : n → α) : diagonalPart b (1 : Matrix n n k) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [diagonalPart]
  · simp [diagonalPart, hij]

omit [DecidableEq n] in
theorem diagonalPart_mul (b : n → α) {M N : Matrix n n k}
    (hM : M.BlockTriangular b) (hN : N.BlockTriangular b) :
    diagonalPart b (M * N) = diagonalPart b M * diagonalPart b N := by
  ext i j
  change (if b i = b j then ∑ l, M i l * N l j else 0) =
    ∑ l, (if b i = b l then M i l else 0) * (if b l = b j then N l j else 0)
  by_cases hij : b i = b j
  · rw [if_pos hij]
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hil : b i = b l
    · rw [if_pos hil, if_pos (hil.symm.trans hij)]
    · rw [if_neg hil, zero_mul]
      rcases lt_or_gt_of_ne hil with hlt | hgt
      · rw [hN (hij ▸ hlt), mul_zero]
      · rw [hM hgt, zero_mul]
  · rw [if_neg hij]
    symm
    apply Finset.sum_eq_zero
    intro l hl
    by_cases hil : b i = b l
    · have hlj : b l ≠ b j := fun h => hij (hil.trans h)
      rw [if_neg hlj, mul_zero]
    · rw [if_neg hil, zero_mul]

omit [Fintype n] [DecidableEq n] in
theorem diagonalPart_blockTriangular (b : n → α) (M : Matrix n n k) :
    (diagonalPart b M).BlockTriangular b := by
  intro i j hij
  simp [diagonalPart, ne_of_gt hij]

theorem det_diagonalPart (b : n → α) {M : Matrix n n k} (hM : M.BlockTriangular b) :
    (diagonalPart b M).det = M.det := by
  rw [(diagonalPart_blockTriangular b M).det, hM.det]
  apply Finset.prod_congr rfl
  intro a ha
  congr 1
  ext i j
  change diagonalPart b M i.val j.val = M i.val j.val
  simp [diagonalPart, i.property, j.property]

/-- Taking diagonal blocks is a group homomorphism on block triangular matrices. -/
def diagonalHom (b : n → α) :
    blockTriangularSubgroup (k := k) b →* Matrix.GeneralLinearGroup n k where
  toFun g :=
    { val := diagonalPart b g.val.val
      inv := diagonalPart b (g⁻¹).val.val
      val_inv := by
        rw [← diagonalPart_mul b g.property (g⁻¹).property]
        change diagonalPart b ((g.val * g.val⁻¹).val) = 1
        rw [mul_inv_cancel, Units.val_one, diagonalPart_one]
      inv_val := by
        rw [← diagonalPart_mul b (g⁻¹).property g.property]
        change diagonalPart b ((g.val⁻¹ * g.val).val) = 1
        rw [inv_mul_cancel, Units.val_one, diagonalPart_one] }
  map_one' := Units.ext (diagonalPart_one b)
  map_mul' g h := Units.ext (diagonalPart_mul b g.property h.property)

def diagonalPolynomial (b : n → α) : Coordinate n → MvPolynomial (Coordinate n) k
  | none => X none
  | some (i, j) => if b i = b j then X (some (i, j)) else 0

theorem diagonalHom_coordinates (b : n → α)
    (g : blockTriangularSubgroup (k := k) b) :
    coordinates (diagonalHom b g) =
      AffinePoint.polynomialMap (diagonalPolynomial b) (coordinates g.val) := by
  apply funext
  intro i
  cases i with
  | none =>
      change (diagonalPart b g.val.val).det⁻¹ =
        aeval (coordinates g.val).toFunction (X none)
      rw [det_diagonalPart b g.property, aeval_X]
      rfl
  | some ij =>
      obtain ⟨i, j⟩ := ij
      change (if b i = b j then g.val.val i j else 0) =
        aeval (coordinates g.val).toFunction (if b i = b j then X (some (i, j)) else 0)
      split_ifs <;> simp only [aeval_X, map_zero]
      rfl

/-- The diagonal-block homomorphism on filtered bilinear-algebra automorphisms. -/
def filteredDiagonalHom
    (B : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (b : n → α) :
    filteredBilinearAutomorphisms B b →* Matrix.GeneralLinearGroup n k :=
  (diagonalHom b).comp (Subgroup.inclusion inf_le_right)

/-- The diagonal-block image of filtered Lie automorphisms is Zariski closed,
formulated for the underlying bilinear bracket. -/
theorem isClosed_filteredDiagonalHom_range [IsAlgClosed k]
    (B : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (b : n → α) :
    letI := topology (k := k) (n := n)
    IsClosed (Set.range (filteredDiagonalHom B b)) := by
  letI := topology (k := k) (n := n)
  exact AffinePolynomialGroup.isClosed_range
    (filteredAutomorphismPresentation B b).toAffinePresentation groupPresentation
    (filteredDiagonalHom B b) (diagonalPolynomial b)
    (fun g => diagonalHom_coordinates b (Subgroup.inclusion inf_le_right g))

/-- Concrete finite-matrix form of H3: the diagonal-block image has polynomial
equations, and these equations contain the diagonal image of every extension-field
point satisfying the explicit determinant, bracket, and flag equations. -/
theorem filteredDiagonal_closed_image_with_generic_containment [IsAlgClosed k]
    {K : Type*} [Field K] [Algebra k K]
    (B : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (b : n → α) :
    ∃ J : Ideal (MvPolynomial (Coordinate n) k),
      coordinates '' Set.range (filteredDiagonalHom B b) = AffinePoint.zeros J ∧
      ∀ x : Coordinate n → K, x ∈ zeroLocus K (subgroupEquations (filteredRelation B b)) →
        (fun i => aeval x (diagonalPolynomial (k := k) b i)) ∈ zeroLocus K J := by
  letI := topology (k := k) (n := n)
  let P := (filteredAutomorphismPresentation B b).toAffinePresentation
  have hF : ∀ g, groupPresentation.coordinates (filteredDiagonalHom B b g) =
      AffinePoint.polynomialMap (diagonalPolynomial b) (P.coordinates g) :=
    fun g => diagonalHom_coordinates b (Subgroup.inclusion inf_le_right g)
  obtain ⟨J, hJ, hgeneric⟩ := AffinePolynomialGroup.closed_image_with_generic_containment
    (K := K) P groupPresentation (filteredDiagonalHom B b) (diagonalPolynomial b) hF
  refine ⟨J, ?_, hgeneric⟩
  exact (P.coordinate_range_eq_polynomial_image groupPresentation.toAffinePresentation
    (filteredDiagonalHom B b) (diagonalPolynomial b) hF).trans hJ

end

end EnvelopingIsomorphism.Descent.MatrixGroup
