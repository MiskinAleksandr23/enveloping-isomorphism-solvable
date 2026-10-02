  import EnvelopingIsomorphism.Descent.ReesCoefficientScaling
import EnvelopingIsomorphism.Descent.NilradicalFlag
import EnvelopingIsomorphism.Poisson.FirstJetEquiv

/-! The actual generic original Lie matrix and its filtered polynomial equations.
All filtration preservation is derived from the nilradical, after constructing
the genuine generic Lie equivalence from the Rees matrix equations. -/

namespace EnvelopingIsomorphism.Descent

open Module MvPolynomial
open scoped TensorProduct BigOperators

noncomputable section

variable {k n L M : Type*} [Field k] [Fintype n] [DecidableEq n]
variable [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]

/-- The native Lie bracket expressed in a chosen finite coordinate basis. -/
def basisBracket (b : Basis n k L) : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k) :=
  ((LieAlgebra.ad k L).compl₁₂ b.equivFun.symm.toLinearMap
    b.equivFun.symm.toLinearMap).compr₂ b.equivFun.toLinearMap

theorem basisBracket_basis (b : Basis n k L) (i j r : n) :
    basisBracket b (Pi.single i 1) (Pi.single j 1) r = Poisson.structureCoeff b i j r := by
  simp [basisBracket, Poisson.structureCoeff, Basis.equivFun_symm_apply, Pi.single_apply]

theorem structureCoeff_baseChange (K : Type*) [Field K] [Algebra k K]
    (b : Basis n k L) (i j r : n) :
    Poisson.structureCoeff (b.baseChange K) i j r =
      algebraMap k K (Poisson.structureCoeff b i j r) := by
  simp [Poisson.structureCoeff, LieAlgebra.ExtendScalars.bracket_tmul, Algebra.smul_def]

namespace MatrixGroup

section Native

/-- A matrix preserving the coordinate brackets gives an equivalence of the
original native Lie algebras. -/
def nativeLieEquivOfMatrix (bL : Basis n k L) (bM : Basis n k M)
    (g : Matrix.GeneralLinearGroup n k)
    (hg : PreservesBilinear (basisBracket bL) (basisBracket bM) g) : L ≃ₗ⁅k⁆ M where
  __ := (bL.equivFun.trans (linearEquiv g)).trans bM.equivFun.symm
  map_lie' := by
    intro x y
    apply bM.equivFun.injective
    change bM.equivFun (bM.equivFun.symm (linearEquiv g (bL.equivFun ⁅x, y⁆))) =
      bM.equivFun ⁅bM.equivFun.symm (linearEquiv g (bL.equivFun x)),
        bM.equivFun.symm (linearEquiv g (bL.equivFun y))⁆
    rw [bM.equivFun.apply_symm_apply]
    have h := hg (bL.equivFun x) (bL.equivFun y)
    change linearEquiv g (bL.equivFun
      ⁅bL.equivFun.symm (bL.equivFun x), bL.equivFun.symm (bL.equivFun y)⁆) =
      bM.equivFun ⁅bM.equivFun.symm (linearEquiv g (bL.equivFun x)),
        bM.equivFun.symm (linearEquiv g (bL.equivFun y))⁆ at h
    simpa only [LinearEquiv.symm_apply_apply] using h

theorem nativeLieEquivOfMatrix_repr_basis (bL : Basis n k L) (bM : Basis n k M)
    (g : Matrix.GeneralLinearGroup n k)
    (hg : PreservesBilinear (basisBracket bL) (basisBracket bM) g) (i r : n) :
    bM.repr (nativeLieEquivOfMatrix bL bM g hg (bL i)) r = g.val r i := by
  change bM.equivFun (bM.equivFun.symm (linearEquiv g (bL.equivFun (bL i)))) r = _
  rw [bM.equivFun.apply_symm_apply]
  have hi : bL.equivFun (bL i) = Pi.single i 1 := by
    ext j
    simp [Basis.equivFun_apply, Pi.single_apply, eq_comm]
  rw [hi, linearEquiv_apply, Matrix.mulVec_single_one]
  rfl

/-- The prescribed diagonal identity gives the marked native coefficients,
including all lower-weight zero coefficients. -/
theorem nativeLieEquivOfMatrix_marked
    (bL : Basis n k L) (bM : Basis n k M) (weight : n → ℕ)
    (g : blockTriangularSubgroup (k := k) (fun i => OrderDual.toDual (weight i)))
    (hg : PreservesBilinear (basisBracket bL) (basisBracket bM) g.val)
    (hdiag : diagonalHom (fun i => OrderDual.toDual (weight i)) g = 1)
    (i r : n) (hweight : weight r ≤ weight i) :
    bM.repr (nativeLieEquivOfMatrix bL bM g.val hg (bL i)) r = if r = i then 1 else 0 := by
  rw [nativeLieEquivOfMatrix_repr_basis]
  rcases lt_or_eq_of_le hweight with hlt | heq
  · have hzero : g.val.val r i = 0 := g.property hlt
    have hne : r ≠ i := fun h => Nat.lt_irrefl _ (h ▸ hlt)
    simp [hzero, hne]
  · have h := congrArg (fun f : Matrix.GeneralLinearGroup n k => f.val r i) hdiag
    change (if OrderDual.toDual (weight r) = OrderDual.toDual (weight i) then g.val.val r i else 0) =
      (1 : Matrix n n k) r i at h
    have hd := congrArg OrderDual.toDual heq
    simpa only [if_pos hd, Matrix.one_apply] using h

end Native

section Equations

variable {K : Type*} [Field K] [Algebra k K]
variable {α : Type*} [LinearOrder α]

/-- A native invertible matrix with coefficient bracket equations and the flag
zeros is an extension-field point of the explicit H3 equation ideal. -/
theorem coordinates_mem_filtered_equations_of_coefficients
    (B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (b : n → α)
    (g : Matrix.GeneralLinearGroup n K)
    (hbracket : ∀ i j r,
      (∑ a, ∑ d, algebraMap k K (C (Pi.single a 1) (Pi.single d 1) r) *
        (g.val a i * g.val d j)) =
      ∑ d, algebraMap k K (B (Pi.single i 1) (Pi.single j 1) d) * g.val r d)
    (hflag : g.val.BlockTriangular b) :
    (coordinates g).toFunction ∈ zeroLocus K (filteredIsomorphismEquations B C b) := by
  have hdet : aeval (coordinates g).toFunction (genericMatrix (k := k) (n := n)).det =
      g.val.det := by
    rw [AlgHom.map_det]
    congr 1
    ext i j
    simp [genericMatrix, coordinates, AffinePoint.toFunction, AffinePoint.ofFunction]
  change filteredIsomorphismEquations B C b ≤
    RingHom.ker (aeval (coordinates g).toFunction).toRingHom
  rw [filteredIsomorphismEquations, subgroupEquations, sup_le_iff]
  constructor
  · rw [equations, Ideal.span_le]
    intro p hp
    rcases hp with rfl
    change aeval (coordinates g).toFunction determinantRelation = 0
    simp only [determinantRelation, map_sub, map_mul, aeval_X, map_one, hdet]
    change g.val.det⁻¹ * g.val.det - 1 = 0
    rw [inv_mul_cancel₀ g.det_ne_zero, sub_self]
  · apply Ideal.span_le.mpr
    rintro p ⟨q, rfl⟩
    cases q with
    | inl q =>
      obtain ⟨r, i, j⟩ := q
      change aeval (coordinates g).toFunction (isomorphismRelation B C r i j) = 0
      simp only [isomorphismRelation, map_sub, map_sum, map_mul, aeval_X, aeval_C]
      apply sub_eq_zero.mpr
      simpa only [coordinates, AffinePoint.toFunction, AffinePoint.ofFunction,
        mul_comm, mul_left_comm, mul_assoc] using (hbracket i j r).symm
    | inr q =>
      change aeval (coordinates g).toFunction (flagRelation (k := k) b q) = 0
      rw [flagRelation, aeval_X]
      exact hflag q.property

end Equations

section Generic

variable {E : Type*} [Field E] [Algebra k E]

local instance laurentBaseModule : Module k (LaurentSeries E) := Algebra.toModule

/-- The generic matrix is a genuine Lie equivalence of the original scalar-extended algebras. -/
def originalGenericLieEquiv
    (bL : Basis n k L) (bM : Basis n k M) (weight : n → ℕ)
    (hcL : ∀ i j r, Poisson.structureCoeff bL i j r ≠ 0 → weight i + weight j ≤ weight r)
    (hcM : ∀ i j r, Poisson.structureCoeff bM i j r ≠ 0 → weight i + weight j ≤ weight r)
    (P : Matrix.GeneralLinearGroup n (PowerSeries E))
    (hP : ∀ i j r,
      (∑ a, ∑ b, reesCoefficient weight (Poisson.structureCoeff bM) a b r * (P.val a i * P.val b j)) =
      ∑ d, reesCoefficient weight (Poisson.structureCoeff bL) i j d * P.val r d) :
    (LaurentSeries E ⊗[k] L) ≃ₗ⁅LaurentSeries E⁆ (LaurentSeries E ⊗[k] M) :=
  Poisson.lieEquivOfStructureEquations (bL.baseChange (LaurentSeries E))
    (bM.baseChange (LaurentSeries E)) (originalGenericMatrix weight P).val
    (originalGenericMatrix weight P).det.isUnit
    (by
      intro i j r
      simpa only [structureCoeff_baseChange] using
        originalGenericMatrix_structure_equation weight (Poisson.structureCoeff bL)
          (Poisson.structureCoeff bM) hcL hcM P hP i j r)

theorem repr_originalGenericLieEquiv_basis
    (bL : Basis n k L) (bM : Basis n k M) (weight : n → ℕ)
    (hcL : ∀ i j r, Poisson.structureCoeff bL i j r ≠ 0 → weight i + weight j ≤ weight r)
    (hcM : ∀ i j r, Poisson.structureCoeff bM i j r ≠ 0 → weight i + weight j ≤ weight r)
    (P : Matrix.GeneralLinearGroup n (PowerSeries E))
    (hP : ∀ i j r,
      (∑ a, ∑ b, reesCoefficient weight (Poisson.structureCoeff bM) a b r * (P.val a i * P.val b j)) =
      ∑ d, reesCoefficient weight (Poisson.structureCoeff bL) i j d * P.val r d)
    (i r : n) :
    (bM.baseChange (LaurentSeries E)).repr
      (originalGenericLieEquiv bL bM weight hcL hcM P hP (bL.baseChange (LaurentSeries E) i)) r =
      (originalGenericMatrix weight P).val r i := by
  change (bM.baseChange (LaurentSeries E)).repr
    (Poisson.firstJetLinearMap (bL.baseChange (LaurentSeries E))
      (bM.baseChange (LaurentSeries E)) (originalGenericMatrix weight P).val
        (bL.baseChange (LaurentSeries E) i)) r = _
  rw [Poisson.firstJetLinearMap_basis]
  simp [Finsupp.single_apply, Algebra.smul_def]

variable [CharZero k] [Module.Finite k L] [Module.Finite k M]

/-- H1 in the coordinates consumed by H3: a Rees Lie matrix satisfies the
original bracket equations and the nilradical flag equations after Laurent scaling. -/
theorem originalGenericMatrix_filtered_equations
    (bL : Basis n k L) (bM : Basis n k M) (weight : n → ℕ)
    (hadaptL : ∀ d, Submodule.span k (bL '' {i | d ≤ weight i}) =
      (Identification.lowerCentralFiltration (Lie.nilradical k L) d).toSubmodule)
    (hadaptM : ∀ d, Submodule.span k (bM '' {i | d ≤ weight i}) =
      (Identification.lowerCentralFiltration (Lie.nilradical k M) d).toSubmodule)
    (hcL : ∀ i j r, Poisson.structureCoeff bL i j r ≠ 0 → weight i + weight j ≤ weight r)
    (hcM : ∀ i j r, Poisson.structureCoeff bM i j r ≠ 0 → weight i + weight j ≤ weight r)
    (P : Matrix.GeneralLinearGroup n (PowerSeries E))
    (hP : ∀ i j r,
      (∑ a, ∑ b, reesCoefficient weight (Poisson.structureCoeff bM) a b r * (P.val a i * P.val b j)) =
      ∑ d, reesCoefficient weight (Poisson.structureCoeff bL) i j d * P.val r d) :
    (coordinates (originalGenericMatrix weight P)).toFunction ∈ zeroLocus (LaurentSeries E)
      (filteredIsomorphismEquations (basisBracket bL) (basisBracket bM)
        (fun i => OrderDual.toDual (weight i))) := by
  apply coordinates_mem_filtered_equations_of_coefficients
  · intro i j r
    simpa only [basisBracket_basis] using originalGenericMatrix_structure_equation weight
      (Poisson.structureCoeff bL) (Poisson.structureCoeff bM) hcL hcM P hP i j r
  · intro r i hri
    change weight r < weight i at hri
    rw [← repr_originalGenericLieEquiv_basis bL bM weight hcL hcM P hP i r]
    exact coefficient_eq_zero_of_lt_weight (LaurentSeries E) bL bM weight hadaptL hadaptM
      (originalGenericLieEquiv bL bM weight hcL hcM P hP) r i hri

/-- H1–H4: the actual marked Rees matrix yields a filtered original isomorphism
over the algebraically closed base, with the prescribed identity graded map. -/
theorem exists_marked_isomorphism_of_rees_matrix [IsAlgClosed k]
    (bL : Basis n k L) (bM : Basis n k M) (weight : n → ℕ)
    (hadaptL : ∀ d, Submodule.span k (bL '' {i | d ≤ weight i}) =
      (Identification.lowerCentralFiltration (Lie.nilradical k L) d).toSubmodule)
    (hadaptM : ∀ d, Submodule.span k (bM '' {i | d ≤ weight i}) =
      (Identification.lowerCentralFiltration (Lie.nilradical k M) d).toSubmodule)
    (hcL : ∀ i j r, Poisson.structureCoeff bL i j r ≠ 0 → weight i + weight j ≤ weight r)
    (hcM : ∀ i j r, Poisson.structureCoeff bM i j r ≠ 0 → weight i + weight j ≤ weight r)
    (P : Matrix.GeneralLinearGroup n (PowerSeries E))
    (hzero : P.val.map PowerSeries.constantCoeff = 1)
    (hP : ∀ i j r,
      (∑ a, ∑ b, reesCoefficient weight (Poisson.structureCoeff bM) a b r * (P.val a i * P.val b j)) =
      ∑ d, reesCoefficient weight (Poisson.structureCoeff bL) i j d * P.val r d) :
    ∃ f : blockTriangularSubgroup (k := k) (fun i => OrderDual.toDual (weight i)),
      PreservesBilinear (basisBracket bL) (basisBracket bM) f.val ∧
        diagonalHom (fun i => OrderDual.toDual (weight i)) f = 1 :=
  marked_isomorphism_of_originalGenericMatrix (basisBracket bL) (basisBracket bM) weight P hzero
    (originalGenericMatrix_filtered_equations bL bM weight hadaptL hadaptM hcL hcM P hP)

end Generic

end MatrixGroup

end

end EnvelopingIsomorphism.Descent
