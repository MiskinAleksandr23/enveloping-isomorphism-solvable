import EnvelopingIsomorphism.Descent.GenericLieMatrix
import EnvelopingIsomorphism.Rees.Family

/-! The H1–H4 specialization theorem at the native Rees-family first-jet boundary. -/

namespace EnvelopingIsomorphism.Descent

open Module
open scoped BigOperators

noncomputable section

variable {k E n L M : Type*} [Field k] [Field E] [Algebra k E]
variable [Fintype n] [DecidableEq n]
variable [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]

namespace MatrixGroup

theorem map_rees_family_coefficient {b : Basis n k L} (d : Rees.WeightData b) (i j r : n) :
    algebraMap (Polynomial k) (PowerSeries E) (d.coeff i j r) =
      reesCoefficient d.weight (Poisson.structureCoeff b) i j r := by
  simp [Rees.WeightData.coeff, reesCoefficient, Poisson.structureCoeff,
    PowerSeries.algebraMap_apply', PowerSeries.algebraMap_apply]

theorem family_structureCoeff_eq_reesCoefficient {b : Basis n k L}
    (d : Rees.WeightData b) (i j r : n) :
    Poisson.structureCoeff ((Rees.Family.basis d).baseChange (PowerSeries E)) i j r =
      reesCoefficient d.weight (Poisson.structureCoeff b) i j r := by
  rw [Poisson.structureCoeff, Rees.Family.baseChange_structureCoeff,
    map_rees_family_coefficient]

variable [CharZero k] [IsAlgClosed k] [Module.Finite k L] [Module.Finite k M]

/-- The marked first-jet matrix between the actual scalar-extended Rees Lie
families produces a filtered isomorphism of the original coordinate Lie algebras.
The input matrix is not required to come bundled as a unit: its marking proves invertibility. -/
theorem exists_marked_isomorphism_of_family_matrix
    (bL : Basis n k L) (bM : Basis n k M)
    (dL : Rees.WeightData bL) (dM : Rees.WeightData bM)
    (hweight : dM.weight = dL.weight)
    (hadaptL : ∀ d, Submodule.span k (bL '' {i | d ≤ dL.weight i}) =
      (Identification.lowerCentralFiltration (Lie.nilradical k L) d).toSubmodule)
    (hadaptM : ∀ d, Submodule.span k (bM '' {i | d ≤ dL.weight i}) =
      (Identification.lowerCentralFiltration (Lie.nilradical k M) d).toSubmodule)
    (P : Matrix n n (PowerSeries E))
    (hzero : P.map PowerSeries.constantCoeff = 1)
    (hP : ∀ i j r,
      (∑ a, ∑ b,
        Poisson.structureCoeff ((Rees.Family.basis dM).baseChange (PowerSeries E)) a b r *
          (P a i * P b j)) =
      ∑ d, Poisson.structureCoeff ((Rees.Family.basis dL).baseChange (PowerSeries E)) i j d *
        P r d) :
    ∃ f : blockTriangularSubgroup (k := k) (fun i => OrderDual.toDual (dL.weight i)),
      PreservesBilinear (basisBracket bL) (basisBracket bM) f.val ∧
        diagonalHom (fun i => OrderDual.toDual (dL.weight i)) f = 1 := by
  let g : Matrix.GeneralLinearGroup n (PowerSeries E) :=
    Matrix.GeneralLinearGroup.mk'' P (Poisson.isUnit_det_of_constantMatrix_eq_one P hzero)
  have hcoeffM : ∀ i j r, Poisson.structureCoeff bM i j r ≠ 0 →
      dL.weight i + dL.weight j ≤ dL.weight r := by
    simpa only [← hweight, Poisson.structureCoeff] using dM.compatible
  apply exists_marked_isomorphism_of_rees_matrix bL bM dL.weight hadaptL hadaptM
    dL.compatible hcoeffM g hzero
  intro i j r
  change (∑ a, ∑ b, reesCoefficient dL.weight (Poisson.structureCoeff bM) a b r *
    (P a i * P b j)) = ∑ d, reesCoefficient dL.weight (Poisson.structureCoeff bL) i j d * P r d
  simpa only [family_structureCoeff_eq_reesCoefficient, hweight] using hP i j r

/-- Native Lie-equivalence form of H1–H4. The coefficient condition states that
the equivalence induces the specified identity on every associated-graded layer. -/
theorem exists_marked_native_isomorphism_of_family_matrix
    (bL : Basis n k L) (bM : Basis n k M)
    (dL : Rees.WeightData bL) (dM : Rees.WeightData bM)
    (hweight : dM.weight = dL.weight)
    (hadaptL : ∀ d, Submodule.span k (bL '' {i | d ≤ dL.weight i}) =
      (Identification.lowerCentralFiltration (Lie.nilradical k L) d).toSubmodule)
    (hadaptM : ∀ d, Submodule.span k (bM '' {i | d ≤ dL.weight i}) =
      (Identification.lowerCentralFiltration (Lie.nilradical k M) d).toSubmodule)
    (P : Matrix n n (PowerSeries E))
    (hzero : P.map PowerSeries.constantCoeff = 1)
    (hP : ∀ i j r,
      (∑ a, ∑ b,
        Poisson.structureCoeff ((Rees.Family.basis dM).baseChange (PowerSeries E)) a b r *
          (P a i * P b j)) =
      ∑ d, Poisson.structureCoeff ((Rees.Family.basis dL).baseChange (PowerSeries E)) i j d *
        P r d) :
    ∃ f : L ≃ₗ⁅k⁆ M, ∀ i r, dL.weight r ≤ dL.weight i →
      bM.repr (f (bL i)) r = if r = i then 1 else 0 := by
  obtain ⟨g, hg, hdiag⟩ := exists_marked_isomorphism_of_family_matrix
    bL bM dL dM hweight hadaptL hadaptM P hzero hP
  exact ⟨nativeLieEquivOfMatrix bL bM g.val hg,
    nativeLieEquivOfMatrix_marked bL bM dL.weight g hg hdiag⟩

end MatrixGroup

end

end EnvelopingIsomorphism.Descent
