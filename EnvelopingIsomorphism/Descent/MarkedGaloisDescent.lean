import EnvelopingIsomorphism.Descent.GaloisLieAction
import EnvelopingIsomorphism.Descent.WeightedMarkedMap
import EnvelopingIsomorphism.Descent.MarkedMatrixPoint
import EnvelopingIsomorphism.FieldTheory.FiniteGaloisPoint

/-! Concrete marked Galois descent for finite-dimensional native Lie algebras.
The original extension field may be transcendental or unrelated to an algebraic closure. -/

namespace EnvelopingIsomorphism.Descent

open Module
open scoped TensorProduct BigOperators

noncomputable section

variable {k K E n L M : Type*} [Field k] [CharZero k]
variable [Field K] [Algebra k K] [Field E] [Algebra k E]
variable [Fintype n] [DecidableEq n]
variable [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]

open GaloisLieAction

omit [CharZero k] [DecidableEq n] in
theorem lieEquiv_structure_equation (bL : Basis n k L) (bM : Basis n k M)
    (f : L ≃ₗ⁅k⁆ M) (i j r : n) :
    (∑ a, ∑ b, Poisson.structureCoeff bM a b r *
      (bM.repr (f (bL i)) a * bM.repr (f (bL j)) b)) =
      ∑ d, Poisson.structureCoeff bL i j d * bM.repr (f (bL d)) r := by
  have h := congrArg (fun z => bM.repr z r) (f.map_lie (bL i) (bL j))
  rw [← bL.sum_repr ⁅bL i, bL j⁆] at h
  rw [← bM.sum_repr (f (bL i)), ← bM.sum_repr (f (bL j))] at h
  simp only [map_sum, map_smul, sum_lie_sum, smul_lie, lie_smul] at h
  simpa [Poisson.structureCoeff, mul_comm, mul_left_comm, mul_assoc] using h.symm

omit [CharZero k] in
theorem galois_preserves_basisWeightFiltration (b : Basis n k L) (weight : n → ℕ)
    (σ : K ≃ₐ[k] K) (d : ℕ) (x : K ⊗[k] L)
    (hx : x ∈ (basisWeightFiltration (b.baseChange K) weight).step d) :
    (action k K L).equiv σ x ∈ (basisWeightFiltration (b.baseChange K) weight).step d := by
  apply (mem_basisWeightFiltration_iff (b.baseChange K) weight d _).mpr
  intro i hi
  rw [basis_repr_action, (mem_basisWeightFiltration_iff _ _ _ _).mp hx i hi, map_zero]

omit [CharZero k] [Fintype n] in
theorem galois_isomAction_marked (bL : Basis n k L) (bM : Basis n k M) (weight : n → ℕ)
    (f : (K ⊗[k] L) ≃ₗ⁅K⁆ (K ⊗[k] M))
    (hf : IsMarkedMap (bL.baseChange K) (bM.baseChange K) weight f.toLinearMap)
    (σ : K ≃ₐ[k] K) :
    IsMarkedMap (bL.baseChange K) (bM.baseChange K) weight
      ((action k K L).isomAction (action k K M) (fun _ => rfl) σ f).toLinearMap := by
  intro i r hri
  have hi : ((action k K L).equiv σ).symm (bL.baseChange K i) = bL.baseChange K i := by
    apply ((action k K L).equiv σ).injective
    rw [LinearEquiv.apply_symm_apply, basis_fixed]
  change (bM.baseChange K).repr
    ((action k K M).equiv σ (f (((action k K L).equiv σ).symm (bL.baseChange K i)))) r = _
  have hfi := hf i r hri
  change (bM.baseChange K).repr (f (bL.baseChange K i)) r = _ at hfi
  rw [hi, basis_repr_action, hfi]
  split_ifs <;> simp

/-- The marked equivalence descends over a finite Galois field. All actions,
fixed-vector descriptions, filtration stability and cocycle membership are constructed. -/
theorem exists_marked_lieEquiv_of_finiteGalois
    [FiniteDimensional k K] [IsGalois k K]
    (bL : Basis n k L) (bM : Basis n k M) (weight : n → ℕ)
    (f : (K ⊗[k] L) ≃ₗ⁅K⁆ (K ⊗[k] M))
    (hf : IsMarkedMap (bL.baseChange K) (bM.baseChange K) weight f.toLinearMap) :
    ∃ g : L ≃ₗ⁅k⁆ M, IsMarkedMap bL bM weight g.toLinearMap := by
  letI : CharZero K := Algebra.charZero_of_charZero k K
  letI : LieAlgebra ℚ (K ⊗[k] M) := rationalLieAlgebra K (K ⊗[k] M)
  letI : Fintype (K ≃ₐ[k] K) := Fintype.ofFinite _
  let F := basisWeightFiltration (bM.baseChange K) weight
  have hcocycle : ∀ σ, (action k K L).isomCocycle (action k K M) (fun _ => rfl) f σ ∈
      F.automorphismSubgroup 0 := by
    intro σ
    exact isomDifference_mem_of_marked (bL.baseChange K) (bM.baseChange K) weight f
      ((action k K L).isomAction (action k K M) (fun _ => rfl) σ f) hf
      (galois_isomAction_marked bL bM weight f hf σ)
  obtain ⟨u, hu, g, hg⟩ := (action k K L).exists_descended_marked_isom (action k K M)
    (fun _ => rfl) k (embedding k K L) (embedding k K M)
    (embedding_injective k K L) (embedding_injective k K M)
    (embedding_range_iff_fixed bL) (embedding_range_iff_fixed bM)
    F (galois_preserves_basisWeightFiltration bM weight) f hcocycle
  refine ⟨g, ?_⟩
  have hcorrected := marked_postcompose (bL.baseChange K) (bM.baseChange K) weight
    f.toLinearMap hf u.toLinearMap hu
  intro i r hri
  apply (FaithfulSMul.algebraMap_injective k K)
  change algebraMap k K (bM.repr (g (bL i)) r) = algebraMap k K (if r = i then 1 else 0)
  rw [← basis_repr_embedding (K := K) bM (g (bL i)) r, hg]
  have h := hcorrected i r hri
  change (bM.baseChange K).repr (u (f (bL.baseChange K i))) r = _ at h
  rw [embedding_apply, ← Basis.baseChange_apply]
  rw [h]
  split_ifs <;> simp

namespace MatrixGroup

/-- Decode a marked matrix over a finite Galois field to a native Lie equivalence,
then apply the concrete Galois descent theorem. -/
theorem exists_marked_lieEquiv_of_finiteGalois_matrix
    [FiniteDimensional k K] [IsGalois k K]
    (bL : Basis n k L) (bM : Basis n k M) (weight : n → ℕ)
    (P : Matrix n n K) (hmark : IsMarkedMatrix weight P)
    (hbracket : ∀ i j r,
      (∑ a, ∑ b, algebraMap k K (Poisson.structureCoeff bM a b r) * (P a i * P b j)) =
        ∑ d, algebraMap k K (Poisson.structureCoeff bL i j d) * P r d) :
    ∃ g : L ≃ₗ⁅k⁆ M, IsMarkedMap bL bM weight g.toLinearMap := by
  have hdet : IsUnit P.det := by rw [marked_matrix_det weight P hmark]; exact isUnit_one
  have hcoeff : ∀ i j r,
      (∑ a, ∑ b, Poisson.structureCoeff (bM.baseChange K) a b r * (P a i * P b j)) =
        ∑ d, Poisson.structureCoeff (bL.baseChange K) i j d * P r d := by
    simpa only [structureCoeff_baseChange] using hbracket
  let f := Poisson.lieEquivOfStructureEquations (bL.baseChange K) (bM.baseChange K) P hdet hcoeff
  apply exists_marked_lieEquiv_of_finiteGalois bL bM weight f
  intro i r hri
  change (bM.baseChange K).repr
    (Poisson.firstJetLinearMap (bL.baseChange K) (bM.baseChange K) P (bL.baseChange K i)) r = _
  rw [Poisson.firstJetLinearMap_basis]
  simpa [Algebra.smul_def, Finsupp.single_apply] using hmark i r hri

/-- A marked Lie matrix over any extension field descends to a marked native
Lie equivalence over the original characteristic-zero field. No algebraicity of
the original extension, or action/cohomology premise, is required. -/
theorem exists_marked_lieEquiv_of_extension_matrix
    (bL : Basis n k L) (bM : Basis n k M) (weight : n → ℕ)
    (P : Matrix n n E) (hmark : IsMarkedMatrix weight P)
    (hbracket : ∀ i j r,
      (∑ a, ∑ b, algebraMap k E (Poisson.structureCoeff bM a b r) * (P a i * P b j)) =
        ∑ d, algebraMap k E (Poisson.structureCoeff bL i j d) * P r d) :
    ∃ g : L ≃ₗ⁅k⁆ M, IsMarkedMap bL bM weight g.toLinearMap := by
  have hx := markedMatrixCoordinates_mem (basisBracket bL) (basisBracket bM) weight P hmark
    (by simpa only [basisBracket_basis] using hbracket)
  obtain ⟨F, y, hy⟩ := FieldTheory.exists_finiteGaloisPoint_of_point
    (weightedMarkedEquations (basisBracket bL) (basisBracket bM) weight)
    (markedMatrixCoordinates P) hx
  apply exists_marked_lieEquiv_of_finiteGalois_matrix (K := F) bL bM weight
    (fun r i => y (some (r, i)))
    (marked_point_matrix_marked (basisBracket bL) (basisBracket bM) weight y hy)
  intro i j r
  simpa only [basisBracket_basis] using
    marked_point_matrix_bracket (basisBracket bL) (basisBracket bM) weight y hy i j r

end MatrixGroup

/-- Native form of marked descent from an arbitrary extension field. This
connects directly to the marked native Lie equivalence produced by H4. -/
theorem exists_marked_lieEquiv_of_extension
    (bL : Basis n k L) (bM : Basis n k M) (weight : n → ℕ)
    (f : (E ⊗[k] L) ≃ₗ⁅E⁆ (E ⊗[k] M))
    (hf : IsMarkedMap (bL.baseChange E) (bM.baseChange E) weight f.toLinearMap) :
    ∃ g : L ≃ₗ⁅k⁆ M, IsMarkedMap bL bM weight g.toLinearMap := by
  apply MatrixGroup.exists_marked_lieEquiv_of_extension_matrix bL bM weight
    (fun r i => (bM.baseChange E).repr (f (bL.baseChange E i)) r)
  · exact hf
  · intro i j r
    simpa only [structureCoeff_baseChange] using
      lieEquiv_structure_equation (bL.baseChange E) (bM.baseChange E) f i j r

end

end EnvelopingIsomorphism.Descent
