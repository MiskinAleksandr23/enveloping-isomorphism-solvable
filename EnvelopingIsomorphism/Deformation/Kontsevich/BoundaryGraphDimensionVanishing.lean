import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphFaceFactorization
import Mathlib.LinearAlgebra.Determinant

/-! The actual finite real-cluster face vanishes unless the internal edge degree matches its shape dimension. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphDimensionVanishing

open scoped BigOperators Classical

/-- A determinant term can be nonzero only if its permutation bijects the two
selected subsets. Unequal block cardinalities therefore force the determinant to vanish. -/
theorem det_eq_zero_of_block_card_ne {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Matrix ι ι R) (S T : Finset ι) (hcard : S.card ≠ T.card)
    (hst : ∀ i ∈ S, ∀ j ∉ T, M i j = 0)
    (hts : ∀ i ∉ S, ∀ j ∈ T, M i j = 0) : M.det = 0 := by
  rw [Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro σ hσ
  suffices hp : (∏ j, M (σ j) j) = 0 by simp [hp]
  by_contra hp
  have hentry (j : ι) : M (σ j) j ≠ 0 := by
    intro hj
    exact hp (Finset.prod_eq_zero (Finset.mem_univ j) hj)
  have hmem (j : ι) : σ j ∈ S ↔ j ∈ T := by
    constructor
    · intro hs
      by_contra ht
      exact hentry j (hst (σ j) hs j ht)
    · intro ht
      by_contra hs
      exact hentry j (hts (σ j) hs j ht)
  have himage : T.image σ = S := by
    ext x
    constructor
    · rintro hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact (hmem j).mpr hj
    · intro hx
      obtain ⟨j, rfl⟩ := σ.surjective x
      exact Finset.mem_image.mpr ⟨j, (hmem j).mp hx, rfl⟩
  have hc := congrArg Finset.card himage
  rw [Finset.card_image_of_injective _ σ.injective] at hc
  exact hcard hc.symm

private def firstRows (r s : ℕ) : Finset (Fin (r + s)) :=
  Finset.univ.image (Fin.castAdd s : Fin r → Fin (r + s))

private theorem card_firstRows (r s : ℕ) : (firstRows r s).card = r := by
  rw [firstRows, Finset.card_image_of_injective _ (Fin.castAdd_injective r s)]
  exact Fintype.card_fin r

private theorem firstRows_inl (r s : ℕ) (j : Fin r) :
    finSumFinEquiv (Sum.inl j) ∈ firstRows r s := by
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

private theorem firstRows_not_inr (r s : ℕ) (j : Fin s) :
    finSumFinEquiv (Sum.inr j) ∉ firstRows r s := by
  rintro hj
  obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hj
  have h := congrArg Fin.val he
  simp only [Fin.val_castAdd, finSumFinEquiv_apply_right, Fin.val_natAdd] at h
  omega

section Covectors

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {r s : ℕ}

/-- The genuine covector evaluation matrix has unequal diagonal blocks whenever
the first-factor covector count differs from the first tangent count. -/
theorem ofCovectors_productVectors_eq_zero
    (α : Fin (r + s) → (E × F) →L[ℝ] ℝ) (T : Finset (Fin (r + s)))
    (v : Fin r → E) (w : Fin s → F) (hcard : T.card ≠ r)
    (hfirst : ∀ j ∈ T, ∀ y : F, α j (0, y) = 0)
    (hsecond : ∀ j ∉ T, ∀ x : E, α j (x, 0) = 0) :
    GraphFormProduct.ofCovectors α (GraphFormProduct.productVectors v w) = 0 := by
  rw [GraphFormProduct.ofCovectors_apply]
  apply det_eq_zero_of_block_card_ne _ (firstRows r s) T
  · simpa only [card_firstRows] using hcard.symm
  · intro i hi j hj
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    cases i with
    | inl i =>
        simpa only [GraphFormProduct.productVectors, Equiv.symm_apply_apply, Sum.elim_inl] using
          hsecond j hj (v i)
    | inr i => exact False.elim (firstRows_not_inr r s i hi)
  · intro i hi j hj
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    cases i with
    | inl i => exact False.elim (hi (firstRows_inl r s i))
    | inr i =>
        simpa only [GraphFormProduct.productVectors, Equiv.symm_apply_apply, Sum.elim_inr] using
          hfirst j hj (w i)

/-- For full bases, the entire actual top alternating form vanishes, in every tangent tuple. -/
theorem ofCovectors_eq_zero_of_block_card_ne
    (α : Fin (r + s) → (E × F) →L[ℝ] ℝ) (T : Finset (Fin (r + s)))
    (v : Module.Basis (Fin r) ℝ E) (w : Module.Basis (Fin s) ℝ F) (hcard : T.card ≠ r)
    (hfirst : ∀ j ∈ T, ∀ y : F, α j (0, y) = 0)
    (hsecond : ∀ j ∉ T, ∀ x : E, α j (x, 0) = 0) :
    GraphFormProduct.ofCovectors α = 0 := by
  let B := (v.prod w).reindex finSumFinEquiv
  have hB : ⇑B = GraphFormProduct.productVectors v w := by
    funext i
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    cases i <;> simp [B, GraphFormProduct.productVectors, Module.Basis.prod_apply]
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  apply (AlternatingMap.map_basis_eq_zero_iff B _).mp
  change GraphFormProduct.ofCovectors α B = 0
  rw [hB]
  exact ofCovectors_productVectors_eq_zero α T v w hcard hfirst hsecond

end Covectors

open Configuration BoundaryGraphFaceFactorization

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

/-- Without any matching-count or no-outgoing hypothesis, an incorrect internal
edge count kills the entire actual top form restricted to the product face. -/
theorem graphForm_face_eq_zero_of_internal_count_ne
    (edges : Fin (shapeDegree a S l u + coarseDegree i S l u) → Edge n m)
    (hcount : Fintype.card {q // (edges q).1 ∈ S} ≠ shapeDegree a S l u)
    (hloop : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1)
    (z : ShapeCoordinates a S l u × CoarseCoordinates i S l u)
    (hy : (faceProductEmbedding z).OpenConditions l u) :
    (graphForm (l := l) (u := u) edges (faceProductEmbedding z)).compContinuousLinearMap
      (faceProductEmbedding (l := l) (u := u)) = 0 := by
  by_cases hnout : ∀ q, (edges q).1 ∈ S → boundaryClusterCollapses S l u (Sum.inl (edges q).2)
  · let T : Finset (Fin (shapeDegree a S l u + coarseDegree i S l u)) :=
      Finset.univ.filter (fun q => (edges q).1 ∈ S)
    have hc : Fintype.card {q // (edges q).1 ∈ S} = T.card :=
      Fintype.card_of_subtype T (fun q => by simp [T])
    rw [graphForm, ofCovectors_comp]
    apply ofCovectors_eq_zero_of_block_card_ne _ T
      (GraphForms.realBasis (shapeN a S) (shapeM l u))
      (GraphForms.realBasis (coarseN i S) (outsideM l u + 1))
    · exact fun h => hcount (hc.trans h)
    · intro q hq v
      have hs : (edges q).1 ∈ S := (Finset.mem_filter.mp hq).2
      have h := edgeLinear_internal z hy (edges q) hs (hnout q hs)
      simpa using congrArg
        (fun f : (ShapeCoordinates a S l u × CoarseCoordinates i S l u) →L[ℝ] ℝ => f (0, v)) h
    · intro q hq v
      have hs : (edges q).1 ∉ S := by simpa [T] using hq
      have h := edgeLinear_external z hy (edges q) (hloop q) hs
      simpa using congrArg
        (fun f : (ShapeCoordinates a S l u × CoarseCoordinates i S l u) →L[ℝ] ℝ => f (v, 0)) h
  · push Not at hnout
    obtain ⟨q, hs, ht⟩ := hnout
    exact graphForm_face_eq_zero_of_outgoing edges q (hloop q) hs ht z hy

/-- The same whole-form vanishing in the inherited native free face coordinates. -/
theorem graphForm_nativeFace_eq_zero_of_internal_count_ne
    (edges : Fin (shapeDegree a S l u + coarseDegree i S l u) → Edge n m)
    (hcount : Fintype.card {q // (edges q).1 ∈ S} ≠ shapeDegree a S l u)
    (hloop : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1)
    (y : FaceCoordinates i a S m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u) :
    (graphForm (l := l) (u := u) edges (BoundaryClusterFreeCoordinates.faceEmbedding y)).compContinuousLinearMap
      BoundaryClusterFreeCoordinates.faceEmbedding = 0 := by
  have hpoint : faceProductEmbedding (splitFace (l := l) (u := u) y) =
      BoundaryClusterFreeCoordinates.faceEmbedding y := by
    change BoundaryClusterFreeCoordinates.faceEmbedding (splitFace.symm (splitFace y)) = _
    rw [LinearEquiv.symm_apply_apply]
  have hz := graphForm_face_eq_zero_of_internal_count_ne edges hcount hloop
    (splitFace (l := l) (u := u) y) (by rwa [hpoint])
  rw [hpoint] at hz
  ext v
  have h := congrArg (fun f => f (fun q => splitFace (l := l) (u := u) (v q))) hz
  change graphForm (l := l) (u := u) edges (BoundaryClusterFreeCoordinates.faceEmbedding y)
    (fun q => faceProductEmbedding (splitFace (l := l) (u := u) (v q))) = 0 at h
  have hv : (fun q => faceProductEmbedding (splitFace (l := l) (u := u) (v q))) =
      fun q => BoundaryClusterFreeCoordinates.faceEmbedding (v q) := by
    funext q
    change BoundaryClusterFreeCoordinates.faceEmbedding (splitFace.symm (splitFace (v q))) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [hv] at h
  exact h

/-- Incorrect shape degree forces the genuine inherited native face density to zero. -/
theorem nativeFaceDensity_eq_zero_of_internal_count_ne
    (edges : Fin (shapeDegree a S l u + coarseDegree i S l u) → Edge n m)
    (hcount : Fintype.card {q // (edges q).1 ∈ S} ≠ shapeDegree a S l u)
    (hloop : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1)
    (y : FaceCoordinates i a S m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u) :
    nativeFaceDensity (l := l) (u := u) edges y = 0 := by
  have h := graphForm_nativeFace_eq_zero_of_internal_count_ne edges hcount hloop y hy
  exact congrArg (fun f => f (fun q => nativeFaceBasis (nativeIndexEnum.symm q))) h

/-- Nonvanishing of the actual native face density forces the precise shape edge count. -/
theorem internal_count_eq_of_nativeFaceDensity_ne_zero
    (edges : Fin (shapeDegree a S l u + coarseDegree i S l u) → Edge n m)
    (hloop : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1)
    (y : FaceCoordinates i a S m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u)
    (hne : nativeFaceDensity (l := l) (u := u) edges y ≠ 0) :
    Fintype.card {q // (edges q).1 ∈ S} = shapeDegree a S l u := by
  by_contra hcount
  exact hne (nativeFaceDensity_eq_zero_of_internal_count_ne edges hcount hloop y hy)

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphDimensionVanishing
