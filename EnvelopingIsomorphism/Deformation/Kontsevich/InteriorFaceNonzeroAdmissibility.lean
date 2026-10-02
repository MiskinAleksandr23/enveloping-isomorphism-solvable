import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceIntegral

/-! Nonzero actual simple-face graph densities force the native internal
degree and exclude parallel coarse arrows. No quotient admissibility is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFaceNonzeroAdmissibility
open InteriorGraphFaceCoordinates ContinuousAlternatingMap GraphFormProduct
open scoped Classical
variable {n m d : ℕ} {i a b : Fin n} {S : Finset (Fin n)}
  (edges : Fin d → Edge n m) (x : ProductCoordinates i a b S m)

theorem faceCovectors_injective_of_nonzero
    (h : (graphForm edges (toAngular x)).compContinuousLinearMap (fderiv ℝ toAngular x) ≠ 0) :
    Function.Injective (fun q => faceCovector (edges q) x) := by
  intro j k he
  by_contra hjk
  apply h
  ext v
  change Matrix.det (fun l q => faceCovector (edges q) x (v l)) = 0
  exact Matrix.det_zero_of_column_eq hjk (fun l => congrArg (fun L => L (v l)) he)

/-- Two external arrows with the same native coarse endpoints have identical
actual pulled-back harmonic covectors, so their determinant vanishes. -/
theorem external_coarseEdge_injective_of_nonzero
    (hx : (toAngular x).toFree.OpenConditions)
    (h : (graphForm edges (toAngular x)).compContinuousLinearMap (fderiv ℝ toAngular x) ≠ 0) :
    Function.Injective (fun q : {q : Fin d // ¬ IsInternal S (edges q)} =>
      coarseEdge (i := i) (a := a) (S := S) (edges q.val)) := by
  intro j k he
  change coarseEdge (i := i) (a := a) (S := S) (edges j.val) = coarseEdge (edges k.val) at he
  apply Subtype.ext
  apply faceCovectors_injective_of_nonzero edges x h
  change faceCovector (edges j.val) x = faceCovector (edges k.val) x
  rw [faceCovector_external x hx (edges j.val) j.property,
    faceCovector_external x hx (edges k.val) k.property, he]

/-- The internal degree is derived from nonvanishing of the actual full form. -/
theorem internal_count_eq_of_nonzero
    (hba : b ≠ a) (hx : (toAngular x).toFree.OpenConditions)
    (hne : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1)
    (hd : d = shapeDegree a b S + coarseDegree i a S m)
    (h : (graphForm edges (toAngular x)).compContinuousLinearMap (fderiv ℝ toAngular x) ≠ 0) :
    Fintype.card {q // IsInternal S (edges q)} = shapeDegree a b S := by
  generalize hk : Fintype.card {q // IsInternal S (edges q)} = k
  have hle : k ≤ d := by
    rw [← hk]
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun q => IsInternal S (edges q))
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hle
  rcases hs with rfl
  by_contra hc
  exact h (graphForm_eq_zero_of_dimension_mismatch edges hk hba x hx hne hd hc)

variable (edges : Fin (shapeDegree a b S + coarseDegree i a S m) → Edge n m)
  (y : RealProductCoordinates i a b S m)

/-- Nonzero scalar density implies nonzero native product pullback form. -/
theorem form_ne_zero_of_density_ne_zero (h : realFaceDensity edges y ≠ 0) :
    (graphForm edges (toAngular (toProduct y))).compContinuousLinearMap
      (fderiv ℝ toAngular (toProduct y)) ≠ 0 := by
  intro hz
  apply h
  unfold realFaceDensity toAngularReal
  rw [fderiv_comp y (contDiff_toAngular.differentiable (by simp)).differentiableAt
    toProduct.differentiableAt, toProduct.fderiv]
  change ((graphForm edges (toAngular (toProduct y))).compContinuousLinearMap
    (fderiv ℝ toAngular (toProduct y))) (fun j => toProduct (faceFrame j)) = 0
  rw [hz]
  rfl

theorem internal_count_eq_of_density_ne_zero
    (ha : a ∈ S) (hba : b ≠ a)
    (hy : y ∈ InteriorFiberAngleSplit.integrationRegion (shapeN a b S) ×ˢ
      GeometricWeights.realDomain (coarseN i a S) m)
    (hne : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1)
    (h : realFaceDensity edges y ≠ 0) :
    Fintype.card {q // IsInternal S (edges q)} = shapeDegree a b S :=
  internal_count_eq_of_nonzero edges (toProduct y) hba
    (openConditions_toAngular ha hba (toProduct y) hy.1.2 hy.2) hne rfl
    (form_ne_zero_of_density_ne_zero edges y h)

theorem external_coarseEdge_injective_of_density_ne_zero
    (ha : a ∈ S) (hba : b ≠ a)
    (hy : y ∈ InteriorFiberAngleSplit.integrationRegion (shapeN a b S) ×ˢ
      GeometricWeights.realDomain (coarseN i a S) m)
    (h : realFaceDensity edges y ≠ 0) :
    Function.Injective (fun q : {q // ¬ IsInternal S (edges q)} =>
      coarseEdge (i := i) (a := a) (S := S) (edges q.val)) :=
  external_coarseEdge_injective_of_nonzero edges (toProduct y)
    (openConditions_toAngular ha hba (toProduct y) hy.1.2 hy.2)
    (form_ne_zero_of_density_ne_zero edges y h)

/-- A genuine two-point interior face has exactly one internal arrow whenever
its actual graph density is nonzero. -/
theorem internal_count_eq_one_of_density_ne_zero
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hS : S.card = 2)
    (hy : y ∈ InteriorFiberAngleSplit.integrationRegion (shapeN a b S) ×ˢ
      GeometricWeights.realDomain (coarseN i a S) m)
    (hne : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1)
    (h : realFaceDensity edges y ≠ 0) : Fintype.card {q // IsInternal S (edges q)} = 1 := by
  rw [internal_count_eq_of_density_ne_zero edges y ha hba hy hne h, shapeDegree_eq ha hb hba, hS]

end EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFaceNonzeroAdmissibility
