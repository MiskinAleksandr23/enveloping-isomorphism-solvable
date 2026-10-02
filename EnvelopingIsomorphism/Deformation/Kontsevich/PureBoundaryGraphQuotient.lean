import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterForms
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphOrderedCoordinates

/-! Actual graph forms on a pure external collision face, with quotient
boundary labels in increasing order. The two-point face is linearly identified
with the genuine quotient configuration coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryGraphQuotient
open scoped Classical
open GraphForms PureBoundaryClusterForms BoundaryGraphFaceFactorization BoundaryGraphOrderedCoordinates
variable {n m : ℕ} {l u : Fin (m + 1)}

/-- Center-first coarse coordinates, before the physical increasing relabelling. -/
def coarseCoordinates : Coarse n (boundaryClusterBlock l u) ≃ₗ[ℝ]
    Coordinates n (outsideM l u + 1) where
  toFun c := (c.1, Fin.cases c.2.1 (fun j ↦ c.2.2 (outsideBoundaryEnum.symm j)))
  invFun x := (x.1, x.2 0, fun j ↦ x.2 (Fin.succ (outsideBoundaryEnum j)))
  left_inv c := by
    refine Prod.ext (by rfl) ?_
    refine Prod.ext (by rfl) ?_
    funext j
    simp
  right_inv x := by
    refine Prod.ext (by rfl) ?_
    funext j
    cases j using Fin.cases <;> simp
  map_add' c d := by
    refine Prod.ext (by rfl) ?_
    funext j
    cases j using Fin.cases <;> rfl
  map_smul' t c := by
    refine Prod.ext (by rfl) ?_
    funext j
    cases j using Fin.cases <;> rfl

def orderedCoarseCoordinates (hlu : l ≤ u) :
    Coarse n (boundaryClusterBlock l u) ≃L[ℝ] Coordinates n (outsideM l u + 1) :=
  coarseCoordinates.toContinuousLinearEquiv.trans (boundaryCoordinates (coarsePermutation hlu))

def collapsedBoundary (hlu : l ≤ u) (j : Fin m) : Fin (outsideM l u + 1) :=
  if hj : j ∈ boundaryClusterBlock l u then centerSlot hlu
  else (centerSlot hlu).succAbove (outsideOrderedEnum l u ⟨j, hj⟩)

def quotientEdge (hlu : l ≤ u) (e : GraphForms.Edge n m) : GraphForms.Edge n (outsideM l u + 1) :=
  ⟨e.source, Sum.map id (collapsedBoundary hlu) e.target⟩

theorem orderedCoarseCoordinates_boundary (hlu : l ≤ u)
    (c : Coarse n (boundaryClusterBlock l u)) (j : Fin m) :
    (orderedCoarseCoordinates hlu c).2 (collapsedBoundary hlu j) =
      boundaryBaseCLM (boundaryClusterBlock l u) j c := by
  change (coarseCoordinates c).2 ((coarsePermutation hlu).symm (collapsedBoundary hlu j)) = _
  by_cases hj : j ∈ boundaryClusterBlock l u
  · rw [collapsedBoundary, dif_pos hj, ← coarsePermutation_center hlu, Equiv.symm_apply_apply]
    simp [coarseCoordinates, boundaryBaseCLM, hj, centerCLM]
  · rw [collapsedBoundary, dif_neg hj, ← coarsePermutation_outside hlu ⟨j, hj⟩, Equiv.symm_apply_apply]
    simp [coarseCoordinates, boundaryBaseCLM, hj, outsideCLM]

theorem edgeMap_coarseMap (hlu : l ≤ u) (e : GraphForms.Edge n m)
    (c : Coarse n (boundaryClusterBlock l u)) :
    edgeMap e (coarseMap (boundaryClusterBlock l u) c) =
      edgeMap (quotientEdge hlu e) (orderedCoarseCoordinates hlu c) := by
  apply Prod.ext
  · cases e.source using Fin.cases <;> rfl
  · cases ht : e.target with
    | inl j =>
      simp only [edgeMap, quotientEdge, ht, Sum.map_inl, id_eq, vertexPoint]
      cases j using Fin.cases <;> rfl
    | inr j =>
      simp only [edgeMap, quotientEdge, ht, Sum.map_inr, vertexPoint]
      change (boundaryBaseCLM (boundaryClusterBlock l u) j c : ℂ) =
        ((orderedCoarseCoordinates hlu c).2 (collapsedBoundary hlu j) : ℂ)
      rw [orderedCoarseCoordinates_boundary]

theorem edgeTangent_coarseMap (hlu : l ≤ u) (e : GraphForms.Edge n m) :
    (edgeTangent e).comp (coarseMap (boundaryClusterBlock l u)) =
      (edgeTangent (quotientEdge hlu e)).comp (orderedCoarseCoordinates hlu).toContinuousLinearMap := by
  have h₁ := ((hasFDerivAt_edgeMap e (coarseMap (boundaryClusterBlock l u) 0)).comp 0
    (coarseMap (boundaryClusterBlock l u)).hasFDerivAt).fderiv
  have h₂ := ((hasFDerivAt_edgeMap (quotientEdge hlu e) (orderedCoarseCoordinates hlu 0)).comp 0
    (orderedCoarseCoordinates hlu).hasFDerivAt).fderiv
  have he : edgeMap e ∘ coarseMap (boundaryClusterBlock l u) =
      edgeMap (quotientEdge hlu e) ∘ orderedCoarseCoordinates hlu :=
    funext (edgeMap_coarseMap hlu e)
  rw [he] at h₁
  exact h₁.symm.trans h₂

theorem coarseEdgeForm_eq_quotient (hlu : l ≤ u) (e : GraphForms.Edge n m)
    (c : Coarse n (boundaryClusterBlock l u)) :
    coarseEdgeForm (boundaryClusterBlock l u) e c =
      (edgeForm (quotientEdge hlu e) (orderedCoarseCoordinates hlu c)).compContinuousLinearMap
        (orderedCoarseCoordinates hlu).toContinuousLinearMap := by
  ext v
  simp only [coarseEdgeForm, edgeForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    edgeMap_coarseMap hlu]
  change harmonicAngleForm _ (fun j ↦ ((edgeTangent e).comp (coarseMap (boundaryClusterBlock l u))) (v j)) = _
  rw [edgeTangent_coarseMap]
  rfl

theorem coarseGraphForm_eq_quotient {r : ℕ} (hlu : l ≤ u)
    (edges : Fin r → GraphForms.Edge n m) (c : Coarse n (boundaryClusterBlock l u)) :
    coarseGraphForm (boundaryClusterBlock l u) edges c =
      (topForm (fun j ↦ quotientEdge hlu (edges j)) (orderedCoarseCoordinates hlu c)).compContinuousLinearMap
        (orderedCoarseCoordinates hlu).toContinuousLinearMap := by
  ext v
  simp only [coarseGraphForm, ContinuousAlternatingMap.compContinuousLinearMap_apply, topForm_apply]
  apply congrArg Matrix.det
  funext i j
  exact congrArg (fun F ↦ F (fun _ : Fin 1 ↦ v i)) (coarseEdgeForm_eq_quotient hlu (edges j) c)

/-- Exact increasing-coordinate chart for the nonvanishing two-external-point face. -/
def twoPointCoordinates (hlu : l ≤ u) (a b : Fin m)
    (ha : a ∈ boundaryClusterBlock l u) (hb : b ∈ boundaryClusterBlock l u)
    (hab : a ≠ b) (hcard : (boundaryClusterBlock l u).card = 2) :
    Face n (boundaryClusterBlock l u) a b ≃L[ℝ] Coordinates n (outsideM l u + 1) :=
  (twoPointFaceEquiv _ a b ha hb hab hcard).trans (orderedCoarseCoordinates hlu)

theorem twoPoint_faceGraphForm_eq_quotient {r : ℕ} (hlu : l ≤ u) (a b : Fin m)
    (ha : a ∈ boundaryClusterBlock l u) (hb : b ∈ boundaryClusterBlock l u)
    (hab : a ≠ b) (hcard : (boundaryClusterBlock l u).card = 2)
    (edges : Fin r → GraphForms.Edge n m) (y : Face n (boundaryClusterBlock l u) a b) :
    faceGraphForm (boundaryClusterBlock l u) a b edges y =
      (topForm (fun j ↦ quotientEdge hlu (edges j)) (twoPointCoordinates hlu a b ha hb hab hcard y)).compContinuousLinearMap
        (twoPointCoordinates hlu a b ha hb hab hcard).toContinuousLinearMap := by
  rw [twoPoint_faceGraphForm_eq_coarse _ a b ha hb hab hcard, coarseGraphForm_eq_quotient hlu]
  ext v
  rfl

end EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryGraphQuotient
