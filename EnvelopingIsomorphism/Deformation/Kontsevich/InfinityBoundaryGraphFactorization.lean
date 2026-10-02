import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryAnchoredInfinitySmoothForms
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphFaceFactorization
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphOrderedCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.AlternatingRankVanishing

/-! Actual graph-form restriction on an all-interior infinity face. An edge
to an outside real vertex vanishes. Otherwise every covector factors through
the normalized inner shape, yielding genuine dimension vanishing. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InfinityBoundaryGraphFactorization
open scoped Classical
open BoundaryAnchoredInfinityFreeCoordinates
open BoundaryGraphOrderedCoordinates
variable {n m : ℕ} {a : Fin n} {o : Fin m} {l u : Fin (m+1)}

abbrev shapeN (a : Fin n) := Fintype.card (BoundaryAnchoredInfinityFreeInterior a)
abbrev shapeM (l u : Fin (m+1)) := BoundaryGraphFaceFactorization.shapeM l u
abbrev Shape (a : Fin n) (l u : Fin (m+1)) := GraphForms.Coordinates (shapeN a) (shapeM l u)
abbrev Edge (n m : ℕ) := Fin n × (Fin n ⊕ Fin m)
abbrev interiorEnum : BoundaryAnchoredInfinityFreeInterior a ≃ Fin (shapeN a) := Fintype.equivFin _

def source (j : Fin n) : Fin (shapeN a + 1) :=
  if hj : j = a then 0 else (interiorEnum ⟨j,hj⟩).succ

def shapeCoordinates (ho : o ∉ boundaryClusterBlock l u) :
    FaceCoordinates a m o →L[ℝ] Shape a l u :=
  (ContinuousLinearMap.pi fun j ↦ (ContinuousLinearMap.proj (interiorEnum.symm j)).comp
    (ContinuousLinearMap.fst ℝ (BoundaryAnchoredInfinityFreeInterior a → ℂ)
      (BoundaryAnchoredInfinityFreeBoundary o → ℝ))).prod
  (ContinuousLinearMap.pi fun j ↦ (ContinuousLinearMap.proj
    (⟨((shapeOrderedEnum l u).symm j).val, fun h ↦ ho (h ▸ ((shapeOrderedEnum l u).symm j).property)⟩ :
      BoundaryAnchoredInfinityFreeBoundary o)).comp (ContinuousLinearMap.snd ℝ (BoundaryAnchoredInfinityFreeInterior a → ℂ)
      (BoundaryAnchoredInfinityFreeBoundary o → ℝ)))

def shapeTarget (v : Fin n ⊕ Fin m) (hv : boundaryAnchoredInfinityCollapses l u (Sum.inl v)) :
    GraphForms.Vertex (shapeN a) (shapeM l u) :=
  match v with
  | Sum.inl j => Sum.inl (source j)
  | Sum.inr j => Sum.inr (shapeOrderedEnum l u ⟨j,hv⟩)

def shapeEdge (e : Edge n m) (he : boundaryAnchoredInfinityCollapses l u (Sum.inl e.2)) :
    GraphForms.Edge (shapeN a) (shapeM l u) := ⟨source e.1, shapeTarget e.2 he⟩

theorem source_position (ho : o ∉ boundaryClusterBlock l u)
    (y : FaceCoordinates a m o) (j : Fin n) :
    GraphForms.interiorPoint (source (a := a) j) (shapeCoordinates ho y) =
      (faceEmbedding y).shape j := by
  by_cases hj : j = a
  · subst j
    simp [source, shape]
  · simp [source, hj, GraphForms.interiorPoint, shapeCoordinates, shape, faceEmbedding]

theorem target_position (ho : o ∉ boundaryClusterBlock l u)
    (y : FaceCoordinates a m o) (v : Fin n ⊕ Fin m)
    (hv : boundaryAnchoredInfinityCollapses l u (Sum.inl v)) :
    GraphForms.vertexPoint (shapeTarget (a := a) v hv) (shapeCoordinates ho y) =
      (faceEmbedding y).targetShape l u v := by
  cases v with
  | inl j => exact source_position ho y j
  | inr j =>
    have hj : j ∈ boundaryClusterBlock l u := hv
    have hjo : j ≠ o := fun h ↦ ho (h ▸ hj)
    simp [shapeTarget, GraphForms.vertexPoint, shapeCoordinates, targetShape,
      boundaryVelocity, boundaryCoordinate, hj, hjo, faceEmbedding]

theorem shapeFacePair_eq_graph (ho : o ∉ boundaryClusterBlock l u) (e : Edge n m)
    (he : boundaryAnchoredInfinityCollapses l u (Sum.inl e.2)) :
    shapeFacePair (a := a) (o := o) l u e.1 e.2 =
      GraphForms.edgeMap (shapeEdge e he) ∘ shapeCoordinates ho := by
  funext y
  exact Prod.ext (source_position ho y e.1).symm (target_position ho y e.2 he).symm

theorem shapeFaceForm_eq_graph (ho : o ∉ boundaryClusterBlock l u) (e : Edge n m)
    (he : boundaryAnchoredInfinityCollapses l u (Sum.inl e.2)) (y : FaceCoordinates a m o) :
    shapeFaceForm l u e.1 e.2 y =
      (GraphForms.edgeForm (shapeEdge e he) (shapeCoordinates ho y)).compContinuousLinearMap
        (shapeCoordinates ho) := by
  rw [shapeFaceForm, shapeFacePair_eq_graph ho e he]
  rw [fderiv_comp y (GraphForms.hasFDerivAt_edgeMap _ _).differentiableAt
    (shapeCoordinates ho).differentiableAt, (GraphForms.hasFDerivAt_edgeMap _ _).fderiv,
    (shapeCoordinates ho).fderiv]
  ext v
  rfl

def edgeLinear (e : Edge n m) (x : BoundaryAnchoredInfinityFreeCoordinates a m o) :
    BoundaryAnchoredInfinityFreeCoordinates a m o →L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := BoundaryAnchoredInfinityFreeCoordinates a m o)
    (F := ℝ) (0 : Fin 1)).symm (extendedEdgeForm l u e.1 e.2 x)

def graphForm {r : ℕ} (edges : Fin r → Edge n m)
    (x : BoundaryAnchoredInfinityFreeCoordinates a m o) :
    BoundaryAnchoredInfinityFreeCoordinates a m o [⋀^Fin r]→L[ℝ] ℝ :=
  GraphFormProduct.ofCovectors (fun j ↦ edgeLinear (l := l) (u := u) (edges j) x)

theorem edgeLinear_apply (e : Edge n m) (x v : BoundaryAnchoredInfinityFreeCoordinates a m o) :
    edgeLinear (l := l) (u := u) e x v = extendedEdgeForm l u e.1 e.2 x (fun _ : Fin 1 ↦ v) := by
  have h := (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ)
    (E := BoundaryAnchoredInfinityFreeCoordinates a m o) (F := ℝ) (0 : Fin 1)).apply_symm_apply
    (extendedEdgeForm l u e.1 e.2 x)
  exact congrArg (fun ω ↦ ω (fun _ : Fin 1 ↦ v)) h

theorem graphForm_face_eq_zero_of_outside {r : ℕ} (edges : Fin r → Edge n m)
    (j : Fin r) (k : Fin m) (hk : k ∉ boundaryClusterBlock l u) (ht : (edges j).2 = Sum.inr k)
    (y : FaceCoordinates a m o) (hy : (faceEmbedding y).OpenConditions l u) :
    (graphForm (l := l) (u := u) edges (faceEmbedding y)).compContinuousLinearMap faceEmbedding = 0 := by
  ext v
  change Matrix.det (fun i t ↦ edgeLinear (l := l) (u := u) (edges t) (faceEmbedding y) (faceEmbedding (v i))) = 0
  apply Matrix.det_eq_zero_of_column_eq_zero j
  intro i
  rw [edgeLinear_apply, ht]
  exact congrArg (fun ω ↦ ω (fun _ : Fin 1 ↦ v i))
    (extendedEdgeForm_face_outside y hy (edges j).1 k hk)

theorem graphForm_face_eq_shape {r : ℕ} (ho : o ∉ boundaryClusterBlock l u)
    (edges : Fin r → Edge n m)
    (hin : ∀ j, boundaryAnchoredInfinityCollapses l u (Sum.inl (edges j).2))
    (y : FaceCoordinates a m o) (hy : (faceEmbedding y).OpenConditions l u) :
    (graphForm (l := l) (u := u) edges (faceEmbedding y)).compContinuousLinearMap faceEmbedding =
      (GraphForms.topForm (fun j ↦ shapeEdge (edges j) (hin j)) (shapeCoordinates ho y)).compContinuousLinearMap
        (shapeCoordinates ho) := by
  ext v
  simp only [graphForm, GraphFormProduct.ofCovectors_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, GraphForms.topForm_apply]
  apply congrArg Matrix.det
  funext i j
  rw [edgeLinear_apply]
  have h := extendedEdgeForm_face_internal y hy (edges j).1 (edges j).2 (hin j)
  rw [shapeFaceForm_eq_graph ho (edges j) (hin j)] at h
  exact congrArg (fun ω ↦ ω (fun _ : Fin 1 ↦ v i)) h

/-- Whole-form vanishing above the actual shape dimension, with the outgoing
edge branch discharged from the actual harmonic restriction. -/
theorem graphForm_face_eq_zero_of_shape_dimension_lt {r : ℕ}
    (ho : o ∉ boundaryClusterBlock l u) (edges : Fin r → Edge n m)
    (hr : GraphForms.dimension (shapeN a) (shapeM l u) < r)
    (y : FaceCoordinates a m o) (hy : (faceEmbedding y).OpenConditions l u) :
    (graphForm (l := l) (u := u) edges (faceEmbedding y)).compContinuousLinearMap faceEmbedding = 0 := by
  by_cases hin : ∀ j, boundaryAnchoredInfinityCollapses l u (Sum.inl (edges j).2)
  · rw [graphForm_face_eq_shape ho edges hin y hy]
    have hdim : Module.finrank ℝ (Shape a l u) < r := by
      simpa [Shape, GraphForms.Coordinates, Module.finrank_prod, Module.finrank_pi_fintype] using hr
    rw [continuousAlternating_eq_zero_of_finrank_lt
      (GraphForms.topForm (fun j ↦ shapeEdge (edges j) (hin j)) (shapeCoordinates ho y)) hdim]
    ext v
    rfl
  · push Not at hin
    obtain ⟨j,hj⟩ := hin
    cases ht : (edges j).2 with
    | inl k => simp [ht, boundaryAnchoredInfinityCollapses] at hj
    | inr k => exact graphForm_face_eq_zero_of_outside edges j k (by simpa only [ht, boundaryAnchoredInfinityCollapses] using hj) ht y hy

/-- Real dimension of the inherited full radial face. -/
abbrev faceDegree (_a : Fin n) (m : ℕ) := 2 * (n - 1) + (m - 1)

theorem finrank_face : Module.finrank ℝ (FaceCoordinates a m o) = faceDegree a m := by
  simp [FaceCoordinates, faceDegree, Module.finrank_prod, Module.finrank_pi_fintype,
    mul_comm]

/-- At least two outside real labels leave a nontrivial coarse tangent.
The actual full-degree graph form vanishes on the entire infinity face. -/
theorem graphForm_fullFace_eq_zero_of_block_card_lt
    (ho : o ∉ boundaryClusterBlock l u) (hcard : (boundaryClusterBlock l u).card < m - 1)
    (edges : Fin (faceDegree a m) → Edge n m)
    (y : FaceCoordinates a m o) (hy : (faceEmbedding y).OpenConditions l u) :
    (graphForm (l := l) (u := u) edges (faceEmbedding y)).compContinuousLinearMap faceEmbedding = 0 := by
  apply graphForm_face_eq_zero_of_shape_dimension_lt ho edges _ y hy
  have hc : shapeM l u = (boundaryClusterBlock l u).card := Fintype.card_coe _
  simp only [GraphForms.dimension, shapeN, card_boundaryAnchoredInfinityFreeInterior, hc, faceDegree]
  omega

theorem noOutgoing_of_face_ne_zero {r : ℕ} (edges : Fin r → Edge n m)
    (y : FaceCoordinates a m o) (hy : (faceEmbedding y).OpenConditions l u)
    (v : Fin r → FaceCoordinates a m o)
    (hne : (graphForm (l := l) (u := u) edges (faceEmbedding y)).compContinuousLinearMap faceEmbedding v ≠ 0) :
    ∀ j, boundaryAnchoredInfinityCollapses l u (Sum.inl (edges j).2) := by
  intro j
  cases ht : (edges j).2 with
  | inl k => trivial
  | inr k =>
    by_contra hk
    have hz := graphForm_face_eq_zero_of_outside edges j k hk ht y hy
    exact hne (congrArg (fun ω ↦ ω v) hz)

/-- Only a single outside real label can survive in full face degree; no
assumption that omitted infinity strata vanish is made. -/
theorem block_card_eq_of_fullFace_ne_zero
    (ho : o ∉ boundaryClusterBlock l u) (edges : Fin (faceDegree a m) → Edge n m)
    (y : FaceCoordinates a m o) (hy : (faceEmbedding y).OpenConditions l u)
    (v : Fin (faceDegree a m) → FaceCoordinates a m o)
    (hne : (graphForm (l := l) (u := u) edges (faceEmbedding y)).compContinuousLinearMap faceEmbedding v ≠ 0) :
    (boundaryClusterBlock l u).card = m - 1 := by
  have hc : (boundaryClusterBlock l u).card ≤ m - 1 := by
    have hs : boundaryClusterBlock l u ⊆ Finset.univ.erase o := by
      intro j hj
      exact Finset.mem_erase.mpr ⟨fun h ↦ ho (h ▸ hj), Finset.mem_univ _⟩
    simpa using Finset.card_le_card hs
  by_contra he
  have hz := graphForm_fullFace_eq_zero_of_block_card_lt ho (by omega) edges y hy
  exact hne (congrArg (fun ω ↦ ω v) hz)

end EnvelopingIsomorphism.Deformation.Kontsevich.InfinityBoundaryGraphFactorization
