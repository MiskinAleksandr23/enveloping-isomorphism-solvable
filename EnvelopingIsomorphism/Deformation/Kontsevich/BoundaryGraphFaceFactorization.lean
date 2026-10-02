import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterFaceForms
import EnvelopingIsomorphism.Deformation.Kontsevich.GraphFormProduct
import EnvelopingIsomorphism.Deformation.Kontsevich.GraphFormDegeneracy
import Mathlib.Logic.Equiv.Set

/-!
Actual graph-form factorization on a simple finite real-cluster face. The face
coordinates split into normalized shape coordinates and coarse coordinates by
an explicit linear equivalence. Native edge endpoints are relabelled by finite
bijections; the determinant signs record edge and tangent orders separately.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphFaceFactorization

open scoped BigOperators
open Configuration

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

abbrev ShapeBoundary (l u : Fin (m + 1)) := {j : Fin m // j ∈ boundaryClusterBlock l u}
abbrev OutsideBoundary (l u : Fin (m + 1)) := {j : Fin m // j ∉ boundaryClusterBlock l u}

abbrev shapeN (a : Fin n) (S : Finset (Fin n)) := Fintype.card (BoundaryClusterShapeIndex a S)
abbrev shapeM (l u : Fin (m + 1)) := Fintype.card (ShapeBoundary l u)
abbrev coarseN (i : Fin n) (S : Finset (Fin n)) := Fintype.card (BoundaryClusterCoarseIndex i S)
abbrev outsideM (l u : Fin (m + 1)) := Fintype.card (OutsideBoundary l u)

abbrev ShapeCoordinates (a : Fin n) (S : Finset (Fin n)) (l u : Fin (m + 1)) :=
  GraphForms.Coordinates (shapeN a S) (shapeM l u)
abbrev CoarseCoordinates (i : Fin n) (S : Finset (Fin n)) (l u : Fin (m + 1)) :=
  GraphForms.Coordinates (coarseN i S) (outsideM l u + 1)
abbrev FaceCoordinates (i a : Fin n) (S : Finset (Fin n)) (m : ℕ) :=
  BoundaryClusterFreeCoordinates.FaceCoordinates i a S m

abbrev shapeEnum : BoundaryClusterShapeIndex a S ≃ Fin (shapeN a S) := Fintype.equivFin _
abbrev coarseEnum : BoundaryClusterCoarseIndex i S ≃ Fin (coarseN i S) := Fintype.equivFin _
abbrev shapeBoundaryEnum : ShapeBoundary l u ≃ Fin (shapeM l u) := Fintype.equivFin _
abbrev outsideBoundaryEnum : OutsideBoundary l u ≃ Fin (outsideM l u) := Fintype.equivFin _

/-- Split every actual free face coordinate. The quotient boundary order is:
contracted center first, then the enumerated outside boundary labels. -/
def splitFace : FaceCoordinates i a S m ≃ₗ[ℝ]
    ShapeCoordinates a S l u × CoarseCoordinates i S l u where
  toFun y :=
    ((fun j => y.2.1 (shapeEnum.symm j), fun j => y.2.2.1 (shapeBoundaryEnum.symm j).val),
      (fun j => y.1 (coarseEnum.symm j),
        Fin.cases y.2.2.2 (fun j => y.2.2.1 (outsideBoundaryEnum.symm j).val)))
  invFun z :=
    (fun j => z.2.1 (coarseEnum j), fun j => z.1.1 (shapeEnum j),
      fun j => if hj : j ∈ boundaryClusterBlock l u
        then z.1.2 (shapeBoundaryEnum ⟨j, hj⟩)
        else z.2.2 (Fin.succ (outsideBoundaryEnum ⟨j, hj⟩)), z.2.2 0)
  left_inv y := by
    apply Prod.ext
    · funext j
      simp
    · apply Prod.ext
      · funext j
        simp
      · apply Prod.ext
        · funext j
          by_cases hj : j ∈ boundaryClusterBlock l u <;> simp [hj]
        · rfl
  right_inv z := by
    apply Prod.ext
    · apply Prod.ext
      · funext j
        simp
      · funext j
        simp [(shapeBoundaryEnum.symm j).property]
    · apply Prod.ext
      · funext j
        simp
      · funext j
        cases j using Fin.cases with
        | zero => rfl
        | succ j => simp [(outsideBoundaryEnum.symm j).property, -mem_boundaryClusterBlock]
  map_add' y z := by
    apply Prod.ext
    · apply Prod.ext <;> funext j <;> rfl
    · apply Prod.ext
      · funext j
        rfl
      · funext j
        cases j using Fin.cases <;> rfl
  map_smul' c y := by
    apply Prod.ext
    · apply Prod.ext <;> funext j <;> rfl
    · apply Prod.ext
      · funext j
        rfl
      · funext j
        cases j using Fin.cases <;> rfl

/-- The same actual splitting as a continuous linear equivalence. -/
def splitFaceContinuous : FaceCoordinates i a S m ≃L[ℝ]
    ShapeCoordinates a S l u × CoarseCoordinates i S l u :=
  splitFace.toContinuousLinearEquiv

/-- The genuine tangent inclusion, with radius zero, of the shape/coarse product. -/
def faceProductEmbedding :
    (ShapeCoordinates a S l u × CoarseCoordinates i S l u) →L[ℝ]
      BoundaryClusterFreeCoordinates i a S m :=
  BoundaryClusterFreeCoordinates.faceEmbedding.comp splitFaceContinuous.symm.toContinuousLinearMap

abbrev shapeDegree (a : Fin n) (S : Finset (Fin n)) (l u : Fin (m + 1)) :=
  GraphForms.dimension (shapeN a S) (shapeM l u)
abbrev coarseDegree (i : Fin n) (S : Finset (Fin n)) (l u : Fin (m + 1)) :=
  GraphForms.dimension (coarseN i S) (outsideM l u + 1)

theorem finrank_shape : Module.finrank ℝ (ShapeCoordinates a S l u) = shapeDegree a S l u := by
  simp [ShapeCoordinates, GraphForms.Coordinates, Module.finrank_prod,
    Module.finrank_pi_fintype, Complex.finrank_real_complex]

theorem finrank_coarse : Module.finrank ℝ (CoarseCoordinates i S l u) = coarseDegree i S l u := by
  simp [CoarseCoordinates, GraphForms.Coordinates, Module.finrank_prod,
    Module.finrank_pi_fintype, Complex.finrank_real_complex]

/-- The block arities are exactly the dimension of the genuine radial face. -/
theorem face_dimension_split : Module.finrank ℝ (FaceCoordinates i a S m) =
    shapeDegree a S l u + coarseDegree i S l u := by
  rw [splitFace.finrank_eq, Module.finrank_prod, finrank_shape, finrank_coarse]

/-- Native labelled directed edges, before any quotient-graph relabelling. -/
abbrev Edge (n m : ℕ) := Fin n × (Fin n ⊕ Fin m)

def shapeSource (j : Fin n) (hj : j ∈ S) : Fin (shapeN a S + 1) :=
  if hja : j = a then 0 else Fin.succ (shapeEnum ⟨j, hj, hja⟩)

def coarseSource (j : Fin n) (hj : j ∉ S) : Fin (coarseN i S + 1) :=
  if hji : j = i then 0 else Fin.succ (coarseEnum ⟨j, hj, hji⟩)

def shapeTarget (v : Fin n ⊕ Fin m) (hv : boundaryClusterCollapses S l u (Sum.inl v)) :
    GraphForms.Vertex (shapeN a S) (shapeM l u) :=
  match v with
  | Sum.inl j => Sum.inl (shapeSource j hv)
  | Sum.inr j => Sum.inr (shapeBoundaryEnum ⟨j, hv⟩)

def coarseTarget (v : Fin n ⊕ Fin m) : GraphForms.Vertex (coarseN i S) (outsideM l u + 1) :=
  match v with
  | Sum.inl j => if hj : j ∈ S then Sum.inr 0 else Sum.inl (coarseSource j hj)
  | Sum.inr j => if hj : j ∈ boundaryClusterBlock l u then Sum.inr 0
      else Sum.inr (Fin.succ (outsideBoundaryEnum ⟨j, hj⟩))

def shapeEdge (e : Edge n m) (hs : e.1 ∈ S)
    (ht : boundaryClusterCollapses S l u (Sum.inl e.2)) : GraphForms.Edge (shapeN a S) (shapeM l u) :=
  ⟨shapeSource e.1 hs, shapeTarget e.2 ht⟩

def coarseEdge (e : Edge n m) (hs : e.1 ∉ S) : GraphForms.Edge (coarseN i S) (outsideM l u + 1) :=
  ⟨coarseSource e.1 hs, coarseTarget e.2⟩

/-- Shape relabelling reproduces the actual normalized shape source. -/
theorem shapeSource_position (y : FaceCoordinates i a S m) (j : Fin n) (hj : j ∈ S) :
    GraphForms.interiorPoint (shapeSource (a := a) j hj) (splitFace (l := l) (u := u) y).1 =
      (BoundaryClusterFreeCoordinates.faceEmbedding y).velocity j := by
  by_cases hja : j = a
  · subst j
    simp [shapeSource, BoundaryClusterFreeCoordinates.velocity, hj]
  · simp [shapeSource, hja, GraphForms.interiorPoint, splitFace,
      BoundaryClusterFreeCoordinates.velocity, hj, BoundaryClusterFreeCoordinates.faceEmbedding]

theorem shapeTarget_position (y : FaceCoordinates i a S m) (v : Fin n ⊕ Fin m)
    (hv : boundaryClusterCollapses S l u (Sum.inl v)) :
    GraphForms.vertexPoint (shapeTarget (a := a) v hv) (splitFace (l := l) (u := u) y).1 =
      (BoundaryClusterFreeCoordinates.faceEmbedding y).targetVelocity l u v := by
  cases v with
  | inl j => exact shapeSource_position y j hv
  | inr j =>
      have hj : j ∈ boundaryClusterBlock l u := hv
      simp [shapeTarget, GraphForms.vertexPoint, splitFace, BoundaryClusterFreeCoordinates.targetVelocity,
        BoundaryClusterFreeCoordinates.boundaryVelocity, hj, BoundaryClusterFreeCoordinates.faceEmbedding,
        -mem_boundaryClusterBlock]

/-- Coarse relabelling reproduces the actual stationary source coordinate. -/
theorem coarseSource_position (y : FaceCoordinates i a S m) (j : Fin n) (hj : j ∉ S) :
    GraphForms.interiorPoint (coarseSource (i := i) j hj) (splitFace (l := l) (u := u) y).2 =
      (BoundaryClusterFreeCoordinates.faceEmbedding y).base j := by
  by_cases hji : j = i
  · subst j
    simp [coarseSource, BoundaryClusterFreeCoordinates.base, hj]
  · simp [coarseSource, hji, GraphForms.interiorPoint, splitFace,
      BoundaryClusterFreeCoordinates.base, hj, BoundaryClusterFreeCoordinates.faceEmbedding]

theorem coarseTarget_position (y : FaceCoordinates i a S m) (v : Fin n ⊕ Fin m) :
    GraphForms.vertexPoint (coarseTarget (i := i) (S := S) (l := l) (u := u) v) (splitFace (l := l) (u := u) y).2 =
      (BoundaryClusterFreeCoordinates.faceEmbedding y).targetBase l u v := by
  cases v with
  | inl j =>
      by_cases hj : j ∈ S
      · simp [coarseTarget, hj, GraphForms.vertexPoint, splitFace,
          BoundaryClusterFreeCoordinates.targetBase, BoundaryClusterFreeCoordinates.base,
          BoundaryClusterFreeCoordinates.center, BoundaryClusterFreeCoordinates.faceEmbedding]
      · simpa only [coarseTarget, dif_neg hj, GraphForms.vertexPoint,
          BoundaryClusterFreeCoordinates.targetBase] using coarseSource_position y j hj
  | inr j =>
      by_cases hj : j ∈ boundaryClusterBlock l u <;>
        simp [coarseTarget, hj, GraphForms.vertexPoint, splitFace,
          BoundaryClusterFreeCoordinates.targetBase, BoundaryClusterFreeCoordinates.boundaryBase,
          BoundaryClusterFreeCoordinates.center, BoundaryClusterFreeCoordinates.faceEmbedding,
          -mem_boundaryClusterBlock]

theorem shapeFacePair_eq_graph (y : FaceCoordinates i a S m) (e : Edge n m)
    (hs : e.1 ∈ S) (ht : boundaryClusterCollapses S l u (Sum.inl e.2)) :
    BoundaryClusterFreeCoordinates.shapeFacePair l u e.1 e.2 y =
      GraphForms.edgeMap (shapeEdge (a := a) e hs ht) (splitFace (l := l) (u := u) y).1 :=
  Prod.ext (shapeSource_position y e.1 hs).symm (shapeTarget_position y e.2 ht).symm

theorem coarseFacePair_eq_graph (y : FaceCoordinates i a S m) (e : Edge n m) (hs : e.1 ∉ S) :
    BoundaryClusterFreeCoordinates.coarseFacePair l u e.1 e.2 y =
      GraphForms.edgeMap (coarseEdge (i := i) (l := l) (u := u) e hs)
        (splitFace (l := l) (u := u) y).2 :=
  Prod.ext (coarseSource_position y e.1 hs).symm (coarseTarget_position y e.2).symm

theorem splitFace_splitFaceContinuous_symm (z : ShapeCoordinates a S l u × CoarseCoordinates i S l u) :
    splitFace (splitFaceContinuous.symm z) = z := splitFace.apply_symm_apply z

theorem shapeFacePair_comp_split (e : Edge n m) (hs : e.1 ∈ S)
    (ht : boundaryClusterCollapses S l u (Sum.inl e.2)) :
    BoundaryClusterFreeCoordinates.shapeFacePair (i := i) (a := a) l u e.1 e.2 ∘ splitFaceContinuous.symm =
      GraphForms.edgeMap (shapeEdge e hs ht) ∘
        (ContinuousLinearMap.fst ℝ (ShapeCoordinates a S l u) (CoarseCoordinates i S l u)) := by
  funext z
  change BoundaryClusterFreeCoordinates.shapeFacePair l u e.1 e.2 (splitFaceContinuous.symm z) = _
  rw [shapeFacePair_eq_graph, splitFace_splitFaceContinuous_symm]
  rfl

theorem coarseFacePair_comp_split (e : Edge n m) (hs : e.1 ∉ S) :
    BoundaryClusterFreeCoordinates.coarseFacePair (i := i) (a := a) l u e.1 e.2 ∘ splitFaceContinuous.symm =
      GraphForms.edgeMap (coarseEdge e hs) ∘
        (ContinuousLinearMap.snd ℝ (ShapeCoordinates a S l u) (CoarseCoordinates i S l u)) := by
  funext z
  change BoundaryClusterFreeCoordinates.coarseFacePair l u e.1 e.2 (splitFaceContinuous.symm z) = _
  rw [coarseFacePair_eq_graph, splitFace_splitFaceContinuous_symm]
  rfl

private theorem harmonicPair_pullback_comp_clm
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → ℂ × ℂ) (g : F → ℂ × ℂ) (D : F →L[ℝ] E) (x : F)
    (hf : DifferentiableAt ℝ f (D x)) (hmap : f ∘ D = g) :
    ((harmonicAngleForm (f (D x))).compContinuousLinearMap (fderiv ℝ f (D x))).compContinuousLinearMap D =
      (harmonicAngleForm (g x)).compContinuousLinearMap (fderiv ℝ g x) := by
  have hpoint : f (D x) = g x := congrFun hmap x
  have hder : fderiv ℝ g x = (fderiv ℝ f (D x)).comp D := by
    rw [← hmap, fderiv_comp x hf D.differentiableAt, D.fderiv]
  rw [hpoint, hder]
  ext v
  rfl

/-- The shape face covector is the actual smaller graph covector pulled from the first factor. -/
theorem shapeFaceForm_split (e : Edge n m) (hs : e.1 ∈ S)
    (ht : boundaryClusterCollapses S l u (Sum.inl e.2))
    (z : ShapeCoordinates a S l u × CoarseCoordinates i S l u) :
    (BoundaryClusterFreeCoordinates.shapeFaceForm l u e.1 e.2 (splitFaceContinuous.symm z)).compContinuousLinearMap
      splitFaceContinuous.symm.toContinuousLinearMap =
        (GraphForms.edgeForm (shapeEdge e hs ht) z.1).compContinuousLinearMap
          (ContinuousLinearMap.fst ℝ (ShapeCoordinates a S l u) (CoarseCoordinates i S l u)) := by
  rw [BoundaryClusterFreeCoordinates.shapeFaceForm]
  have h := harmonicPair_pullback_comp_clm
    (BoundaryClusterFreeCoordinates.shapeFacePair (i := i) (a := a) (S := S) l u e.1 e.2)
    (GraphForms.edgeMap (shapeEdge e hs ht) ∘
      (ContinuousLinearMap.fst ℝ (ShapeCoordinates a S l u) (CoarseCoordinates i S l u)))
    splitFaceContinuous.symm.toContinuousLinearMap z
    ((BoundaryClusterFreeCoordinates.contDiff_shapeFacePair l u e.1 e.2).contDiffAt.differentiableAt (by simp))
    (shapeFacePair_comp_split e hs ht)
  simp only [ContinuousLinearEquiv.coe_coe] at h
  rw [h]
  simp only [ContinuousLinearMap.coe_fst']
  rw [((GraphForms.hasFDerivAt_edgeMap (shapeEdge e hs ht) z.1).comp z
    (ContinuousLinearMap.fst ℝ (ShapeCoordinates a S l u) (CoarseCoordinates i S l u)).hasFDerivAt).fderiv]
  ext v
  rfl

/-- The coarse face covector is the actual quotient-graph covector pulled from the second factor. -/
theorem coarseFaceForm_split (e : Edge n m) (hs : e.1 ∉ S)
    (z : ShapeCoordinates a S l u × CoarseCoordinates i S l u) :
    (BoundaryClusterFreeCoordinates.coarseFaceForm l u e.1 e.2 (splitFaceContinuous.symm z)).compContinuousLinearMap
      splitFaceContinuous.symm.toContinuousLinearMap =
        (GraphForms.edgeForm (coarseEdge e hs) z.2).compContinuousLinearMap
          (ContinuousLinearMap.snd ℝ (ShapeCoordinates a S l u) (CoarseCoordinates i S l u)) := by
  rw [BoundaryClusterFreeCoordinates.coarseFaceForm]
  have h := harmonicPair_pullback_comp_clm
    (BoundaryClusterFreeCoordinates.coarseFacePair (i := i) (a := a) (S := S) l u e.1 e.2)
    (GraphForms.edgeMap (coarseEdge e hs) ∘
      (ContinuousLinearMap.snd ℝ (ShapeCoordinates a S l u) (CoarseCoordinates i S l u)))
    splitFaceContinuous.symm.toContinuousLinearMap z
    ((BoundaryClusterFreeCoordinates.contDiff_coarseFacePair l u e.1 e.2).contDiffAt.differentiableAt (by simp))
    (coarseFacePair_comp_split e hs)
  simp only [ContinuousLinearEquiv.coe_coe] at h
  rw [h]
  simp only [ContinuousLinearMap.coe_snd']
  rw [((GraphForms.hasFDerivAt_edgeMap (coarseEdge e hs) z.2).comp z
    (ContinuousLinearMap.snd ℝ (ShapeCoordinates a S l u) (CoarseCoordinates i S l u)).hasFDerivAt).fderiv]
  ext v
  rfl

section Covectors

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

def formLinear (ω : E [⋀^Fin 1]→L[ℝ] ℝ) : E →L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).symm ω

theorem formLinear_apply (ω : E [⋀^Fin 1]→L[ℝ] ℝ) (v : E) :
    formLinear ω v = ω (fun _ : Fin 1 => v) := rfl

theorem formLinear_comp (ω : E [⋀^Fin 1]→L[ℝ] ℝ) (D : F →L[ℝ] E) :
    formLinear (ω.compContinuousLinearMap D) = (formLinear ω).comp D := by
  apply ContinuousLinearMap.ext
  intro v
  rw [formLinear_apply, ContinuousLinearMap.comp_apply, formLinear_apply]
  rfl

private theorem form_pullback_assoc (ω : E [⋀^Fin 1]→L[ℝ] ℝ)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (D : F →L[ℝ] E) (T : G →L[ℝ] F) :
    (ω.compContinuousLinearMap D).compContinuousLinearMap T = ω.compContinuousLinearMap (D.comp T) := by
  ext v
  rfl

end Covectors

/-- The actual covector of a native edge in the full free cluster chart. -/
def edgeLinear (e : Edge n m) (x : BoundaryClusterFreeCoordinates i a S m) :
    BoundaryClusterFreeCoordinates i a S m →L[ℝ] ℝ :=
  formLinear (BoundaryClusterFreeCoordinates.extendedEdgeForm l u e.1 e.2 x)

/-- The genuine ordered determinant product of those actual one-forms. -/
def graphForm {r : ℕ} (edges : Fin r → Edge n m) (x : BoundaryClusterFreeCoordinates i a S m) :
    BoundaryClusterFreeCoordinates i a S m [⋀^Fin r]→L[ℝ] ℝ :=
  GraphFormProduct.ofCovectors (fun q => edgeLinear (l := l) (u := u) (edges q) x)

/-- Internal native edges give the first actual graph-covector block, proved from the face theorem. -/
theorem edgeLinear_internal (z : ShapeCoordinates a S l u × CoarseCoordinates i S l u)
    (hy : (faceProductEmbedding z).OpenConditions l u)
    (e : Edge n m) (hs : e.1 ∈ S) (ht : boundaryClusterCollapses S l u (Sum.inl e.2)) :
    (edgeLinear (l := l) (u := u) e (faceProductEmbedding z)).comp (faceProductEmbedding (l := l) (u := u)) =
      (GraphForms.edgeLinear (shapeEdge e hs ht) z.1).comp
        (ContinuousLinearMap.fst ℝ (ShapeCoordinates a S l u) (CoarseCoordinates i S l u)) := by
  have hface := BoundaryClusterFreeCoordinates.extendedEdgeForm_face_internal
    (splitFaceContinuous.symm z) hy e.1 e.2 hs ht
  have hform :
      (BoundaryClusterFreeCoordinates.extendedEdgeForm l u e.1 e.2 (faceProductEmbedding z)).compContinuousLinearMap
          faceProductEmbedding =
        (GraphForms.edgeForm (shapeEdge e hs ht) z.1).compContinuousLinearMap
          (ContinuousLinearMap.fst ℝ (ShapeCoordinates a S l u) (CoarseCoordinates i S l u)) := by
    rw [faceProductEmbedding, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ← form_pullback_assoc, hface]
    exact shapeFaceForm_split e hs ht z
  have h := congrArg formLinear hform
  rw [formLinear_comp, formLinear_comp] at h
  exact h

/-- Noncluster source edges give the second, genuinely contracted graph-covector block. -/
theorem edgeLinear_external (z : ShapeCoordinates a S l u × CoarseCoordinates i S l u)
    (hy : (faceProductEmbedding z).OpenConditions l u)
    (e : Edge n m) (hloop : e.2 ≠ Sum.inl e.1) (hs : e.1 ∉ S) :
    (edgeLinear (l := l) (u := u) e (faceProductEmbedding z)).comp (faceProductEmbedding (l := l) (u := u)) =
      (GraphForms.edgeLinear (coarseEdge e hs) z.2).comp
        (ContinuousLinearMap.snd ℝ (ShapeCoordinates a S l u) (CoarseCoordinates i S l u)) := by
  have hface := BoundaryClusterFreeCoordinates.extendedEdgeForm_face_external
    (splitFaceContinuous.symm z) hy e.1 e.2 hloop (fun h => hs h.1)
  have hform :
      (BoundaryClusterFreeCoordinates.extendedEdgeForm l u e.1 e.2 (faceProductEmbedding z)).compContinuousLinearMap
          faceProductEmbedding =
        (GraphForms.edgeForm (coarseEdge e hs) z.2).compContinuousLinearMap
          (ContinuousLinearMap.snd ℝ (ShapeCoordinates a S l u) (CoarseCoordinates i S l u)) := by
    rw [faceProductEmbedding, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ← form_pullback_assoc, hface]
    exact coarseFaceForm_split e hs z
  have h := congrArg formLinear hform
  rw [formLinear_comp, formLinear_comp] at h
  exact h

section EdgePartition

variable {r s : ℕ}
variable (edges : Fin (r + s) → Edge n m) (S : Finset (Fin n))
variable (hcount : Fintype.card {q : Fin (r + s) // (edges q).1 ∈ S} = r)

def internalEnum : {q : Fin (r + s) // (edges q).1 ∈ S} ≃ Fin r :=
  Fintype.equivFinOfCardEq hcount

include hcount in
theorem external_card : Fintype.card {q : Fin (r + s) // (edges q).1 ∉ S} = s := by
  rw [Fintype.card_subtype_compl, Fintype.card_fin, hcount]
  omega

def externalEnum : {q : Fin (r + s) // (edges q).1 ∉ S} ≃ Fin s :=
  Fintype.equivFinOfCardEq (external_card edges S hcount)

def internalIndex (q : Fin r) : Fin (r + s) := (internalEnum edges S hcount |>.symm q).val

def externalIndex (q : Fin s) : Fin (r + s) := (externalEnum edges S hcount |>.symm q).val

theorem internalIndex_mem (q : Fin r) : (edges (internalIndex edges S hcount q)).1 ∈ S :=
  (internalEnum edges S hcount |>.symm q).property

theorem externalIndex_not_mem (q : Fin s) : (edges (externalIndex edges S hcount q)).1 ∉ S :=
  (externalEnum edges S hcount |>.symm q).property

/-- The explicit permutation taking shape-first/coarse-second edge order to the original order. -/
def edgeBlockPermutation : Equiv.Perm (Fin (r + s)) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (internalEnum edges S hcount).symm (externalEnum edges S hcount).symm).trans
      (Equiv.sumCompl (fun q : Fin (r + s) => (edges q).1 ∈ S)))

@[simp] theorem edgeBlockPermutation_inl (q : Fin r) :
    edgeBlockPermutation edges S hcount (finSumFinEquiv (Sum.inl q)) = internalIndex edges S hcount q := by
  simp [edgeBlockPermutation, internalIndex]

@[simp] theorem edgeBlockPermutation_inr (q : Fin s) :
    edgeBlockPermutation edges S hcount (finSumFinEquiv (Sum.inr q)) = externalIndex edges S hcount q := by
  simp [edgeBlockPermutation, externalIndex]

def shapeEdges (hnout : ∀ q, (edges q).1 ∈ S → boundaryClusterCollapses S l u (Sum.inl (edges q).2)) :
    Fin r → GraphForms.Edge (shapeN a S) (shapeM l u) :=
  fun q => shapeEdge (edges (internalIndex edges S hcount q)) (internalIndex_mem edges S hcount q)
    (hnout _ (internalIndex_mem edges S hcount q))

def coarseEdges : Fin s → GraphForms.Edge (coarseN i S) (outsideM l u + 1) :=
  fun q => coarseEdge (edges (externalIndex edges S hcount q)) (externalIndex_not_mem edges S hcount q)

end EdgePartition

section Determinants

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {r : ℕ}

theorem ofCovectors_comp (α : Fin r → E →L[ℝ] ℝ) (D : F →L[ℝ] E) :
    (GraphFormProduct.ofCovectors α).compContinuousLinearMap D =
      GraphFormProduct.ofCovectors (fun q => (α q).comp D) := by
  ext v
  rfl

end Determinants

/-- A complete basis of the genuine radial face, with the shape block before the coarse block. -/
def productFaceBasis : Module.Basis
    (Fin (shapeDegree a S l u + coarseDegree i S l u)) ℝ (FaceCoordinates i a S m) :=
  (((GraphForms.realBasis (shapeN a S) (shapeM l u)).prod
    (GraphForms.realBasis (coarseN i S) (outsideM l u + 1))).reindex finSumFinEquiv).map splitFace.symm

theorem productFaceBasis_apply (q : Fin (shapeDegree a S l u + coarseDegree i S l u)) :
    productFaceBasis (i := i) (a := a) (S := S) (l := l) (u := u) q =
      splitFaceContinuous.symm (GraphFormProduct.productVectors
        (GraphForms.realBasis (shapeN a S) (shapeM l u))
        (GraphForms.realBasis (coarseN i S) (outsideM l u + 1)) q) := by
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective q
  cases q <;> simp [productFaceBasis, GraphFormProduct.productVectors, Module.Basis.prod_apply,
    splitFaceContinuous]

/-- Every tangent in the product basis lies in the actual radius-zero tangent hyperplane. -/
theorem product_tangent_radius_zero (q : Fin (shapeDegree a S l u + coarseDegree i S l u)) :
    (faceProductEmbedding (GraphFormProduct.productVectors
      (GraphForms.realBasis (shapeN a S) (shapeM l u))
      (GraphForms.realBasis (coarseN i S) (outsideM l u + 1)) q)).radius = 0 := rfl

/-- The actual full face density factors into genuine shape and contracted-graph
densities. Both finite permutations contribute their exact determinant signs. -/
theorem graphForm_face_product
    (edges : Fin (shapeDegree a S l u + coarseDegree i S l u) → Edge n m)
    (hcount : Fintype.card {q // (edges q).1 ∈ S} = shapeDegree a S l u)
    (hnout : ∀ q, (edges q).1 ∈ S → boundaryClusterCollapses S l u (Sum.inl (edges q).2))
    (hloop : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1)
    (z : ShapeCoordinates a S l u × CoarseCoordinates i S l u)
    (hy : (faceProductEmbedding z).OpenConditions l u)
    (τ : Equiv.Perm (Fin (shapeDegree a S l u + coarseDegree i S l u))) :
    graphForm (l := l) (u := u) edges (faceProductEmbedding z)
      (fun q => faceProductEmbedding (GraphFormProduct.productVectors
        (GraphForms.realBasis (shapeN a S) (shapeM l u))
        (GraphForms.realBasis (coarseN i S) (outsideM l u + 1)) (τ q))) =
      (Equiv.Perm.sign (edgeBlockPermutation edges S hcount).symm : ℝ) * (Equiv.Perm.sign τ : ℝ) *
        (GraphForms.topDensity (shapeEdges (a := a) edges S hcount hnout) z.1 *
          GraphForms.topDensity (coarseEdges (i := i) (l := l) (u := u) edges S hcount) z.2) := by
  let α := fun q => GraphForms.edgeLinear (shapeEdges (a := a) edges S hcount hnout q) z.1
  let β := fun q => GraphForms.edgeLinear (coarseEdges (i := i) (l := l) (u := u) edges S hcount q) z.2
  have hblock (q : Fin (shapeDegree a S l u + coarseDegree i S l u)) :
      (edgeLinear (l := l) (u := u) (edges (edgeBlockPermutation edges S hcount q))
        (faceProductEmbedding z)).comp (faceProductEmbedding (l := l) (u := u)) = GraphFormProduct.productCovectors α β q := by
    obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective q
    cases q with
    | inl q =>
        rw [edgeBlockPermutation_inl]
        simp only [GraphFormProduct.productCovectors, Equiv.symm_apply_apply, Sum.elim_inl]
        exact edgeLinear_internal z hy _ (internalIndex_mem edges S hcount q)
          (hnout _ (internalIndex_mem edges S hcount q))
    | inr q =>
        rw [edgeBlockPermutation_inr]
        simp only [GraphFormProduct.productCovectors, Equiv.symm_apply_apply, Sum.elim_inr]
        exact edgeLinear_external z hy _ (hloop _) (externalIndex_not_mem edges S hcount q)
  have hperm (q : Fin (shapeDegree a S l u + coarseDegree i S l u)) :
      (edgeLinear (l := l) (u := u) (edges q) (faceProductEmbedding z)).comp (faceProductEmbedding (l := l) (u := u)) =
        GraphFormProduct.productCovectors α β ((edgeBlockPermutation edges S hcount).symm q) := by
    simpa only [Equiv.apply_symm_apply] using hblock ((edgeBlockPermutation edges S hcount).symm q)
  change (GraphFormProduct.ofCovectors (fun q =>
      edgeLinear (l := l) (u := u) (edges q) (faceProductEmbedding z))).compContinuousLinearMap
      faceProductEmbedding (fun q => GraphFormProduct.productVectors
        (GraphForms.realBasis (shapeN a S) (shapeM l u))
        (GraphForms.realBasis (coarseN i S) (outsideM l u + 1)) (τ q)) = _
  rw [ofCovectors_comp]
  simp_rw [hperm]
  exact GraphFormProduct.form_product_permuted_apply α β
    (GraphForms.realBasis (shapeN a S) (shapeM l u))
    (GraphForms.realBasis (coarseN i S) (outsideM l u + 1))
    (edgeBlockPermutation edges S hcount).symm τ

/-- An outgoing cluster edge kills the actual face form in every degree. -/
theorem graphForm_face_eq_zero_of_outgoing {r : ℕ} (edges : Fin r → Edge n m)
    (q : Fin r) (hloop : (edges q).2 ≠ Sum.inl (edges q).1)
    (hs : (edges q).1 ∈ S) (ht : ¬boundaryClusterCollapses S l u (Sum.inl (edges q).2))
    (z : ShapeCoordinates a S l u × CoarseCoordinates i S l u)
    (hy : (faceProductEmbedding z).OpenConditions l u) :
    (graphForm (l := l) (u := u) edges (faceProductEmbedding z)).compContinuousLinearMap
      (faceProductEmbedding (l := l) (u := u)) = 0 := by
  have hface := BoundaryClusterFreeCoordinates.extendedEdgeForm_face_outgoing
    (splitFaceContinuous.symm z) hy (edges q).1 (edges q).2 hloop hs ht
  have hform :
      (BoundaryClusterFreeCoordinates.extendedEdgeForm l u (edges q).1 (edges q).2
        (faceProductEmbedding z)).compContinuousLinearMap (faceProductEmbedding (l := l) (u := u)) = 0 := by
    rw [faceProductEmbedding, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ← form_pullback_assoc, hface]
    ext v
    rfl
  have hlinear : (edgeLinear (l := l) (u := u) (edges q) (faceProductEmbedding z)).comp (faceProductEmbedding (l := l) (u := u)) = 0 := by
    have h := congrArg formLinear hform
    rw [formLinear_comp] at h
    exact h
  rw [graphForm, ofCovectors_comp]
  ext v
  change GraphFormProduct.ofCovectors _ v = 0
  rw [GraphFormProduct.ofCovectors_apply]
  apply Matrix.det_eq_zero_of_column_eq_zero q
  intro j
  exact congrArg (fun f : (ShapeCoordinates a S l u × CoarseCoordinates i S l u) →L[ℝ] ℝ => f (v j)) hlinear

/-- Native face coordinate labels, in the inherited coarse/shape/boundary/center order. -/
abbrev NativeFaceIndex (i a : Fin n) (S : Finset (Fin n)) (m : ℕ) :=
  (Σ _ : BoundaryClusterCoarseIndex i S, Fin 2) ⊕
    (Σ _ : BoundaryClusterShapeIndex a S, Fin 2) ⊕ Fin m ⊕ Unit

/-- The exact native product basis with the radial coordinate removed. -/
def nativeFaceBasis : Module.Basis (NativeFaceIndex i a S m) ℝ (FaceCoordinates i a S m) :=
  (Pi.basis (fun _ : BoundaryClusterCoarseIndex i S => Complex.basisOneI)).prod
    ((Pi.basis (fun _ : BoundaryClusterShapeIndex a S => Complex.basisOneI)).prod
      ((Pi.basisFun ℝ (Fin m)).prod (Module.Basis.singleton Unit ℝ)))

/-- Explicit label splitting: inside boundary coordinates join the shape block;
outside boundary coordinates and the center join the coarse block. -/
def nativeIndexSplit : NativeFaceIndex i a S m ≃
    (((Fin (shapeN a S) × Fin 2) ⊕ Fin (shapeM l u)) ⊕
      ((Fin (coarseN i S) × Fin 2) ⊕ Fin (outsideM l u + 1))) where
  toFun
    | Sum.inl ⟨j, t⟩ => Sum.inr (Sum.inl (coarseEnum j, t))
    | Sum.inr (Sum.inl ⟨j, t⟩) => Sum.inl (Sum.inl (shapeEnum j, t))
    | Sum.inr (Sum.inr (Sum.inl j)) =>
        if hj : j ∈ boundaryClusterBlock l u then Sum.inl (Sum.inr (shapeBoundaryEnum ⟨j, hj⟩))
        else Sum.inr (Sum.inr (Fin.succ (outsideBoundaryEnum ⟨j, hj⟩)))
    | Sum.inr (Sum.inr (Sum.inr _)) => Sum.inr (Sum.inr 0)
  invFun
    | Sum.inl (Sum.inl (j, t)) => Sum.inr (Sum.inl ⟨shapeEnum.symm j, t⟩)
    | Sum.inl (Sum.inr j) => Sum.inr (Sum.inr (Sum.inl (shapeBoundaryEnum.symm j).val))
    | Sum.inr (Sum.inl (j, t)) => Sum.inl ⟨coarseEnum.symm j, t⟩
    | Sum.inr (Sum.inr j) => Fin.cases (Sum.inr (Sum.inr (Sum.inr ())))
        (fun k => Sum.inr (Sum.inr (Sum.inl (outsideBoundaryEnum.symm k).val))) j
  left_inv := by
    rintro (⟨j, t⟩ | ⟨j, t⟩ | j | ⟨⟩)
    · simp
    · simp
    · by_cases hj : j ∈ boundaryClusterBlock l u <;> simp [hj, -mem_boundaryClusterBlock]
    · rfl
  right_inv := by
    rintro ((⟨j, t⟩ | j) | (⟨j, t⟩ | j))
    · simp
    · simp [(shapeBoundaryEnum.symm j).property, -mem_boundaryClusterBlock]
    · simp
    · cases j using Fin.cases with
      | zero => rfl
      | succ j => simp [(outsideBoundaryEnum.symm j).property, -mem_boundaryClusterBlock]

/-- Native coordinate labels sent to the explicit shape-first product order. -/
def nativeIndexToBlock : NativeFaceIndex i a S m ≃ Fin (shapeDegree a S l u + coarseDegree i S l u) :=
  nativeIndexSplit.trans
    ((Equiv.sumCongr (GraphForms.coordinateIndexEquiv (shapeN a S) (shapeM l u))
      (GraphForms.coordinateIndexEquiv (coarseN i S) (outsideM l u + 1))).trans finSumFinEquiv)

theorem boundary_card_sum : shapeM l u + outsideM l u = m := by
  have hs : shapeM l u = (boundaryClusterBlock l u).card :=
    Fintype.card_of_subtype (boundaryClusterBlock l u) (fun _ => Iff.rfl)
  have ho : outsideM l u = (boundaryClusterBlock l u)ᶜ.card := by
    apply Fintype.card_of_subtype
    intro j
    simp
  have hle : (boundaryClusterBlock l u).card ≤ m := by
    simpa using Finset.card_le_card (Finset.subset_univ (boundaryClusterBlock l u))
  rw [hs, ho, Finset.card_compl, Fintype.card_fin]
  omega

private def complexIndexEnum (J : Type*) [Fintype J] : (Σ _ : J, Fin 2) ≃ Fin (Fintype.card J * 2) :=
  (Equiv.sigmaEquivProd J (Fin 2)).trans
    ((Equiv.prodCongr (Fintype.equivFin J) (Equiv.refl (Fin 2))).trans finProdFinEquiv)

private def boundaryCenterIndexEnum : (Fin m ⊕ Unit) ≃ Fin (m + 1) :=
  (Equiv.sumCongr (Equiv.refl (Fin m)) (Fintype.equivFin Unit)).trans finSumFinEquiv

private def nativeIndexEnumPre : NativeFaceIndex i a S m ≃
    Fin (coarseN i S * 2 + (shapeN a S * 2 + (m + 1))) :=
  (Equiv.sumCongr (complexIndexEnum (BoundaryClusterCoarseIndex i S))
    ((Equiv.sumCongr (complexIndexEnum (BoundaryClusterShapeIndex a S)) boundaryCenterIndexEnum).trans
      finSumFinEquiv)).trans finSumFinEquiv

private theorem nativeIndexCount_eq : coarseN i S * 2 + (shapeN a S * 2 + (m + 1)) =
    shapeDegree a S l u + coarseDegree i S l u := by
  have h := boundary_card_sum (l := l) (u := u)
  simp only [shapeDegree, coarseDegree, GraphForms.dimension]
  omega

/-- Flatten the inherited native coordinate order; no tangent permutation is assumed. -/
def nativeIndexEnum : NativeFaceIndex i a S m ≃ Fin (shapeDegree a S l u + coarseDegree i S l u) :=
  nativeIndexEnumPre.trans (finCongr nativeIndexCount_eq)

/-- The actual permutation from native tangent order to shape/coarse block order. -/
def tangentBlockPermutation : Equiv.Perm (Fin (shapeDegree a S l u + coarseDegree i S l u)) :=
  nativeIndexEnum.symm.trans nativeIndexToBlock

private theorem realBasis_external_index (n m : ℕ) (j : Fin m) :
    GraphForms.realBasis n m (GraphForms.coordinateIndexEquiv n m (Sum.inr j)) = (0, Pi.single j 1) :=
  GraphForms.realBasis_external j

private theorem single_comp_symm {J K V : Type*} [DecidableEq J] [DecidableEq K] [Zero V]
    (e : J ≃ K) (j : J) (v : V) :
    (fun k => (Pi.single j v : J → V) (e.symm k)) = (Pi.single (e j) v : K → V) := by
  funext k
  by_cases hk : k = e j
  · subst k
    simp
  · have hj : e.symm k ≠ j := fun h => hk (e.symm_apply_eq.mp h)
    simp [hk, hj]

private theorem single_subtype_enum {J K V : Type*} [DecidableEq J] [DecidableEq K] [Zero V]
    (p : J → Prop) (e : {j // p j} ≃ K) (j : J) (v : V) (hj : p j) :
    (fun k => (Pi.single j v : J → V) (e.symm k).val) = (Pi.single (e ⟨j, hj⟩) v : K → V) := by
  funext k
  by_cases hk : k = e ⟨j, hj⟩
  · subst k
    simp
  · have hv : (e.symm k).val ≠ j := by
      intro h
      exact hk (e.symm_apply_eq.mp (Subtype.ext h))
    simp [hk, hv]

private theorem single_subtype_enum_zero {J K V : Type*} [DecidableEq J] [Zero V]
    (p : J → Prop) (e : {j // p j} ≃ K) (j : J) (v : V) (hj : ¬p j) :
    (fun k => (Pi.single j v : J → V) (e.symm k).val) = (0 : K → V) := by
  funext k
  have hv : (e.symm k).val ≠ j := fun h => hj (h ▸ (e.symm k).property)
  simp [hv]

private theorem finCases_zero_single {d : ℕ} (j : Fin d) (v : ℝ) :
    (fun k : Fin (d + 1) => Fin.cases 0 (Pi.single j v) k) = Pi.single j.succ v := by
  funext k
  cases k using Fin.cases <;> simp [Pi.single_apply]

private theorem finCases_single_zero {d : ℕ} (v : ℝ) :
    (fun k : Fin (d + 1) => Fin.cases v (fun _ => 0) k) = Pi.single 0 v := by
  funext k
  cases k using Fin.cases <;> simp

/-- Pointwise verification that the explicit label permutation matches genuine tangent vectors. -/
theorem splitFace_nativeFaceBasis (q : NativeFaceIndex i a S m) :
    splitFace (l := l) (u := u) (nativeFaceBasis q) =
      GraphFormProduct.productVectors
        (GraphForms.realBasis (shapeN a S) (shapeM l u))
        (GraphForms.realBasis (coarseN i S) (outsideM l u + 1)) (nativeIndexToBlock q) := by
  classical
  rcases q with (⟨j, t⟩ | ⟨j, t⟩ | j | ⟨⟩)
  · simp [nativeIndexToBlock, nativeIndexSplit, GraphFormProduct.productVectors,
      GraphForms.realBasis_internal, nativeFaceBasis, Module.Basis.prod_apply, Pi.basis_apply, splitFace,
      single_comp_symm, finCases_single_zero, Pi.zero_def]
  · simp [nativeIndexToBlock, nativeIndexSplit, GraphFormProduct.productVectors,
      GraphForms.realBasis_internal, nativeFaceBasis, Module.Basis.prod_apply, Pi.basis_apply, splitFace,
      single_comp_symm, finCases_single_zero, Pi.zero_def]
  · by_cases hj : j ∈ boundaryClusterBlock l u <;>
      simp [nativeIndexToBlock, nativeIndexSplit, GraphFormProduct.productVectors,
        realBasis_external_index, nativeFaceBasis, Module.Basis.prod_apply, Pi.basisFun_apply,
        splitFace, hj, single_subtype_enum, single_subtype_enum_zero,
        finCases_zero_single, finCases_single_zero, Pi.zero_def,
        -mem_boundaryClusterBlock]
  · simp [nativeIndexToBlock, nativeIndexSplit, GraphFormProduct.productVectors,
      realBasis_external_index, nativeFaceBasis, Module.Basis.prod_apply, splitFace,
      finCases_single_zero, Pi.zero_def]

/-- The density in the inherited native face basis, rather than a postulated product frame. -/
def nativeFaceDensity
    (edges : Fin (shapeDegree a S l u + coarseDegree i S l u) → Edge n m) (y : FaceCoordinates i a S m) : ℝ :=
  graphForm (l := l) (u := u) edges (BoundaryClusterFreeCoordinates.faceEmbedding y)
    (fun q => BoundaryClusterFreeCoordinates.faceEmbedding (nativeFaceBasis (nativeIndexEnum.symm q)))

/-- The dimension sum is the actual codimension-one configuration dimension. -/
theorem face_degree_eq (ha : a ∈ S) (hi : i ∉ S) :
    shapeDegree a S l u + coarseDegree i S l u = 2 * n + m - 3 := by
  rw [← face_dimension_split]
  exact BoundaryClusterFreeCoordinates.finrank_face ha hi

theorem nativeFaceBasis_via_product (q : NativeFaceIndex i a S m) :
    nativeFaceBasis q = splitFaceContinuous.symm (GraphFormProduct.productVectors
      (GraphForms.realBasis (shapeN a S) (shapeM l u))
      (GraphForms.realBasis (coarseN i S) (outsideM l u + 1)) (nativeIndexToBlock q)) := by
  apply (splitFace (l := l) (u := u)).injective
  rw [splitFace_nativeFaceBasis, splitFace_splitFaceContinuous_symm]

/-- Exact factorization in the inherited native face-coordinate order.
The edge and tangent signs are both computed from explicit finite bijections. -/
theorem nativeFaceDensity_eq_product
    (edges : Fin (shapeDegree a S l u + coarseDegree i S l u) → Edge n m)
    (hcount : Fintype.card {q // (edges q).1 ∈ S} = shapeDegree a S l u)
    (hnout : ∀ q, (edges q).1 ∈ S → boundaryClusterCollapses S l u (Sum.inl (edges q).2))
    (hloop : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1)
    (y : FaceCoordinates i a S m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u) :
    nativeFaceDensity (l := l) (u := u) edges y =
      (Equiv.Perm.sign (edgeBlockPermutation edges S hcount).symm : ℝ) *
        (Equiv.Perm.sign (tangentBlockPermutation (i := i) (a := a) (S := S) (l := l) (u := u)) : ℝ) *
        (GraphForms.topDensity (shapeEdges (a := a) edges S hcount hnout)
            (splitFace (l := l) (u := u) y).1 *
          GraphForms.topDensity (coarseEdges (i := i) (l := l) (u := u) edges S hcount)
            (splitFace (l := l) (u := u) y).2) := by
  let z := splitFace (l := l) (u := u) y
  have hmerge : splitFaceContinuous.symm z = y := splitFace.symm_apply_apply y
  have hpoint : faceProductEmbedding z = BoundaryClusterFreeCoordinates.faceEmbedding y := by
    change BoundaryClusterFreeCoordinates.faceEmbedding (splitFaceContinuous.symm z) = _
    rw [hmerge]
  have hraw : (faceProductEmbedding z).OpenConditions l u := by rwa [hpoint]
  have htangent (q : Fin (shapeDegree a S l u + coarseDegree i S l u)) :
      BoundaryClusterFreeCoordinates.faceEmbedding (nativeFaceBasis (nativeIndexEnum.symm q)) =
        faceProductEmbedding (GraphFormProduct.productVectors
          (GraphForms.realBasis (shapeN a S) (shapeM l u))
          (GraphForms.realBasis (coarseN i S) (outsideM l u + 1)) (tangentBlockPermutation q)) := by
    rw [nativeFaceBasis_via_product]
    rfl
  have h := graphForm_face_product edges hcount hnout hloop z hraw
    (tangentBlockPermutation (i := i) (a := a) (S := S) (l := l) (u := u))
  rw [hpoint] at h
  have hvec : (fun q => faceProductEmbedding (GraphFormProduct.productVectors
      (GraphForms.realBasis (shapeN a S) (shapeM l u))
      (GraphForms.realBasis (coarseN i S) (outsideM l u + 1)) (tangentBlockPermutation q))) =
      fun q => BoundaryClusterFreeCoordinates.faceEmbedding (nativeFaceBasis (nativeIndexEnum.symm q)) :=
    funext (fun q => (htangent q).symm)
  rw [hvec] at h
  exact h

/-- At nonzero radius this determinant is the actual ordered product of the
unmodified harmonic pullbacks, not an independently postulated face form. -/
theorem graphForm_eq_actual {r : ℕ} (edges : Fin r → Edge n m)
    (x : BoundaryClusterFreeCoordinates i a S m) (hr : x.radius ≠ 0) :
    graphForm (l := l) (u := u) edges x = GraphFormProduct.ofCovectors
      (fun q => formLinear (BoundaryClusterFreeCoordinates.actualEdgeForm l u (edges q).1 (edges q).2 x)) := by
  unfold graphForm edgeLinear
  simp_rw [BoundaryClusterFreeCoordinates.extendedEdgeForm_eq_actual x _ _ hr]

/-- A repeated edge in the actual contracted graph kills the native face density. -/
theorem nativeFaceDensity_eq_zero_of_duplicate_coarse
    (edges : Fin (shapeDegree a S l u + coarseDegree i S l u) → Edge n m)
    (hcount : Fintype.card {q // (edges q).1 ∈ S} = shapeDegree a S l u)
    (hnout : ∀ q, (edges q).1 ∈ S → boundaryClusterCollapses S l u (Sum.inl (edges q).2))
    (hloop : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1)
    (y : FaceCoordinates i a S m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u)
    (q t : Fin (coarseDegree i S l u)) (hqt : q ≠ t)
    (heq : coarseEdges (i := i) (l := l) (u := u) edges S hcount q =
      coarseEdges (i := i) (l := l) (u := u) edges S hcount t) :
    nativeFaceDensity (l := l) (u := u) edges y = 0 := by
  rw [nativeFaceDensity_eq_product edges hcount hnout hloop y hy,
    GraphForms.topDensity_eq_zero_of_duplicate _ q t hqt heq]
  simp

/-- An unhit boundary vertex of the genuine quotient graph kills the native face density. -/
theorem nativeFaceDensity_eq_zero_of_untargeted_coarse
    (edges : Fin (shapeDegree a S l u + coarseDegree i S l u) → Edge n m)
    (hcount : Fintype.card {q // (edges q).1 ∈ S} = shapeDegree a S l u)
    (hnout : ∀ q, (edges q).1 ∈ S → boundaryClusterCollapses S l u (Sum.inl (edges q).2))
    (hloop : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1)
    (y : FaceCoordinates i a S m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u)
    (j : Fin (outsideM l u + 1))
    (hj : ∀ q, (coarseEdges (i := i) (l := l) (u := u) edges S hcount q).target ≠ Sum.inr j) :
    nativeFaceDensity (l := l) (u := u) edges y = 0 := by
  rw [nativeFaceDensity_eq_product edges hcount hnout hloop y hy,
    GraphForms.topDensity_eq_zero_of_untargeted _ j hj]
  simp

section Integration

open MeasureTheory

/-- The actual inherited face density expressed in the explicit product coordinates. -/
def splitNativeFaceDensity
    (edges : Fin (shapeDegree a S l u + coarseDegree i S l u) → Edge n m)
    (z : ShapeCoordinates a S l u × CoarseCoordinates i S l u) : ℝ :=
  nativeFaceDensity (l := l) (u := u) edges (splitFaceContinuous.symm z)

theorem splitNativeFaceDensity_eq_product
    (edges : Fin (shapeDegree a S l u + coarseDegree i S l u) → Edge n m)
    (hcount : Fintype.card {q // (edges q).1 ∈ S} = shapeDegree a S l u)
    (hnout : ∀ q, (edges q).1 ∈ S → boundaryClusterCollapses S l u (Sum.inl (edges q).2))
    (hloop : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1)
    (z : ShapeCoordinates a S l u × CoarseCoordinates i S l u)
    (hy : (faceProductEmbedding z).OpenConditions l u) :
    splitNativeFaceDensity edges z =
      ((Equiv.Perm.sign (edgeBlockPermutation edges S hcount).symm : ℝ) *
        (Equiv.Perm.sign (tangentBlockPermutation (i := i) (a := a) (S := S) (l := l) (u := u)) : ℝ)) *
      (GraphForms.topDensity (shapeEdges (a := a) edges S hcount hnout) z.1 *
        GraphForms.topDensity (coarseEdges (i := i) (l := l) (u := u) edges S hcount) z.2) := by
  have h := nativeFaceDensity_eq_product edges hcount hnout hloop (splitFaceContinuous.symm z) hy
  simpa only [splitNativeFaceDensity, splitFace_splitFaceContinuous_symm] using h

variable {μ : Measure (ShapeCoordinates a S l u)} {ν : Measure (CoarseCoordinates i S l u)}
  [SFinite μ] [SFinite ν]
  {U : Set (ShapeCoordinates a S l u)} {V : Set (CoarseCoordinates i S l u)}

/-- Actual L1 of the smaller graph densities proves L1 of the inherited native face
coefficient on any admissible measurable product region. -/
theorem integrableOn_splitNativeFaceDensity
    (edges : Fin (shapeDegree a S l u + coarseDegree i S l u) → Edge n m)
    (hcount : Fintype.card {q // (edges q).1 ∈ S} = shapeDegree a S l u)
    (hnout : ∀ q, (edges q).1 ∈ S → boundaryClusterCollapses S l u (Sum.inl (edges q).2))
    (hloop : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1)
    (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hface : ∀ z ∈ U ×ˢ V, (faceProductEmbedding z).OpenConditions l u)
    (hshape : IntegrableOn (GraphForms.topDensity (shapeEdges (a := a) edges S hcount hnout)) U μ)
    (hcoarse : IntegrableOn (GraphForms.topDensity
      (coarseEdges (i := i) (l := l) (u := u) edges S hcount)) V ν) :
    IntegrableOn (splitNativeFaceDensity edges) (U ×ˢ V) (μ.prod ν) := by
  apply (integrableOn_congr_fun
    (fun z hz => splitNativeFaceDensity_eq_product edges hcount hnout hloop z (hface z hz))
    (hU.prod hV)).mpr
  apply Integrable.const_mul
  rw [← Measure.prod_restrict]
  exact hshape.mul_prod hcoarse

/-- Fubini for the actual face density, retaining its native tangent sign and edge
sign. Admissibility and L1 of each genuine smaller graph density are explicit hypotheses. -/
theorem integral_splitNativeFaceDensity
    (edges : Fin (shapeDegree a S l u + coarseDegree i S l u) → Edge n m)
    (hcount : Fintype.card {q // (edges q).1 ∈ S} = shapeDegree a S l u)
    (hnout : ∀ q, (edges q).1 ∈ S → boundaryClusterCollapses S l u (Sum.inl (edges q).2))
    (hloop : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1)
    (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hface : ∀ z ∈ U ×ˢ V, (faceProductEmbedding z).OpenConditions l u)
    (hshape : IntegrableOn (GraphForms.topDensity (shapeEdges (a := a) edges S hcount hnout)) U μ)
    (hcoarse : IntegrableOn (GraphForms.topDensity
      (coarseEdges (i := i) (l := l) (u := u) edges S hcount)) V ν) :
    (∫ z in U ×ˢ V, splitNativeFaceDensity edges z ∂μ.prod ν) =
      ((Equiv.Perm.sign (edgeBlockPermutation edges S hcount).symm : ℝ) *
        (Equiv.Perm.sign (tangentBlockPermutation (i := i) (a := a) (S := S) (l := l) (u := u)) : ℝ)) *
      ((∫ x in U, GraphForms.topDensity (shapeEdges (a := a) edges S hcount hnout) x ∂μ) *
        ∫ y in V, GraphForms.topDensity
          (coarseEdges (i := i) (l := l) (u := u) edges S hcount) y ∂ν) := by
  have he := setIntegral_congr_fun (μ := μ.prod ν) (hU.prod hV)
    (fun z hz => splitNativeFaceDensity_eq_product edges hcount hnout hloop z (hface z hz))
  rw [he, integral_const_mul]
  congr 1
  have hp : IntegrableOn (fun z : ShapeCoordinates a S l u × CoarseCoordinates i S l u =>
      GraphForms.topDensity (shapeEdges (a := a) edges S hcount hnout) z.1 *
        GraphForms.topDensity (coarseEdges (i := i) (l := l) (u := u) edges S hcount) z.2)
      (U ×ˢ V) (μ.prod ν) := by
    change Integrable _ ((μ.prod ν).restrict (U ×ˢ V))
    rw [← Measure.prod_restrict]
    exact hshape.mul_prod hcoarse
  rw [setIntegral_prod _ hp]
  simp_rw [integral_const_mul, integral_mul_const]

end Integration

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphFaceFactorization
