import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphFaceFactorization
import EnvelopingIsomorphism.Deformation.Kontsevich.GraphCoordinateDomain

/-! Ordered boundary relabelling with exact coordinate, graph-form and domain transport. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphOrderedCoordinates
open Configuration BoundaryGraphFaceFactorization
open scoped BigOperators Classical
variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

def shapeOrderedEnum (l u : Fin (m + 1)) : ShapeBoundary l u ≃ Fin (shapeM l u) :=
  ((boundaryClusterBlock l u).orderIsoOfFin (by exact (Fintype.card_coe (boundaryClusterBlock l u)).symm)).toEquiv.symm

def outsideOrderedEnum (l u : Fin (m + 1)) : OutsideBoundary l u ≃ Fin (outsideM l u) :=
  (Equiv.subtypeEquivRight (fun j ↦ by simp)).trans
    (((boundaryClusterBlock l u)ᶜ).orderIsoOfFin (by simpa only [Finset.mem_compl] using (Fintype.card_coe ((boundaryClusterBlock l u)ᶜ)).symm)).toEquiv.symm

theorem shapeOrderedEnum_symm_strictMono :
    StrictMono (fun j : Fin (shapeM l u) ↦ ((shapeOrderedEnum l u).symm j).val) :=
  (boundaryClusterBlock l u).orderEmbOfFin (by exact (Fintype.card_coe (boundaryClusterBlock l u)).symm) |>.strictMono

theorem outsideOrderedEnum_symm_strictMono :
    StrictMono (fun j : Fin (outsideM l u) ↦ ((outsideOrderedEnum l u).symm j).val) :=
  ((boundaryClusterBlock l u)ᶜ).orderEmbOfFin (by simpa only [Finset.mem_compl] using (Fintype.card_coe ((boundaryClusterBlock l u)ᶜ)).symm) |>.strictMono

def blockOffsetEquiv (hlu : l ≤ u) : ShapeBoundary l u ≃ Fin (u.val - l.val) where
  toFun j := ⟨j.val.val - l.val, by have h := (mem_boundaryClusterBlock l u j.val).mp j.property; omega⟩
  invFun j := ⟨⟨l.val + j.val, by have hu := u.isLt; omega⟩, by simp only [mem_boundaryClusterBlock]; omega⟩
  left_inv j := by
    apply Subtype.ext
    apply Fin.ext
    change l.val + (j.val.val - l.val) = j.val.val
    have h := (mem_boundaryClusterBlock l u j.val).mp j.property
    omega
  right_inv j := by
    apply Fin.ext
    change (l.val + j.val) - l.val = j.val
    omega

theorem shapeM_eq_sub (hlu : l ≤ u) : shapeM l u = u.val - l.val := by
  have h := Fintype.card_congr (blockOffsetEquiv hlu)
  simpa only [Fintype.card_fin] using h

theorem outsideM_eq_sub (hlu : l ≤ u) : outsideM l u = m - (u.val - l.val) := by
  have h := BoundaryGraphFaceFactorization.boundary_card_sum (l := l) (u := u)
  rw [shapeM_eq_sub hlu] at h
  omega

def centerSlot (hlu : l ≤ u) : Fin (outsideM l u + 1) :=
  ⟨l.val, by rw [outsideM_eq_sub hlu]; have hu := u.isLt; have hl : l.val ≤ u.val := hlu; omega⟩

@[simp] theorem centerSlot_val (hlu : l ≤ u) : (centerSlot hlu).val = l.val := rfl

def shapePermutation (l u : Fin (m + 1)) : Equiv.Perm (Fin (shapeM l u)) :=
  shapeBoundaryEnum.symm.trans (shapeOrderedEnum l u)

def outsidePermutation (l u : Fin (m + 1)) : Equiv.Perm (Fin (outsideM l u)) :=
  outsideBoundaryEnum.symm.trans (outsideOrderedEnum l u)

def coarsePermutation (hlu : l ≤ u) : Equiv.Perm (Fin (outsideM l u + 1)) :=
  (finSuccEquiv _).trans ((Equiv.optionCongr (outsidePermutation l u)).trans (finSuccEquiv' (centerSlot hlu)).symm)

@[simp] theorem coarsePermutation_center (hlu : l ≤ u) : coarsePermutation hlu 0 = centerSlot hlu := by
  simp [coarsePermutation]

@[simp] theorem coarsePermutation_outside (hlu : l ≤ u) (j : OutsideBoundary l u) :
    coarsePermutation hlu (Fin.succ (outsideBoundaryEnum j)) =
      (centerSlot hlu).succAbove (outsideOrderedEnum l u j) := by
  change (finSuccEquiv' (centerSlot hlu)).symm (some (outsidePermutation l u (outsideBoundaryEnum j))) = _
  rw [show outsidePermutation l u (outsideBoundaryEnum j) = outsideOrderedEnum l u j by simp [outsidePermutation]]
  rfl

@[simp] theorem shapePermutation_native (j : ShapeBoundary l u) :
    shapePermutation l u (shapeBoundaryEnum j) = shapeOrderedEnum l u j := by
  simp [shapePermutation]


section BoundaryRelabel
variable {p q : ℕ}

def boundaryCoordinatesLinear (σ : Equiv.Perm (Fin q)) :
    GraphForms.Coordinates p q ≃ₗ[ℝ] GraphForms.Coordinates p q where
  toFun x := (x.1, x.2 ∘ σ.symm)
  invFun x := (x.1, x.2 ∘ σ)
  left_inv x := by apply Prod.ext; rfl; funext j; simp
  right_inv x := by apply Prod.ext; rfl; funext j; simp
  map_add' x y := rfl
  map_smul' c x := rfl

def boundaryCoordinates (σ : Equiv.Perm (Fin q)) :
    GraphForms.Coordinates p q ≃L[ℝ] GraphForms.Coordinates p q :=
  (boundaryCoordinatesLinear σ).toContinuousLinearEquiv

def boundaryVertex (σ : Equiv.Perm (Fin q)) : Equiv.Perm (GraphForms.Vertex p q) :=
  Equiv.sumCongr (Equiv.refl _) σ

def boundaryEdge (σ : Equiv.Perm (Fin q)) (e : GraphForms.Edge p q) : GraphForms.Edge p q :=
  ⟨e.source, boundaryVertex σ e.target⟩

@[simp] theorem boundaryCoordinates_fst (σ : Equiv.Perm (Fin q)) (x : GraphForms.Coordinates p q) :
    (boundaryCoordinates σ x).1 = x.1 := rfl

@[simp] theorem boundaryCoordinates_snd (σ : Equiv.Perm (Fin q)) (x : GraphForms.Coordinates p q) (j : Fin q) :
    (boundaryCoordinates σ x).2 j = x.2 (σ.symm j) := rfl

@[simp] theorem interiorPoint_boundaryCoordinates (σ : Equiv.Perm (Fin q))
    (x : GraphForms.Coordinates p q) (j : Fin (p+1)) :
    GraphForms.interiorPoint j (boundaryCoordinates σ x) = GraphForms.interiorPoint j x := rfl

@[simp] theorem vertexPoint_boundaryCoordinates (σ : Equiv.Perm (Fin q))
    (x : GraphForms.Coordinates p q) (v : GraphForms.Vertex p q) :
    GraphForms.vertexPoint (boundaryVertex σ v) (boundaryCoordinates σ x) = GraphForms.vertexPoint v x := by
  cases v with
  | inl j => rfl
  | inr j => simp [GraphForms.vertexPoint, boundaryVertex]

@[simp] theorem edgeMap_boundaryCoordinates (σ : Equiv.Perm (Fin q))
    (e : GraphForms.Edge p q) (x : GraphForms.Coordinates p q) :
    GraphForms.edgeMap (boundaryEdge σ e) (boundaryCoordinates σ x) = GraphForms.edgeMap e x := by
  apply Prod.ext
  · rfl
  · exact vertexPoint_boundaryCoordinates σ x e.target

theorem edgeTangent_boundaryCoordinates (σ : Equiv.Perm (Fin q)) (e : GraphForms.Edge p q) :
    (GraphForms.edgeTangent (boundaryEdge σ e)).comp (boundaryCoordinates σ).toContinuousLinearMap =
      GraphForms.edgeTangent e := by
  have h := ((GraphForms.hasFDerivAt_edgeMap (boundaryEdge σ e) (boundaryCoordinates σ 0)).comp 0
    (boundaryCoordinates σ).hasFDerivAt).fderiv
  have hm : GraphForms.edgeMap (boundaryEdge σ e) ∘ boundaryCoordinates σ = GraphForms.edgeMap e :=
    funext (edgeMap_boundaryCoordinates σ e)
  rw [hm, (GraphForms.hasFDerivAt_edgeMap e 0).fderiv] at h
  exact h.symm

theorem edgeForm_boundaryCoordinates (σ : Equiv.Perm (Fin q))
    (e : GraphForms.Edge p q) (x : GraphForms.Coordinates p q) :
    (GraphForms.edgeForm (boundaryEdge σ e) (boundaryCoordinates σ x)).compContinuousLinearMap
      (boundaryCoordinates σ).toContinuousLinearMap = GraphForms.edgeForm e x := by
  ext v
  simp only [GraphForms.edgeForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    edgeMap_boundaryCoordinates]
  have ht := edgeTangent_boundaryCoordinates σ e
  change harmonicAngleForm (GraphForms.edgeMap e x)
    (fun i ↦ ((GraphForms.edgeTangent (boundaryEdge σ e)).comp (boundaryCoordinates σ).toContinuousLinearMap) (v i)) = _
  rw [ht]
  rfl

theorem topForm_boundaryCoordinates {r : ℕ} (σ : Equiv.Perm (Fin q))
    (edges : Fin r → GraphForms.Edge p q) (x : GraphForms.Coordinates p q) :
    (GraphForms.topForm (fun j ↦ boundaryEdge σ (edges j)) (boundaryCoordinates σ x)).compContinuousLinearMap
      (boundaryCoordinates σ).toContinuousLinearMap = GraphForms.topForm edges x := by
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, GraphForms.topForm_apply]
  apply congrArg Matrix.det
  funext i j
  exact congrArg (fun F ↦ F (fun _ : Fin 1 ↦ v i)) (edgeForm_boundaryCoordinates σ (edges j) x)

def boundaryTangentPermutation (p : ℕ) (σ : Equiv.Perm (Fin q)) :
    Equiv.Perm (Fin (GraphForms.dimension p q)) :=
  (GraphForms.coordinateIndexEquiv p q).permCongr (Equiv.sumCongr (Equiv.refl _) σ)

@[simp] theorem boundaryTangentPermutation_sign (p : ℕ) (σ : Equiv.Perm (Fin q)) :
    (boundaryTangentPermutation p σ).sign = σ.sign := by
  simp [boundaryTangentPermutation, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr]

@[simp] theorem boundaryTangentPermutation_index (σ : Equiv.Perm (Fin q))
    (j : (Fin p × Fin 2) ⊕ Fin q) :
    boundaryTangentPermutation p σ (GraphForms.coordinateIndexEquiv p q j) =
      GraphForms.coordinateIndexEquiv p q (Equiv.sumCongr (Equiv.refl _) σ j) := by
  change GraphForms.coordinateIndexEquiv p q
    (Equiv.sumCongr (Equiv.refl _) σ ((GraphForms.coordinateIndexEquiv p q).symm
      (GraphForms.coordinateIndexEquiv p q j))) = _
  rw [Equiv.symm_apply_apply]

theorem boundaryCoordinates_realBasis (σ : Equiv.Perm (Fin q)) (j : Fin (GraphForms.dimension p q)) :
    boundaryCoordinates σ (GraphForms.realBasis p q j) =
      GraphForms.realBasis p q (boundaryTangentPermutation p σ j) := by
  obtain ⟨j, rfl⟩ := (GraphForms.coordinateIndexEquiv p q).surjective j
  rw [boundaryTangentPermutation_index]
  cases j with
  | inl j =>
      rcases j with ⟨v,t⟩
      change boundaryCoordinates σ (GraphForms.realBasis p q (GraphForms.coordinateIndexEquiv p q (Sum.inl (v,t)))) =
        GraphForms.realBasis p q (GraphForms.coordinateIndexEquiv p q (Sum.inl (v,t)))
      rw [GraphForms.realBasis_internal]
      rfl
  | inr j =>
      change boundaryCoordinates σ (GraphForms.realBasis p q (GraphForms.externalBasisIndex p j)) =
        GraphForms.realBasis p q (GraphForms.externalBasisIndex p (σ j))
      rw [GraphForms.realBasis_external, GraphForms.realBasis_external]
      apply Prod.ext
      · rfl
      · funext r
        change (Pi.single j (1 : ℝ) : Fin q → ℝ) (σ.symm r) = (Pi.single (σ j) (1 : ℝ) : Fin q → ℝ) r
        by_cases hr : r = σ j
        · subst r; simp
        · have hj : σ.symm r ≠ j := fun h ↦ hr ((σ.symm_apply_eq).mp h)
          simp [hr, hj]

theorem topDensity_boundaryCoordinates (σ : Equiv.Perm (Fin q))
    (edges : Fin (GraphForms.dimension p q) → GraphForms.Edge p q) (x : GraphForms.Coordinates p q) :
    GraphForms.topDensity (fun j ↦ boundaryEdge σ (edges j)) (boundaryCoordinates σ x) =
      (σ.sign : ℝ) * GraphForms.topDensity edges x := by
  let τ := boundaryTangentPermutation p σ
  have h := congrArg (fun F ↦ F (fun j ↦ GraphForms.realBasis p q (τ.symm j)))
    (topForm_boundaryCoordinates σ edges x)
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at h
  have hb : (fun j ↦ boundaryCoordinates σ (GraphForms.realBasis p q (τ.symm j))) = GraphForms.realBasis p q := by
    funext j
    rw [boundaryCoordinates_realBasis]
    exact congrArg (GraphForms.realBasis p q) (τ.apply_symm_apply j)
  change GraphForms.topForm (fun j ↦ boundaryEdge σ (edges j)) (boundaryCoordinates σ x)
    (fun j ↦ boundaryCoordinates σ (GraphForms.realBasis p q (τ.symm j))) = _ at h
  rw [hb] at h
  change GraphForms.topDensity (fun j ↦ boundaryEdge σ (edges j)) (boundaryCoordinates σ x) = _ at h
  rw [h, GraphForms.topForm_apply, GraphForms.topDensity, GraphForms.topForm_apply]
  have hd := Matrix.det_permute τ.symm
    (fun i j ↦ GraphForms.edgeForm (edges j) x (fun _ : Fin 1 ↦ GraphForms.realBasis p q i))
  have hm : Matrix.submatrix
      (fun i j ↦ GraphForms.edgeForm (edges j) x (fun _ : Fin 1 ↦ GraphForms.realBasis p q i)) τ.symm id =
      (fun i j ↦ GraphForms.edgeForm (edges j) x (fun _ : Fin 1 ↦ GraphForms.realBasis p q (τ.symm i))) := by
    funext i j
    rfl
  rw [hm] at hd
  simpa only [Equiv.Perm.sign_symm, τ, boundaryTangentPermutation_sign] using hd

def ReorderedAdmissible (σ : Equiv.Perm (Fin q)) (x : GraphForms.Coordinates p q) : Prop :=
  (∀ j, 0 < (x.1 j).im) ∧ Function.Injective (fun j ↦ GraphForms.interiorPoint j x) ∧ StrictMono (x.2 ∘ σ.symm)

theorem admissible_boundaryCoordinates_iff (σ : Equiv.Perm (Fin q)) (x : GraphForms.Coordinates p q) :
    GraphForms.Admissible (boundaryCoordinates σ x) ↔ ReorderedAdmissible σ x := Iff.rfl

theorem image_reorderedAdmissible (σ : Equiv.Perm (Fin q)) :
    boundaryCoordinates σ '' {x : GraphForms.Coordinates p q | ReorderedAdmissible σ x} =
      GraphForms.admissibleSet p q := by
  change boundaryCoordinates σ '' ((boundaryCoordinates σ) ⁻¹' GraphForms.admissibleSet p q) = _
  exact Set.image_preimage_eq _ (boundaryCoordinates σ).surjective

end BoundaryRelabel


theorem shapeM_pos (hlu : l < u) : 0 < shapeM l u := by
  rw [shapeM_eq_sub (le_of_lt hlu)]
  have h : l.val < u.val := hlu
  omega

theorem graft_external_count (hlu : l < u) : outsideM l u + (shapeM l u - 1) + 1 = m := by
  have hc := BoundaryGraphFaceFactorization.boundary_card_sum (l := l) (u := u)
  have hp := shapeM_pos hlu
  omega

def orderedSplitFace (hlu : l ≤ u) : FaceCoordinates i a S m ≃L[ℝ]
    ShapeCoordinates a S l u × CoarseCoordinates i S l u :=
  splitFaceContinuous.trans ((boundaryCoordinates (p := shapeN a S) (shapePermutation l u)).prodCongr
    (boundaryCoordinates (p := coarseN i S) (coarsePermutation hlu)))

@[simp] theorem orderedSplitFace_fst (hlu : l ≤ u) (y : FaceCoordinates i a S m) :
    (orderedSplitFace hlu y).1 = boundaryCoordinates (shapePermutation l u) (splitFace (l := l) (u := u) y).1 := rfl

@[simp] theorem orderedSplitFace_snd (hlu : l ≤ u) (y : FaceCoordinates i a S m) :
    (orderedSplitFace hlu y).2 = boundaryCoordinates (coarsePermutation hlu) (splitFace (l := l) (u := u) y).2 := rfl

@[simp] theorem ordered_shape_boundary (hlu : l ≤ u) (y : FaceCoordinates i a S m) (j : ShapeBoundary l u) :
    (orderedSplitFace hlu y).1.2 (shapeOrderedEnum l u j) = y.2.2.1 j.val := by
  change (boundaryCoordinates (shapePermutation l u) (splitFace (l := l) (u := u) y).1).2
    (shapeOrderedEnum l u j) = _
  rw [← shapePermutation_native j, boundaryCoordinates_snd, Equiv.symm_apply_apply]
  simp [splitFace]

@[simp] theorem ordered_coarse_center (hlu : l ≤ u) (y : FaceCoordinates i a S m) :
    (orderedSplitFace hlu y).2.2 (centerSlot hlu) = y.2.2.2 := by
  change (boundaryCoordinates (coarsePermutation hlu) (splitFace (l := l) (u := u) y).2).2 (centerSlot hlu) = _
  rw [← coarsePermutation_center hlu, boundaryCoordinates_snd, Equiv.symm_apply_apply]
  rfl

@[simp] theorem ordered_coarse_outside (hlu : l ≤ u) (y : FaceCoordinates i a S m) (j : OutsideBoundary l u) :
    (orderedSplitFace hlu y).2.2 ((centerSlot hlu).succAbove (outsideOrderedEnum l u j)) = y.2.2.1 j.val := by
  change (boundaryCoordinates (coarsePermutation hlu) (splitFace (l := l) (u := u) y).2).2 _ = _
  rw [← coarsePermutation_outside hlu j, boundaryCoordinates_snd, Equiv.symm_apply_apply]
  simp [splitFace]

def orderedShapeEdge (e : BoundaryGraphFaceFactorization.Edge n m) (hs : e.1 ∈ S)
    (ht : boundaryClusterCollapses S l u (Sum.inl e.2)) : GraphForms.Edge (shapeN a S) (shapeM l u) :=
  boundaryEdge (shapePermutation l u) (shapeEdge (a := a) e hs ht)

def orderedCoarseEdge (hlu : l ≤ u) (e : BoundaryGraphFaceFactorization.Edge n m) (hs : e.1 ∉ S) :
    GraphForms.Edge (coarseN i S) (outsideM l u + 1) :=
  boundaryEdge (coarsePermutation hlu) (coarseEdge (i := i) (l := l) (u := u) e hs)

theorem orderedShapeEdge_position (hlu : l ≤ u) (e : BoundaryGraphFaceFactorization.Edge n m)
    (hs : e.1 ∈ S) (ht : boundaryClusterCollapses S l u (Sum.inl e.2)) (y : FaceCoordinates i a S m) :
    GraphForms.edgeMap (orderedShapeEdge e hs ht) (orderedSplitFace hlu y).1 =
      BoundaryClusterFreeCoordinates.shapeFacePair l u e.1 e.2 y := by
  change GraphForms.edgeMap (boundaryEdge (shapePermutation l u) (shapeEdge e hs ht))
    (boundaryCoordinates (shapePermutation l u) (splitFace (l := l) (u := u) y).1) = _
  rw [edgeMap_boundaryCoordinates, ← shapeFacePair_eq_graph]

theorem orderedCoarseEdge_position (hlu : l ≤ u) (e : BoundaryGraphFaceFactorization.Edge n m)
    (hs : e.1 ∉ S) (y : FaceCoordinates i a S m) :
    GraphForms.edgeMap (orderedCoarseEdge hlu e hs) (orderedSplitFace hlu y).2 =
      BoundaryClusterFreeCoordinates.coarseFacePair l u e.1 e.2 y := by
  change GraphForms.edgeMap (boundaryEdge (coarsePermutation hlu) (coarseEdge e hs))
    (boundaryCoordinates (coarsePermutation hlu) (splitFace (l := l) (u := u) y).2) = _
  rw [edgeMap_boundaryCoordinates, ← coarseFacePair_eq_graph]

theorem topDensity_eq_ordered {p q : ℕ} (σ : Equiv.Perm (Fin q))
    (edges : Fin (GraphForms.dimension p q) → GraphForms.Edge p q) (x : GraphForms.Coordinates p q) :
    GraphForms.topDensity edges x = (σ.sign : ℝ) *
      GraphForms.topDensity (fun j ↦ boundaryEdge σ (edges j)) (boundaryCoordinates σ x) := by
  rw [topDensity_boundaryCoordinates, ← mul_assoc]
  have hs : (σ.sign : ℝ) * (σ.sign : ℝ) = 1 := by simp [← Int.cast_mul, ← Units.val_mul]
  rw [hs, one_mul]

theorem nativeFaceDensity_ordered (hlu : l ≤ u)
    (edges : Fin (shapeDegree a S l u + coarseDegree i S l u) → BoundaryGraphFaceFactorization.Edge n m)
    (hcount : Fintype.card {q // (edges q).1 ∈ S} = shapeDegree a S l u)
    (hnout : ∀ q, (edges q).1 ∈ S → boundaryClusterCollapses S l u (Sum.inl (edges q).2))
    (hloop : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1)
    (y : FaceCoordinates i a S m) (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u) :
    nativeFaceDensity (l := l) (u := u) edges y =
      (Equiv.Perm.sign (edgeBlockPermutation edges S hcount).symm : ℝ) *
        (tangentBlockPermutation (i := i) (a := a) (S := S) (l := l) (u := u)).sign *
        (shapePermutation l u).sign * (coarsePermutation hlu).sign *
        (GraphForms.topDensity (fun j ↦ boundaryEdge (shapePermutation l u)
          (shapeEdges (a := a) edges S hcount hnout j)) (orderedSplitFace hlu y).1 *
        GraphForms.topDensity (fun j ↦ boundaryEdge (coarsePermutation hlu)
          (coarseEdges (i := i) (l := l) (u := u) edges S hcount j)) (orderedSplitFace hlu y).2) := by
  rw [nativeFaceDensity_eq_product edges hcount hnout hloop y hy,
    topDensity_eq_ordered (shapePermutation l u), topDensity_eq_ordered (coarsePermutation hlu)]
  rw [orderedSplitFace_fst, orderedSplitFace_snd]
  ring

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphOrderedCoordinates
