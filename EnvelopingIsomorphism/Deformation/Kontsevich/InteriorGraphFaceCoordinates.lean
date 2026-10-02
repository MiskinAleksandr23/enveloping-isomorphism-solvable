import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterSmoothForms
import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarInnerFaceVanishing
import EnvelopingIsomorphism.Deformation.Kontsevich.GraphFormProduct

/-! Actual rotating planar/coarse product coordinates on a simple interior face.
All original labels are retained in the endpoint identities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceCoordinates
open InteriorFiberAngleSplit ClusterFreeCoordinates

variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

abbrev shapeN (a b : Fin n) (S : Finset (Fin n)) := Fintype.card (ClusterShapeIndex a b S)
abbrev coarseN (i a : Fin n) (S : Finset (Fin n)) := Fintype.card (ClusterCoarseIndex i a S)
abbrev shapeEnum : ClusterShapeIndex a b S ≃ Fin (shapeN a b S) := Fintype.equivFin _
abbrev coarseEnum : ClusterCoarseIndex i a S ≃ Fin (coarseN i a S) := Fintype.equivFin _
abbrev ShapeCoordinates (a b : Fin n) (S : Finset (Fin n)) := Parameters (shapeN a b S)
abbrev CoarseCoordinates (i a : Fin n) (S : Finset (Fin n)) (m : ℕ) := GraphForms.Coordinates (coarseN i a S) m
abbrev ProductCoordinates (i a b : Fin n) (S : Finset (Fin n)) (m : ℕ) :=
  ShapeCoordinates a b S × CoarseCoordinates i a S m

/-- Native cluster labels in the two-marked-point planar coordinate convention. -/
def shapeLabel (j : Fin n) (hj : j ∈ S) : Point (shapeN a b S) :=
  if hja : j = a then 0 else if hjb : j = b then 1
    else (shapeEnum ⟨j, hj, hja, hjb⟩).succ.succ

def shapeLabelInverse : Point (shapeN a b S) → Fin n :=
  Fin.cases a (Fin.cases b (fun j ↦ (shapeEnum.symm j).val))

theorem shapeLabelInverse_label (j : Fin n) (hj : j ∈ S) :
    shapeLabelInverse (shapeLabel (a := a) (b := b) j hj) = j := by
  unfold shapeLabel
  split_ifs with hja hjb
  · exact hja.symm
  · exact hjb.symm
  · simp [shapeLabelInverse]

theorem shapeLabel_injective (j k : Fin n) (hj : j ∈ S) (hk : k ∈ S)
    (h : shapeLabel (a := a) (b := b) j hj = shapeLabel k hk) : j = k := by
  have hh := congrArg (shapeLabelInverse (a := a) (b := b)) h
  simpa only [shapeLabelInverse_label] using hh

def coarseLabel (j : Fin n) : Fin (coarseN i a S + 1) :=
  if h : representative S a j = i then 0
    else (coarseEnum ⟨representative S a j, representative_mem S a j, h⟩).succ

def coarseTarget : Fin n ⊕ Fin m → GraphForms.Vertex (coarseN i a S) m
  | .inl j => .inl (coarseLabel j)
  | .inr j => .inr j

abbrev Edge (n m : ℕ) := Fin n × (Fin n ⊕ Fin m)
def coarseEdge (e : Edge n m) : GraphForms.Edge (coarseN i a S) m :=
  ⟨coarseLabel e.1, coarseTarget e.2⟩

/-- Radius zero, with every free planar velocity actually rotated by θ. -/
def toAngular (x : ProductCoordinates i a b S m) : ClusterAngularCoordinates i a b S m :=
  (fun j ↦ x.2.1 (coarseEnum j),
    fun j ↦ circleParameter x.1.1 * x.1.2 (shapeEnum j), x.2.2, x.1.1, 0)

theorem contDiff_toAngular : ContDiff ℝ ⊤ (toAngular : ProductCoordinates i a b S m → _) := by
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro j
    fun_prop
  · apply ContDiff.prodMk
    · apply contDiff_pi.mpr
      intro j
      exact (contDiff_circleParameter.comp (by fun_prop)).mul (by fun_prop)
    · fun_prop

@[simp] theorem radius_toAngular (x : ProductCoordinates i a b S m) :
    (toAngular x).toFree.radius = 0 := rfl

theorem base_toAngular (x : ProductCoordinates i a b S m) (j : Fin n) :
    (toAngular x).toFree.base j = GraphForms.interiorPoint (coarseLabel j) x.2 := by
  simp only [ClusterFreeCoordinates.base, coarseLabel]
  split_ifs <;> rfl

theorem targetBase_toAngular (x : ProductCoordinates i a b S m) (v : Fin n ⊕ Fin m) :
    (toAngular x).targetBase v = GraphForms.vertexPoint (coarseTarget v) x.2 := by
  cases v with
  | inl j => exact base_toAngular x j
  | inr j => rfl

theorem velocity_toAngular (hba : b ≠ a) (x : ProductCoordinates i a b S m)
    (j : Fin n) (hj : j ∈ S) :
    (toAngular x).toFree.velocity j = rotatedPoint x.1 (shapeLabel j hj) := by
  unfold ClusterFreeCoordinates.velocity shapeLabel
  split_ifs with hja hjb
  · simp [rotatedPoint]
  · simp [rotatedPoint, toAngular, ClusterAngularCoordinates.toFree, circleParameter_eq]
  · rfl

theorem actualPair_toAngular (x : ProductCoordinates i a b S m) (e : Edge n m) :
    ClusterAngularCoordinates.actualPair e.1 e.2 (toAngular x) =
      GraphForms.edgeMap (coarseEdge e) x.2 := by
  rw [ClusterAngularCoordinates.actualPair_face _ (radius_toAngular x)]
  exact Prod.ext (base_toAngular x e.1) (targetBase_toAngular x e.2)

/-- The actual original chart maps positive-radius points to the original
configuration; the present map is precisely its zero-radius specialization. -/
theorem position_toAngular (x : ProductCoordinates i a b S m) (j : Fin n) :
    (toAngular x).position j = GraphForms.interiorPoint (coarseLabel j) x.2 := by
  rw [ClusterAngularCoordinates.position, radius_toAngular]
  simpa using base_toAngular x j

end EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceCoordinates
