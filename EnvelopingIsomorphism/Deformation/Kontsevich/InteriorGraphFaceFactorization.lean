import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceForms
import Mathlib.Logic.Equiv.Set

/-! Actual full graph-form factorization on a simple interior cluster face.
The block permutation is constructed from the native internal-edge predicate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceCoordinates
open InteriorFiberAngleSplit ClusterAngularCoordinates ContinuousAlternatingMap GraphFormProduct
open scoped Classical
variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

def IsInternal (S : Finset (Fin n)) (e : Edge n m) : Prop :=
  ∃ k, e.2 = Sum.inl k ∧ e.1 ∈ S ∧ k ∈ S

def internalTarget (e : Edge n m) (h : IsInternal S e) : Fin n := h.choose

theorem internalTarget_spec (e : Edge n m) (h : IsInternal S e) :
    e.2 = Sum.inl (internalTarget e h) ∧ e.1 ∈ S ∧ internalTarget e h ∈ S := h.choose_spec

def planarEdge (e : Edge n m) (h : IsInternal S e) : Point (shapeN a b S) × Point (shapeN a b S) :=
  (shapeLabel e.1 (internalTarget_spec e h).2.1,
    shapeLabel (internalTarget e h) (internalTarget_spec e h).2.2)

theorem planarEdge_nonloop (e : Edge n m) (h : IsInternal S e) (hne : e.2 ≠ Sum.inl e.1) :
    (planarEdge (a := a) (b := b) e h).1 ≠ (planarEdge e h).2 := by
  intro heq
  have he := shapeLabel_injective _ _ (internalTarget_spec e h).2.1 (internalTarget_spec e h).2.2 heq
  exact hne ((internalTarget_spec e h).1.trans (congrArg Sum.inl he.symm))

def edgeLinear (e : Edge n m) (y : ClusterAngularCoordinates i a b S m) :
    ClusterAngularCoordinates i a b S m →L[ℝ] ℝ :=
  formLinear (extendedEdgeForm e.1 e.2 y)

def graphForm {r : ℕ} (edges : Fin r → Edge n m) (y : ClusterAngularCoordinates i a b S m) :
    ClusterAngularCoordinates i a b S m [⋀^Fin r]→L[ℝ] ℝ :=
  ofCovectors (fun j ↦ edgeLinear (edges j) y)

def faceCovector (e : Edge n m) (x : ProductCoordinates i a b S m) :
    ProductCoordinates i a b S m →L[ℝ] ℝ :=
  (edgeLinear e (toAngular x)).comp (fderiv ℝ toAngular x)

theorem faceCovector_internal (hba : b ≠ a) (x : ProductCoordinates i a b S m)
    (hx : (toAngular x).toFree.OpenConditions) (e : Edge n m) (h : IsInternal S e)
    (hne : e.2 ≠ Sum.inl e.1) :
    faceCovector e x =
      (formLinear (rotatedEdgeForm (planarEdge e h).1 (planarEdge e h).2 x.1)).comp
        (ContinuousLinearMap.fst ℝ (ShapeCoordinates a b S) (CoarseCoordinates i a S m)) := by
  have ht := internalTarget_spec e h
  have hkj : internalTarget e h ≠ e.1 := fun he ↦ hne (ht.1.trans (congrArg Sum.inl he))
  have hf := internalEdgeForm_product hba x hx e.1 (internalTarget e h) ht.2.1 ht.2.2 hkj
  apply ContinuousLinearMap.ext
  intro v
  change extendedEdgeForm e.1 e.2 (toAngular x) (fun _ ↦ fderiv ℝ toAngular x v) = _
  rw [ht.1, extendedEdgeForm, if_pos ⟨ht.2.1, ht.2.2⟩]
  exact congrArg (fun ω : ProductCoordinates i a b S m [⋀^Fin 1]→L[ℝ] ℝ ↦ ω (fun _ ↦ v)) hf

theorem faceCovector_external (x : ProductCoordinates i a b S m)
    (hx : (toAngular x).toFree.OpenConditions) (e : Edge n m) (h : ¬IsInternal S e) :
    faceCovector e x = (GraphForms.edgeLinear (coarseEdge e) x.2).comp
      (ContinuousLinearMap.snd ℝ (ShapeCoordinates a b S) (CoarseCoordinates i a S m)) := by
  have hext : extendedEdgeForm (i := i) (a := a) (b := b) (S := S) e.1 e.2 = actualEdgeForm e.1 e.2 := by
    cases hv : e.2 with
    | inl k =>
      rw [extendedEdgeForm, if_neg]
      exact fun hk ↦ h ⟨k, hv, hk⟩
    | inr k => rfl
  apply ContinuousLinearMap.ext
  intro v
  change extendedEdgeForm e.1 e.2 (toAngular x) (fun _ ↦ fderiv ℝ toAngular x v) = _
  rw [hext]
  exact congrArg (fun ω : ProductCoordinates i a b S m [⋀^Fin 1]→L[ℝ] ℝ ↦ ω (fun _ ↦ v))
    (actualEdgeForm_product x hx e)

section Partition
variable {r s : ℕ} (edges : Fin (r + s) → Edge n m)
variable (hcount : Fintype.card {q // IsInternal S (edges q)} = r)

def internalEnum : {q // IsInternal S (edges q)} ≃ Fin r := Fintype.equivFinOfCardEq hcount

include hcount in
theorem external_card : Fintype.card {q // ¬IsInternal S (edges q)} = s := by
  rw [Fintype.card_subtype_compl, Fintype.card_fin, hcount]
  omega

def externalEnum : {q // ¬IsInternal S (edges q)} ≃ Fin s := Fintype.equivFinOfCardEq (external_card edges hcount)
def internalIndex (q : Fin r) := (internalEnum edges hcount |>.symm q).val
def externalIndex (q : Fin s) := (externalEnum edges hcount |>.symm q).val

def edgeBlockPermutation : Equiv.Perm (Fin (r + s)) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (internalEnum edges hcount).symm (externalEnum edges hcount).symm).trans
      (Equiv.sumCompl (fun q ↦ IsInternal S (edges q))))

@[simp] theorem edgeBlockPermutation_inl (q : Fin r) :
    edgeBlockPermutation edges hcount (finSumFinEquiv (Sum.inl q)) = internalIndex edges hcount q := by
  simp [edgeBlockPermutation, internalIndex]
@[simp] theorem edgeBlockPermutation_inr (q : Fin s) :
    edgeBlockPermutation edges hcount (finSumFinEquiv (Sum.inr q)) = externalIndex edges hcount q := by
  simp [edgeBlockPermutation, externalIndex]

def planarEdges : Fin r → Point (shapeN a b S) × Point (shapeN a b S) :=
  fun q ↦ planarEdge (edges (internalIndex edges hcount q)) ((internalEnum edges hcount).symm q).property

def coarseEdges : Fin s → GraphForms.Edge (coarseN i a S) m :=
  fun q ↦ coarseEdge (edges (externalIndex edges hcount q))

def planarCovectors (x : ShapeCoordinates a b S) : Fin r → ShapeCoordinates a b S →L[ℝ] ℝ :=
  fun q ↦ formLinear (rotatedEdgeForm (planarEdges edges hcount q).1 (planarEdges edges hcount q).2 x)

theorem faceCovector_block (hba : b ≠ a) (x : ProductCoordinates i a b S m)
    (hx : (toAngular x).toFree.OpenConditions) (hne : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1)
    (q : Fin (r + s)) :
    faceCovector (edges (edgeBlockPermutation edges hcount q)) x =
      productCovectors (planarCovectors edges hcount x.1)
        (fun j ↦ GraphForms.edgeLinear (coarseEdges edges hcount j) x.2) q := by
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective q
  cases q with
  | inl q =>
    rw [edgeBlockPermutation_inl]
    simpa [productCovectors, planarCovectors, planarEdges] using
      faceCovector_internal hba x hx (edges (internalIndex edges hcount q))
        ((internalEnum edges hcount).symm q).property (hne _)
  | inr q =>
    rw [edgeBlockPermutation_inr]
    simpa [productCovectors, coarseEdges] using
      faceCovector_external x hx (edges (externalIndex edges hcount q))
        ((externalEnum edges hcount).symm q).property

/-- Genuine graph pullback with both independently recorded orientation signs.
The edge permutation is the actual internal/coarse grouping; τ records the
chosen tangent-frame order. -/
theorem graphForm_product (hba : b ≠ a) (x : ProductCoordinates i a b S m)
    (hx : (toAngular x).toFree.OpenConditions) (hne : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1)
    (v : Fin r → ShapeCoordinates a b S) (w : Fin s → CoarseCoordinates i a S m)
    (τ : Equiv.Perm (Fin (r + s))) :
    (graphForm edges (toAngular x)).compContinuousLinearMap (fderiv ℝ toAngular x)
        (fun j ↦ productVectors v w (τ j)) =
      (Equiv.Perm.sign (edgeBlockPermutation edges hcount).symm : ℝ) * (Equiv.Perm.sign τ : ℝ) *
        (ofCovectors (planarCovectors edges hcount x.1) v *
          GraphForms.topForm (coarseEdges edges hcount) x.2 w) := by
  have heq (q : Fin (r + s)) : faceCovector (edges q) x =
      productCovectors (planarCovectors edges hcount x.1)
        (fun j ↦ GraphForms.edgeLinear (coarseEdges edges hcount j) x.2)
        ((edgeBlockPermutation edges hcount).symm q) := by
    have hh := faceCovector_block edges hcount hba x hx hne ((edgeBlockPermutation edges hcount).symm q)
    simpa using hh
  change ofCovectors (fun q ↦ faceCovector (edges q) x) (fun j ↦ productVectors v w (τ j)) = _
  simp_rw [heq]
  exact form_product_permuted_apply _ _ v w _ τ

end Partition
end EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceCoordinates
