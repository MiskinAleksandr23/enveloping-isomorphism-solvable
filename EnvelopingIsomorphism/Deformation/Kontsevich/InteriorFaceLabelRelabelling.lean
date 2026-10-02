import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFaceDomainConverse
import EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeightRelabel

/-! Relabelling the literal coarse labels of an interior face, with the
normalization anchor transported together with the cluster. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFaceLabelRelabelling
open InteriorGraphFaceCoordinates ClusterFreeCoordinates
open scoped Classical
variable {n m : ℕ} (σ : Equiv.Perm (Fin n)) {S T : Finset (Fin n)}
  (hST : ∀ j, σ j ∈ T ↔ j ∈ S) {i a b : Fin n}

def coarseIndexEquiv : ClusterCoarseIndex i a S ≃ ClusterCoarseIndex (σ i) (σ a) T :=
  σ.subtypeEquiv (fun j => by
    change ((j = a ∨ j ∉ S) ∧ j ≠ i) ↔ ((σ j = σ a ∨ σ j ∉ T) ∧ σ j ≠ σ i)
    simp only [ne_eq, σ.injective.eq_iff, hST])

def shapeIndexEquiv : ClusterShapeIndex a b S ≃ ClusterShapeIndex (σ a) (σ b) T :=
  σ.subtypeEquiv (fun j => by
    change (j ∈ S ∧ j ≠ a ∧ j ≠ b) ↔ (σ j ∈ T ∧ σ j ≠ σ a ∧ σ j ≠ σ b)
    simp only [ne_eq, σ.injective.eq_iff, hST])

include hST in
theorem coarseN_eq : coarseN (σ i) (σ a) T = coarseN i a S :=
  (Fintype.card_congr (coarseIndexEquiv σ hST)).symm

include hST in
theorem shapeN_eq : shapeN (σ a) (σ b) T = shapeN a b S :=
  (Fintype.card_congr (shapeIndexEquiv σ hST)).symm

def coarseFreeEquiv : Fin (coarseN i a S) ≃ Fin (coarseN (σ i) (σ a) T) :=
  coarseEnum.symm.trans ((coarseIndexEquiv σ hST).trans coarseEnum)

def coarseLabelEquiv : Fin (coarseN i a S + 1) ≃ Fin (coarseN (σ i) (σ a) T + 1) :=
  (finSuccEquiv _).trans ((Equiv.optionCongr (coarseFreeEquiv σ hST)).trans (finSuccEquiv _).symm)

@[simp] theorem coarseLabelEquiv_zero : coarseLabelEquiv (i := i) (a := a) σ hST 0 = 0 := by
  simp [coarseLabelEquiv]

@[simp] theorem coarseLabelEquiv_succ (q : Fin (coarseN i a S)) :
    coarseLabelEquiv σ hST q.succ = (coarseFreeEquiv σ hST q).succ := by
  simp [coarseLabelEquiv]

include hST in
theorem representative_relabel (j : Fin n) :
    representative T (σ a) (σ j) = σ (representative S a j) := by
  simp only [representative, hST]
  split_ifs <;> rfl

theorem coarseLabel_relabel (j : Fin n) :
    coarseLabel (i := σ i) (a := σ a) (S := T) (σ j) =
      coarseLabelEquiv σ hST (coarseLabel (i := i) (a := a) (S := S) j) := by
  unfold coarseLabel
  by_cases hj : representative S a j = i
  · have hj' : representative T (σ a) (σ j) = σ i := by
      rw [representative_relabel σ hST, hj]
    simp only [dif_pos hj', dif_pos hj, coarseLabelEquiv_zero]
  · have hj' : representative T (σ a) (σ j) ≠ σ i := by
      rw [representative_relabel σ hST]
      exact σ.injective.ne hj
    rw [dif_neg hj', dif_neg hj, coarseLabelEquiv_succ]
    congr 1
    simp only [coarseFreeEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
    apply congrArg coarseEnum
    apply Subtype.ext
    exact representative_relabel σ hST j

def relabelEdge (e : Edge n m) : Edge n m := (σ e.1, Sum.map σ id e.2)

include hST in
theorem isInternal_relabel (e : Edge n m) :
    IsInternal T (relabelEdge σ e) ↔ IsInternal S e := by
  rcases e with ⟨s, t | t⟩
  · simp only [IsInternal, relabelEdge, Sum.map_inl, Sum.inl.injEq]
    constructor
    · rintro ⟨j,hj,hs,ht⟩
      subst j
      exact ⟨t,rfl,(hST s).mp hs,(hST t).mp ht⟩
    · rintro ⟨j,hj,hs,ht⟩
      subst j
      exact ⟨σ t,rfl,(hST s).mpr hs,(hST t).mpr ht⟩
  · simp [IsInternal, relabelEdge]

def relabelCoarseEdge (e : GraphForms.Edge (coarseN i a S) m) :
    GraphForms.Edge (coarseN (σ i) (σ a) T) m :=
  ⟨coarseLabelEquiv σ hST e.source, Sum.map (coarseLabelEquiv σ hST) id e.target⟩

theorem coarseEdge_relabel (e : Edge n m) :
    coarseEdge (i := σ i) (a := σ a) (S := T) (relabelEdge σ e) =
      relabelCoarseEdge σ hST (coarseEdge (i := i) (a := a) (S := S) e) := by
  rcases e with ⟨s, t | t⟩ <;>
    simp [coarseEdge, coarseTarget, relabelEdge, relabelCoarseEdge, coarseLabel_relabel σ hST]

def relabelBetween {p q : ℕ} (τ : Fin (p + 1) ≃ Fin (q + 1))
    (e : GraphForms.Edge p m) : GraphForms.Edge q m :=
  ⟨τ e.source, Sum.map τ id e.target⟩

/-- Genuine coarse graph integrals are invariant under bijective labels even
when the two native finite-coordinate counts are presented differently. -/
theorem rawIntegral_between {p q : ℕ} (h : q = p)
    (τ : Fin (p + 1) ≃ Fin (q + 1))
    (es : Fin (GraphForms.dimension q m) → GraphForms.Edge q m)
    (fs : Fin (GraphForms.dimension p m) → GraphForms.Edge p m)
    (he : ∀ j, es j = relabelBetween τ
      (fs (finCongr (congrArg (fun t => GraphForms.dimension t m) h) j))) :
    GeometricWeights.rawIntegral es = GeometricWeights.rawIntegral fs := by
  subst q
  have hfun : es = fun j => GeometricWeights.relabelEdge τ (fs j) := by
    funext j
    exact he j
  rw [hfun, GeometricWeights.rawIntegral_relabel]

end EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFaceLabelRelabelling
