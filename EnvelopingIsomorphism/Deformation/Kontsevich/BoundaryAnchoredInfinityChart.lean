import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryAnchoredInfinityIdentification
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryAnchoredInfinityTopology

/-! Joint continuity of the genuine infinity insertion in every shape, coarse
boundary, and radial parameter. The combinatorial collision mask is fixed;
no outside interior label is required. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryAnchoredInfinityDomain

open Configuration Topology Set

variable {n m : ℕ} {a : Fin n} {l u : Fin (m + 1)} {o : Fin m}

def coordinates (x : BoundaryAnchoredInfinityDomain a m l u o) : DRData n m :=
  x.datum.resolvedDR x.scale

@[fun_prop] theorem continuous_activeDifference (p : DoubledPair n m) :
    Continuous (fun x : BoundaryAnchoredInfinityDomain a m l u o ↦
      x.datum.activeDifference x.scale p) := by
  unfold BoundaryAnchoredInfinityData.activeDifference
  fun_prop

theorem activeDifference_ne_zero (x : BoundaryAnchoredInfinityDomain a m l u o)
    (p : DoubledPair n m) (hp : ¬ boundaryAnchoredInfinityPairCollapses l u p) :
    x.datum.activeDifference x.scale p ≠ 0 :=
  BoundaryAnchoredInfinityData.activeDifference_ne_zero x.property p
    (fun h ↦ hp ((x.datum.pairBase_eq_zero_iff_pairCollapses p).mp h))

@[fun_prop] theorem continuous_coordinates :
    Continuous (coordinates : BoundaryAnchoredInfinityDomain a m l u o → DRData n m) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro p
    change Continuous (fun x : BoundaryAnchoredInfinityDomain a m l u o ↦
      if x.datum.pairBase p = 0 then _ else _)
    simp only [BoundaryAnchoredInfinityData.pairBase_eq_zero_iff_pairCollapses]
    by_cases hp : boundaryAnchoredInfinityPairCollapses l u p
    · simp only [if_pos hp]
      apply continuous_iff_continuousAt.mpr
      intro x
      have hne := x.datum.pairVelocity_ne_zero_of_pairBase_eq_zero p
        ((x.datum.pairBase_eq_zero_iff_pairCollapses p).mpr hp)
      exact (continuousAt_complexPhase hne).comp
        (f := fun y : BoundaryAnchoredInfinityDomain a m l u o ↦ y.datum.pairVelocity p)
        (x := x) ((BoundaryAnchoredInfinityData.continuous_pairVelocity p).comp continuous_datum).continuousAt
    · simp only [if_neg hp]
      apply continuous_iff_continuousAt.mpr
      intro x
      exact (continuousAt_complexPhase (x.activeDifference_ne_zero p hp)).comp
        (f := fun y : BoundaryAnchoredInfinityDomain a m l u o ↦ y.datum.activeDifference y.scale p)
        (x := x) (continuous_activeDifference p).continuousAt
  · apply continuous_pi
    intro t
    let p : DoubledPair n m := ⟨(t.val.1, t.val.2.1), t.property.1⟩
    let q : DoubledPair n m := ⟨(t.val.1, t.val.2.2), t.property.2⟩
    change Continuous (fun x : BoundaryAnchoredInfinityDomain a m l u o ↦
      if x.datum.pairBase p = 0 ∧ x.datum.pairBase q = 0 then _ else _)
    simp only [BoundaryAnchoredInfinityData.pairBase_eq_zero_iff_pairCollapses]
    by_cases hpq : boundaryAnchoredInfinityPairCollapses l u p ∧ boundaryAnchoredInfinityPairCollapses l u q
    · simp only [if_pos hpq]
      apply continuous_iff_continuousAt.mpr
      intro x
      have hne : ¬ (x.datum.pairVelocity p = 0 ∧ x.datum.pairVelocity q = 0) := by
        intro h
        exact x.datum.pairVelocity_ne_zero_of_pairBase_eq_zero p
          ((x.datum.pairBase_eq_zero_iff_pairCollapses p).mpr hpq.1) h.1
      have hpair : Continuous (fun y : BoundaryAnchoredInfinityDomain a m l u o ↦
          (y.datum.pairVelocity p, y.datum.pairVelocity q)) := by fun_prop
      exact (continuousAt_normalizedNormRatio _ _ hne).comp
        (f := fun y : BoundaryAnchoredInfinityDomain a m l u o ↦
          (y.datum.pairVelocity p, y.datum.pairVelocity q)) (x := x) hpair.continuousAt
    · simp only [if_neg hpq]
      apply continuous_iff_continuousAt.mpr
      intro x
      have hne : ¬ (x.datum.activeDifference x.scale p = 0 ∧
          x.datum.activeDifference x.scale q = 0) := by
        intro h
        by_cases hp : boundaryAnchoredInfinityPairCollapses l u p
        · exact x.activeDifference_ne_zero q (fun hq ↦ hpq ⟨hp, hq⟩) h.2
        · exact x.activeDifference_ne_zero p hp h.1
      exact (continuousAt_normalizedNormRatio _ _ hne).comp
        (f := fun y : BoundaryAnchoredInfinityDomain a m l u o ↦
          (y.datum.activeDifference y.scale p, y.datum.activeDifference y.scale q)) (x := x)
        ((continuous_activeDifference p).prodMk (continuous_activeDifference q)).continuousAt

def insertion (x : BoundaryAnchoredInfinityDomain a m l u o) : Compactification a m :=
  x.datum.compactInsertion x.property

@[fun_prop] theorem continuous_insertion :
    Continuous (insertion : BoundaryAnchoredInfinityDomain a m l u o → Compactification a m) :=
  (toDRHomeomorph a).symm.continuous.comp (continuous_coordinates.subtype_mk _)

@[simp] theorem insertion_projectDR (x : BoundaryAnchoredInfinityDomain a m l u o) :
    projectDR x.insertion.val = x.coordinates :=
  x.datum.compactInsertion_projectDR x.property

theorem insertion_pos (x : BoundaryAnchoredInfinityDomain a m l u o) (hr : 0 < x.scale) :
    x.insertion = compactificationEmbedding a
      (x.datum.normalized (x.property.isSafeScale hr) hr (le_refl x.scale)) :=
  x.datum.compactInsertion_pos x.property hr

@[simp] theorem insertion_zeroParameter (D : BoundaryAnchoredInfinityData a m l u o) :
    (zeroParameter D).insertion = D.compactInsertion D.admissibleScale_zero := rfl

theorem insertion_eq_zero_of_scale_zero (x : BoundaryAnchoredInfinityDomain a m l u o)
    (hr : x.scale = 0) : x.insertion = x.datum.compactInsertion x.datum.admissibleScale_zero := by
  apply projectDR_injective_on_compactification a
  change projectDR x.insertion.val = projectDR (x.datum.compactInsertion x.datum.admissibleScale_zero).val
  rw [insertion_projectDR, x.datum.compactInsertion_projectDR]
  change x.datum.resolvedDR x.scale = x.datum.resolvedDR 0
  rw [hr]

theorem insertion_shape (x : BoundaryAnchoredInfinityDomain a m l u o) (j : Fin n) :
    x.insertion.val.1 (Sum.inl j) = ((x.datum.shape j : ℂ) : OnePoint ℂ) :=
  x.datum.compactInsertion_shape x.property j

theorem insertion_boundary_inside (x : BoundaryAnchoredInfinityDomain a m l u o)
    (j : Fin m) (hj : j ∈ boundaryClusterBlock l u) :
    x.insertion.val.1 (Sum.inr j) = ((x.datum.boundaryVelocity j : ℂ) : OnePoint ℂ) :=
  x.datum.compactInsertion_boundary_inside x.property j hj

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryAnchoredInfinityDomain
