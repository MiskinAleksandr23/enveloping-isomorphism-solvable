import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterInsertionJacobian
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Label coordinates for the actual interior-cluster insertion

The free original labels are partitioned into the coarse labels, the shape
labels, and the reference label.  The resulting continuous linear equivalence
groups the output of the native insertion in its actual angular-coordinate
carrier.  No admissibility or orientation hypothesis is used in this identity.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterInsertionCoordinates

open ClusterFreeCoordinates

variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

abbrev FreeIndex (i : Fin n) := {j : Fin n // j ≠ i}
abbrev LabelIndex (i a b : Fin n) (S : Finset (Fin n)) :=
  ClusterCoarseIndex i a S ⊕ ClusterShapeIndex a b S ⊕ Unit
abbrev FreeCoordinates (i : Fin n) (m : ℕ) := (FreeIndex i → ℂ) × (Fin m → ℝ)

theorem reference_ne_anchor (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) : b ≠ i := by
  intro h
  exact hba ((hanchor (h ▸ hb)).trans h.symm).symm

theorem shape_ne_anchor (hanchor : i ∈ S → a = i) (j : ClusterShapeIndex a b S) :
    j.val ≠ i := by
  intro h
  exact j.property.2.1 (h.trans (hanchor (h ▸ j.property.1)).symm)

/-- The explicit label partition, retaining the original label on every summand. -/
def labelEquiv (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i) :
    LabelIndex i a b S ≃ FreeIndex i where
  toFun
    | .inl j => ⟨j.val, j.property.2⟩
    | .inr (.inl j) => ⟨j.val, shape_ne_anchor hanchor j⟩
    | .inr (.inr _) => ⟨b, reference_ne_anchor hb hba hanchor⟩
  invFun j := if hj : j.val = a ∨ j.val ∉ S then
      .inl ⟨j.val, hj, j.property⟩
    else if hjb : j.val = b then .inr (.inr ())
    else .inr (.inl ⟨j.val, by tauto, by tauto, hjb⟩)
  left_inv j := by
    rcases j with j | j | u
    · simp only [dif_pos j.property.1]
      rfl
    · have hj : ¬(j.val = a ∨ j.val ∉ S) := by
        have := j.property
        tauto
      simp only [dif_neg hj, dif_neg j.property.2.2]
      rfl
    · have hb' : ¬(b = a ∨ b ∉ S) := by tauto
      cases u
      simp [hb']
  right_inv j := by
    dsimp
    split_ifs with hj hjb
    · rfl
    · exact Subtype.ext hjb.symm
    · rfl

@[simp] theorem labelEquiv_coarse (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (j : ClusterCoarseIndex i a S) :
    labelEquiv hb hba hanchor (.inl j) = ⟨j.val, j.property.2⟩ := rfl

@[simp] theorem labelEquiv_shape (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (j : ClusterShapeIndex a b S) :
    labelEquiv hb hba hanchor (.inr (.inl j)) = ⟨j.val, shape_ne_anchor hanchor j⟩ := rfl

@[simp] theorem labelEquiv_reference (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) :
    labelEquiv hb hba hanchor (.inr (.inr ())) =
      ⟨b, reference_ne_anchor hb hba hanchor⟩ := rfl

/-- Output coordinates: coarse pairs, shape pairs, boundaries, reference real
part, reference imaginary part.  The inverse uses the explicit label partition. -/
def outputCoordinates (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i) :
    FreeCoordinates i m ≃L[ℝ] ClusterAngularCoordinates i a b S m :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun z =>
      (fun j => z.1 ⟨j.val, j.property.2⟩,
       fun j => z.1 ⟨j.val, shape_ne_anchor hanchor j⟩,
       z.2, (z.1 ⟨b, reference_ne_anchor hb hba hanchor⟩).re,
       (z.1 ⟨b, reference_ne_anchor hb hba hanchor⟩).im)
    invFun := fun x =>
      (fun j => match (labelEquiv hb hba hanchor).symm j with
        | .inl q => x.1 q
        | .inr (.inl q) => x.2.1 q
        | .inr (.inr _) => Complex.equivRealProdCLM.symm x.2.2.2,
       x.2.2.1)
    left_inv := by
      intro z
      apply Prod.ext
      · funext j
        obtain ⟨j, rfl⟩ := (labelEquiv hb hba hanchor).surjective j
        rcases j with j | j | u
        · simp only [Equiv.symm_apply_apply]; rfl
        · simp only [Equiv.symm_apply_apply]; rfl
        · simp only [Equiv.symm_apply_apply]
          exact Complex.equivRealProdCLM.symm_apply_apply _
      · rfl
    right_inv := by
      intro x
      apply Prod.ext
      · funext j
        change (match (labelEquiv hb hba hanchor).symm
          (labelEquiv hb hba hanchor (.inl j)) with
          | .inl q => x.1 q
          | .inr (.inl q) => x.2.1 q
          | .inr (.inr _) => Complex.equivRealProdCLM.symm x.2.2.2) = x.1 j
        simp only [Equiv.symm_apply_apply]
      · apply Prod.ext
        · funext j
          change (match (labelEquiv hb hba hanchor).symm
            (labelEquiv hb hba hanchor (.inr (.inl j))) with
            | .inl q => x.1 q
            | .inr (.inl q) => x.2.1 q
            | .inr (.inr _) => Complex.equivRealProdCLM.symm x.2.2.2) = x.2.1 j
          simp only [Equiv.symm_apply_apply]
        · apply Prod.ext
          · rfl
          · change Complex.equivRealProdCLM
              (match (labelEquiv hb hba hanchor).symm
                (labelEquiv hb hba hanchor (.inr (.inr ()))) with
              | .inl q => x.1 q
              | .inr (.inl q) => x.2.1 q
              | .inr (.inr _) => Complex.equivRealProdCLM.symm x.2.2.2) = x.2.2.2
            simp only [Equiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]
    map_add' := by intros; rfl
    map_smul' := by intros; ext <;> simp [Complex.real_smul] }

/-- The actual native insertion, with only the fixed anchor omitted. -/
def insertion (x : ClusterAngularCoordinates i a b S m) : FreeCoordinates i m :=
  (fun j => x.toFree.base j.val + (x.toFree.radius : ℂ) * x.toFree.velocity j.val, x.2.2.1)

def center (x : ClusterAngularCoordinates i a b S m) : ℂ := x.toFree.base a

theorem insertion_coarse (x : ClusterAngularCoordinates i a b S m)
    (ha : a ∈ S) (hb : b ∈ S) (j : ClusterCoarseIndex i a S) :
    (insertion x).1 ⟨j.val, j.property.2⟩ = x.1 j := by
  have hrep : representative S a j.val = j.val := by
    rcases j.property.1 with h | h
    · simp [representative, h, ha]
    · simp [representative, h]
  have hv : x.toFree.velocity j.val = 0 := by
    rcases j.property.1 with h | h
    · rw [h, x.toFree.velocity_anchor]
    · exact x.toFree.velocity_zero_off ha hb j.val h
  change x.toFree.base j.val + _ = _
  rw [hv, mul_zero, add_zero]
  simp only [ClusterFreeCoordinates.base, hrep, dif_neg j.property.2,
    ClusterAngularCoordinates.toFree]
  rfl

theorem insertion_shape (x : ClusterAngularCoordinates i a b S m)
    (ha : a ∈ S) (hanchor : i ∈ S → a = i) (j : ClusterShapeIndex a b S) :
    (insertion x).1 ⟨j.val, shape_ne_anchor hanchor j⟩ =
      center x + (x.2.2.2.2 : ℂ) * x.2.1 j := by
  have hbase := x.toFree.base_eq_of_same (Or.inr ⟨j.property.1, ha⟩)
  change x.toFree.base j.val + _ = _
  rw [hbase]
  simp [center, ClusterFreeCoordinates.velocity, j.property.1,
    j.property.2.1, j.property.2.2, ClusterAngularCoordinates.toFree,
    ClusterFreeCoordinates.radius]

theorem insertion_reference (x : ClusterAngularCoordinates i a b S m)
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i) :
    (insertion x).1 ⟨b, reference_ne_anchor hb hba hanchor⟩ =
      center x + (x.2.2.2.2 : ℂ) * circleParameter x.2.2.2.1 := by
  have hbase := x.toFree.base_eq_of_same (Or.inr ⟨hb, ha⟩)
  change x.toFree.base b + _ = _
  rw [hbase, x.toFree.velocity_reference hba]
  simp only [center, ClusterAngularCoordinates.toFree, ClusterFreeCoordinates.radius, circleParameter_eq]

/-- The native grouped formula, valid at every radius, including zero. -/
theorem outputCoordinates_insertion (x : ClusterAngularCoordinates i a b S m)
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i) :
    outputCoordinates hb hba hanchor (insertion x) =
      (x.1, fun j => center x + (x.2.2.2.2 : ℂ) * x.2.1 j, x.2.2.1,
        ClusterInsertionJacobian.polarInsertion (Complex.equivRealProdCLM (center x)) x.2.2.2) := by
  apply Prod.ext
  · funext j
    exact insertion_coarse x ha hb j
  · apply Prod.ext
    · funext j
      exact insertion_shape x ha hanchor j
    · apply Prod.ext
      · rfl
      · change Complex.equivRealProdCLM
          ((insertion x).1 ⟨b, reference_ne_anchor hb hba hanchor⟩) = _
        rw [insertion_reference x ha hb hba hanchor]
        ext <;> simp [ClusterInsertionJacobian.polarInsertion, circleParameter,
          Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, mul_comm Complex.I]

end EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterInsertionCoordinates
