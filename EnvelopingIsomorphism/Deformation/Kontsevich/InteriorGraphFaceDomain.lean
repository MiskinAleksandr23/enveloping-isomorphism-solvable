import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceFactorization
import EnvelopingIsomorphism.Deformation.Kontsevich.GraphCoordinateDomain

/-! The full shape/coarse product is genuinely admissible at radius zero. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceCoordinates
open InteriorFiberAngleSplit ClusterFreeCoordinates
variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

 theorem coarseLabel_rep (j : Fin n) :
    Fin.cases i (fun q ↦ (coarseEnum (i := i) (a := a) (S := S)).symm q |>.val) (coarseLabel j) =
      representative S a j := by
  unfold coarseLabel
  split_ifs with h
  · exact h.symm
  · simp

theorem coarseLabel_eq_imp (j k : Fin n) (h : coarseLabel (i := i) (a := a) (S := S) j = coarseLabel k) :
    representative S a j = representative S a k := by
  have hh := congrArg (Fin.cases i (fun q ↦ (coarseEnum (i := i) (a := a) (S := S)).symm q |>.val)) h
  simpa only [coarseLabel_rep] using hh

theorem representative_ne (ha : a ∈ S) (j k : Fin n) (h : ¬sameInteriorClusterBase S j k) :
    representative S a j ≠ representative S a k := by
  have hjk : j ≠ k := fun he ↦ h (Or.inl he)
  have hboth : ¬(j ∈ S ∧ k ∈ S) := fun he ↦ h (Or.inr he)
  by_cases hj : j ∈ S <;> by_cases hk : k ∈ S
  · exact False.elim (hboth ⟨hj, hk⟩)
  · simp only [representative, if_pos hj, if_neg hk]
    exact fun he ↦ hk (he ▸ ha)
  · simp only [representative, if_neg hj, if_pos hk]
    exact fun he ↦ hj (he.symm ▸ ha)
  · simpa only [representative, if_neg hj, if_neg hk] using hjk

/-- No extra admissibility premise is needed on the full original product domain. -/
theorem openConditions_toAngular (ha : a ∈ S) (hba : b ≠ a)
    (x : ProductCoordinates i a b S m)
    (hshape : x.1.2 ∈ shapeConfiguration (shapeN a b S)) (hcoarse : GraphForms.Admissible x.2) :
    (toAngular x).toFree.OpenConditions := by
  have hpos (j : Fin n) : 0 < ((toAngular x).toFree.base j).im := by
    rw [base_toAngular]
    exact hcoarse.interiorPoint_im_pos _
  have hsep (j k : Fin n) (h : ¬sameInteriorClusterBase S j k) :
      (toAngular x).toFree.base j ≠ (toAngular x).toFree.base k := by
    rw [base_toAngular, base_toAngular]
    intro he
    exact representative_ne ha j k h (coarseLabel_eq_imp j k (hcoarse.2.1 he))
  refine ⟨⟨⟨a, ha⟩, hpos, hsep, ?_, hcoarse.2.2⟩, ?_, ?_⟩
  · intro j k hjk hsame
    rcases hsame with he | ⟨hj, hk⟩
    · exact False.elim (hjk he)
    · change (toAngular x).toFree.velocity j ≠ (toAngular x).toFree.velocity k
      rw [velocity_toAngular hba x j hj, velocity_toAngular hba x k hk]
      intro he
      apply hjk
      apply shapeLabel_injective j k hj hk
      apply hshape
      exact mul_left_cancel₀ (circleParameter_ne_zero x.1.1) he
  · intro j
    change 0 * ‖(toAngular x).toFree.velocity j‖ < ((toAngular x).toFree.base j).im
    simpa using hpos j
  · intro j k h
    change 0 * ‖(toAngular x).toFree.velocity j - (toAngular x).toFree.velocity k‖ <
      ‖(toAngular x).toFree.base j - (toAngular x).toFree.base k‖
    simpa using norm_pos_iff.mpr (sub_ne_zero.mpr (hsep j k h))

end EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceCoordinates
