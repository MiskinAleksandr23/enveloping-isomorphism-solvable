import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceDomain

/-! The converse product-domain characterization on the actual zero-radius
interior face. All shape and coarse admissibility conditions are recovered. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceCoordinates
open InteriorFiberAngleSplit ClusterFreeCoordinates
open scoped Classical
variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

theorem shapeLabelInverse_mem (ha : a ∈ S) (hb : b ∈ S)
    (j : Point (shapeN a b S)) : shapeLabelInverse (a := a) (b := b) (S := S) j ∈ S := by
  refine Fin.cases ?_ (fun j => ?_) j
  · exact ha
  · refine Fin.cases ?_ (fun j => ?_) j
    · exact hb
    · exact (shapeEnum.symm j).property.1

theorem shapeLabel_labelInverse (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (j : Point (shapeN a b S)) :
    shapeLabel (shapeLabelInverse (a := a) (b := b) (S := S) j)
      (shapeLabelInverse_mem ha hb j) = j := by
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [shapeLabelInverse, shapeLabel]
  · refine Fin.cases ?_ (fun j => ?_) j
    · change shapeLabel b hb = (1 : Point (shapeN a b S))
      simp [shapeLabel, hba]
    · simp only [shapeLabelInverse, Fin.cases_succ]
      have hj := (shapeEnum (a := a) (b := b) (S := S)).symm j |>.property
      simp [shapeLabel, hj.2.1, hj.2.2]

theorem coarseLabel_surjective (hanchor : i ∈ S → a = i) :
    Function.Surjective (coarseLabel (i := i) (a := a) (S := S)) := by
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · refine ⟨i, ?_⟩
    have hi : representative S a i = i := by
      by_cases hi : i ∈ S
      · simp [representative, hi, hanchor hi]
      · simp [representative, hi]
    simp [coarseLabel, hi]
  · let k := (coarseEnum (i := i) (a := a) (S := S)).symm j
    refine ⟨k.val, ?_⟩
    simp only [coarseLabel, representative_coarse k, dif_neg k.property.2]
    change (coarseEnum k).succ = j.succ
    simp only [k, Equiv.apply_symm_apply]

theorem coarseLabel_eq_of_same {j k : Fin n} (h : sameInteriorClusterBase S j k) :
    coarseLabel (i := i) (a := a) (S := S) j = coarseLabel k := by
  rcases h with rfl | ⟨hj, hk⟩
  · rfl
  · simp only [coarseLabel, representative, if_pos hj, if_pos hk]

/-- The actual open angular face conditions force both the planar shape
configuration and the native coarse graph configuration, without extra premises. -/
theorem shape_coarse_of_openConditions_toAngular (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (x : ProductCoordinates i a b S m)
    (hx : (toAngular x).toFree.OpenConditions) :
    x.1.2 ∈ shapeConfiguration (shapeN a b S) ∧ GraphForms.Admissible x.2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j k he
    let j' := shapeLabelInverse (a := a) (b := b) (S := S) j
    let k' := shapeLabelInverse (a := a) (b := b) (S := S) k
    have hj : j' ∈ S := shapeLabelInverse_mem ha hb j
    have hk : k' ∈ S := shapeLabelInverse_mem ha hb k
    have hv : (toAngular x).toFree.velocity j' = (toAngular x).toFree.velocity k' := by
      rw [velocity_toAngular hba x j' hj, velocity_toAngular hba x k' hk]
      simp only [j', k', shapeLabel_labelInverse ha hb hba, rotatedPoint]
      exact congrArg (fun z : ℂ => circleParameter x.1.1 * z) he
    have hjk : j' = k' := by
      by_contra hne
      exact hx.1.2.2.2.1 j' k' hne (Or.inr ⟨hj, hk⟩) hv
    have heq := congrArg (fun v : {v : Fin n // v ∈ S} => shapeLabel (a := a) (b := b) v.val v.property)
      (show (⟨j',hj⟩ : {v : Fin n // v ∈ S}) = ⟨k',hk⟩ from Subtype.ext hjk)
    simpa only [j', k', shapeLabel_labelInverse ha hb hba] using heq
  · intro j
    obtain ⟨k, hk⟩ := coarseLabel_surjective hanchor j.succ
    have hpos := hx.1.2.1 k
    change 0 < ((toAngular x).toFree.base k).im at hpos
    rw [base_toAngular, hk] at hpos
    exact hpos
  · intro j k he
    obtain ⟨u, rfl⟩ := coarseLabel_surjective hanchor j
    obtain ⟨v, rfl⟩ := coarseLabel_surjective hanchor k
    by_contra hne
    have hsep := hx.1.2.2.1 u v (fun h => hne (coarseLabel_eq_of_same h))
    apply hsep
    change (toAngular x).toFree.base u = (toAngular x).toFree.base v
    rw [base_toAngular, base_toAngular]
    exact he
  · exact hx.1.2.2.2.2

/-- Exact characterization of the actual product domain at radius zero. -/
theorem openConditions_toAngular_iff (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (x : ProductCoordinates i a b S m) :
    (toAngular x).toFree.OpenConditions ↔
      x.1.2 ∈ shapeConfiguration (shapeN a b S) ∧ GraphForms.Admissible x.2 :=
  ⟨shape_coarse_of_openConditions_toAngular ha hb hba hanchor x,
    fun hx => openConditions_toAngular ha hba x hx.1 hx.2⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceCoordinates
