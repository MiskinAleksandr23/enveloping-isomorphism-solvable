import EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFaceReconstruction
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestSimpleOverlap

/-! A necessary and sufficient finite-tree criterion for reverse paired-face
coverage, with the original label mask retained. This does not assume or claim
that the criterion follows from simple collision data: that remaining analytic
identification must show that the actual extracted tree has just the upper
collision cluster and its reflected mate as nonroot internal nodes. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestReverseCoverageCriterion

open Configuration ExtractedForestParameters ExtractedForestFrames
open ReflectedRadiusCoordinates ForestRadialFaceClassification ForestRadialClusterLabels
open ForestRadialFaceReconstruction
open scoped Classical

variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m)
  (S : Finset (Fin (n + 1)))

/-- Original upper labels, viewed in the doubled label set. -/
def upperMask : Finset (DoubledLabel (n + 1) m) := S.image (fun j => Sum.inl (Sum.inl j))

/-- The reflected mask is literal reflection of the original upper mask. -/
def lowerMask : Finset (DoubledLabel (n + 1) m) := (upperMask (m := m) S).image doubledReflection

theorem isUpper_of_label (u : ActiveNode (tree 0 x)) (hu : u.val.val = upperMask S) :
    IsUpper 0 x u.val := by
  intro a ha
  rw [hu] at ha
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
  exact ⟨j, rfl⟩

theorem interiorLabels_of_label (u : ActiveNode (tree 0 x)) (hu : u.val.val = upperMask S) :
    interiorLabels 0 x u.val = S := by
  ext j
  simp only [mem_interiorLabels, hu, upperMask, Finset.mem_image,
    Sum.inl.injEq, exists_eq_right]

/-- A concrete upper active node supplies the paired kind; it is not an
additional face classification hypothesis. -/
theorem kind_of_label (u : ActiveNode (tree 0 x)) (hu : u.val.val = upperMask S) :
    kind 0 x (orbitClass (tree 0 x) (reflection 0 x) (reflection_reflection 0 x) u) = .paired := by
  rw [kind_orbitClass, nodeKind_paired_iff]
  intro he
  have hupper := isUpper_of_label x S u hu
  exact not_isUpper_reflection 0 x u.val hupper (he.symm ▸ hupper)

/-- No other active labels means no other radial orbit, including orbits
hidden below the collision node. -/
theorem unique_orbit_of_labels (u : ActiveNode (tree 0 x))
    (hu : u.val.val = upperMask S)
    (hlabels : ∀ v : ActiveNode (tree 0 x),
      v.val.val = upperMask S ∨ v.val.val = lowerMask S) :
    ∀ o : ForestRadialFaceClassification.Orbit 0 x,
      o = orbitClass (tree 0 x) (reflection 0 x) (reflection_reflection 0 x) u := by
  intro o
  induction o using Quotient.inductionOn with
  | h v =>
    apply (orbitClass_eq_iff _ _ _ v u).mpr
    rcases hlabels v with hv | hv
    · exact Or.inl (Subtype.ext (Subtype.ext (hv.trans hu.symm)))
    · right
      apply Subtype.ext
      apply (reflection 0 x).injective
      change reflection 0 x (reflection 0 x v.val) = reflection 0 x u.val
      rw [reflection_reflection]
      apply Subtype.ext
      rw [reflection_label, hu]
      exact hv

/-- The canonical upper representative recovers the original mask exactly. -/
theorem upperNode_labels_of_label (u : ActiveNode (tree 0 x))
    (hu : u.val.val = upperMask S) :
    PairedForestSimpleCluster.S x
      (orbitClass (tree 0 x) (reflection 0 x) (reflection_reflection 0 x) u)
      (kind_of_label x S u hu) = S := by
  have he : upperNode 0 x
      (orbitClass (tree 0 x) (reflection 0 x) (reflection_reflection 0 x) u)
      (kind_of_label x S u hu) = u := by
    exact ((existsUnique_upper_node 0 x _ (kind_of_label x S u hu)).choose_spec.2
      u ⟨rfl, isUpper_of_label x S u hu⟩).symm
  change interiorLabels 0 x (upperNode 0 x _ _).val = S
  rw [he]
  exact interiorLabels_of_label x S u hu

/-- Sharp reverse-coverage criterion. The right side mentions only the finite
labels of actual active nodes; the left side is membership of the actual
localized strict face with the prescribed mask and literal point equality. -/
theorem source_with_mask_iff :
    (∃ (o : ForestRadialFaceClassification.Orbit 0 x) (ho : kind 0 x o = .paired)
      (z : ForestRadialFaceLocalization.source hdim x o),
      PairedForestSimpleCluster.S x o ho = S ∧
      PairedForestSimpleOverlap.facePoint hdim x o z = x) ↔
    (∃ u : ActiveNode (tree 0 x), u.val.val = upperMask S ∧
      ∀ v : ActiveNode (tree 0 x),
        v.val.val = upperMask S ∨ v.val.val = lowerMask S) := by
  constructor
  · rintro ⟨o, ho, z, hS, hz⟩
    have huniq := unique_orbit_of_source_center hdim x o z hz
    let u := upperNode 0 x o ho
    have hu : u.val.val = upperMask S := by
      rw [isUpper_label_eq_image 0 x u.val (upperNode_spec 0 x o ho).2]
      change (PairedForestSimpleCluster.S x o ho).image _ = _
      rw [hS]
      rfl
    refine ⟨u, hu, ?_⟩
    intro v
    have he := (orbitClass_eq_iff _ _ _ u v).mp
      ((upperNode_spec 0 x o ho).1.trans (huniq _).symm)
    rcases he with he | he
    · left
      exact (congrArg (fun v : ActiveNode (tree 0 x) => v.val.val) he).symm.trans hu
    · right
      have hev : reflection 0 x u.val = v.val := congrArg Subtype.val he
      rw [← hev, reflection_label, hu]
      rfl
  · rintro ⟨u, hu, hlabels⟩
    let o := orbitClass (tree 0 x) (reflection 0 x) (reflection_reflection 0 x) u
    have ho : kind 0 x o = .paired := kind_of_label x S u hu
    obtain ⟨z, hz⟩ := exists_source_center_of_unique_orbit hdim x o
      (unique_orbit_of_labels x S u hu hlabels)
    exact ⟨o, ho, z, upperNode_labels_of_label x S u hu, hz⟩

/-- The criterion also produces the already constructed normalized simple
slice, whose full insertion is the original compactification point. -/
theorem exists_slice_of_active_labels
    (hlabels : ∃ u : ActiveNode (tree 0 x), u.val.val = upperMask S ∧
      ∀ v : ActiveNode (tree 0 x), v.val.val = upperMask S ∨ v.val.val = lowerMask S) :
    ∃ (o : ForestRadialFaceClassification.Orbit 0 x) (ho : kind 0 x o = .paired)
      (z : ForestRadialFaceLocalization.source hdim x o),
      PairedForestSimpleCluster.S x o ho = S ∧
      (PairedForestSimpleCluster.slice hdim x o ho z).insertion = x := by
  obtain ⟨o, ho, z, hS, hz⟩ := (source_with_mask_iff hdim x S).mpr hlabels
  exact ⟨o, ho, z, hS, (PairedForestSimpleOverlap.slice_insertion hdim x o ho z).trans hz⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestReverseCoverageCriterion
