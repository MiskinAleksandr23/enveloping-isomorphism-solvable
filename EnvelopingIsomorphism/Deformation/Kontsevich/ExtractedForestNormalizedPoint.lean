import EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestDRRegion
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestParameterSpace

/-! Actual normalized, reflected marked-limit parameters with all geometric
unit inequalities derived from the original extracted child shapes. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestNormalizedPoint

open Configuration ComplexConjugate ForestMarkedFrames ForestMarkedFrameInverse
open ExtractedForestParameters ExtractedForestChildShapes ExtractedForestFrames
open ExtractedMarkedFrameLimits ExtractedMarkedFrameReflection
open ForestInsertionDifference ForestDirectionRatioCoordinates
open scoped Classical

variable {n m : ℕ} (i : Fin n) (x : Compactification i m)

def parameters : ForestDirectionRatioCoordinates.Parameters (tree i x) :=
  (limitingRadii i x, limitingIncrements i x)

theorem radii_admissible : ReflectedRadiusOrthant.Admissible (tree i x) (reflection i x) (limitingRadii i x) := by
  refine ⟨?_, ?_, limitingRadii_reflection i x, ?_⟩
  · simp [limitingRadii]
  · intro v hv
    have hc := (ClusterPartitionTree.isMax_iff_card_eq_one
      (hR := ⟨Sum.inr i, Finset.mem_univ _⟩) v).mp hv
    simp [limitingRadii, hc]
  · intro v
    simp only [limitingRadii]
    split_ifs <;> norm_num

theorem increment_root : limitingIncrements i x (⊥ : tree i x) = 0 := by simp [limitingIncrements]

theorem position_fixed_im (v : tree i x) (hv : reflection i x v = v) :
    (position (tree i x) (limitingRadii i x) (limitingIncrements i x) v).im = 0 := by
  have h := ReflectedForestInsertion.position_reflect (tree i x) (reflection i x)
    (limitingRadii i x) (limitingRadii_reflection i x)
    (limitingIncrements i x) (limitingIncrements_reflection i x) v
  rw [hv] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- Exact free frame equations at the marked limit, including real cumulative
positions at stable nodes. -/
theorem normalized : ForestMarkedFrameInverse.Normalized (tree i x) (frames i x)
    (limitingRadii i x) (limitingIncrements i x) := by
  intro v hv
  have ht := frames_typeCorrect i x v hv
  have hp := ExtractedForestFrames.leadingRadius_pos i x v hv
  cases hf : frames i x v hv with
  | complex a b ha hb hne =>
    rw [hf] at hp
    constructor
    · rw [limitingIncrements_child i x v a ha, hf]
      exact Frame.complex_zero a b ha hb hne _
    · rw [limitingIncrements_child i x v b hb, hf]
      exact Frame.complex_norm_one a b ha hb hne _ hp
  | stableHeight a ha =>
    rw [hf] at ht hp
    constructor
    · rw [limitingIncrements_child i x v a ha, hf]
      exact Frame.stableHeight_I a ha _ hp
    · exact position_fixed_im i x v ht.1
  | stableRealPair a b ha hb hne =>
    rw [hf] at ht hp
    refine ⟨?_, ?_, position_fixed_im i x v ht.1⟩
    · rw [limitingIncrements_child i x v a ha, hf]
      exact Frame.stableRealPair_zero a b ha hb hne _ ht.2.2.2.1
    · rw [limitingIncrements_child i x v b hb, hf]
      exact Frame.stableRealPair_one a b ha hb hne _ ht.2.2.2.2 hp

theorem constraints : ForestParameterSpace.Constraints (tree i x) (reflection i x) (frames i x) (parameters i x) :=
  ⟨radii_admissible i x, normalized i x, limitingIncrements_reflection i x, increment_root i x⟩

def parameterPoint : ForestParameterSpace.Space (tree i x) (reflection i x) (frames i x) :=
  ⟨parameters i x, constraints i x⟩

theorem increment_sub_children (v d e : tree i x) (hd : v ⋖ d) (he : v ⋖ e) :
    limitingIncrements i x d - limitingIncrements i x e =
      (canonicalIncrement i x d - canonicalIncrement i x e) / (leadingRadius i x v : ℂ) := by
  have hdn : d ≠ ⊥ := ne_of_gt (lt_of_le_of_lt bot_le hd.lt)
  have hen : e ≠ ⊥ := ne_of_gt (lt_of_le_of_lt bot_le he.lt)
  rw [limitingIncrements, if_neg hdn, limitingIncrements, if_neg hen, hd.pred_eq, he.pred_eq, ← sub_div]
  congr 1
  abel

theorem siblings_distinct (v d e : tree i x) (hd : v ⋖ d) (he : v ⋖ e) (hne : d ≠ e) :
    limitingIncrements i x d ≠ limitingIncrements i x e := by
  apply sub_ne_zero.mp
  rw [increment_sub_children i x v d e hd he]
  exact div_ne_zero (sub_ne_zero.mpr (canonicalIncrement_siblings_distinct i x v d e hd he hne))
    (Complex.ofReal_ne_zero.mpr (ExtractedMarkedFrameLimits.leadingRadius_pos i x v).ne')

/-- The new normalized child shapes retain every actual sibling separation
and upper/boundary sign, by division by one positive parent marked gap. -/
def normalizedShapeData : ForestPositiveScale.ShapeData (tree i x) n m :=
  { shapeData i x with
    increment := limitingIncrements i x
    increment_reflect := limitingIncrements_reflection i x
    siblings_distinct := siblings_distinct i x
    upper_gap := by
      intro j d e hd hdu he hel
      rw [increment_sub_children i x _ d e hd he, Complex.div_ofReal_im]
      exact div_pos (canonical_upper_gap i x j d e hd hdu he hel)
        (ExtractedMarkedFrameLimits.leadingRadius_pos i x _)
    boundary_gap := by
      intro j k hjk d e hd hdk he hej
      rw [increment_sub_children i x _ d e hd he, Complex.div_ofReal_re]
      exact div_pos (canonical_boundary_gap i x j k hjk d e hd hdk he hej)
        (ExtractedMarkedFrameLimits.leadingRadius_pos i x _) }

theorem regularUnits : RegularUnits (tree i x) (canonicalLeaf i x) (parameters i x) := by
  intro p
  change unitDifference (tree i x) (limitingRadii i x) (limitingIncrements i x) _ _ ≠ 0
  rw [ForestLeafRadii.unitDifference_eq (tree i x) _ _ (ExtractedForestIdentification.limitingRadii_agree i x)]
  exact (normalizedShapeData i x).regularUnits_zero p

theorem upper_unit_pos (j : Fin n) :
    0 < (unitDifference (tree i x) (limitingRadii i x) (limitingIncrements i x)
      (canonicalLeaf i x (Sum.inl (Sum.inl j))) (canonicalLeaf i x (Sum.inr j))).im := by
  rw [ForestLeafRadii.unitDifference_eq (tree i x) _ _ (ExtractedForestIdentification.limitingRadii_agree i x)]
  exact (normalizedShapeData i x).upper_unit_zero_pos j

theorem boundary_unit_pos (j k : Fin m) (hjk : j < k) :
    0 < (unitDifference (tree i x) (limitingRadii i x) (limitingIncrements i x)
      (canonicalLeaf i x (Sum.inl (Sum.inr k))) (canonicalLeaf i x (Sum.inl (Sum.inr j)))).re := by
  rw [ForestLeafRadii.unitDifference_eq (tree i x) _ _ (ExtractedForestIdentification.limitingRadii_agree i x)]
  exact (normalizedShapeData i x).boundary_unit_zero_pos j k hjk

theorem decoder_constraints : ForestParameterSpace.Constraints (tree i x) (reflection i x) (frames i x)
    (ForestDRInverse.decode (tree i x) (ExtractedForestDRReferences.lab i x) (frames i x)
      (ExtractedForestDRReferences.reference i x) (projectDR x.val)) := by
  rw [ExtractedForestDRRegion.decode_eq_limitingParameters]
  exact constraints i x

end EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestNormalizedPoint
