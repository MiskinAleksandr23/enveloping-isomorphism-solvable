import EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestChartCoverage
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestMarkedFactoryNormalized

/-! Fixed extracted frames decode every original configuration in their open
reference region into actual normalized reflected parameters. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestOriginalDecode

open Configuration ComplexConjugate ForestMarkedFrames ForestInsertionDifference
open ForestDirectionRatioCoordinates ExtractedForestParameters ExtractedForestChildShapes
open ExtractedForestFrames ExtractedForestDRReferences ExtractedForestDRRegion
open scoped Classical

variable {n m : ℕ} (i : Fin n) (x : Compactification i m)

def input (c : Configuration n m) (v : tree i x) : ℂ := c.doubledPoint (lab i x v)

theorem lab_reflection_leaf (v : tree i x) (hv : IsMax v) :
    lab i x (reflection i x v) = doubledReflection (lab i x v) := by
  obtain ⟨j, _, hj⟩ := ((extraction i x).tree_leaf_iff_singleton Finset.univ
    ⟨Sum.inr i, Finset.mem_univ _⟩ v).mp hv
  have he : v = canonicalLeaf i x j := Subtype.ext hj
  subst v
  rw [canonicalLeaf_reflect, lab_canonicalLeaf, lab_canonicalLeaf]

theorem input_reflection_leaf (c : Configuration n m) (v : tree i x) (hv : IsMax v) :
    input i x c (reflection i x v) = conj (input i x c v) := by
  rw [input, lab_reflection_leaf i x v hv, Configuration.doubledPoint_reflection]
  rfl

theorem realPairFixed : ForestMarkedFactoryNormalized.RealPairFixed (tree i x) (reflection i x) (frames i x) := by
  intro v hv a b ha hb hne hf
  have ht := frames_typeCorrect i x v hv
  rw [hf] at ht
  exact ⟨ht.2.1, ht.2.2.1⟩

theorem compatible (c : Configuration n m) :
    ForestDRInverse.Compatible (tree i x) (frames i x) (reference i x) c.doubledPoint :=
  ForestDRInverse.compatible_of_reflection (tree i x) (frames i x) (reference i x) doubledReflection
    (referenceModes i x) c.doubledPoint c.doubledPoint_reflection

theorem references_distinct (c : Configuration n m) :
    ForestDRInverse.DistinctReferences (tree i x) (reference i x) c.doubledPoint :=
  fun A hA => c.doubledPoint_injective.ne (reference_ne i x A hA)

/-- Local recovered-radius positivity in the actual decoder Region forces
positive gaps of the fixed recursive factory on any original configuration. -/
theorem positiveGaps (c : Configuration n m)
    (hc : directionRatioCoordinates c ∈ ForestDRInverse.Region (tree i x) (lab i x) (frames i x) (reference i x)) :
    input i x c ∈ ForestMarkedFrames.PositiveGaps (tree i x) (frames i x) := by
  intro A
  by_cases hA : IsMax A
  · simp [ForestMarkedFrames.radius, hA]
  · have h := (hc A hA).2
    change 0 < radius (tree i x) (frames i x)
      (ForestDRParameterIdentification.recoveredArray (tree i x) (lab i x) A (reference i x A hA)
        (MarkedDRIdentification.ofPositions c.doubledPoint)) A at h
    rw [ForestDRParameterIdentification.radius_recovered_ofPositions (tree i x) (lab i x)
      (frames i x) A (reference i x A hA) c.doubledPoint (input i x c)
      (references_distinct i x c A hA) (fun _ _ _ => rfl) (compatible i x c A hA) A le_rfl hA] at h
    exact (div_pos_iff_of_pos_right (norm_pos_iff.mpr
      (sub_ne_zero.mpr (references_distinct i x c A hA).symm))).mp h

def factoryParameters (c : Configuration n m) : Parameters (tree i x) :=
  (ForestLeafRadii.fixLeaves (tree i x) (ForestMarkedFrames.localRadii (tree i x) (frames i x) (input i x c)),
    ForestMarkedFrames.increments (tree i x) (frames i x) (input i x c))

theorem decode_eq_factory (c : Configuration n m)
    (hc : directionRatioCoordinates c ∈ ForestDRInverse.Region (tree i x) (lab i x) (frames i x) (reference i x)) :
    ForestDRInverse.decode (tree i x) (lab i x) (frames i x) (reference i x) (directionRatioCoordinates c) =
      factoryParameters i x c :=
  ForestDRInverse.decode_ofPositions (tree i x) (lab i x) (frames i x) (reference i x) c.doubledPoint
    (input i x c) (references_distinct i x c) (fun _ _ => rfl) (compatible i x c) (positiveGaps i x c hc)

theorem factory_constraints (c : Configuration n m)
    (hc : directionRatioCoordinates c ∈ ForestDRInverse.Region (tree i x) (lab i x) (frames i x) (reference i x)) :
    ForestParameterSpace.Constraints (tree i x) (reflection i x) (frames i x) (factoryParameters i x c) :=
  ForestMarkedFactoryNormalized.constraints_factory (tree i x) (reflection i x) (frames i x)
    (ExtractedMarkedFrameReflection.compatible i x) (realPairFixed i x) (input i x c)
      (input_reflection_leaf i x c) (positiveGaps i x c hc)

theorem decoder_constraints (c : Configuration n m)
    (hc : directionRatioCoordinates c ∈ ForestDRInverse.Region (tree i x) (lab i x) (frames i x) (reference i x)) :
    ForestParameterSpace.Constraints (tree i x) (reflection i x) (frames i x)
      (ForestDRInverse.decode (tree i x) (lab i x) (frames i x) (reference i x) (directionRatioCoordinates c)) := by
  rw [decode_eq_factory i x c hc]
  exact factory_constraints i x c hc

theorem factory_radii_pos (c : Configuration n m)
    (hc : directionRatioCoordinates c ∈ ForestDRInverse.Region (tree i x) (lab i x) (frames i x) (reference i x))
    (v : tree i x) : 0 < (factoryParameters i x c).1 v := by
  change 0 < ForestLeafRadii.fixLeaves (tree i x) _ v
  by_cases hv : IsMax v
  · simp [ForestLeafRadii.fixLeaves, hv]
  · simp only [ForestLeafRadii.fixLeaves, if_neg hv]
    exact ForestMarkedFrames.localRadii_pos _ _ _ (positiveGaps i x c hc) v

def rootCenter (c : Configuration n m) : ℂ := center (tree i x) (frames i x) ⊥ (input i x c)
def rootRadius (c : Configuration n m) : ℝ := radius (tree i x) (frames i x) (input i x c) ⊥

theorem rootCenter_real (c : Configuration n m) : (rootCenter i x c).im = 0 :=
  ForestMarkedFactoryNormalized.center_fixed_im (tree i x) (reflection i x) (frames i x)
    (ExtractedMarkedFrameReflection.compatible i x) (input i x c) (input_reflection_leaf i x c) ⊥
      (reflection i x).map_bot

theorem leaf_position (c : Configuration n m)
    (hc : directionRatioCoordinates c ∈ ForestDRInverse.Region (tree i x) (lab i x) (frames i x) (reference i x))
    (j : DoubledLabel n m) :
    position (tree i x) (factoryParameters i x c).1 (factoryParameters i x c).2 (canonicalLeaf i x j) =
      (rootRadius i x c)⁻¹ • (c.doubledPoint j - rootCenter i x c) := by
  change position (tree i x) (ForestLeafRadii.fixLeaves (tree i x) _) _ _ = _
  rw [← ForestLeafRadii.position_eq (tree i x) _ _ (ForestLeafRadii.fixLeaves_agree (tree i x) _)]
  have h := ForestNormalizationTelescope.position_localRadius_increment (tree i x)
    (radius (tree i x) (frames i x) (input i x c)) (positiveGaps i x c hc)
    (centers (tree i x) (frames i x) (input i x c)) (canonicalLeaf i x j)
  simpa only [centers_apply, center_leaf _ _ _ (canonicalLeaf_isMax i x j), input,
    lab_canonicalLeaf, rootRadius, rootCenter, factoryParameters,
    ForestMarkedFrames.localRadii, ForestMarkedFrames.increments] using h

theorem position_difference (c : Configuration n m)
    (hc : directionRatioCoordinates c ∈ ForestDRInverse.Region (tree i x) (lab i x) (frames i x) (reference i x))
    (v w : DoubledLabel n m) :
    position (tree i x) (factoryParameters i x c).1 (factoryParameters i x c).2 (canonicalLeaf i x v) -
      position (tree i x) (factoryParameters i x c).1 (factoryParameters i x c).2 (canonicalLeaf i x w) =
        (rootRadius i x c)⁻¹ • (c.doubledPoint v - c.doubledPoint w) := by
  rw [leaf_position i x c hc, leaf_position i x c hc, ← smul_sub]
  congr 1
  abel

theorem rootRadius_pos (c : Configuration n m)
    (hc : directionRatioCoordinates c ∈ ForestDRInverse.Region (tree i x) (lab i x) (frames i x) (reference i x)) :
    0 < rootRadius i x c := positiveGaps i x c hc ⊥

theorem regularUnits (c : Configuration n m)
    (hc : directionRatioCoordinates c ∈ ForestDRInverse.Region (tree i x) (lab i x) (frames i x) (reference i x)) :
    ForestDirectionRatioCoordinates.RegularUnits (tree i x) (canonicalLeaf i x) (factoryParameters i x c) := by
  intro p hp
  change unitDifference (tree i x) (factoryParameters i x c).1 (factoryParameters i x c).2
    (canonicalLeaf i x p.val.2) (canonicalLeaf i x p.val.1) = 0 at hp
  have hz := position_sub_position (tree i x) (factoryParameters i x c).1 (factoryParameters i x c).2
    (canonicalLeaf i x p.val.2) (canonicalLeaf i x p.val.1)
  rw [hp, smul_zero, position_difference i x c hc] at hz
  exact (smul_ne_zero (inv_ne_zero (rootRadius_pos i x c hc).ne')
    (sub_ne_zero.mpr (c.doubledPoint_injective.ne p.property.symm))) hz

theorem unit_projection_pos (c : Configuration n m)
    (hc : directionRatioCoordinates c ∈ ForestDRInverse.Region (tree i x) (lab i x) (frames i x) (reference i x))
    (v w : DoubledLabel n m) (f : ℂ →L[ℝ] ℝ) (h : 0 < f (c.doubledPoint v - c.doubledPoint w)) :
    0 < f (unitDifference (tree i x) (factoryParameters i x c).1 (factoryParameters i x c).2
      (canonicalLeaf i x v) (canonicalLeaf i x w)) := by
  have hpos : 0 < f (position (tree i x) (factoryParameters i x c).1 (factoryParameters i x c).2 (canonicalLeaf i x v) -
      position (tree i x) (factoryParameters i x c).1 (factoryParameters i x c).2 (canonicalLeaf i x w)) := by
    rw [position_difference i x c hc, map_smul]
    exact mul_pos (inv_pos.mpr (rootRadius_pos i x c hc)) h
  rw [position_sub_position, map_smul] at hpos
  exact (mul_pos_iff_of_pos_left (AncestorScaleRatios.scale_pos _ (factory_radii_pos i x c hc) _)).mp hpos

theorem openConditions (c : Configuration n m)
    (hc : directionRatioCoordinates c ∈ ForestDRInverse.Region (tree i x) (lab i x) (frames i x) (reference i x)) :
    ForestChartConfigurations.OpenConditions (shapeData i x) (factoryParameters i x c) := by
  refine ⟨regularUnits i x c hc, ?_, ?_⟩
  · intro j
    apply unit_projection_pos i x c hc _ _ Complex.imCLM
    change 0 < (c.doubledPoint (Sum.inl (Sum.inl j)) - c.doubledPoint (Sum.inr j)).im
    have h := (c.interior j).im_pos
    simpa only [doubledPoint, vertexPoint, Sum.elim_inl, Complex.sub_im, Complex.conj_im,
      sub_neg_eq_add, UpperHalfPlane.coe_im] using add_pos h h
  · intro j k hjk
    apply unit_projection_pos i x c hc _ _ Complex.reCLM
    change 0 < (c.doubledPoint (Sum.inl (Sum.inr k)) - c.doubledPoint (Sum.inl (Sum.inr j))).re
    simpa only [doubledPoint, vertexPoint, Sum.elim_inl, Sum.elim_inr, Complex.sub_re,
      Complex.ofReal_re] using sub_pos.mpr (c.boundary_strictMono hjk)

theorem decoder_openConditions (c : Configuration n m)
    (hc : directionRatioCoordinates c ∈ ForestDRInverse.Region (tree i x) (lab i x) (frames i x) (reference i x)) :
    ForestChartConfigurations.OpenConditions (shapeData i x)
      (ForestDRInverse.decode (tree i x) (lab i x) (frames i x) (reference i x) (directionRatioCoordinates c)) := by
  rw [decode_eq_factory i x c hc]
  exact openConditions i x c hc

def chartPoint (c : Configuration n m)
    (hc : directionRatioCoordinates c ∈ ForestDRInverse.Region (tree i x) (lab i x) (frames i x) (reference i x)) :
    ForestChartConfigurations.CornerDomain (shapeData i x) :=
  ⟨factoryParameters i x c, (factory_constraints i x c hc).1,
    (factory_constraints i x c hc).2.2.1, openConditions i x c hc⟩

theorem chartPoint_eq_decode (c : Configuration n m)
    (hc : directionRatioCoordinates c ∈ ForestDRInverse.Region (tree i x) (lab i x) (frames i x) (reference i x)) :
    (chartPoint i x c hc).val =
      ForestDRInverse.decode (tree i x) (lab i x) (frames i x) (reference i x) (directionRatioCoordinates c) :=
  (decode_eq_factory i x c hc).symm

/-- The actual fixed-frame decoder is also a forward right inverse on every
original configuration in the explicit open Region. -/
theorem fullDR_chartPoint (c : Configuration n m)
    (hc : directionRatioCoordinates c ∈ ForestDRInverse.Region (tree i x) (lab i x) (frames i x) (reference i x)) :
    ForestChartConfigurations.fullDR (shapeData i x) (chartPoint i x c hc) = directionRatioCoordinates c := by
  change doubledCoordinates (tree i x) (canonicalLeaf i x) _ = _
  rw [doubledCoordinates_eq_raw _ _ _ (factory_radii_pos i x c hc)]
  have hd (p : DoubledPair n m) :
      ForestDirectionRatioCoordinates.pairDifference (tree i x) (canonicalLeaf i x) (factoryParameters i x c) p =
        (rootRadius i x c)⁻¹ • c.pairDifference p := position_difference i x c hc p.val.2 p.val.1
  have hr := inv_pos.mpr (rootRadius_pos i x c hc)
  apply Prod.ext
  · funext p
    change complexPhase (ForestDirectionRatioCoordinates.pairDifference _ _ (factoryParameters i x c) p) = _
    rw [hd, complexPhase_pos_real_smul hr]
    rfl
  · funext q
    apply Subtype.ext
    change ‖ForestDirectionRatioCoordinates.pairDifference _ _ (factoryParameters i x c) (firstPair q)‖ /
      (‖ForestDirectionRatioCoordinates.pairDifference _ _ (factoryParameters i x c) (firstPair q)‖ +
        ‖ForestDirectionRatioCoordinates.pairDifference _ _ (factoryParameters i x c) (secondPair q)‖) = _
    simp only [hd, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    rw [← mul_add, mul_div_mul_left _ _ hr.ne']
    rfl

theorem compactificationInsertion_eq_original (c : Configuration.Normalized i m)
    (hc : directionRatioCoordinates c.val ∈ ForestDRInverse.Region (tree i x) (lab i x) (frames i x) (reference i x)) :
    ForestChartConfigurations.compactificationInsertion (shapeData i x) i (chartPoint i x c.val hc) =
      compactificationEmbedding i c := by
  apply projectDR_injective_on_compactification i
  change projectDR (ForestChartConfigurations.compactificationInsertion (shapeData i x) i (chartPoint i x c.val hc)).val = _
  rw [ForestChartConfigurations.compactificationInsertion_projectDR, fullDR_chartPoint]
  rfl

end EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestOriginalDecode
