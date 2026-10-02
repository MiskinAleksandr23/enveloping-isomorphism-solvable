import EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestParameters
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestLeafRadii

/-! The forest extracted from each actual compactification point has exactly
that point's complete direction/ratio array. This uses convergence of the actual
telescoping parameters and continuity of the full resolved encoder. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestIdentification

open Filter Topology Configuration ForestDirectionRatioCoordinates
open ExtractedForestParameters ExtractedForestChildShapes
open scoped Classical

variable {n m : ℕ} (i : Fin n) (x : Compactification i m)

def parameters (k : ℕ) : Parameters (tree i x) := (localRadii i x k, localIncrements i x k)

def faceParameters : Parameters (tree i x) := (limitingRadii i x, canonicalIncrement i x)

theorem tendsto_parameters : Tendsto (parameters i x) atTop (𝓝 (faceParameters i x)) :=
  (tendsto_pi_nhds.mpr (tendsto_localRadii i x)).prodMk_nhds
    (tendsto_pi_nhds.mpr (tendsto_localIncrements i x))

theorem parameters_difference (k : ℕ) (p : DoubledPair n m) :
    ForestDirectionRatioCoordinates.pairDifference (tree i x) (canonicalLeaf i x) (parameters i x k) p =
      (positiveRadius i x k ⊥)⁻¹ •
        (normalizedSequence i x ((extraction i x).subsequence k)).val.pairDifference p :=
  pairDifference_eq i x k p.val.2 p.val.1

theorem parameters_admissible (k : ℕ) : Admissible (tree i x) (canonicalLeaf i x) (parameters i x k) := by
  refine ⟨fun v => (localRadii_pos i x k v).le, ?_⟩
  intro p hp
  have hz : ForestDirectionRatioCoordinates.pairDifference (tree i x) (canonicalLeaf i x)
      (parameters i x k) p = 0 := by
    rw [pairDifference_factor, hp, smul_zero]
  rw [parameters_difference] at hz
  have hne := sub_ne_zero.mpr ((point_injective i x k).ne p.property.symm)
  exact (smul_ne_zero (inv_ne_zero (positiveRadius_pos i x k ⊥).ne') hne) hz

theorem nonleaf_large (v : tree i x) (hv : ¬IsMax v) : 1 < v.val.card := by
  by_contra h
  have hc : v.val.card = 1 := by
    have := Finset.card_pos.mpr (node_nonempty i x v)
    omega
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc
  exact hv (((extraction i x).tree_leaf_iff_singleton Finset.univ
    ⟨Sum.inr i, Finset.mem_univ _⟩ v).mpr ⟨j, Finset.mem_univ _, hj⟩)

theorem limitingRadii_agree (v : tree i x) (hv : ¬IsMax v) :
    limitingRadii i x v = ForestPositiveScale.radii (tree i x) 0 v := by
  simp only [limitingRadii, ForestPositiveScale.radii, if_pos (nonleaf_large i x v hv)]

theorem face_admissible : Admissible (tree i x) (canonicalLeaf i x) (faceParameters i x) := by
  constructor
  · intro v
    simp only [faceParameters, limitingRadii]
    split_ifs <;> norm_num
  · intro p
    change ForestInsertionDifference.unitDifference (tree i x) (limitingRadii i x)
      (canonicalIncrement i x) _ _ ≠ 0
    rw [ForestLeafRadii.unitDifference_eq (tree i x) _ _ (limitingRadii_agree i x)]
    exact (shapeData i x).regularUnits_zero p

def resolvedParameters (k : ℕ) : Domain (tree i x) (canonicalLeaf i x) :=
  ⟨parameters i x k, parameters_admissible i x k⟩

def resolvedFaceParameters : Domain (tree i x) (canonicalLeaf i x) :=
  ⟨faceParameters i x, face_admissible i x⟩

theorem tendsto_resolvedParameters :
    Tendsto (resolvedParameters i x) atTop (𝓝 (resolvedFaceParameters i x)) :=
  tendsto_subtype_rng.mpr (tendsto_parameters i x)

/-- The encoder of the actual telescoping parameters equals every original
pair direction and triple ratio, before taking limits. -/
theorem resolvedParameters_eq_original (k : ℕ) :
    doubledCoordinates (tree i x) (canonicalLeaf i x) (resolvedParameters i x k) =
      directionRatioCoordinates (normalizedSequence i x ((extraction i x).subsequence k)).val := by
  rw [doubledCoordinates_eq_raw _ _ _ (localRadii_pos i x k)]
  have hr := inv_pos.mpr (positiveRadius_pos i x k ⊥)
  apply Prod.ext
  · funext p
    change complexPhase (ForestDirectionRatioCoordinates.pairDifference _ _ (parameters i x k) p) = _
    rw [parameters_difference, complexPhase_pos_real_smul hr]
    rfl
  · funext q
    apply Subtype.ext
    change ‖ForestDirectionRatioCoordinates.pairDifference _ _ (parameters i x k) (firstPair q)‖ /
        (‖ForestDirectionRatioCoordinates.pairDifference _ _ (parameters i x k) (firstPair q)‖ +
          ‖ForestDirectionRatioCoordinates.pairDifference _ _ (parameters i x k) (secondPair q)‖) = _
    simp only [parameters_difference, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    rw [← mul_add, mul_div_mul_left _ _ hr.ne']
    rfl

theorem tendsto_original_DR :
    Tendsto (fun k => directionRatioCoordinates
      (normalizedSequence i x ((extraction i x).subsequence k)).val) atTop (𝓝 (projectDR x.val)) := by
  apply Tendsto.prodMk_nhds
  · exact tendsto_pi_nhds.mpr (ReflectedForestExtraction.compactificationExtraction_directions i x)
  · exact tendsto_pi_nhds.mpr (ReflectedForestExtraction.compactificationExtraction_ratios i x)

/-- Unconditional full-coordinate identification with the SAME point used for extraction. -/
theorem resolvedFace_eq_original_DR :
    doubledCoordinates (tree i x) (canonicalLeaf i x) (resolvedFaceParameters i x) = projectDR x.val := by
  have h := (continuous_doubledCoordinates (tree i x) (canonicalLeaf i x)).continuousAt.tendsto.comp
    (tendsto_resolvedParameters i x)
  have he : (fun k => doubledCoordinates (tree i x) (canonicalLeaf i x) (resolvedParameters i x k)) =
      (fun k => directionRatioCoordinates (normalizedSequence i x ((extraction i x).subsequence k)).val) :=
    funext (resolvedParameters_eq_original i x)
  exact tendsto_nhds_unique (he ▸ h) (tendsto_original_DR i x)

/-- The admissibility producer's canonical descendant-zero face has the same
full DR array; unused leaf radii disappear from every stored coordinate. -/
theorem shapeData_resolvedFace_eq_original_DR :
    (shapeData i x).resolvedDR (shapeData i x).zeroRadius = projectDR x.val := by
  rw [← resolvedFace_eq_original_DR i x]
  exact (ForestLeafRadii.resolvedCoordinates_eq (tree i x) (canonicalLeaf i x)
    (canonicalLeaf_injective i x) (canonicalLeaf_isMax i x) _ _ (limitingRadii_agree i x)
      (canonicalIncrement i x) (face_admissible i x) _).symm

/-- Every actual compactification point is the constructed face of its extracted finite forest. -/
theorem compactFace_eq_original : (shapeData i x).compactFace i = x := by
  apply projectDR_injective_on_compactification i
  change projectDR ((shapeData i x).compactFace i).val = projectDR x.val
  rw [(shapeData i x).compactFace_projectDR, shapeData_resolvedFace_eq_original_DR]

end EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestIdentification
