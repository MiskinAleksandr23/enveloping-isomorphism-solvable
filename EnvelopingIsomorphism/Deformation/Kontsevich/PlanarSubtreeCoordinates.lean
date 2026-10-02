import EnvelopingIsomorphism.Deformation.Kontsevich.SubtreeForestInsertion
import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarComplexForestCharts
import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarFiberPositions

/-! The genuine planar DR array of a fiber chart is the root-reset upper-subtree
insertion. Its positive stratum is positivity only below the collapsed upper cluster. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PlanarSubtreeCoordinates

open Configuration ExtractedForestParameters ExtractedForestChildShapes ExtractedForestFrames
open PlanarClusterFrames PlanarComplexForestCharts InteriorFiberAngleSplit
open ForestInsertionDifference ForestDirectionRatioCoordinates PlanarClusterDoubledData
open scoped Classical

variable {N : ℕ} (a : Point N) (x : Compactification a 0) (hx : PlanarClusterFiber.IsFiber a x)

abbrev ParameterSpace := ForestChartOpenImage.ParameterSpace a x
abbrev Source := ForestChartOpenImage.Source a x

def parameters (p : ParameterSpace a x) : Parameters (upperTree a x hx) :=
  SubtreeForestInsertion.parameters (tree a x) (upperNode a x hx) p.val

theorem pairUnit_eq (p : ParameterSpace a x) (e : Pair (Point N)) :
    pairUnit (tree a x) (canonicalLeaf a x) p.val (upperPair e) =
      pairUnit (upperTree a x hx) (leaf a x hx) (parameters a x hx p) e :=
  SubtreeForestInsertion.unitDifference_eq (tree a x) (upperNode a x hx) p.val.1 p.val.2 (leaf a x hx e.val.2) (leaf a x hx e.val.1)

theorem ratioValue_eq (p : ParameterSpace a x) (e : Triple (Point N)) :
    ratioValue (tree a x) (canonicalLeaf a x) p.val (upperTriple e) =
      ratioValue (upperTree a x hx) (leaf a x hx) (parameters a x hx p) e :=
  SubtreeForestInsertion.ratioValue_eq (tree a x) (upperNode a x hx) (leaf a x hx) p.val e

def domain (p : Source a x) : Domain (upperTree a x hx) (leaf a x hx) :=
  ⟨parameters a x hx p.val,
    SubtreeForestInsertion.radius_nonneg (tree a x) (upperNode a x hx) p.val.val.1 p.val.property.1.2.2.2,
    fun e => (pairUnit_eq a x hx p.val e).symm ▸ p.property.1 (upperPair e)⟩

/-- Equality of every retained direction and triple ratio, including on all deeper corners. -/
theorem upperDR_eq (p : Source a x) :
    projectUpper (ForestChartConfigurations.fullDR (shapeData a x) (ForestChartOpenImage.toCorner a x p)) =
      resolvedCoordinates (upperTree a x hx) (leaf a x hx) (domain a x hx p) := by
  apply Prod.ext
  · funext e
    exact congrArg complexPhase (pairUnit_eq a x hx p.val e)
  · funext e
    apply Subtype.ext
    exact ratioValue_eq a x hx p.val e

theorem forward_upperDR (p : Source a x) :
    projectUpper (projectDR (ForestChartOpenImage.forward a x p).val) =
      resolvedCoordinates (upperTree a x hx) (leaf a x hx) (domain a x hx p) := by
  change projectUpper (projectDR (ForestChartConfigurations.compactificationInsertion
    (shapeData a x) a (ForestChartOpenImage.toCorner a x p)).val) = _
  rw [ForestChartConfigurations.compactificationInsertion_projectDR, upperDR_eq]

/-- The upper root radius is deliberately absent from this positivity condition. -/
def PositiveBelowUpper (p : ParameterSpace a x) : Prop :=
  ∀ v : upperTree a x hx, v ≠ ⊥ → ¬IsMax v → 0 < p.val.1 v.val

theorem radius_pos (p : ParameterSpace a x) (hp : PositiveBelowUpper a x hx p)
    (v : upperTree a x hx) : 0 < (parameters a x hx p).1 v := by
  by_cases hv : v = ⊥
  · subst v
    change 0 < SubtreeForestInsertion.radius (tree a x) (upperNode a x hx) p.val.1 ⊥
    rw [SubtreeForestInsertion.radius_root]
    exact zero_lt_one
  · change 0 < SubtreeForestInsertion.radius (tree a x) (upperNode a x hx) p.val.1 v
    rw [SubtreeForestInsertion.radius_nonroot _ _ _ _ hv]
    by_cases hn : IsMax v
    · rw [p.property.1.2.1 v.val ((PlanarComplexForestCharts.isMax_iff a x hx v).mp hn)]
      exact zero_lt_one
    · exact hp v hv hn

def positions (p : ParameterSpace a x) (j : Point N) : ℂ :=
  position (upperTree a x hx) (parameters a x hx p).1 (parameters a x hx p).2 (leaf a x hx j)

theorem positions_eq_branchUnit (p : ParameterSpace a x) (j : Point N) :
    positions a x hx p j = branchUnit (tree a x) p.val.1 p.val.2 (upperNode a x hx)
      (canonicalLeaf a x (Sum.inl (Sum.inl j))) :=
  SubtreeForestInsertion.position_eq_branchUnit (tree a x) (upperNode a x hx) p.val.1 p.val.2 (leaf a x hx j)

theorem positions_injective (p : Source a x) (hp : PositiveBelowUpper a x hx p.val) :
    Function.Injective (positions a x hx p.val) := by
  intro j k he
  by_contra hjk
  exact ForestDRInverse.inserted_reference_ne (upperTree a x hx) (leaf a x hx)
    (domain a x hx p) (radius_pos a x hx p.val hp) j k hjk he

theorem upperDR_eq_ofPositions (p : Source a x) (hp : PositiveBelowUpper a x hx p.val) :
    projectUpper (projectDR (ForestChartOpenImage.forward a x p).val) =
      MarkedDRIdentification.ofPositions (positions a x hx p.val) := by
  rw [forward_upperDR, resolvedCoordinates_eq_raw _ _ _ (radius_pos a x hx p.val hp)]
  rfl

variable (b : Point N) (hab : a ≠ b)

def referenceRadius (p : ParameterSpace a x) : ℝ := ‖positions a x hx p b - positions a x hx p a‖

include hab

theorem referenceRadius_pos (p : Source a x) (hp : PositiveBelowUpper a x hx p.val) :
    0 < referenceRadius a x hx b p.val :=
  norm_pos_iff.mpr (sub_ne_zero.mpr ((positions_injective a x hx p hp).ne hab.symm))

/-- Literal translation and positive scaling of the noncollapsed upper-subtree positions. -/
def normalized (p : Source a x) (hp : PositiveBelowUpper a x hx p.val) :
    PlanarClusterCompactification.Normalized a b :=
  ⟨fun j => (positions a x hx p.val j - positions a x hx p.val a) / (referenceRadius a x hx b p.val : ℂ), by
    intro j k he
    apply positions_injective a x hx p hp
    have h := congrArg (fun z : ℂ => z * (referenceRadius a x hx b p.val : ℂ)) he
    rw [div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (referenceRadius_pos a x hx b hab p hp).ne'),
      div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (referenceRadius_pos a x hx b hab p hp).ne')] at h
    exact sub_left_inj.mp h,
    by simp,
    by rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (referenceRadius_pos a x hx b hab p hp).le]
       exact div_self (referenceRadius_pos a x hx b hab p hp).ne'⟩

theorem normalized_encode (p : Source a x) (hp : PositiveBelowUpper a x hx p.val) :
    PlanarClusterCompactification.encode a b (normalized a x hx b hab p hp) =
      MarkedDRIdentification.ofPositions (positions a x hx p.val) := by
  have hd (j k : Point N) :
      (normalized a x hx b hab p hp).val k - (normalized a x hx b hab p hp).val j =
        (referenceRadius a x hx b p.val)⁻¹ • (positions a x hx p.val k - positions a x hx p.val j) := by
    change (_ / _) - (_ / _) = _
    rw [← sub_div]
    have he : (positions a x hx p.val k - positions a x hx p.val a) -
        (positions a x hx p.val j - positions a x hx p.val a) =
        positions a x hx p.val k - positions a x hx p.val j := by abel
    rw [he]
    simp only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]
  have hr := inv_pos.mpr (referenceRadius_pos a x hx b hab p hp)
  apply Prod.ext
  · funext e
    change complexPhase ((normalized a x hx b hab p hp).val e.val.2 -
      (normalized a x hx b hab p hp).val e.val.1) = _
    rw [hd, complexPhase_pos_real_smul hr]
    rfl
  · funext e
    apply Subtype.ext
    change ‖(normalized a x hx b hab p hp).val e.val.2.1 - (normalized a x hx b hab p hp).val e.val.1‖ /
      (‖(normalized a x hx b hab p hp).val e.val.2.1 - (normalized a x hx b hab p hp).val e.val.1‖ +
        ‖(normalized a x hx b hab p hp).val e.val.2.2 - (normalized a x hx b hab p hp).val e.val.1‖) = _
    simp only [hd, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    rw [← mul_add, mul_div_mul_left _ _ hr.ne']
    rfl

/-- The genuine planar point represented by the forest chart is exactly this
original normalized upper-subtree configuration on the positive planar stratum. -/
theorem projection_eq_normalized_embedding (p : Source a x) (hp : PositiveBelowUpper a x hx p.val) :
    PlanarClusterFiber.projection a b hab (ForestChartOpenImage.forward a x p) =
      PlanarClusterCompactification.embedding a b (normalized a x hx b hab p hp) := by
  apply Subtype.ext
  change projectUpper (projectDR (ForestChartOpenImage.forward a x p).val) =
    PlanarClusterCompactification.encode a b (normalized a x hx b hab p hp)
  rw [upperDR_eq_ofPositions a x hx p hp, normalized_encode]

end EnvelopingIsomorphism.Deformation.Kontsevich.PlanarSubtreeCoordinates
