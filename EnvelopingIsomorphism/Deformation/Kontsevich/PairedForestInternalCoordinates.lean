import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestResolvedCoordinates

/-! Literal internal directions and ratios for the normalized native subtree
velocities used in the extracted simple cluster. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestInternalCoordinates
open Configuration ExtractedForestParameters ExtractedForestFrames ExtractedForestChildShapes
open ForestRadialFaceClassification ForestRadialClusterLabels ForestOrthantRealization
open ForestInsertionDifference AncestorScaleRatios ComplexConjugate
open BoxStokes PairedForestCoarsePositions PairedForestSimpleCluster
open ForestDirectionRatioCoordinates
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m)
  (o : ForestRadialFaceClassification.Orbit 0 x) (ho : kind 0 x o = .paired)
  (z : ForestRadialFaceLocalization.source hdim x o)

omit hdim z in
def upperPair (j k : Fin (n + 1)) (h : j ≠ k) : DoubledPair (n + 1) m :=
  ⟨(Sum.inl (Sum.inl j), Sum.inl (Sum.inl k)), fun he => h (Sum.inl.inj (Sum.inl.inj he))⟩

omit hdim z in
def upperTriple (j k l : Fin (n + 1)) (hjk : j ≠ k) (hjl : j ≠ l) : DoubledTriple (n + 1) m :=
  ⟨(Sum.inl (Sum.inl j), Sum.inl (Sum.inl k), Sum.inl (Sum.inl l)),
    fun he => hjk (Sum.inl.inj (Sum.inl.inj he)), fun he => hjl (Sum.inl.inj (Sum.inl.inj he))⟩

theorem direction_shape (j k : Fin (n + 1)) (hj : j ∈ S x o ho) (hk : k ∈ S x o ho) (hjk : j ≠ k) :
    direction (tree 0 x) (canonicalLeaf 0 x) (PairedForestCoarsePositions.parameters hdim x o z) (upperPair j k hjk) =
      complexPhase (shapePosition hdim x o ho z k - shapePosition hdim x o ho z j) := by
  obtain ⟨a, rfl⟩ : j ∈ Set.range (ActualPairedForestPlanarFactor.labels x o ho) :=
    (ActualPairedForestPlanarFactor.labels_range x o ho).symm ▸ hj
  obtain ⟨b, rfl⟩ : k ∈ Set.range (ActualPairedForestPlanarFactor.labels x o ho) :=
    (ActualPairedForestPlanarFactor.labels_range x o ho).symm ▸ hk
  have hab : a ≠ b := fun h => hjk (congrArg _ h)
  have H := ForestDescendantPlanarCoordinates.project_forward_eq_ofPositions 0 x (node x o ho)
    (ActualPairedForestPlanarFactor.labels x o ho) (ActualPairedForestPlanarFactor.labels_injective x o ho)
    (ActualPairedForestPlanarFactor.labels_below x o ho)
    (PairedForestCoarsePositions.sourcePoint hdim x o z) (positiveBelow hdim x o ho z)
  rw [ForestChartOpenImage.forward, ForestChartConfigurations.compactificationInsertion_projectDR] at H
  have h := congrArg (fun d => d.1 (⟨(a, b), hab⟩ : Pair _)) H
  change complexPhase (unitDifference (tree 0 x)
    (PairedForestCoarsePositions.sourcePoint hdim x o z).val.val.1
    (PairedForestCoarsePositions.sourcePoint hdim x o z).val.val.2 _ _) =
      complexPhase (branchUnit _ _ _ _ _ - branchUnit _ _ _ _ _) at h
  rw [sourcePoint_parameters] at h
  exact h

theorem ratio_shape (j k l : Fin (n + 1)) (hj : j ∈ S x o ho)
    (hk : k ∈ S x o ho) (hl : l ∈ S x o ho) (hjk : j ≠ k) (hjl : j ≠ l) :
    ratioValue (tree 0 x) (canonicalLeaf 0 x) (PairedForestCoarsePositions.parameters hdim x o z)
      (upperTriple j k l hjk hjl) =
      (normalizedNormRatio (shapePosition hdim x o ho z k - shapePosition hdim x o ho z j)
        (shapePosition hdim x o ho z l - shapePosition hdim x o ho z j) : ℝ) := by
  obtain ⟨a, rfl⟩ : j ∈ Set.range (ActualPairedForestPlanarFactor.labels x o ho) :=
    (ActualPairedForestPlanarFactor.labels_range x o ho).symm ▸ hj
  obtain ⟨b, rfl⟩ : k ∈ Set.range (ActualPairedForestPlanarFactor.labels x o ho) :=
    (ActualPairedForestPlanarFactor.labels_range x o ho).symm ▸ hk
  obtain ⟨c, rfl⟩ : l ∈ Set.range (ActualPairedForestPlanarFactor.labels x o ho) :=
    (ActualPairedForestPlanarFactor.labels_range x o ho).symm ▸ hl
  have hab : a ≠ b := fun h => hjk (congrArg _ h)
  have hac : a ≠ c := fun h => hjl (congrArg _ h)
  have H := ForestDescendantPlanarCoordinates.project_forward_eq_ofPositions 0 x (node x o ho)
    (ActualPairedForestPlanarFactor.labels x o ho) (ActualPairedForestPlanarFactor.labels_injective x o ho)
    (ActualPairedForestPlanarFactor.labels_below x o ho)
    (PairedForestCoarsePositions.sourcePoint hdim x o z) (positiveBelow hdim x o ho z)
  rw [ForestChartOpenImage.forward, ForestChartConfigurations.compactificationInsertion_projectDR] at H
  have h := congrArg (fun d => (d.2 (⟨(a, b, c), hab, hac⟩ : Triple _) : ℝ)) H
  change ratioValue (tree 0 x) (canonicalLeaf 0 x)
    (PairedForestCoarsePositions.sourcePoint hdim x o z).val.val _ =
      (normalizedNormRatio (branchUnit _ _ _ _ _ - branchUnit _ _ _ _ _)
        (branchUnit _ _ _ _ _ - branchUnit _ _ _ _ _) : ℝ) at h
  rw [sourcePoint_parameters] at h
  exact h

theorem velocity_sub (j k : Fin (n + 1)) (hj : j ∈ S x o ho) (hk : k ∈ S x o ho) :
    velocity hdim x o ho z k - velocity hdim x o ho z j =
      (shapeRadius hdim x o ho z)⁻¹ • (shapePosition hdim x o ho z k - shapePosition hdim x o ho z j) := by
  rw [velocity, if_pos hk, velocity, if_pos hj]
  simp only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
  ring

theorem direction_upper (j k : Fin (n + 1)) (hj : j ∈ S x o ho) (hk : k ∈ S x o ho) (hjk : j ≠ k) :
    direction (tree 0 x) (canonicalLeaf 0 x) (PairedForestCoarsePositions.parameters hdim x o z) (upperPair j k hjk) =
      complexPhase ((datum hdim x o ho z).toInteriorCollisionData.pairVelocity (upperPair j k hjk)) := by
  change _ = complexPhase (velocity hdim x o ho z k - velocity hdim x o ho z j)
  rw [velocity_sub hdim x o ho z j k hj hk,
    complexPhase_pos_real_smul (inv_pos.mpr (shapeRadius_pos hdim x o ho z))]
  exact direction_shape hdim x o ho z j k hj hk hjk

theorem ratio_upper (j k l : Fin (n + 1)) (hj : j ∈ S x o ho)
    (hk : k ∈ S x o ho) (hl : l ∈ S x o ho) (hjk : j ≠ k) (hjl : j ≠ l) :
    ratioValue (tree 0 x) (canonicalLeaf 0 x) (PairedForestCoarsePositions.parameters hdim x o z)
      (upperTriple j k l hjk hjl) =
      (normalizedNormRatio ((datum hdim x o ho z).toInteriorCollisionData.pairVelocity (upperPair j k hjk))
        ((datum hdim x o ho z).toInteriorCollisionData.pairVelocity (upperPair j l hjl)) : ℝ) := by
  change _ = (normalizedNormRatio (velocity hdim x o ho z k - velocity hdim x o ho z j)
    (velocity hdim x o ho z l - velocity hdim x o ho z j) : ℝ)
  rw [velocity_sub hdim x o ho z j k hj hk, velocity_sub hdim x o ho z j l hj hl]
  simp only [Complex.real_smul]
  rw [normalizedNormRatio_pos_real_mul _ (inv_pos.mpr (shapeRadius_pos hdim x o ho z))]
  exact ratio_shape hdim x o ho z j k l hj hk hl hjk hjl

/-- Reflection acts on the actual original doubled label indices. -/
def reflectPair (e : DoubledPair (n + 1) m) : DoubledPair (n + 1) m :=
  ⟨(doubledReflection e.val.1, doubledReflection e.val.2),
    fun h => e.property (doubledReflection_involutive.injective h)⟩

def reflectTriple (q : DoubledTriple (n + 1) m) : DoubledTriple (n + 1) m :=
  ⟨(doubledReflection q.val.1, doubledReflection q.val.2.1, doubledReflection q.val.2.2),
    fun h => q.property.1 (doubledReflection_involutive.injective h),
    fun h => q.property.2 (doubledReflection_involutive.injective h)⟩

theorem pairNode_reflect (e : DoubledPair (n + 1) m) :
    pairNode (tree 0 x) (canonicalLeaf 0 x) (reflectPair e) =
      reflection 0 x (pairNode (tree 0 x) (canonicalLeaf 0 x) e) := by
  change canonicalLeaf 0 x (doubledReflection e.val.1) ⊓ canonicalLeaf 0 x (doubledReflection e.val.2) = _
  rw [← canonicalLeaf_reflect, ← canonicalLeaf_reflect]
  exact ((reflection 0 x).map_inf _ _).symm

theorem pairUnit_reflect (e : DoubledPair (n + 1) m) :
    pairUnit (tree 0 x) (canonicalLeaf 0 x) (PairedForestCoarsePositions.parameters hdim x o z) (reflectPair e) =
      conj (pairUnit (tree 0 x) (canonicalLeaf 0 x) (PairedForestCoarsePositions.parameters hdim x o z) e) := by
  change unitDifference _ _ _ (canonicalLeaf 0 x (doubledReflection e.val.2))
    (canonicalLeaf 0 x (doubledReflection e.val.1)) = _
  rw [← canonicalLeaf_reflect, ← canonicalLeaf_reflect]
  exact ReflectedForestInsertion.unitDifference_reflect (tree 0 x) (reflection 0 x)
    _ (radius_reflect hdim x o z) _ (increment_reflect hdim x o z) _ _

theorem direction_reflect (e : DoubledPair (n + 1) m) :
    direction (tree 0 x) (canonicalLeaf 0 x) (PairedForestCoarsePositions.parameters hdim x o z) (reflectPair e) =
      (direction (tree 0 x) (canonicalLeaf 0 x) (PairedForestCoarsePositions.parameters hdim x o z) e)⁻¹ := by
  unfold direction
  rw [pairUnit_reflect, complexPhase_conj]

theorem ratioValue_reflect (q : DoubledTriple (n + 1) m) :
    ratioValue (tree 0 x) (canonicalLeaf 0 x) (PairedForestCoarsePositions.parameters hdim x o z) (reflectTriple q) =
      ratioValue (tree 0 x) (canonicalLeaf 0 x) (PairedForestCoarsePositions.parameters hdim x o z) q := by
  unfold ratioValue
  change resolvedRatio _ (pairNode _ _ (reflectPair (firstPair q))) (pairNode _ _ (reflectPair (secondPair q)))
    ‖pairUnit _ _ _ (reflectPair (firstPair q))‖ ‖pairUnit _ _ _ (reflectPair (secondPair q))‖ = _
  rw [pairNode_reflect, pairNode_reflect, pairUnit_reflect, pairUnit_reflect,
    Complex.norm_conj, Complex.norm_conj]
  unfold resolvedRatio resolvedDenominator
  rw [← (reflection 0 x).map_inf]
  rw [ReflectedForestInsertion.residualScale_reflect (tree 0 x) (reflection 0 x) _ (radius_reflect hdim x o z),
    ReflectedForestInsertion.residualScale_reflect (tree 0 x) (reflection 0 x) _ (radius_reflect hdim x o z)]

theorem doubledVelocity_reflect (a : DoubledLabel (n + 1) m) :
    (datum hdim x o ho z).toInteriorCollisionData.doubledVelocity (doubledReflection a) =
      conj ((datum hdim x o ho z).toInteriorCollisionData.doubledVelocity a) := by
  rcases a with (j | j) | j <;> simp [InteriorCollisionData.doubledVelocity, doubledReflection]

theorem pairVelocity_reflect (e : DoubledPair (n + 1) m) :
    (datum hdim x o ho z).toInteriorCollisionData.pairVelocity (reflectPair e) =
      conj ((datum hdim x o ho z).toInteriorCollisionData.pairVelocity e) := by
  change (datum hdim x o ho z).toInteriorCollisionData.doubledVelocity (doubledReflection e.val.2) -
    (datum hdim x o ho z).toInteriorCollisionData.doubledVelocity (doubledReflection e.val.1) = _
  rw [doubledVelocity_reflect, doubledVelocity_reflect, ← map_sub]
  rfl

/-- All collapsed doubled directions, including the mirror cluster, agree
with the actual simple datum. -/
theorem direction_internal (e : DoubledPair (n + 1) m) (he : clusterPairCollapses (S x o ho) e) :
    direction (tree 0 x) (canonicalLeaf 0 x) (PairedForestCoarsePositions.parameters hdim x o z) e =
      complexPhase ((datum hdim x o ho z).toInteriorCollisionData.pairVelocity e) := by
  obtain ⟨⟨a, b⟩, hab⟩ := e
  rcases a with (a | a) | a <;> rcases b with (b | b) | b <;>
    simp only [clusterPairCollapses] at he
  · exact direction_upper hdim x o ho z a b he.1 he.2
      (fun h => hab (congrArg (fun j => Sum.inl (Sum.inl j)) h))
  · have hab' : a ≠ b := fun h => hab (congrArg Sum.inr h)
    change direction _ _ _ (reflectPair (upperPair a b hab')) =
      complexPhase ((datum hdim x o ho z).toInteriorCollisionData.pairVelocity (reflectPair (upperPair a b hab')))
    rw [direction_reflect, pairVelocity_reflect, complexPhase_conj,
      direction_upper hdim x o ho z a b he.1 he.2 hab']

/-- All doubly collapsed triples lie in one selected half-plane cluster;
their native ratio is the simple shape-velocity ratio. -/
theorem ratio_internal (q : DoubledTriple (n + 1) m)
    (hq : clusterPairCollapses (S x o ho) (firstPair q) ∧
      clusterPairCollapses (S x o ho) (secondPair q)) :
    ratioValue (tree 0 x) (canonicalLeaf 0 x) (PairedForestCoarsePositions.parameters hdim x o z) q =
      (normalizedNormRatio ((datum hdim x o ho z).toInteriorCollisionData.pairVelocity (firstPair q))
        ((datum hdim x o ho z).toInteriorCollisionData.pairVelocity (secondPair q)) : ℝ) := by
  obtain ⟨⟨a, b, c⟩, hab, hac⟩ := q
  rcases a with (a | a) | a <;> rcases b with (b | b) | b <;> rcases c with (c | c) | c <;>
    simp only [firstPair, secondPair, clusterPairCollapses, false_and, and_false] at hq
  · exact ratio_upper hdim x o ho z a b c hq.1.1 hq.1.2 hq.2.2
      (fun h => hab (congrArg (fun j => Sum.inl (Sum.inl j)) h))
      (fun h => hac (congrArg (fun j => Sum.inl (Sum.inl j)) h))
  · have hab' : a ≠ b := fun h => hab (congrArg Sum.inr h)
    have hac' : a ≠ c := fun h => hac (congrArg Sum.inr h)
    change ratioValue _ _ _ (reflectTriple (upperTriple a b c hab' hac')) =
      (normalizedNormRatio
        ((datum hdim x o ho z).toInteriorCollisionData.pairVelocity (reflectPair (upperPair a b hab')))
        ((datum hdim x o ho z).toInteriorCollisionData.pairVelocity (reflectPair (upperPair a c hac'))) : ℝ)
    rw [ratioValue_reflect, pairVelocity_reflect, pairVelocity_reflect]
    change _ = ‖conj _‖ / (‖conj _‖ + ‖conj _‖)
    simp only [Complex.norm_conj]
    exact ratio_upper hdim x o ho z a b c hq.1.1 hq.1.2 hq.2.2 hab' hac'

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestInternalCoordinates
