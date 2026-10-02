import EnvelopingIsomorphism.Deformation.MixedGraphPhysicalPairFibres
import EnvelopingIsomorphism.Deformation.MixedGraphFullOutgoing
import EnvelopingIsomorphism.Deformation.MixedGraphClusterSums

/-! Genuine source and correction sums over physical pairs. The vector marker,
all outgoing signs, and the two-odd placement signs are retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
namespace EnvelopingIsomorphism.Deformation.MixedGraphPhysicalPairSums
open scoped BigOperators Classical
open KontsevichGraph.General GraphCurvatureLabelCounting
open MixedGraphProfileCarrier MixedGraphAveraging MixedGraphBlockRelabelling
open MixedGraphPairLabelCounting MixedGraphPhysicalPairFibres
open MixedGraphInternalPairRelabelling MixedGraphCorrectionProfiles
open MixedGraphClusterSums GraphCanonicalBinaryWeights
variable {n : ℕ}

private def sourceRepresentative (T : PhysicalPair n) (v : Fin (n + 2)) (hv : v ∈ T.val) :
    SourcePairLabels T v :=
  Classical.choice (Fintype.card_pos_iff.mp (by rw [card_sourcePairLabels T v hv]; exact Nat.factorial_pos _))

private def correctionRepresentative (T : PhysicalPair (n + 1)) (v : Fin (n + 3))
    (hv : v ∉ T.val) : CorrectionPairLabels T v :=
  Classical.choice (Fintype.card_pos_iff.mp (by
    rw [card_correctionPairLabels T v hv]; exact Nat.mul_pos (by decide) (Nat.factorial_pos _)))

/-- A source pair contains the vector. Its raw quotient coefficient keeps
forward minus twice backward, and is zero for every other physical pair. -/
def rawSourcePairCoefficient (H : VectorGraph (n + 1) 2) (T : PhysicalPair n) : ℝ :=
  if hv : H.vertex ∈ T.val then
    let D := sourceRepresentative T H.vertex hv
    ((n + 1).factorial : ℝ) * Source.pairProfile
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) (n + 1)) D.1
      ((internalGraphEquiv D.2.val.val 2).symm H)
  else 0

/-- A correction pair excludes the retained vector. Removing precisely the
quotient factorial leaves its genuine two-odd signed raw weight. -/
def rawCorrectionPairCoefficient (H : VectorGraph (n + 2) 2) (T : PhysicalPair (n + 1)) : ℝ :=
  if hv : H.vertex ∉ T.val then
    let D := correctionRepresentative T H.vertex hv
    ((n + 2).factorial : ℝ) * Correction.pairProfile D.1
      ((internalGraphEquiv D.2.val.val 2).symm H)
  else 0

theorem sum_source_pair_fiber (H : VectorGraph (n + 1) 2) (T : PhysicalPair n) :
    (∑ D : SourcePairLabels T H.vertex, Source.pairProfile
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) (n + 1)) D.1
        ((internalGraphEquiv D.2.val.val 2).symm H)) = rawSourcePairCoefficient H T := by
  by_cases hv : H.vertex ∈ T.val
  · rw [rawSourcePairCoefficient, dif_pos hv]
    have he (D : SourcePairLabels T H.vertex) := sourcePairProfile_same_fiber
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) (n + 1))
      (fun Γ σ => by rw [canonicalBinaryWeight_eq_factorial, canonicalBinaryWeight_eq_factorial,
        rawBinaryWeight_permuteInternal]) T H.vertex D (sourceRepresentative T H.vertex hv) H
    simp only [he, Finset.sum_const, Finset.card_univ, card_sourcePairLabels T H.vertex hv,
      nsmul_eq_mul]
  · haveI : IsEmpty (SourcePairLabels T H.vertex) := ⟨fun D =>
      (sourcePairFiber_isEmpty D.1 T H.vertex hv).false D.2⟩
    simp [rawSourcePairCoefficient, hv]

theorem sum_correction_pair_fiber (H : VectorGraph (n + 2) 2) (T : PhysicalPair (n + 1)) :
    (∑ D : CorrectionPairLabels T H.vertex,
      Correction.pairProfile D.1 ((internalGraphEquiv D.2.val.val 2).symm H)) =
      2 * rawCorrectionPairCoefficient H T := by
  by_cases hv : H.vertex ∉ T.val
  · rw [rawCorrectionPairCoefficient, dif_pos hv]
    have he (D : CorrectionPairLabels T H.vertex) := correctionPairProfile_same_fiber
      T H.vertex D (correctionRepresentative T H.vertex hv) H
    simp only [he, Finset.sum_const, Finset.card_univ, card_correctionPairLabels T H.vertex hv,
      nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    ring
  · haveI : IsEmpty (CorrectionPairLabels T H.vertex) := ⟨fun D =>
      (correctionPairFiber_isEmpty D.1 T H.vertex (not_not.mp hv)).false D.2⟩
    simp [rawCorrectionPairCoefficient, hv]

/-- Any exterior-marked pair labelling represents the same normalized
correction coefficient before outgoing averaging. -/
theorem rawCorrectionPairCoefficient_eq_scaled (H : VectorGraph (n + 2) 2)
    (T : PhysicalPair (n + 1)) (D : CorrectionPairLabels T H.vertex) :
    rawCorrectionPairCoefficient H T = ((n + 2).factorial : ℝ) *
      Correction.pairProfile D.1 ((internalGraphEquiv D.2.val.val 2).symm H) := by
  have hv : H.vertex ∉ T.val := by
    intro hv
    exact (correctionPairFiber_isEmpty D.1 T H.vertex hv).false D.2
  rw [rawCorrectionPairCoefficient, dif_pos hv]
  dsimp only
  rw [correctionPairProfile_same_fiber T H.vertex (correctionRepresentative T H.vertex hv) D H]

private theorem mul_pushforward {I A : Type*} [Fintype I] (f : I → A)
    (w : I → ℝ) (s : ℝ) (H : A) :
    s * GraphCoefficientProfiles.pushforward f w H =
      GraphCoefficientProfiles.pushforward f (fun i => s * w i) H := by
  simp only [GraphCoefficientProfiles.pushforward, Finset.mul_sum, mul_ite, mul_zero]

private theorem source_pairProfile_raw (i : Fin (n + 1)) (H : VectorGraph (n + 1) 2) :
    ((n + 1).factorial : ℝ) * Source.pairProfile
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) (n + 1)) i H =
      Source.pairProfile (rawBinaryWeight (n + 1)) i H := by
  have hw (Γ : UniformBinaryGraphs.BinaryGraph (n + 1) 2) :
      ((n + 1).factorial : ℝ) * GraphBoundaryProfiles.canonicalBinaryWeight (n + 1) Γ =
        rawBinaryWeight (n + 1) Γ := by
    rw [canonicalBinaryWeight_eq_factorial, ← mul_assoc, mul_inv_cancel₀, one_mul]
    exact_mod_cast Nat.factorial_ne_zero (n + 1)
  simp only [Source.pairProfile, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    MixedGraphActionSplits.forwardTemplateProfile, MixedGraphActionSplits.backwardTemplateProfile,
    mul_sub, mul_left_comm ((n + 1).factorial : ℝ) 2, mul_pushforward, hw]

/-- Every marked representative gives this same literal raw source fibre. -/
theorem rawSourcePairCoefficient_eq (H : VectorGraph (n + 1) 2) (T : PhysicalPair n)
    (D : SourcePairLabels T H.vertex) :
    rawSourcePairCoefficient H T = Source.pairProfile (rawBinaryWeight (n + 1)) D.1
      ((internalGraphEquiv D.2.val.val 2).symm H) := by
  have hv : H.vertex ∈ T.val := by
    rw [← D.2.property]
    exact (D.2.val.property _).mpr (by simp [childPair])
  rw [rawSourcePairCoefficient, dif_pos hv]
  dsimp only
  rw [sourcePairProfile_same_fiber _ (canonicalBinaryWeight_permuteInternal (n + 1))
    T H.vertex (sourceRepresentative T H.vertex hv) D H]
  exact source_pairProfile_raw D.1 _

/-- The correction quotient's actual integral, with only its MC factorial removed. -/
def rawCorrectionQuotientWeight (Γ : CorrectionGraph n) : ℝ :=
  Kontsevich.GeometricWeights.canonicalWeight Γ.2 (edgeCount Γ.1)

private theorem correction_weight_raw (Γ : CorrectionGraph n) :
    ((n + 2).factorial : ℝ) * canonicalQuotientWeight (k := ℝ) Γ =
      rawCorrectionQuotientWeight Γ := by
  have hw : canonicalQuotientWeight (k := ℝ) Γ = ((n + 2).factorial : ℝ)⁻¹ *
      rawCorrectionQuotientWeight Γ := by
    simp only [canonicalQuotientWeight, rawCorrectionQuotientWeight,
      Kontsevich.GeometricWeights.canonicalEffectiveWeight]
    simp [Kontsevich.effectiveMCWeight, Rat.smul_def]
  rw [hw, ← mul_assoc, mul_inv_cancel₀, one_mul]
  exact_mod_cast Nat.factorial_ne_zero (n + 2)

/-- Every exterior-marked representative gives the same raw correction fibre,
including its vector/trivector placement sign in each actual quotient datum. -/
theorem rawCorrectionPairCoefficient_eq (H : VectorGraph (n + 2) 2) (T : PhysicalPair (n + 1))
    (D : CorrectionPairLabels T H.vertex) :
    rawCorrectionPairCoefficient H T = ∑ a : Fin 2,
      GraphCoefficientProfiles.pushforward (Correction.canonicalDataGraph D.1 a)
        (fun E => placementSign D.1 * rawCorrectionQuotientWeight ⟨D.1,E.1⟩)
        ((internalGraphEquiv D.2.val.val 2).symm H) := by
  have hv : H.vertex ∉ T.val := by
    intro hv
    exact (correctionPairFiber_isEmpty D.1 T H.vertex hv).false D.2
  rw [rawCorrectionPairCoefficient, dif_pos hv]
  dsimp only
  rw [correctionPairProfile_same_fiber T H.vertex (correctionRepresentative T H.vertex hv) D H]
  simp only [Correction.pairProfile, Finset.sum_apply, Finset.mul_sum, Correction.canonicalProfile,
    mul_pushforward, mul_left_comm ((n + 2).factorial : ℝ) (placementSign D.1), correction_weight_raw]

/-- The source quotient factorial cancels its actual marked label fibre. -/
theorem internalAverage_canonical_source_eq_pairs (H : VectorGraph (n + 1) 2) :
    internalAverage (MixedGraphActionSplits.sourceActionProfile
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) (n + 1))) H =
      ((n + 2).factorial : ℝ)⁻¹ * ∑ T : PhysicalPair n, rawSourcePairCoefficient H T := by
  rw [MixedGraphCanonicalSplitFibres.Source.canonical_sourceActionProfile_two_templates,
    internalAverage_apply]
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  change _ * (∑ i, ∑ σ, Source.pairProfile _ i ((internalGraphEquiv σ 2).symm H)) = _
  rw [sum_source_labels H.vertex _ (fun i σ h => sourcePairProfile_zero_of_vertex _ i _
    (inverse_vertex_ne_of_not_marked σ _ H h))]
  simp only [sum_source_pair_fiber]

private theorem correction_pairProfile_eq (p : Placement n) :
    Correction.pairProfile p = signedForwardTemplateProfile p 0 canonicalQuotientWeight +
      signedReverseTemplateProfile p 0 canonicalQuotientWeight := by
  rw [Correction.pairProfile, Fin.sum_univ_two]
  rfl

/-- The exchanged-child multiplicity is two. Together with the three-halves
cyclic coefficient it leaves three before the outgoing sum is performed. -/
theorem internalAverage_canonical_correction_eq_pairs (H : VectorGraph (n + 2) 2) :
    internalAverage (correctionProfile (canonicalQuotientWeight (k := ℝ))) H =
      3 * ((n + 3).factorial : ℝ)⁻¹ *
        ∑ T : PhysicalPair (n + 1), rawCorrectionPairCoefficient H T := by
  rw [MixedGraphCanonicalSplitFibres.Correction.canonical_correctionProfile_three_halves]
  simp only [← correction_pairProfile_eq]
  rw [internalAverage_smul, Pi.smul_apply, smul_eq_mul, internalAverage_apply]
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  rw [sum_correction_labels H.vertex _ (fun p σ h => correctionPairProfile_zero_of_vertex p _
    (inverse_vertex_ne_of_not_marked σ _ H h))]
  simp only [sum_correction_pair_fiber, ← Finset.mul_sum]
  ring

/-- Full outgoing-signed source sum, with no remaining local label factorial. -/
theorem boundaryAverage_canonical_source_eq_pairs (H : VectorGraph (n + 1) 2) :
    boundaryAverage (MixedGraphActionSplits.sourceActionProfile
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) (n + 1))) H =
      ((2 : ℝ)^(n + 1))⁻¹ * ((n + 2).factorial : ℝ)⁻¹ *
        ∑ τ : OutgoingGroup (n + 1), outgoingSign (k := ℝ) τ *
          ∑ T : PhysicalPair n, rawSourcePairCoefficient ((outgoingGraphEquiv τ 2).symm H) T := by
  rw [boundaryAverage, outgoingAverage_apply]
  simp only [internalAverage_canonical_source_eq_pairs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  apply Finset.sum_congr rfl
  intro T _
  ring

/-- Literal full outgoing correction sum. Its three records both the 3/2
cyclic factor and the two exchanged-child labels; every outgoing sign remains. -/
theorem boundaryAverage_canonical_correction_eq_pairs (H : VectorGraph (n + 2) 2) :
    boundaryAverage (correctionProfile (canonicalQuotientWeight (k := ℝ))) H =
      3 * ((2 : ℝ)^(n + 2))⁻¹ * ((n + 3).factorial : ℝ)⁻¹ *
        ∑ τ : OutgoingGroup (n + 2), outgoingSign (k := ℝ) τ *
          ∑ T : PhysicalPair (n + 1), rawCorrectionPairCoefficient ((outgoingGraphEquiv τ 2).symm H) T := by
  rw [boundaryAverage, outgoingAverage_apply]
  simp only [internalAverage_canonical_correction_eq_pairs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  apply Finset.sum_congr rfl
  intro T _
  ring

/-- The source endpoint is empty in degree zero. -/
def sourcePhysicalSum : (N : ℕ) → VectorGraph N 2 → ℝ
  | 0, _ => 0
  | n + 1, H => ∑ τ : OutgoingGroup (n + 1), outgoingSign (k := ℝ) τ *
      ∑ T : PhysicalPair n, rawSourcePairCoefficient ((outgoingGraphEquiv τ 2).symm H) T

/-- The correction endpoint is empty in degrees zero and one. Its three is
exactly the product of the cyclic 3/2 and the exchanged-child multiplicity. -/
def correctionPhysicalSum : (N : ℕ) → VectorGraph N 2 → ℝ
  | 0, _ => 0
  | 1, _ => 0
  | n + 2, H => 3 * ∑ τ : OutgoingGroup (n + 2), outgoingSign (k := ℝ) τ *
      ∑ T : PhysicalPair (n + 1), rawCorrectionPairCoefficient ((outgoingGraphEquiv τ 2).symm H) T

/-- Actual target endpoint, with all mixed binary clusters and both nullary
factor endpoints present. -/
def targetPhysicalSum (N : ℕ) (H : VectorGraph N 2) : ℝ :=
  ∑ τ : OutgoingGroup N, outgoingSign (k := ℝ) τ *
    ∑ a : Fin (N + 1), ∑ T : GraphLabelledClusterCounting.Clusters
      (MixedGraphLabelledClusterCounting.binaryBlock a (N - a)),
      rawActionClusterCoefficient
        (castVertices (MixedGraphTargetProfiles.splitDegree N a).symm
          ((outgoingGraphEquiv τ 2).symm H)) T

private theorem boundaryAverage_add (c d : VectorGraph n 2 → ℝ) :
    boundaryAverage (c + d) = boundaryAverage c + boundaryAverage d := by
  funext H
  simp [boundaryAverage, outgoingAverage_apply, internalAverage_apply,
    Finset.sum_add_distrib, mul_add]

private theorem boundaryAverage_zero : boundaryAverage (0 : VectorGraph n 2 → ℝ) = 0 := by
  funext H
  simp [boundaryAverage, outgoingAverage_apply, internalAverage_apply]

theorem boundaryAverage_full_source_eq_pairs (N : ℕ) (H : VectorGraph N 2) :
    boundaryAverage (MixedGraphSourceProfiles.fullSourceActionProfile
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ)) N) H =
      ((2 : ℝ)^N)⁻¹ * ((N + 1).factorial : ℝ)⁻¹ * sourcePhysicalSum N H := by
  cases N with
  | zero => simp [MixedGraphSourceProfiles.fullSourceActionProfile, sourcePhysicalSum, boundaryAverage_zero]
  | succ n => exact boundaryAverage_canonical_source_eq_pairs H

theorem boundaryAverage_full_correction_eq_pairs (N : ℕ) (H : VectorGraph N 2) :
    boundaryAverage (MixedGraphBoundaryProfiles.fullCorrectionProfile
      (fun _ => canonicalQuotientWeight (k := ℝ)) N) H =
      ((2 : ℝ)^N)⁻¹ * ((N + 1).factorial : ℝ)⁻¹ * correctionPhysicalSum N H := by
  cases N with
  | zero => simp [MixedGraphBoundaryProfiles.fullCorrectionProfile, correctionPhysicalSum, boundaryAverage_zero]
  | succ n =>
    cases n with
    | zero => simp [MixedGraphBoundaryProfiles.fullCorrectionProfile, correctionPhysicalSum, boundaryAverage_zero]
    | succ n =>
      rw [MixedGraphBoundaryProfiles.fullCorrectionProfile, boundaryAverage_canonical_correction_eq_pairs]
      unfold correctionPhysicalSum
      ring

/-- Fully assembled mixed left endpoint with its common global factor. -/
theorem boundaryAverage_source_add_correction_eq_pairs (N : ℕ) (H : VectorGraph N 2) :
    boundaryAverage (MixedGraphSourceProfiles.fullSourceActionProfile
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ)) N +
      MixedGraphBoundaryProfiles.fullCorrectionProfile
        (fun _ => canonicalQuotientWeight (k := ℝ)) N) H =
      ((2 : ℝ)^N)⁻¹ * ((N + 1).factorial : ℝ)⁻¹ *
        (sourcePhysicalSum N H + correctionPhysicalSum N H) := by
  rw [boundaryAverage_add, Pi.add_apply, boundaryAverage_full_source_eq_pairs,
    boundaryAverage_full_correction_eq_pairs, mul_add]

/-- Geometry has precisely this remaining scalar endpoint obligation. It is
an explicit equality of actual pair and cluster sums, with all signs retained. -/
def PhysicalMixedBoundaryEndpoints : Prop :=
  ∀ N (H : VectorGraph N 2), sourcePhysicalSum N H + correctionPhysicalSum N H = targetPhysicalSum N H

/-- The physical endpoint equation and the canonical scalar boundary relation
are equivalent; no operator or tangent equation is assumed in this bridge. -/
theorem canonicalScalarMixedBoundaryRelation_iff_physical_endpoints :
    MixedGraphBoundaryProfiles.CanonicalScalarMixedBoundaryRelation (k := ℝ) ↔
      PhysicalMixedBoundaryEndpoints := by
  unfold MixedGraphBoundaryProfiles.CanonicalScalarMixedBoundaryRelation
    MixedGraphBoundaryProfiles.ScalarMixedBoundaryRelation PhysicalMixedBoundaryEndpoints
  constructor
  · intro h N H
    have he := congrFun (h N) H
    rw [boundaryAverage_source_add_correction_eq_pairs,
      boundaryAverage_canonical_targetAction_eq_clusters] at he
    have hf : ((2 : ℝ)^N)⁻¹ * ((N + 1).factorial : ℝ)⁻¹ ≠ 0 := by
      apply mul_ne_zero (inv_ne_zero (pow_ne_zero _ (by norm_num)))
      exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (N + 1))
    exact (mul_left_cancel₀ hf he)
  · intro h N
    funext H
    rw [boundaryAverage_source_add_correction_eq_pairs,
      boundaryAverage_canonical_targetAction_eq_clusters]
    exact congrArg (fun x : ℝ => ((2 : ℝ)^N)⁻¹ * ((N + 1).factorial : ℝ)⁻¹ * x) (h N H)

/-- Supply the geometric physical endpoints to obtain the actual canonical
mixed boundary relation, including its nullary and unary equations. -/
theorem canonicalScalarMixedBoundaryRelation_of_physical_endpoints
    (h : PhysicalMixedBoundaryEndpoints) :
    MixedGraphBoundaryProfiles.CanonicalScalarMixedBoundaryRelation (k := ℝ) :=
  canonicalScalarMixedBoundaryRelation_iff_physical_endpoints.mpr h

end EnvelopingIsomorphism.Deformation.MixedGraphPhysicalPairSums
