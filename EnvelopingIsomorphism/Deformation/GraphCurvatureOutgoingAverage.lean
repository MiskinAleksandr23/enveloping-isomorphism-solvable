import EnvelopingIsomorphism.Deformation.UniformCurvatureOutgoing
import EnvelopingIsomorphism.Deformation.GraphCurvatureCanonicalFibres
import EnvelopingIsomorphism.Deformation.GraphCurvatureLabelCounting
import EnvelopingIsomorphism.Deformation.BinaryOutgoingAverageCovariance

/-! Actual signed outgoing normalization of the main curvature fibres. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.GraphCurvatureOutgoingAverage
open KontsevichGraph.General KontsevichGraph.General.Graph
open UniformBinaryGraphs UniformCurvatureSplits UniformCurvatureTargets
open UniformCurvatureOutgoing GraphCurvatureProfiles BinaryGraphAveraging GraphCoefficientProfiles
open Kontsevich.GeometricWeightOutgoing
open scoped Classical BigOperators
variable {n : ℕ} (i : Fin (n + 1)) (a : Fin 2)

/-- The actual geometric profile of the canonical orientation of one pair. -/
def canonicalProfile : BinaryGraph (n + 2) 3 → ℝ :=
  pushforward (canonicalDataGraph i a) (fun D ↦ canonicalWeight i D.1)

theorem canonicalDataGraph_injective : Function.Injective (canonicalDataGraph i a) := by
  fin_cases a
  · exact forwardDataGraph_injective i 0
  · exact reverseDataGraph_injective i 0

theorem canonicalProfile_split (D : CurvatureSplitData i) :
    canonicalProfile i a (canonicalDataGraph i a D) = canonicalWeight i D.1 := by
  simp only [canonicalProfile, pushforward, (canonicalDataGraph_injective i a).eq_iff]
  simp

theorem canonicalWeight_quotientOutgoing
    (τ : Fin (n + 2) → Equiv.Perm (Fin 2))
    (hτ : τ (vertexSplitChild i a) = Equiv.refl _) (Γ : CurvatureGraph i) :
    canonicalWeight (k := ℝ) i (Γ.permuteOutgoing (quotientOutgoing i a τ)) =
      outgoingSign τ * canonicalWeight i Γ := by
  unfold canonicalWeight
  rw [canonicalEffectiveWeight_permuteOutgoing, quotientOutgoing_sign i a τ hτ]
  simp only [map_mul, algebraMap.coe_prod, outgoingSign]
  rfl

/-- Signed covariance is proved by reindexing the actual quotient/choice
pairs. No covariance of the resulting coefficient table is assumed. -/
theorem canonicalProfile_outgoing
    (τ : Fin (n + 2) → Equiv.Perm (Fin 2))
    (hτ : τ (vertexSplitChild i a) = Equiv.refl _) (H : BinaryGraph (n + 2) 3) :
    canonicalProfile i a (H.permuteOutgoing τ) = outgoingSign τ * canonicalProfile i a H := by
  change (∑ D : CurvatureSplitData i,
    if canonicalDataGraph i a D = H.permuteOutgoing τ then canonicalWeight i D.1 else 0) = _
  rw [← Equiv.sum_comp (outgoingDataEquiv i a τ)]
  unfold canonicalProfile pushforward
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D _
  rw [canonicalDataGraph_outgoing i a τ hτ]
  have hinj : Function.Injective (fun G : BinaryGraph (n + 2) 3 ↦ G.permuteOutgoing τ) :=
    (outgoingGraphEquiv (fun _ ↦ 2) 3 τ).injective
  rw [hinj.eq_iff]
  change (if _ then canonicalWeight (k := ℝ) i (D.1.permuteOutgoing (quotientOutgoing i a τ)) else 0) = _
  rw [canonicalWeight_quotientOutgoing i a τ hτ D.1]
  split_ifs <;> simp

/-- Every contributing template has this literal first-slot internal arrow. -/
theorem canonicalDataGraph_internal (D : CurvatureSplitData i) :
    (canonicalDataGraph i a D).target ⟨vertexSplitChild i a,0⟩ =
      Sum.inl (vertexSplitChild i (receiver a)) := by
  rw [canonicalDataGraph, target_child, canonicalTemplate_sender_zero]
  rfl

theorem canonicalProfile_zero (H : BinaryGraph (n + 2) 3)
    (hH : H.target ⟨vertexSplitChild i a,0⟩ ≠ Sum.inl (vertexSplitChild i (receiver a))) :
    canonicalProfile i a H = 0 := by
  apply Finset.sum_eq_zero
  intro D _
  apply if_neg
  intro he
  exact hH (he ▸ canonicalDataGraph_internal i a D)

/-- If the sender's permutation moves slot zero to slot one, this orientation
has no contributing graph datum. -/
theorem canonicalProfile_sender_swap_zero (D : CurvatureSplitData i)
    (τ : Fin (n + 2) → Equiv.Perm (Fin 2)) (hτ : τ (vertexSplitChild i a) 0 = 1) :
    canonicalProfile i a ((canonicalDataGraph i a D).permuteOutgoing τ) = 0 := by
  apply canonicalProfile_zero
  change (canonicalDataGraph i a D).target ⟨vertexSplitChild i a,τ (vertexSplitChild i a) 0⟩ ≠ _
  rw [hτ, canonicalDataGraph, target_child, canonicalTemplate_sender_one, vertexSplitTemplateVertex_leg]
  exact vertexSplitOldVertex_ne_child i _ (D.1.noLoops i _) _

/-- The reverse orientation cannot appear through an outgoing reordering:
its candidate sender is the original receiver, whose arrows both leave. -/
theorem canonicalProfile_other_zero (D : CurvatureSplitData i)
    (τ : Fin (n + 2) → Equiv.Perm (Fin 2)) :
    canonicalProfile i (receiver a) ((canonicalDataGraph i a D).permuteOutgoing τ) = 0 := by
  apply canonicalProfile_zero
  change (canonicalDataGraph i a D).target
    ⟨vertexSplitChild i (receiver a),τ (vertexSplitChild i (receiver a)) 0⟩ ≠ _
  rw [canonicalDataGraph, target_child, canonicalTemplate_receiver, vertexSplitTemplateVertex_leg]
  exact vertexSplitOldVertex_ne_child i _ (D.1.noLoops i _) _

def pairProfile : BinaryGraph (n + 2) 3 → ℝ := ∑ a : Fin 2, canonicalProfile i a

theorem pairProfile_eq : pairProfile i =
    forwardTemplateProfile i 0 (canonicalWeight (k := ℝ) i) +
      reverseTemplateProfile i 0 (canonicalWeight i) := by
  rw [pairProfile, Fin.sum_univ_two]
  rfl

private theorem permTwo_zero_iff (s : Fin 2) :
    ∀ τ : Equiv.Perm (Fin 2), τ 0 = s ↔ τ = Equiv.swap 0 s := by
  fin_cases s <;> decide

/-- For every outgoing relabelling, the two canonical orientation fibres
reduce to the actual one; the sender-slot condition is the only survivor. -/
theorem weighted_pairProfile_split (D : CurvatureSplitData i)
    (τ : Fin (n + 2) → Equiv.Perm (Fin 2)) :
    outgoingSign τ * pairProfile i ((canonicalDataGraph i a D).permuteOutgoing (fun v ↦ (τ v).symm)) =
      if τ (vertexSplitChild i a) 0 = 0 then canonicalWeight i D.1 else 0 := by
  have hp : pairProfile i ((canonicalDataGraph i a D).permuteOutgoing (fun v ↦ (τ v).symm)) =
      canonicalProfile i a ((canonicalDataGraph i a D).permuteOutgoing (fun v ↦ (τ v).symm)) := by
    rw [pairProfile, Finset.sum_apply]
    apply Finset.sum_eq_single a
    · intro b _ hba
      have hb : b = receiver a := by fin_cases a <;> fin_cases b <;> simp_all [receiver]
      rw [hb]
      exact canonicalProfile_other_zero i a D _
    · intro h
      exact (h (Finset.mem_univ a)).elim
  rw [hp]
  by_cases hτ : τ (vertexSplitChild i a) 0 = 0
  · rw [if_pos hτ]
    have hf : τ (vertexSplitChild i a) = Equiv.refl _ := by
      simpa using (permTwo_zero_iff 0 _).mp hτ
    have hfi : (fun v ↦ (τ v).symm) (vertexSplitChild i a) = Equiv.refl _ := by simp [hf]
    rw [canonicalProfile_outgoing i a _ hfi, canonicalProfile_split]
    have hs : outgoingSign (k := ℝ) (fun v ↦ (τ v).symm) = outgoingSign τ := by
      simp [outgoingSign, permutationSign]
    rw [hs, ← mul_assoc, outgoingSign_sq, one_mul]
  · rw [if_neg hτ]
    have h1 : τ (vertexSplitChild i a) 0 = 1 := by omega
    have hf := (permTwo_zero_iff 1 _).mp h1
    have hfi : (τ (vertexSplitChild i a)).symm 0 = 1 := by rw [hf]; decide
    rw [canonicalProfile_sender_swap_zero i a D _ hfi, mul_zero]

/-- The full signed outgoing average has exactly one-half of the literal
quotient weight. Both zero fibres and the normalizer multiplicity are proved. -/
theorem outgoingAverage_pairProfile_split (D : CurvatureSplitData i) :
    outgoingAverage (pairProfile i) (canonicalDataGraph i a D) = (1 / 2 : ℝ) * canonicalWeight i D.1 := by
  rw [outgoingAverage_apply]
  simp only [weighted_pairProfile_split i a D]
  have hsum : (∑ τ : Fin (n + 2) → Equiv.Perm (Fin 2),
      if τ (vertexSplitChild i a) 0 = 0 then canonicalWeight (k := ℝ) i D.1 else 0) =
      Fintype.card {τ : Fin (n + 2) → Equiv.Perm (Fin 2) // τ (vertexSplitChild i a) 0 = 0} *
        canonicalWeight i D.1 := by
    simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 1
    congr 1
    exact (Fintype.card_subtype _).symm
  rw [hsum, ← mul_assoc, GraphCurvatureLabelCounting.outgoingNormalizer_ratio]

/-- The original arbitrary-slot graph has exactly the signed one-half
quotient weight. The quotient and incoming data are extracted from that graph. -/
theorem outgoingAverage_pairProfile_original (H : BinaryGraph (n + 2) 3) (s : Fin 2)
    (hi : UniformBinaryContraction.UniqueInternalAt i H a s)
    (hd : UniformBinaryContraction.CoarseDistinct i H)
    (hx : UniformBinaryContraction.ExitsDistinctAt i H a s) :
    outgoingAverage (pairProfile i) H = ((-1 : ℝ) ^ s.val / 2) *
      canonicalWeight i (UniformBinaryContraction.curvatureGraph i H a s hi hd hx) := by
  let D : CurvatureSplitData i :=
    ⟨UniformBinaryContraction.curvatureGraph i H a s hi hd hx,
      UniformBinaryContraction.incomingChoices i H a s hi hd hx⟩
  have hr : (canonicalDataGraph i a D).permuteOutgoing (UniformBinaryContraction.slotPermutation i a s) = H := by
    have h := UniformBinaryContraction.reconstruct_original i H a s hi hd hx
    by_cases ha : a = 0 <;>
      simpa only [canonicalDataGraph, uniformSplit, BinaryVertexContraction.canonicalTemplate,
        uniformCurvatureForward, uniformCurvatureReverse, ha, if_true, if_false, D] using h
  conv_lhs => rw [← hr]
  rw [outgoingAverage_permuteOutgoing, outgoingAverage_pairProfile_split]
  have hs : outgoingSign (k := ℝ) (UniformBinaryContraction.slotPermutation i a s) = (-1 : ℝ) ^ s.val :=
    UniformBinaryContraction.slotPermutation_sign i a s
  rw [hs]
  change (-1 : ℝ) ^ s.val * ((1 / 2 : ℝ) * canonicalWeight i D.1) = _
  ring

end EnvelopingIsomorphism.Deformation.GraphCurvatureOutgoingAverage
