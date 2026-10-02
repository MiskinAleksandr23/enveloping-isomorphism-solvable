import EnvelopingIsomorphism.Deformation.MixedGraphGraftOutgoing
import EnvelopingIsomorphism.Deformation.GraphBinaryOutgoingClusterSums

/-! Outgoing covariance of actual mixed scalar graft coefficients. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace EnvelopingIsomorphism.Deformation.MixedGraphOutgoingClusterSums
open scoped Classical BigOperators
open KontsevichGraph.General MixedGraphProfileCarrier MixedGraphTargetProfiles
open MixedGraphGraftOutgoing MixedGraphClusterSums MixedGraphBlockRelabelling
open MixedGraphLabelledClusterCounting
open UniformBinaryGraphs GraphCanonicalBinaryWeights
variable {a b n m : ℕ}

def familySign (τ : OutgoingFamily n) (i : Fin (n+1)) : ℝ :=
  ∏ v, permutationSign (R := ℝ) (τ i v)

theorem rawVelocityWeight_permuteOutgoing (Γ : VectorGraph n 1)
    (τ : (v : Fin (n+1)) → Equiv.Perm (Fin (vectorArity Γ.vertex v))) :
    rawVelocityWeight n ⟨Γ.vertex, Γ.graph.permuteOutgoing τ⟩ =
      (∏ v, permutationSign (R := ℝ) (τ v)) * rawVelocityWeight n Γ :=
  Kontsevich.GeometricWeightOutgoing.canonicalWeight_permuteOutgoing Γ.graph
    (Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 1 Γ.vertex) τ

theorem outputOutgoing_sign (τ : OutgoingFamily (a+b)) (i : Fin (a+1)) :
    (∏ v, permutationSign (R := ℝ) (outputOutgoing i τ v)) =
      familySign τ (vectorEmbedding a b i) := by
  simp only [outputOutgoing, permutationSign, Equiv.Perm.sign_permCongr]
  exact (outputVertexEquiv a b).prod_comp (fun v ↦ permutationSign (R := ℝ) (τ _ v))

theorem inputOutgoing_sign (τ : OutgoingFamily (a+b)) (i : Fin (a+1)) :
    (∏ v, permutationSign (R := ℝ) (inputOutgoing i τ v)) =
      familySign τ (vectorEmbedding a b i) := by
  simp only [inputOutgoing, permutationSign, Equiv.Perm.sign_permCongr]
  exact (inputVertexEquiv a b).prod_comp (fun v ↦ permutationSign (R := ℝ) (τ _ v))

theorem restrict_sign {c d : ℕ} {q : Fin c → ℕ} {p : Fin d → ℕ}
    (τ : (v : Fin (c+d)) → Equiv.Perm (Fin (graftArity q p v))) :
    (∏ v, permutationSign (R := ℝ) (outerOutgoing τ v)) *
      (∏ v, permutationSign (R := ℝ) (innerOutgoing τ v)) =
        ∏ v, permutationSign (R := ℝ) (τ v) := by
  rw [← graftOutgoing_sign, graftOutgoing_restrict]

theorem outputData_weight (τ : OutgoingFamily (a+b)) (D : OutputIndex a b) :
    rawVelocityWeight a (outputData τ D).1 * rawBinaryWeight b (outputData τ D).2.1 =
      familySign τ (vectorEmbedding a b D.1.vertex) *
        (rawVelocityWeight a D.1 * rawBinaryWeight b D.2.1) := by
  change rawVelocityWeight a ⟨D.1.vertex, D.1.graph.permuteOutgoing _⟩ *
    rawBinaryWeight b (D.2.1.permuteOutgoing _) = _
  rw [rawVelocityWeight_permuteOutgoing,
    GraphBinaryOutgoingClusterSums.rawBinaryWeight_permuteOutgoing]
  change ((_ : ℝ) * _) * ((∏ v, permutationSign (R := ℝ)
    (innerOutgoing (outputOutgoing D.1.vertex τ) v)) * _) = _
  rw [show ((∏ v, permutationSign (R := ℝ) (outerOutgoing (outputOutgoing D.1.vertex τ) v)) *
      rawVelocityWeight a D.1) *
      ((∏ v, permutationSign (R := ℝ) (innerOutgoing (outputOutgoing D.1.vertex τ) v)) *
      rawBinaryWeight b D.2.1) =
      ((∏ v, permutationSign (R := ℝ) (outerOutgoing (outputOutgoing D.1.vertex τ) v)) *
      (∏ v, permutationSign (R := ℝ) (innerOutgoing (outputOutgoing D.1.vertex τ) v))) *
      (rawVelocityWeight a D.1 * rawBinaryWeight b D.2.1) by ring,
    restrict_sign, outputOutgoing_sign]

theorem inputData_weight (r : Fin 2) (τ : OutgoingFamily (a+b)) (D : InputIndex a b r) :
    rawVelocityWeight a (inputData r τ D).1 * rawBinaryWeight b (inputData r τ D).2.1 =
      familySign τ (vectorEmbedding a b D.1.vertex) *
        (rawVelocityWeight a D.1 * rawBinaryWeight b D.2.1) := by
  change rawVelocityWeight a ⟨D.1.vertex, D.1.graph.permuteOutgoing _⟩ *
    rawBinaryWeight b (D.2.1.permuteOutgoing _) = _
  rw [rawVelocityWeight_permuteOutgoing,
    GraphBinaryOutgoingClusterSums.rawBinaryWeight_permuteOutgoing]
  change ((_ : ℝ) * _) * ((∏ v, permutationSign (R := ℝ)
    (outerOutgoing (inputOutgoing D.1.vertex τ) v)) * _) = _
  rw [show ((∏ v, permutationSign (R := ℝ) (innerOutgoing (inputOutgoing D.1.vertex τ) v)) *
      rawVelocityWeight a D.1) *
      ((∏ v, permutationSign (R := ℝ) (outerOutgoing (inputOutgoing D.1.vertex τ) v)) *
      rawBinaryWeight b D.2.1) =
      ((∏ v, permutationSign (R := ℝ) (outerOutgoing (inputOutgoing D.1.vertex τ) v)) *
      (∏ v, permutationSign (R := ℝ) (innerOutgoing (inputOutgoing D.1.vertex τ) v))) *
      (rawVelocityWeight a D.1 * rawBinaryWeight b D.2.1) by ring,
    restrict_sign, inputOutgoing_sign]

theorem raw_outputProfile_outgoing (τ : OutgoingFamily (a+b)) (H : VectorGraph (a+b) 2) :
    outputProfile (rawVelocityWeight a) (rawBinaryWeight b) (outgoingEquiv τ 2 H) =
      familySign τ H.vertex * outputProfile (rawVelocityWeight a) (rawBinaryWeight b) H := by
  classical
  unfold outputProfile GraphCoefficientProfiles.pushforward
  rw [← Equiv.sum_comp (outputDataEquiv τ), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D _
  have hf : outputGraft ((MixedGraphGraftOutgoing.outputDataEquiv τ) D).1
      ((MixedGraphGraftOutgoing.outputDataEquiv τ) D).2.1
      ((MixedGraphGraftOutgoing.outputDataEquiv τ) D).2.2 =
      outgoingEquiv τ 2 (outputGraft D.1 D.2.1 D.2.2) := outputGraft_outgoing τ D
  have hw : rawVelocityWeight a ((MixedGraphGraftOutgoing.outputDataEquiv τ) D).1 *
      rawBinaryWeight b ((MixedGraphGraftOutgoing.outputDataEquiv τ) D).2.1 =
      familySign τ (vectorEmbedding a b D.1.vertex) *
        (rawVelocityWeight a D.1 * rawBinaryWeight b D.2.1) := outputData_weight τ D
  simp only [hf, hw, (outgoingEquiv τ 2).injective.eq_iff]
  split_ifs with h
  · rw [show vectorEmbedding a b D.1.vertex = H.vertex from congrArg VectorGraph.vertex h]
  · simp

theorem raw_inputProfile_outgoing (r : Fin 2) (τ : OutgoingFamily (a+b)) (H : VectorGraph (a+b) 2) :
    inputProfile r (rawVelocityWeight a) (rawBinaryWeight b) (outgoingEquiv τ 2 H) =
      familySign τ H.vertex * inputProfile r (rawVelocityWeight a) (rawBinaryWeight b) H := by
  classical
  unfold inputProfile GraphCoefficientProfiles.pushforward
  rw [← Equiv.sum_comp (inputDataEquiv r τ), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D _
  have hf : inputGraft ((MixedGraphGraftOutgoing.inputDataEquiv r τ) D).1
      ((MixedGraphGraftOutgoing.inputDataEquiv r τ) D).2.1 r
      ((MixedGraphGraftOutgoing.inputDataEquiv r τ) D).2.2 =
      outgoingEquiv τ 2 (inputGraft D.1 D.2.1 r D.2.2) := inputGraft_outgoing r τ D
  have hw : rawVelocityWeight a ((MixedGraphGraftOutgoing.inputDataEquiv r τ) D).1 *
      rawBinaryWeight b ((MixedGraphGraftOutgoing.inputDataEquiv r τ) D).2.1 =
      familySign τ (vectorEmbedding a b D.1.vertex) *
        (rawVelocityWeight a D.1 * rawBinaryWeight b D.2.1) := inputData_weight r τ D
  simp only [hf, hw, (outgoingEquiv τ 2).injective.eq_iff]
  split_ifs with h
  · rw [show vectorEmbedding a b D.1.vertex = H.vertex from congrArg VectorGraph.vertex h]
  · simp

theorem raw_actionProfile_outgoing (τ : OutgoingFamily (a+b)) (H : VectorGraph (a+b) 2) :
    actionProfile (rawVelocityWeight a) (rawBinaryWeight b) (outgoingEquiv τ 2 H) =
      familySign τ H.vertex * actionProfile (rawVelocityWeight a) (rawBinaryWeight b) H := by
  simp only [actionProfile, Pi.sub_apply, raw_outputProfile_outgoing, raw_inputProfile_outgoing,
    mul_sub]

/-- A single carrier placement accepts an arbitrary genuine dependent family. -/
theorem raw_actionProfile_permuteOutgoing (H : VectorGraph (a+b) 2)
    (τ : (v : Fin (a+b+1)) → Equiv.Perm (Fin (vectorArity H.vertex v))) :
    actionProfile (rawVelocityWeight a) (rawBinaryWeight b) ⟨H.vertex, H.graph.permuteOutgoing τ⟩ =
      (∏ v, permutationSign (R := ℝ) (τ v)) *
        actionProfile (rawVelocityWeight a) (rawBinaryWeight b) H := by
  classical
  let α : OutgoingFamily (a+b) := fun i ↦
    if h : i = H.vertex then h.symm ▸ τ else fun _ ↦ Equiv.refl _
  have hα : α H.vertex = τ := by simp [α]
  have he : outgoingEquiv α 2 H = ⟨H.vertex, H.graph.permuteOutgoing τ⟩ := by
    change (⟨H.vertex, H.graph.permuteOutgoing (α H.vertex)⟩ : VectorGraph (a+b) 2) = _
    rw [hα]
  simpa only [he, familySign, hα] using raw_actionProfile_outgoing α H

open GraphLabelledClusterCounting

/-- The actual physical subset coefficient has the full outgoing sign even
after its distinguished vertex and incoming choices are internally relabelled. -/
theorem rawActionClusterCoefficient_permuteOutgoing (H : VectorGraph (a+b) 2)
    (T : Clusters (binaryBlock a b))
    (τ : (v : Fin (a+b+1)) → Equiv.Perm (Fin (vectorArity H.vertex v))) :
    rawActionClusterCoefficient ⟨H.vertex, H.graph.permuteOutgoing τ⟩ T =
      (∏ v, permutationSign (R := ℝ) (τ v)) * rawActionClusterCoefficient H T := by
  let σ := (clusterRepresentative (binaryBlock a b) T).val.symm
  obtain ⟨β, he, hs⟩ := exists_internal_outgoing σ H τ
  unfold rawActionClusterCoefficient
  simp only [internalGraphEquiv_symm_apply]
  change actionProfile _ _ (MixedGraphAveraging.internalGraphEquiv σ 2
    ⟨H.vertex, H.graph.permuteOutgoing τ⟩) = _
  rw [he]
  exact (raw_actionProfile_permuteOutgoing (MixedGraphAveraging.internalGraphEquiv σ 2 H) β).trans
    (congrArg (fun s ↦ s * actionProfile (rawVelocityWeight a) (rawBinaryWeight b)
      (MixedGraphAveraging.internalGraphEquiv σ 2 H)) hs)

theorem rawActionClusterCoefficient_outgoingGraphEquiv (H : VectorGraph (a+b) 2)
    (T : Clusters (binaryBlock a b)) (τ : MixedGraphAveraging.OutgoingGroup (a+b)) :
    rawActionClusterCoefficient (MixedGraphAveraging.outgoingGraphEquiv τ 2 H) T =
      MixedGraphAveraging.outgoingSign (k := ℝ) τ * rawActionClusterCoefficient H T := by
  change rawActionClusterCoefficient ⟨H.vertex, H.graph.permuteOutgoing _⟩ T = _
  rw [rawActionClusterCoefficient_permuteOutgoing, MixedGraphAveraging.outgoingAt_sign_prod]

theorem rawActionClusterCoefficient_outgoingGraphEquiv_symm (H : VectorGraph (a+b) 2)
    (T : Clusters (binaryBlock a b)) (τ : MixedGraphAveraging.OutgoingGroup (a+b)) :
    rawActionClusterCoefficient ((MixedGraphAveraging.outgoingGraphEquiv τ 2).symm H) T =
      MixedGraphAveraging.outgoingSign (k := ℝ) τ * rawActionClusterCoefficient H T := by
  have h := rawActionClusterCoefficient_outgoingGraphEquiv
    ((MixedGraphAveraging.outgoingGraphEquiv τ 2).symm H) T τ
  rw [Equiv.apply_symm_apply] at h
  rw [h, ← mul_assoc, MixedGraphAveraging.outgoingSign_sq, one_mul]

theorem rawActionClusterCoefficient_cast_outgoing_symm {N : ℕ} (h : N = a+b)
    (H : VectorGraph N 2) (T : Clusters (binaryBlock a b))
    (τ : MixedGraphAveraging.OutgoingGroup N) :
    rawActionClusterCoefficient
        (castVertices h ((MixedGraphAveraging.outgoingGraphEquiv τ 2).symm H)) T =
      MixedGraphAveraging.outgoingSign (k := ℝ) τ *
        rawActionClusterCoefficient (castVertices h H) T := by
  subst N
  exact rawActionClusterCoefficient_outgoingGraphEquiv_symm H T τ

/-- Both actual graft weights cancel the outgoing average, retaining every
physical cluster and precisely the global internal factorial. -/
theorem boundaryAverage_canonical_targetAction_eq_unaveraged (N : ℕ) (H : VectorGraph N 2) :
    MixedGraphAveraging.boundaryAverage (targetActionProfile N
      (fun _ ↦ MixedGraphBoundaryProfiles.canonicalVelocityWeight (k := ℝ))
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ))) H =
      ((N+1).factorial : ℝ)⁻¹ * ∑ a : Fin (N+1),
        ∑ T : Clusters (binaryBlock a (N-a)),
          rawActionClusterCoefficient (castVertices (splitDegree N a).symm H) T := by
  rw [boundaryAverage_canonical_targetAction_eq_clusters]
  simp_rw [rawActionClusterCoefficient_cast_outgoing_symm]
  simp only [← Finset.mul_sum, ← mul_assoc, MixedGraphAveraging.outgoingSign_sq, one_mul]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [Fintype.card_fun, Fintype.card_perm, Fintype.card_fin, Nat.factorial_two,
    Nat.cast_pow, Nat.cast_ofNat]
  have hn : (2 : ℝ)^N ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

end EnvelopingIsomorphism.Deformation.MixedGraphOutgoingClusterSums
