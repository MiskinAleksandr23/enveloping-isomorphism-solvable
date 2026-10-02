import EnvelopingIsomorphism.Deformation.MainScalarBoundaryAssembly
import EnvelopingIsomorphism.Deformation.BinaryAverageLinearity
import EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeightOutgoing

/-! Genuine outgoing covariance of both extracted real-boundary factors,
including the dependent incoming-edge assignment, and cancellation of the
outgoing average in the actual physical cluster sum. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.GraphBinaryOutgoingClusterSums
open KontsevichGraph.General UniformBinaryGraphs GraphWeightedInsertion
open GraphBinaryGraftRelabelling GraphBinaryGraftFibres GraphCanonicalBinaryWeights
open GraphBinaryClusterSums GraphLabelledClusterCounting BinaryGraphAveraging
open scoped Classical BigOperators
variable {a b : ℕ}

/-- The actual incoming edge is transported with its outgoing slot. -/
def incomingOutgoingEquiv (Γ : BinaryGraph a 2) (r : Fin 2)
    (τ : Fin a → Equiv.Perm (Fin 2)) :
    {e : Edge (fun _ : Fin a ↦ 2) // (Γ.permuteOutgoing τ).target e = Sum.inr r} ≃
      {e : Edge (fun _ : Fin a ↦ 2) // Γ.target e = Sum.inr r} :=
  Equiv.subtypeEquiv (outgoingEdgePerm τ) (by intro e; rfl)

def outgoingChoices (Γ : BinaryGraph a 2) (r : Fin 2)
    (τ : Fin a → Equiv.Perm (Fin 2)) (χ : GraftChoices (b := b) Γ r) :
    GraftChoices (b := b) (Γ.permuteOutgoing τ) r := fun e ↦ χ (incomingOutgoingEquiv Γ r τ e)

/-- Both graph factors and every incoming assignment transform literally. -/
theorem uniformGraft_permuteOutgoing (Γ : BinaryGraph a 2) (Δ : BinaryGraph b 2)
    (r : Fin 2) (χ : GraftChoices Γ r) (τ : Fin (a+b) → Equiv.Perm (Fin 2)) :
    (uniformGraft Γ Δ r χ).permuteOutgoing τ =
      uniformGraft (Γ.permuteOutgoing (fun v ↦ τ (Fin.castAdd b v)))
        (Δ.permuteOutgoing (fun v ↦ τ (Fin.natAdd a v))) r
        (outgoingChoices Γ r (fun v ↦ τ (Fin.castAdd b v)) χ) := by
  apply Graph.ext
  funext e
  rcases e with ⟨v,j⟩
  refine Fin.addCases (fun v ↦ ?_) (fun v ↦ ?_) v
  · change (uniformGraft Γ Δ r χ).target ⟨Fin.castAdd b v, τ (Fin.castAdd b v) j⟩ = _
    rw [uniformGraft_target_outer, uniformGraft_target_outer]
    unfold Graph.graftOuterTarget
    by_cases h : Γ.target ⟨v,τ (Fin.castAdd b v) j⟩ = Sum.inr r
    · simp only [Graph.permuteOutgoing, outgoingEdgePerm_apply, dif_pos h]
      rfl
    · simp only [Graph.permuteOutgoing, outgoingEdgePerm_apply, dif_neg h]
  · change (uniformGraft Γ Δ r χ).target ⟨Fin.natAdd a v, τ (Fin.natAdd a v) j⟩ = _
    rw [uniformGraft_target_inner, uniformGraft_target_inner]
    rfl

def outgoingData (r : Fin 2) (τ : Fin (a+b) → Equiv.Perm (Fin 2))
    (D : GraftIndex a b r) : GraftIndex a b r :=
  ⟨D.1.permuteOutgoing (fun v ↦ τ (Fin.castAdd b v)),
    D.2.1.permuteOutgoing (fun v ↦ τ (Fin.natAdd a v)),
    outgoingChoices D.1 r (fun v ↦ τ (Fin.castAdd b v)) D.2.2⟩

theorem graftGraph_outgoingData (r : Fin 2) (τ : Fin (a+b) → Equiv.Perm (Fin 2))
    (D : GraftIndex a b r) :
    graftGraph r (outgoingData r τ D) = (graftGraph r D).permuteOutgoing τ :=
  (uniformGraft_permuteOutgoing D.1 D.2.1 r D.2.2 τ).symm

def outgoingDataEquiv (r : Fin 2) (τ : Fin (a+b) → Equiv.Perm (Fin 2)) :
    Equiv.Perm (GraftIndex a b r) where
  toFun := outgoingData r τ
  invFun := outgoingData r (fun v ↦ (τ v).symm)
  left_inv D := by
    apply graftGraph_injective r
    rw [graftGraph_outgoingData, graftGraph_outgoingData]
    exact (Graph.outgoingGraphEquiv (fun _ ↦ 2) 3 τ).left_inv _
  right_inv D := by
    apply graftGraph_injective r
    rw [graftGraph_outgoingData, graftGraph_outgoingData]
    exact (Graph.outgoingGraphEquiv (fun _ ↦ 2) 3 τ).right_inv _

/-- The true raw weight, including the nullary multiplication endpoint,
has the outgoing sign furnished by its geometric edge-form determinant. -/
theorem rawBinaryWeight_permuteOutgoing (n : ℕ) (Γ : BinaryGraph n 2)
    (τ : Fin n → Equiv.Perm (Fin 2)) :
    rawBinaryWeight n (Γ.permuteOutgoing τ) = outgoingSign (k := ℝ) τ * rawBinaryWeight n Γ := by
  cases n with
  | zero => simp [rawBinaryWeight, outgoingSign]
  | succ n =>
    exact Kontsevich.GeometricWeightOutgoing.canonicalWeight_permuteOutgoing Γ
      (Kontsevich.GeometricWeights.binaryEdgeCount n) τ

private theorem outgoingSign_split (τ : Fin (a+b) → Equiv.Perm (Fin 2)) :
    outgoingSign (k := ℝ) (fun v ↦ τ (Fin.castAdd b v)) *
      outgoingSign (k := ℝ) (fun v ↦ τ (Fin.natAdd a v)) = outgoingSign (k := ℝ) τ := by
  symm
  exact Fin.prod_univ_add _

/-- Actual finite graft profile covariance, without a weight-covariance or
extraction hypothesis. The incoming-choice equivalence is explicit above. -/
theorem raw_graftProfile_permuteOutgoing (r : Fin 2) (H : BinaryGraph (a+b) 3)
    (τ : Fin (a+b) → Equiv.Perm (Fin 2)) :
    graftProfile r (rawBinaryWeight a) (rawBinaryWeight b) (H.permuteOutgoing τ) =
      outgoingSign (k := ℝ) τ * graftProfile r (rawBinaryWeight a) (rawBinaryWeight b) H := by
  unfold graftProfile GraphCoefficientProfiles.pushforward
  rw [← Equiv.sum_comp (outgoingDataEquiv r τ), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D _
  change (if graftGraph r (outgoingData r τ D) = H.permuteOutgoing τ then
    rawBinaryWeight a (D.1.permuteOutgoing (fun v ↦ τ (Fin.castAdd b v))) *
      rawBinaryWeight b (D.2.1.permuteOutgoing (fun v ↦ τ (Fin.natAdd a v))) else 0) = _
  rw [graftGraph_outgoingData]
  have he : (graftGraph r D).permuteOutgoing τ = H.permuteOutgoing τ ↔ graftGraph r D = H :=
    (Graph.outgoingGraphEquiv (fun _ ↦ 2) 3 τ).injective.eq_iff
  rw [he, rawBinaryWeight_permuteOutgoing, rawBinaryWeight_permuteOutgoing]
  split_ifs
  · rw [show (outgoingSign (k := ℝ) (fun v ↦ τ (Fin.castAdd b v)) * rawBinaryWeight a D.1) *
        (outgoingSign (k := ℝ) (fun v ↦ τ (Fin.natAdd a v)) * rawBinaryWeight b D.2.1) =
        (outgoingSign (k := ℝ) (fun v ↦ τ (Fin.castAdd b v)) *
          outgoingSign (k := ℝ) (fun v ↦ τ (Fin.natAdd a v))) *
          (rawBinaryWeight a D.1 * rawBinaryWeight b D.2.1) by ring,
      outgoingSign_split]
  · simp

/-- The genuinely extracted product transforms by the full graph sign. -/
theorem raw_extractedCoefficient_permuteOutgoing (r : Fin 2) (H : BinaryGraph (a+b) 3)
    (τ : Fin (a+b) → Equiv.Perm (Fin 2)) :
    extractedCoefficient r (rawBinaryWeight a) (rawBinaryWeight b) (H.permuteOutgoing τ) =
      outgoingSign (k := ℝ) τ * extractedCoefficient r (rawBinaryWeight a) (rawBinaryWeight b) H := by
  simp only [← graftProfile_eq_extractedCoefficient]
  exact raw_graftProfile_permuteOutgoing r H τ

/-- A fixed physical cluster retains its actual extracted incoming assignment
and receives precisely the outgoing sign of the entire original graph. -/
theorem rawClusterCoefficient_permuteOutgoing (r : Fin 2) (H : BinaryGraph (a+b) 3)
    (T : Clusters (innerBlock a b)) (τ : Fin (a+b) → Equiv.Perm (Fin 2)) :
    rawClusterCoefficient r (H.permuteOutgoing τ) T = outgoingSign (k := ℝ) τ * rawClusterCoefficient r H T := by
  let σ := (clusterRepresentative (innerBlock a b) T).val.symm
  have he : (H.permuteOutgoing τ).permuteInternal σ =
      (H.permuteInternal σ).permuteOutgoing (fun v ↦ τ (σ.symm v)) := by
    apply Graph.ext
    funext e
    rcases e with ⟨v,j⟩
    rfl
  change extractedCoefficient r (rawBinaryWeight a) (rawBinaryWeight b) ((H.permuteOutgoing τ).permuteInternal σ) = _
  rw [he, raw_extractedCoefficient_permuteOutgoing, outgoingSign_reindex]
  rfl

open GraphAssociatorProfiles

private theorem rawClusterCoefficient_cast_outgoing {N : ℕ} (h : N = a+b)
    (r : Fin 2) (H : BinaryGraph N 3) (T : Clusters (innerBlock a b))
    (τ : Fin N → Equiv.Perm (Fin 2)) :
    rawClusterCoefficient r (castVertices h (H.permuteOutgoing τ)) T =
      outgoingSign (k := ℝ) τ * rawClusterCoefficient r (castVertices h H) T := by
  subst N
  exact rawClusterCoefficient_permuteOutgoing r H T τ

private theorem outgoingSign_symm {N : ℕ} (τ : Fin N → Equiv.Perm (Fin 2)) :
    outgoingSign (k := ℝ) (fun v ↦ (τ v).symm) = outgoingSign (k := ℝ) τ := by
  simp [outgoingSign, permutationSign, Equiv.Perm.sign_symm]

/-- The outgoing average cancels exactly against the genuine graph-form
covariance. All degree splits and physical subsets remain, each once. -/
theorem realClusterSum_eq_unaveraged {N : ℕ} (H : BinaryGraph N 3) :
    MainScalarBoundaryAssembly.realClusterSum H =
      ∑ a : Fin (N+1), ∑ T : Clusters (innerBlock a (N-a)),
        (rawClusterCoefficient 0 (castVertices (splitDegree N a).symm H) T -
          rawClusterCoefficient 1 (castVertices (splitDegree N a).symm H) T) := by
  unfold MainScalarBoundaryAssembly.realClusterSum
  simp_rw [rawClusterCoefficient_cast_outgoing, outgoingSign_symm]
  simp only [← mul_sub, ← Finset.mul_sum, ← mul_assoc, outgoingSign_sq, one_mul]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [Fintype.card_fun, Fintype.card_perm, Fintype.card_fin, Nat.factorial_two,
    Nat.cast_pow, Nat.cast_ofNat]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num)), one_mul]

end EnvelopingIsomorphism.Deformation.GraphBinaryOutgoingClusterSums
