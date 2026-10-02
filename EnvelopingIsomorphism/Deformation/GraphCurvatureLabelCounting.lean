import EnvelopingIsomorphism.Deformation.GraphLabelledClusterCounting
import EnvelopingIsomorphism.Deformation.UniformBinaryContraction

/-! Exact finite label multiplicities for the two-child curvature boundary:
all root placements, unordered physical pairs, and outgoing slot normalizers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.GraphCurvatureLabelCounting
open KontsevichGraph.General GraphLabelledClusterCounting
open scoped Classical BigOperators
variable {n : ℕ}

def childPair (i : Fin (n + 1)) : Finset (Fin (n + 2)) :=
  {vertexSplitChild i 0, vertexSplitChild i 1}

@[simp] theorem card_childPair (i : Fin (n + 1)) : (childPair i).card = 2 := by
  have h : vertexSplitChild i 0 ≠ vertexSplitChild i 1 :=
    (vertexSplitChild_injective i).ne (by decide)
  exact Finset.card_pair h

abbrev PhysicalPair (n : ℕ) := {T : Finset (Fin (n + 2)) // T.card = 2}

def movedPair (i : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 2))) : PhysicalPair n :=
  ⟨(childPair i).map σ.toEmbedding, by simp⟩

theorem movedPair_eq_iff (i : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 2))) (T : PhysicalPair n) :
      movedPair i σ = T ↔ ∀ x, σ x ∈ T.val ↔ x ∈ childPair i := by
  simpa only [Subtype.ext_iff, movedPair, movedCluster] using
    movedCluster_eq_iff (childPair i) σ ⟨T.val, T.property.trans (card_childPair i).symm⟩

theorem card_pairLabelFiber (i : Fin (n + 1)) (T : PhysicalPair n) :
    Fintype.card {σ : Equiv.Perm (Fin (n + 2)) // movedPair i σ = T} = 2 * n.factorial := by
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun σ ↦ movedPair_eq_iff i σ T))]
  change Fintype.card (ClusterFiber (childPair i) T.val) = _
  have h := card_clusterFiber (childPair i) T.val ((card_childPair i).trans T.property.symm)
  convert h using 1
  · congr 1
    exact Subsingleton.elim _ _
  · simp

abbrev PairLabelFiber (T : PhysicalPair n) :=
  {D : Fin (n + 1) × Equiv.Perm (Fin (n + 2)) // movedPair D.1 D.2 = T}

def pairLabelFiberEquiv (T : PhysicalPair n) : PairLabelFiber T ≃
    ((i : Fin (n + 1)) × {σ : Equiv.Perm (Fin (n + 2)) // movedPair i σ = T}) where
  toFun D := ⟨D.val.1, D.val.2, D.property⟩
  invFun D := ⟨(D.1,D.2.val),D.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Including every placed curvature root gives exactly twice the quotient
internal-label factorial for each physical unordered pair. -/
theorem card_pairLabelFiber_all (T : PhysicalPair n) :
    Fintype.card (PairLabelFiber T) = 2 * (n + 1).factorial := by
  rw [Fintype.card_congr (pairLabelFiberEquiv T), Fintype.card_sigma]
  simp only [card_pairLabelFiber, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Nat.factorial_succ]
  norm_cast
  ring

/-- This is a genuine finite fibre sum, with every root position and label
permutation counted once. No graph-invariance premise is hidden here. -/
theorem sum_pair_labels {k : Type*} [CommSemiring k] (f : PhysicalPair n → k) :
    (∑ D : Fin (n + 1) × Equiv.Perm (Fin (n + 2)), f (movedPair D.1 D.2)) =
      (2 * (n + 1).factorial : ℕ) * ∑ T : PhysicalPair n, f T := by
  rw [← Fintype.sum_fiberwise (fun D : Fin (n + 1) × Equiv.Perm (Fin (n + 2)) ↦ movedPair D.1 D.2)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  calc
    _ = ∑ _D : PairLabelFiber T, f T := Finset.sum_congr rfl (fun D _ ↦ congrArg f D.property)
    _ = _ := by simp [card_pairLabelFiber_all, nsmul_eq_mul]

private theorem permTwo_zero_iff (s : Fin 2) :
    ∀ τ : Equiv.Perm (Fin 2), τ 0 = s ↔ τ = Equiv.swap 0 s := by
  fin_cases s <;> decide

/-- Exactly one local permutation sends outgoing slot zero to the chosen slot. -/
def outgoingNormalizerEquiv (v : Fin (n + 2)) (s : Fin 2) :
    {τ : Fin (n + 2) → Equiv.Perm (Fin 2) // τ v 0 = s} ≃
      ({w : Fin (n + 2) // w ≠ v} → Equiv.Perm (Fin 2)) where
  toFun τ w := τ.val w.val
  invFun f := ⟨fun w ↦ if h : w = v then Equiv.swap 0 s else f ⟨w,h⟩, by simp⟩
  left_inv τ := by
    apply Subtype.ext
    funext w
    dsimp only
    split_ifs with h
    · subst w
      exact ((permTwo_zero_iff s (τ.val v)).mp τ.property).symm
    · rfl
  right_inv f := by
    funext w
    simp only [dif_neg w.property]

/-- Half of all outgoing permutations normalize the unique internal arrow;
all other vertex slots remain freely permuted. -/
theorem card_outgoingNormalizer (v : Fin (n + 2)) (s : Fin 2) :
    Fintype.card {τ : Fin (n + 2) → Equiv.Perm (Fin 2) // τ v 0 = s} = 2 ^ (n + 1) := by
  rw [Fintype.card_congr (outgoingNormalizerEquiv v s), Fintype.card_fun]
  simp [Fintype.card_perm, Fintype.card_subtype_compl]

/-- The outgoing-normalizer fibre occupies exactly one half of the full
signed-averaging index set, independently of the number of outside vertices. -/
theorem outgoingNormalizer_ratio (v : Fin (n + 2)) (s : Fin 2) :
    ((2 : ℝ) ^ (n + 2))⁻¹ *
      Fintype.card {τ : Fin (n + 2) → Equiv.Perm (Fin 2) // τ v 0 = s} = 1 / 2 := by
  rw [card_outgoingNormalizer, Nat.cast_pow, Nat.cast_ofNat]
  have h : (2 : ℝ) ^ (n + 1) ≠ 0 := by positivity
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
  field_simp

/-- All concrete multiplicities cancel against the exact averaging and MC
factorials, leaving the actual two-point geometric coefficient three-halves. -/
theorem curvature_normalization_count :
    (3 / 2 : ℝ) * (1 / 2 : ℝ) * ((n + 1).factorial : ℝ)⁻¹ * ((n + 2).factorial : ℝ)⁻¹ *
      (2 * (n + 1).factorial : ℕ) = (3 / 2 : ℝ) * ((n + 2).factorial : ℝ)⁻¹ := by
  have h : ((n + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n + 1)
  push_cast
  field_simp

end EnvelopingIsomorphism.Deformation.GraphCurvatureLabelCounting
