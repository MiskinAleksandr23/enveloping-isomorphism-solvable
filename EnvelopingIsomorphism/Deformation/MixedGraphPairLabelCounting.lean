import EnvelopingIsomorphism.Deformation.GraphMarkedClusterCounting
import EnvelopingIsomorphism.Deformation.GraphCurvatureLabelCounting
import EnvelopingIsomorphism.Deformation.MixedGraphCorrectionProfiles

/-! Exact physical-pair label multiplicities with the genuine retained vector.
Source pairs contain the vector, curvature pairs exclude it. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
namespace EnvelopingIsomorphism.Deformation.MixedGraphPairLabelCounting
open scoped BigOperators Classical
open KontsevichGraph.General GraphLabelledClusterCounting GraphMarkedClusterCounting
open GraphCurvatureLabelCounting MixedGraphCorrectionProfiles
variable {n : ℕ}

abbrev SourcePairFiber (i : Fin (n + 1)) (T : PhysicalPair n) (v : Fin (n + 2)) :=
  {σ : ClusterFiber (childPair i) T.val // σ.val (vertexSplitChild i 0) = v}

abbrev SourcePairLabels (T : PhysicalPair n) (v : Fin (n + 2)) :=
  (i : Fin (n + 1)) × SourcePairFiber i T v

theorem card_sourcePairFiber (i : Fin (n + 1)) (T : PhysicalPair n) (v : Fin (n + 2))
    (hv : v ∈ T.val) : Fintype.card (SourcePairFiber i T v) = n.factorial := by
  have h := card_markedInsideFiber (childPair i) T.val (vertexSplitChild i 0) v
    (by simp [childPair]) hv ((card_childPair i).trans T.property.symm)
  simp only [← Nat.card_eq_fintype_card] at h ⊢
  simpa only [card_childPair, Nat.card_fin, Nat.add_sub_cancel, Nat.reduceSub,
    Nat.factorial_one, one_mul] using h

/-- The actual vector position fixes the orientation of a source pair, so
its root and permutation labels have exactly the quotient factorial, with no 2. -/
theorem card_sourcePairLabels (T : PhysicalPair n) (v : Fin (n + 2)) (hv : v ∈ T.val) :
    Fintype.card (SourcePairLabels T v) = (n + 1).factorial := by
  rw [Fintype.card_sigma]
  simp only [card_sourcePairFiber _ T v hv, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.factorial_succ]
  norm_cast

theorem sourcePairFiber_isEmpty (i : Fin (n + 1)) (T : PhysicalPair n) (v : Fin (n + 2))
    (hv : v ∉ T.val) : IsEmpty (SourcePairFiber i T v) := by
  refine ⟨fun σ => hv ?_⟩
  rw [← σ.property]
  exact (σ.val.property _).mpr (by simp [childPair])

abbrev CorrectionPairFiber (p : Placement n) (T : PhysicalPair (n + 1)) (v : Fin (n + 3)) :=
  {σ : ClusterFiber (childPair p.2.val) T.val // σ.val (expandedVector p) = v}

abbrev CorrectionPairLabels (T : PhysicalPair (n + 1)) (v : Fin (n + 3)) :=
  (p : Placement n) × CorrectionPairFiber p T v

theorem expandedVector_not_childPair (p : Placement n) : expandedVector p ∉ childPair p.2.val := by
  simp only [childPair, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨vertexSplitOld_ne_child p.2.val p.1 p.2.property.symm 0,
    vertexSplitOld_ne_child p.2.val p.1 p.2.property.symm 1⟩

theorem card_correctionPairFiber (p : Placement n) (T : PhysicalPair (n + 1))
    (v : Fin (n + 3)) (hv : v ∉ T.val) :
    Fintype.card (CorrectionPairFiber p T v) = 2 * n.factorial := by
  have h := card_markedOutsideFiber (childPair p.2.val) T.val (expandedVector p) v
    (expandedVector_not_childPair p) hv ((card_childPair p.2.val).trans T.property.symm)
  simp only [← Nat.card_eq_fintype_card] at h ⊢
  simpa only [card_childPair, Nat.card_fin, Nat.add_sub_cancel, Nat.add_sub_cancel_right,
    Nat.reduceSub, Nat.factorial_two] using h

/-- The marked exterior vector is fixed, but the two bivector children can
be exchanged. Every correction pair therefore has twice the quotient factorial. -/
theorem card_correctionPairLabels (T : PhysicalPair (n + 1)) (v : Fin (n + 3))
    (hv : v ∉ T.val) : Fintype.card (CorrectionPairLabels T v) = 2 * (n + 2).factorial := by
  rw [Fintype.card_sigma]
  simp only [card_correctionPairFiber _ T v hv, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hp : Fintype.card (Placement n) = (n + 2) * (n + 1) := by
    simp [Placement, Fintype.card_sigma, Fintype.card_subtype_compl]
  rw [hp, Nat.factorial_succ, Nat.factorial_succ]
  norm_cast
  ring

theorem correctionPairFiber_isEmpty (p : Placement n) (T : PhysicalPair (n + 1))
    (v : Fin (n + 3)) (hv : v ∈ T.val) : IsEmpty (CorrectionPairFiber p T v) := by
  refine ⟨fun σ => expandedVector_not_childPair p ?_⟩
  apply (σ.val.property _).mp
  rwa [σ.property]

/-- All normalized source pair label multiplicities cancel their actual
quotient factorial, leaving only the expanded graph's global average. -/
theorem source_pair_normalization_count :
    ((n + 1).factorial : ℝ)⁻¹ * ((n + 2).factorial : ℝ)⁻¹ *
      ((n + 1).factorial : ℝ) = ((n + 2).factorial : ℝ)⁻¹ := by
  have hn : ((n + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n + 1)
  field_simp

/-- The mixed correction retains the same three-halves two-point coefficient:
its half-outgoing normalizer and exchanged-child multiplicity cancel. -/
theorem correction_pair_normalization_count :
    (3 / 2 : ℝ) * (1 / 2 : ℝ) * ((n + 2).factorial : ℝ)⁻¹ *
      ((n + 3).factorial : ℝ)⁻¹ * (2 * (n + 2).factorial : ℕ) =
      (3 / 2 : ℝ) * ((n + 3).factorial : ℝ)⁻¹ := by
  have hn : ((n + 2).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n + 2)
  push_cast
  field_simp

end EnvelopingIsomorphism.Deformation.MixedGraphPairLabelCounting
