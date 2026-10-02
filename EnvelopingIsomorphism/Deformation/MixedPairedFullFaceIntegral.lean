import EnvelopingIsomorphism.Deformation.MixedPairedCoreFullFace

/-! Actual mixed Stokes paired contributions on full physical cluster faces.
All natural-number degrees, including N=0, use the same graph-independent
coverage, angular fundamental domain and signed integration proofs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedPairedFullFaceIntegral
open Kontsevich MixedGraphProfileCarrier MixedScalarBoundaryAssembly
open MixedPairedCoreData MixedPairedCoreCover MeasureTheory
open scoped Classical
variable {N : ℕ} {H : VectorGraph N 2} (P : MixedPartition H)

def clusterValue (T : Finset (Fin (N+1))) : ℝ :=
  MixedPairedCoreFullFace.clusterValue (ofMixed P) T

def density (T : Finset (Fin (N+1))) (hT : 1 < T.card) : RealSpace (m := 2) T → ℝ :=
  MixedPairedCoreIntegral.density (hdim := mixed_dimension N) (es := mixedEdges H) T hT

theorem clusterValue_eq_neg_integral (T : Finset (Fin (N+1))) (hT : 1 < T.card) :
    clusterValue P T = -(∫ y in Face (m := 2) T, density (H := H) T hT y) :=
  MixedPairedCoreFullFace.clusterValue_eq_neg_integral (ofMixed P) T hT

theorem clusterValue_eq_zero_of_large (T : Finset (Fin (N+1))) (hT : 3 ≤ T.card) :
    clusterValue P T = 0 :=
  MixedPairedCoreFullFace.clusterValue_eq_zero_of_large (ofMixed P) T hT

theorem clusterValue_eq_zero_of_small (T : Finset (Fin (N+1))) (hT : T.card < 2) :
    clusterValue P T = 0 := by
  unfold clusterValue MixedPairedCoreFullFace.clusterValue
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro o _
  split_ifs with ho he
  · have hc := ForestRadialClusterLabels.upperNode_card 0 j.val o ho
    change 1 < (PairedForestSimpleCluster.S j.val o ho).card at hc
    rw [he] at hc
    omega
  · rfl
  · rfl

theorem sum_clusterValue_eq_paired :
    (∑ T : Finset (Fin (N+1)), clusterValue P T) = nativeKindBoundary P .paired := by
  unfold clusterValue MixedPairedCoreFullFace.clusterValue
  dsimp only [ofMixed]
  rw [Finset.sum_comm]
  unfold nativeKindBoundary ForestRadialFaceLocalization.classifiedContribution
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o _
  by_cases ho : ForestRadialFaceClassification.kind 0 j.val o = .paired
  · simp only [dif_pos ho, if_pos ho]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    unfold PairedData.orbitValue
    dsimp only
    rw [ForestRadialFaceLocalization.contribution_eq_integral_source
      (mixed_dimension N) j.val o (P.partition j) (mixedEdges H) (mixedEdges_noLoops H)
      (P.localizer j) (P.localization j)]
  · simp only [dif_neg ho, if_neg ho, Finset.sum_const_zero, mul_zero]

/-- Only two-element physical masks survive in the mixed paired boundary.
The zero and large strata are eliminated by proved native/integral facts. -/
theorem paired_eq_sum_pairs :
    nativeKindBoundary P .paired =
      ∑ T : {T : Finset (Fin (N+1)) // T.card = 2}, clusterValue P T.val := by
  rw [← sum_clusterValue_eq_paired P,
    ← Fintype.sum_subtype_add_sum_subtype (fun T : Finset (Fin (N+1)) ↦ T.card = 2)]
  have hz : ∀ T : {T : Finset (Fin (N+1)) // ¬ T.card = 2}, clusterValue P T.val = 0 := by
    intro T
    rcases lt_or_gt_of_ne T.property with hsmall | hlarge
    · exact clusterValue_eq_zero_of_small P T.val hsmall
    · exact clusterValue_eq_zero_of_large P T.val (by omega)
  simp only [hz, Finset.sum_const_zero, add_zero]

end EnvelopingIsomorphism.Deformation.MixedPairedFullFaceIntegral
