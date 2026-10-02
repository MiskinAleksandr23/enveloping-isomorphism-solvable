import EnvelopingIsomorphism.Deformation.MixedInfinityOrbitAssembly
import EnvelopingIsomorphism.Deformation.MainInfinityValenceVanishing

/-! The two full-internal-cluster mixed infinity endpoints, with their
actual remaining boundary labels and original Stokes orientations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedInfinityPhysicalAssembly
open Kontsevich Configuration ForestRadialFaceClassification ForestRadialClusterLabels
open InfinityForestSimpleCluster (lower upper)
open MixedScalarBoundaryAssembly MixedPairedCoreData MixedInfinityPhysicalFace MixedInfinityOrbitAssembly
open MeasureTheory OrientedFormChangeVariables
open scoped Classical

def face (s : Fin 2) : FaceData where
  l := Fin.castAdd 1 s
  u := Fin.natAdd 1 s
  a := s
  ordered := by change s.val ≤ 1 + s.val; omega
  left_mem := by fin_cases s <;> decide
  card_eq := by fin_cases s <;> decide
  q := if s = 0 then 1 else 0
  outside := by fin_cases s <;> decide

variable {N : ℕ} {H : MixedGraphProfileCarrier.VectorGraph N 2} (P : MixedPartition H)

theorem nativeKind_infinity_eq_clusters :
    nativeKindBoundary P .infinity =
      clusterValue (ofMixed P) (face 0) + clusterValue (ofMixed P) (face 1) := by
  unfold nativeKindBoundary ForestRadialFaceLocalization.classifiedContribution
  simp only [Finset.mul_sum,clusterValue,← Finset.sum_add_distrib,orbitSum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro o _
  by_cases ho : kind 0 j.val o = .infinity
  · rw [if_pos ho]
    rw [← ForestRadialFaceLocalization.contribution_eq_integral_source
      (mixed_dimension N) j.val o (P.partition j) (mixedEdges H) (mixedEdges_noLoops H)
      (P.localizer j) (P.localization j)]
    change PairedData.orbitValue (ofMixed P) j o = _
    by_cases hc : (boundaryClusterBlock (lower j.val o) (upper j.val o)).card = 1
    · have hh : ∀ l u : Fin 3, l ≤ u → (boundaryClusterBlock l u).card = 1 →
          (l = 0 ∧ u = 1) ∨ (l = 1 ∧ u = 2) := by decide
      rcases hh _ _ (block_order 0 j.val (RealForestCoarsePositions.node j.val o)) hc with h | h
      · simp [ho,h.1,h.2,face]
      · simp [ho,h.1,h.2,face]
    · have hz := MainInfinityValenceVanishing.mixed_orbitValue_eq_zero P j o ho hc
      have h0 : ¬ (kind 0 j.val o = .infinity ∧ lower j.val o = (face 0).l ∧ upper j.val o = (face 0).u) := by
        rintro ⟨_,hl,hu⟩
        exact hc (by rw [hl,hu]; exact (face 0).card_eq)
      have h1 : ¬ (kind 0 j.val o = .infinity ∧ lower j.val o = (face 1).l ∧ upper j.val o = (face 1).u) := by
        rintro ⟨_,hl,hu⟩
        exact hc (by rw [hl,hu]; exact (face 1).card_eq)
      rw [hz,if_neg h0,if_neg h1,zero_add]
  · simp only [ho,false_and,if_false,mul_zero,zero_add]

theorem face_sign (s : Fin 2) :
    BoundaryAnchoredInfinityData.referenceSign (face s).l (face s).q * (-1 : ℝ)^(face s).q.val = -1 := by
  fin_cases s <;> norm_num [face,BoundaryAnchoredInfinityData.referenceSign]

theorem nativeKind_infinity_eq_integrals :
    nativeKindBoundary P .infinity =
      -(∫ y in region (mixed_dimension N) (face 0),
        density (form (mixed_dimension N) (face 0) (mixedEdges H)) y) -
      (∫ y in region (mixed_dimension N) (face 1),
        density (form (mixed_dimension N) (face 1) (mixedEdges H)) y) := by
  rw [nativeKind_infinity_eq_clusters,clusterValue_eq_integral,clusterValue_eq_integral,
    face_sign,face_sign]
  ring

end EnvelopingIsomorphism.Deformation.MixedInfinityPhysicalAssembly
