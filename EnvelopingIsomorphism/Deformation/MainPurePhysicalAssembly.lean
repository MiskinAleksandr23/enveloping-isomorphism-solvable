import EnvelopingIsomorphism.Deformation.MainPureOrbitAssembly
import EnvelopingIsomorphism.Deformation.MainPureInfinityVanishing

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.MainPurePhysicalAssembly
open Kontsevich Configuration ForestRadialFaceClassification ForestRadialClusterLabels
open PureForestSimpleCluster (lower upper)
open MainScalarBoundaryAssembly MainPurePhysicalFace MainPureOrbitAssembly
open scoped Classical

def face (s : Fin 2) : FaceData 3 where
  l := Fin.castAdd 2 s
  u := Fin.natAdd 2 s
  a := s.castSucc
  b := s.succ
  ordered := by change s.val ≤ 2 + s.val; omega
  left_mem := by fin_cases s <;> decide
  right_mem := by fin_cases s <;> decide
  endpoints := by change s.val < s.val + 1; omega
  left_eq := rfl
  right_eq := by change s.val + 1 + 1 = 2 + s.val; omega
  card_eq := by fin_cases s <;> decide

def ofMain {n : ℕ} {H : UniformBinaryGraphs.BinaryGraph (n+2) 3} (P : MainPartition H) :
    MixedPairedCoreData.PairedData (main_dimension n) (mainEdges H) where
  noLoops := mainEdges_noLoops H
  charts := P.charts
  partition := P.partition
  localizer := P.localizer
  orientation := P.orientation
  support := P.support
  regular := P.regular
  localization := P.localization
  orientation_jacobian := P.orientation_jacobian

variable {n : ℕ} {H : UniformBinaryGraphs.BinaryGraph (n+2) 3} (P : MainPartition H)

theorem nativeKind_pureBoundary_eq_clusters :
    nativeKindBoundary P .pureBoundary =
      clusterValue (ofMain P) (face 0) + clusterValue (ofMain P) (face 1) := by
  rw [← MainClassifiedFaceAssembly.transportedKind_eq_nativeKind P
    (MainClassifiedFaceAssembly.defaultCoordinates P) .pureBoundary]
  simp only [MainClassifiedFaceAssembly.transportedKind,
    MainClassifiedFaceAssembly.transportedValue_eq_orbitValue,clusterValue,← Finset.sum_add_distrib,orbitSum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro o _
  by_cases ho : kind 0 j.val o = .pureBoundary
  · rw [if_pos ho]
    by_cases hc : (boundaryClusterBlock (lower j.val o) (upper j.val o)).card = 2
    · have hh : ∀ l u : Fin 4, l ≤ u → (boundaryClusterBlock l u).card = 2 →
          (l = 0 ∧ u = 2) ∨ (l = 1 ∧ u = 3) := by decide
      rcases hh _ _ (block_order 0 j.val (RealForestCoarsePositions.node j.val o)) hc with h | h
      · simp [ho,h.1,h.2,face,ofMain,MixedPairedCoreData.PairedData.orbitValue,
          MainClassifiedFaceAssembly.orbitValue]
      · simp [ho,h.1,h.2,face,ofMain,MixedPairedCoreData.PairedData.orbitValue,
          MainClassifiedFaceAssembly.orbitValue]
    · have hz := MainPureInfinityVanishing.main_pure_orbitValue_eq_zero P j o ho hc
      have h0 : ¬ (kind 0 j.val o = .pureBoundary ∧ lower j.val o = (face 0).l ∧ upper j.val o = (face 0).u) := by
        rintro ⟨_,hl,hu⟩
        exact hc (by rw [hl,hu]; exact (face 0).card_eq)
      have h1 : ¬ (kind 0 j.val o = .pureBoundary ∧ lower j.val o = (face 1).l ∧ upper j.val o = (face 1).u) := by
        rintro ⟨_,hl,hu⟩
        exact hc (by rw [hl,hu]; exact (face 1).card_eq)
      rw [hz,if_neg h0,if_neg h1,zero_add]
  · simp only [ho,false_and,if_false,zero_add]

end EnvelopingIsomorphism.Deformation.MainPurePhysicalAssembly
