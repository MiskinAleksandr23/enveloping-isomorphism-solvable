import EnvelopingIsomorphism.Deformation.MainInfinityOrbitAssembly
import EnvelopingIsomorphism.Deformation.MainPurePhysicalAssembly
import EnvelopingIsomorphism.Deformation.MainInfinityValenceVanishing

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.MainInfinityPhysicalAssembly
open Kontsevich Configuration ForestRadialFaceClassification ForestRadialClusterLabels
open InfinityForestSimpleCluster (lower upper)
open MainScalarBoundaryAssembly MainInfinityPhysicalFace MainInfinityOrbitAssembly
open scoped Classical

def face (s : Fin 2) : FaceData where
  toFaceData := MainPurePhysicalAssembly.face s
  q := if s = 0 then 2 else 0
  outside := by fin_cases s <;> decide

abbrev ofMain := @MainPurePhysicalAssembly.ofMain

variable {n : ℕ} {H : UniformBinaryGraphs.BinaryGraph (n+2) 3} (P : MainPartition H)

theorem nativeKind_infinity_eq_clusters :
    nativeKindBoundary P .infinity =
      clusterValue (ofMain P) (face 0) + clusterValue (ofMain P) (face 1) := by
  rw [← MainClassifiedFaceAssembly.transportedKind_eq_nativeKind P
    (MainClassifiedFaceAssembly.defaultCoordinates P) .infinity]
  simp only [MainClassifiedFaceAssembly.transportedKind,
    MainClassifiedFaceAssembly.transportedValue_eq_orbitValue,clusterValue,← Finset.sum_add_distrib,orbitSum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro o _
  change (if kind 0 j.val o = .infinity then MainClassifiedFaceAssembly.orbitValue P j o else 0) = _
  by_cases ho : kind 0 j.val o = .infinity
  · rw [if_pos ho]
    by_cases hc : (boundaryClusterBlock (lower j.val o) (upper j.val o)).card = 2
    · have hh : ∀ l u : Fin 4, l ≤ u → (boundaryClusterBlock l u).card = 2 →
          (l = 0 ∧ u = 2) ∨ (l = 1 ∧ u = 3) := by decide
      rcases hh _ _ (block_order 0 j.val (RealForestCoarsePositions.node j.val o)) hc with h | h
      · simp [ho,h.1,h.2,face,MainPurePhysicalAssembly.face,ofMain,MainPurePhysicalAssembly.ofMain,MixedPairedCoreData.PairedData.orbitValue,
          MainClassifiedFaceAssembly.orbitValue]
      · simp [ho,h.1,h.2,face,MainPurePhysicalAssembly.face,ofMain,MainPurePhysicalAssembly.ofMain,MixedPairedCoreData.PairedData.orbitValue,
          MainClassifiedFaceAssembly.orbitValue]
    · have hz := MainInfinityValenceVanishing.main_orbitValue_eq_zero P j o ho hc
      have h0 : ¬ (kind 0 j.val o = .infinity ∧ lower j.val o = (face 0).l ∧ upper j.val o = (face 0).u) := by
        rintro ⟨_,hl,hu⟩
        exact hc (by rw [hl,hu]; exact (face 0).card_eq)
      have h1 : ¬ (kind 0 j.val o = .infinity ∧ lower j.val o = (face 1).l ∧ upper j.val o = (face 1).u) := by
        rintro ⟨_,hl,hu⟩
        exact hc (by rw [hl,hu]; exact (face 1).card_eq)
      rw [hz,if_neg h0,if_neg h1,zero_add]
  · simp only [ho,false_and,if_false,zero_add]

end EnvelopingIsomorphism.Deformation.MainInfinityPhysicalAssembly
