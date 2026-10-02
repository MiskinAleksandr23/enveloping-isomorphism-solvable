import EnvelopingIsomorphism.Deformation.MixedRealPhysicalClusterCoefficients
import EnvelopingIsomorphism.Deformation.MixedGraphPhysicalSubsetIndex

/-! The individual output and two input terms indexed by one original binary
subset, with proved transport across every actual factor-count equality. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedRealPhysicalSubsetCoefficients
open MixedGraphProfileCarrier MixedGraphTargetProfiles MixedGraphLabelledClusterCounting
open GraphLabelledClusterCounting MixedGraphPhysicalSubsetIndex
open MixedRealPhysicalClusterCoefficients
open scoped Classical

abbrev ClusterCoefficient := (a b : ℕ) → VectorGraph (a+b) 2 → Clusters (binaryBlock a b) → ℝ

def indexedSubsetCoefficient (c : ClusterCoefficient) {N : ℕ} (H : VectorGraph N 2)
    (p : Index N) : ℝ :=
  c p.1 (N-p.1) (castVertices (splitDegree N p.1).symm H) p.2

def subsetCoefficient (c : ClusterCoefficient) {N : ℕ} (H : VectorGraph N 2)
    (S : Finset (Fin (N+1))) : ℝ :=
  if hs : S.card ≤ N then
    indexedSubsetCoefficient c H ((indexEquiv N).symm ⟨S,hs⟩)
  else 0

def outputCoefficient {N : ℕ} (H : VectorGraph N 2) (S : Finset (Fin (N+1))) : ℝ :=
  subsetCoefficient (fun _ _ ↦ rawOutputClusterCoefficient) H S

def inputCoefficient {N : ℕ} (r : Fin 2) (H : VectorGraph N 2)
    (S : Finset (Fin (N+1))) : ℝ :=
  subsetCoefficient (fun _ _ ↦ rawInputClusterCoefficient r) H S

theorem subsetCoefficient_eq_of_count (c : ClusterCoefficient) {a b N : ℕ}
    (h : a+b = N) (H : VectorGraph N 2) (T : Clusters (binaryBlock a b))
    (S : Finset (Fin (N+1)))
    (hS : T.val.map (finCongr (congrArg (· + 1) h)).toEmbedding = S) :
    subsetCoefficient c H S = c a b (castVertices h.symm H) T := by
  have hc : S.card ≤ N := by
    rw [← hS,Finset.card_map,T.property,card_binaryBlock]
    omega
  have hp : (indexEquiv N).symm ⟨S,hc⟩ = indexOfCount h T := by
    apply (indexEquiv N).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    exact ((subset_indexOfCount h T).trans hS).symm
  rw [subsetCoefficient,dif_pos hc,hp]
  have hb : b = N-a := by omega
  subst b
  rfl

theorem outputCoefficient_eq_of_count {a b N : ℕ} (h : a+b = N)
    (H : VectorGraph N 2) (T : Clusters (binaryBlock a b)) (S : Finset (Fin (N+1)))
    (hS : T.val.map (finCongr (congrArg (· + 1) h)).toEmbedding = S) :
    outputCoefficient H S = rawOutputClusterCoefficient (castVertices h.symm H) T :=
  subsetCoefficient_eq_of_count _ h H T S hS

theorem inputCoefficient_eq_of_count {a b N : ℕ} (r : Fin 2) (h : a+b = N)
    (H : VectorGraph N 2) (T : Clusters (binaryBlock a b)) (S : Finset (Fin (N+1)))
    (hS : T.val.map (finCongr (congrArg (· + 1) h)).toEmbedding = S) :
    inputCoefficient r H S = rawInputClusterCoefficient r (castVertices h.symm H) T :=
  subsetCoefficient_eq_of_count _ h H T S hS

theorem coefficient_eq_output_sub_inputs {N : ℕ} (H : VectorGraph N 2)
    (S : Finset (Fin (N+1))) :
    coefficient H S = outputCoefficient H S - inputCoefficient 0 H S - inputCoefficient 1 H S := by
  unfold coefficient outputCoefficient inputCoefficient subsetCoefficient
  split_ifs with h
  · exact rawActionClusterCoefficient_eq _ _
  · ring

end EnvelopingIsomorphism.Deformation.MixedRealPhysicalSubsetCoefficients
