import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestSimpleCluster

/-! The marks used by actual paired product charts depend only on the intrinsic
cluster label set. Native forest reference choices have already disappeared. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCanonicalMarks
open Configuration PairedForestSimpleCluster ForestRadialFaceClassification ForestRadialClusterLabels
open scoped Classical
variable {n : ℕ}

def canonicalAnchor (S : Finset (Fin (n+1))) : Fin (n+1) :=
  if 0 ∈ S then 0 else if h : S.Nonempty then h.choose else 0

def canonicalReference (S : Finset (Fin (n+1))) : Fin (n+1) :=
  if h : 1 < S.card then (S.exists_mem_ne h (canonicalAnchor S)).choose else canonicalAnchor S

theorem canonicalAnchor_mem (S : Finset (Fin (n+1))) (hS : S.Nonempty) : canonicalAnchor S ∈ S := by
  unfold canonicalAnchor
  split_ifs with h
  · exact h
  · exact hS.choose_spec

theorem canonicalReference_mem (S : Finset (Fin (n+1))) (hS : 1 < S.card) : canonicalReference S ∈ S := by
  simp only [canonicalReference, dif_pos hS]
  exact (S.exists_mem_ne hS (canonicalAnchor S)).choose_spec.1

theorem canonicalReference_ne (S : Finset (Fin (n+1))) (hS : 1 < S.card) : canonicalReference S ≠ canonicalAnchor S := by
  simp only [canonicalReference, dif_pos hS]
  exact (S.exists_mem_ne hS (canonicalAnchor S)).choose_spec.2

variable {m : ℕ} (x : Compactification (0 : Fin (n+1)) m)
  (o : ForestRadialFaceClassification.Orbit 0 x) (ho : kind 0 x o = .paired)

theorem anchor_eq_canonical : anchor x o ho = canonicalAnchor (S x o ho) := by
  simp only [anchor, canonicalAnchor, dif_pos (S_nonempty x o ho)]

theorem reference_eq_canonical : reference x o ho = canonicalReference (S x o ho) := by
  have hS : 1 < (S x o ho).card := upperNode_card 0 x o ho
  simp only [reference, canonicalReference, dif_pos hS, anchor_eq_canonical]

variable {m' : ℕ} (y : Compactification (0 : Fin (n+1)) m')
  (p : ForestRadialFaceClassification.Orbit 0 y) (hp : kind 0 y p = .paired)

/-- Identical intrinsic label sets force identical marked labels, including
the branch where the original fixed anchor lies inside the cluster. -/
theorem anchor_eq_of_labels_eq (h : S x o ho = S y p hp) : anchor x o ho = anchor y p hp := by
  rw [anchor_eq_canonical, anchor_eq_canonical, h]

theorem reference_eq_of_labels_eq (h : S x o ho = S y p hp) : reference x o ho = reference y p hp := by
  rw [reference_eq_canonical, reference_eq_canonical, h]

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCanonicalMarks
