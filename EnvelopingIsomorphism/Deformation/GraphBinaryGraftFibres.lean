import EnvelopingIsomorphism.Deformation.GraphGraftFibreCoefficients
import EnvelopingIsomorphism.Deformation.GraphWeightedInsertion

/-! Exact scalar bridge between the uniform binary grafts used in the
associator and the native extracted grafts used by boundary integration. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.GraphBinaryGraftFibres
open scoped BigOperators Classical
open KontsevichGraph.General UniformBinaryGraphs GraphWeightedInsertion
variable {a b n m : ℕ} {q q' : Fin n → ℕ}

/-- Transporting an arity equality loses no genuine graph data. -/
theorem castGraph_injective (h : q = q') :
    Function.Injective (castGraph (m := m) h) := by
  cases h
  exact Function.injective_id

/-- The uniform graft is an injective encoding of both factor graphs and every
incoming assignment, including zero-vertex factors. -/
theorem graftGraph_injective (r : Fin 2) :
    Function.Injective (graftGraph (a := a) (b := b) r) := by
  intro D E h
  exact Graph.graftDataGraph_injective r
    ((castGraph_injective graftArity_two) h)

variable {k : Type*} [CommRing k]

/-- This is the literal finite profile supplied by native real-face matching. -/
theorem graftProfile_eq_native (r : Fin 2)
    (w : BinaryGraph a 2 → k) (v : BinaryGraph b 2 → k)
    (H : Graph (graftArity (fun _ : Fin a ↦ 2) (fun _ : Fin b ↦ 2)) 3) :
    GraphWeightedInsertion.graftProfile r w v (castGraph graftArity_two H) =
      GraphGeneralWeightedGraft.graftProfile r w v H := by
  simp only [GraphWeightedInsertion.graftProfile, GraphGeneralWeightedGraft.graftProfile,
    GraphCoefficientProfiles.pushforward, graftGraph, uniformGraft,
    (castGraph_injective graftArity_two).eq_iff]

/-- All admissible graph fibres have multiplicity one and the actual extracted
weight product. No orientation or graph-weight invariance is assumed. -/
theorem graftProfile_eq_extractedProduct (r : Fin 2)
    (w : BinaryGraph a 2 → k) (v : BinaryGraph b 2 → k)
    (H : Graph (graftArity (fun _ : Fin a ↦ 2) (fun _ : Fin b ↦ 2)) 3)
    (hc : H.InnerClosed (l := 1) r) (hd : H.CoarseDistinct (l := 1) r) :
    GraphWeightedInsertion.graftProfile r w v (castGraph graftArity_two H) =
      w (H.extractedOuter (l := 1) r hd) * v (H.extractedInner (l := 1) r hc) := by
  rw [graftProfile_eq_native]
  exact GraphGeneralWeightedGraft.graftProfile_eq_extractedProduct r w v H hc hd

/-- Inadmissible native boundary graphs contribute zero to the literal
associator graft profile. -/
theorem graftProfile_eq_zero_of_not_admissible (r : Fin 2)
    (w : BinaryGraph a 2 → k) (v : BinaryGraph b 2 → k)
    (H : Graph (graftArity (fun _ : Fin a ↦ 2) (fun _ : Fin b ↦ 2)) 3)
    (hH : ¬ (H.InnerClosed (l := 1) r ∧ H.CoarseDistinct (l := 1) r)) :
    GraphWeightedInsertion.graftProfile r w v (castGraph graftArity_two H) = 0 := by
  rw [graftProfile_eq_native]
  exact GraphGeneralWeightedGraft.graftProfile_eq_zero_of_not_admissible r w v H hH

/-- The actual native graph before its uniform arity transport. -/
def nativeGraph (H : BinaryGraph (a + b) 3) :
    Graph (graftArity (fun _ : Fin a ↦ 2) (fun _ : Fin b ↦ 2)) 3 :=
  castGraph graftArity_two.symm H

theorem castGraph_nativeGraph (H : BinaryGraph (a + b) 3) :
    castGraph graftArity_two (nativeGraph H) = H := by
  have he {l m : ℕ} {p p' : Fin l → ℕ} (h : p = p') (G : Graph p' m) :
      castGraph h (castGraph h.symm G) = G := by
    cases h
    rfl
  exact he graftArity_two H

/-- A literal extracted product on each admissible boundary graph; the bad
quotients have no graft data and give zero. -/
def extractedCoefficient (r : Fin 2) (w : BinaryGraph a 2 → k) (v : BinaryGraph b 2 → k)
    (H : BinaryGraph (a + b) 3) : k :=
  if h : (nativeGraph H).InnerClosed (l := 1) r ∧ (nativeGraph H).CoarseDistinct (l := 1) r then
    w ((nativeGraph H).extractedOuter (l := 1) r h.2) *
      v ((nativeGraph H).extractedInner (l := 1) r h.1)
  else 0

theorem graftProfile_eq_extractedCoefficient (r : Fin 2)
    (w : BinaryGraph a 2 → k) (v : BinaryGraph b 2 → k)
    (H : BinaryGraph (a + b) 3) :
    GraphWeightedInsertion.graftProfile r w v H = extractedCoefficient r w v H := by
  unfold extractedCoefficient
  split_ifs with h
  · have he := graftProfile_eq_extractedProduct r w v (nativeGraph H) h.1 h.2
    rwa [castGraph_nativeGraph] at he
  · have he := graftProfile_eq_zero_of_not_admissible r w v (nativeGraph H) h
    rwa [castGraph_nativeGraph] at he

end EnvelopingIsomorphism.Deformation.GraphBinaryGraftFibres
