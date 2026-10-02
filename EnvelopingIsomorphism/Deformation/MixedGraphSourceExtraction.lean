import EnvelopingIsomorphism.Deformation.GeneralGraphVertexSplitExtraction
import EnvelopingIsomorphism.Deformation.MixedGraphActionSplits

/-! Actual extraction of the mixed vector/bivector two-child source boundary.
The quotient graph and every incoming assignment are read from the original
expanded graph; the local three-edge template is identified explicitly. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
namespace EnvelopingIsomorphism.Deformation.MixedGraphActionSplits
open scoped Classical
open KontsevichGraph.General KontsevichGraph.General.TwoVertexContraction
open MixedGraphProfileCarrier UniformBinaryGraphs SchoutenGraphContraction
variable {n : ℕ}
variable (i : Fin (n + 1))
variable (H : Graph (vertexSplitArity (fun _ : Fin (n + 1) => 2) vectorBivectorArity i) 2)

abbrev forwardInternal : Prop :=
  H.target (vertexSplitLocalEdge (fun _ : Fin (n + 1) => 2) vectorBivectorArity i ⟨0, 0⟩) =
    Sum.inl (vertexSplitChild i 1)

abbrev backwardInternal : Prop :=
  H.target (vertexSplitLocalEdge (fun _ : Fin (n + 1) => 2) vectorBivectorArity i ⟨1, 0⟩) =
    Sum.inl (vertexSplitChild i 0)

/-- The two bivector edges exhaust the exiting legs when the vector arrow is internal. -/
theorem forwardLegsComplete (hi : forwardInternal i H) :
    H.SplitLegsComplete i vectorBivectorForwardLeg := by
  rintro ⟨v, j⟩ he
  fin_cases v
  · fin_cases j
    exact (he (hi ▸ vertexSplitCollapseVertex_child i 1)).elim
  · exact ⟨j, rfl⟩

/-- With the first bivector arrow internal, the vector arrow and remaining
bivector arrow are exactly the two quotient slots, in the specified order. -/
theorem backwardLegsComplete (ρ : Equiv.Perm (Fin 2)) (hi : backwardInternal i H) :
    H.SplitLegsComplete i (vectorBivectorBackwardLeg ρ) := by
  rintro ⟨v, j⟩ he
  fin_cases v
  · fin_cases j
    refine ⟨ρ 0, ?_⟩
    simp [vectorBivectorBackwardLeg]
  · fin_cases j
    · exact (he (hi ▸ vertexSplitCollapseVertex_child i 0)).elim
    · refine ⟨ρ 1, ?_⟩
      simp [vectorBivectorBackwardLeg]

variable (hd : H.SplitCoarseDistinct i)
include hd

theorem contractedTemplate_forward (hi : forwardInternal i H)
    (ho : H.SplitLegsOutside i vectorBivectorForwardLeg)
    (hl : H.SplitLegsDistinct i vectorBivectorForwardLeg) :
    H.contractedTemplate i rfl vectorBivectorForwardLeg hd ho hl
      (forwardLegsComplete i H hi) = vectorBivectorForward := by
  apply Graph.ext
  funext e
  rcases e with ⟨v, j⟩
  fin_cases v
  · fin_cases j
    exact H.contractedTemplate_target_child i rfl vectorBivectorForwardLeg hd ho hl
      (forwardLegsComplete i H hi) ⟨0, 0⟩ 1 hi
  · exact H.contractedTemplate_target_leg i rfl vectorBivectorForwardLeg hd ho hl
      (forwardLegsComplete i H hi) j

theorem contractedTemplate_backward (ρ : Equiv.Perm (Fin 2)) (hi : backwardInternal i H)
    (ho : H.SplitLegsOutside i (vectorBivectorBackwardLeg ρ))
    (hl : H.SplitLegsDistinct i (vectorBivectorBackwardLeg ρ)) :
    H.contractedTemplate i rfl (vectorBivectorBackwardLeg ρ) hd ho hl
      (backwardLegsComplete i H ρ hi) = vectorBivectorBackward ρ := by
  apply Graph.ext
  funext e
  rcases e with ⟨v, j⟩
  fin_cases v
  · fin_cases j
    simpa [vectorBivectorBackwardLeg, vectorBivectorBackward] using
      H.contractedTemplate_target_leg i rfl (vectorBivectorBackwardLeg ρ) hd ho hl
        (backwardLegsComplete i H ρ hi) (ρ 0)
  · fin_cases j
    · exact H.contractedTemplate_target_child i rfl (vectorBivectorBackwardLeg ρ) hd ho hl
        (backwardLegsComplete i H ρ hi) ⟨1, 0⟩ 0 hi
    · simpa [vectorBivectorBackwardLeg, vectorBivectorBackward] using
        H.contractedTemplate_target_leg i rfl (vectorBivectorBackwardLeg ρ) hd ho hl
          (backwardLegsComplete i H ρ hi) (ρ 1)

/-- Actual admissible forward faces occur in the source profile's graph fibre. -/
theorem exists_splitForward_eq (hi : forwardInternal i H)
    (ho : H.SplitLegsOutside i vectorBivectorForwardLeg)
    (hl : H.SplitLegsDistinct i vectorBivectorForwardLeg) :
    ∃ (Θ : BinaryGraph (n + 1) 2) (χ : SplitChoices Θ i),
      splitForward Θ i χ = ofProfile (vertexSplitChild i 0) (actionSplitArity i) H := by
  refine ⟨H.contractedGraph i rfl vectorBivectorForwardLeg hd ho hl,
    H.contractedChoices i rfl vectorBivectorForwardLeg hd ho hl, ?_⟩
  have he := H.vertexSplit_contracted i rfl vectorBivectorForwardLeg hd ho hl
    (forwardLegsComplete i H hi)
  rw [contractedTemplate_forward i H hd hi ho hl] at he
  exact congrArg (ofProfile (vertexSplitChild i 0) (actionSplitArity i)) he

/-- Both signed backward source terms contain their actual contracted faces. -/
theorem exists_splitBackward_eq (ρ : Equiv.Perm (Fin 2)) (hi : backwardInternal i H)
    (ho : H.SplitLegsOutside i (vectorBivectorBackwardLeg ρ))
    (hl : H.SplitLegsDistinct i (vectorBivectorBackwardLeg ρ)) :
    ∃ (Θ : BinaryGraph (n + 1) 2) (χ : SplitChoices Θ i),
      splitBackward Θ i ρ χ = ofProfile (vertexSplitChild i 0) (actionSplitArity i) H := by
  refine ⟨H.contractedGraph i rfl (vectorBivectorBackwardLeg ρ) hd ho hl,
    H.contractedChoices i rfl (vectorBivectorBackwardLeg ρ) hd ho hl, ?_⟩
  have he := H.vertexSplit_contracted i rfl (vectorBivectorBackwardLeg ρ) hd ho hl
    (backwardLegsComplete i H ρ hi)
  rw [contractedTemplate_backward i H hd ρ hi ho hl] at he
  exact congrArg (ofProfile (vertexSplitChild i 0) (actionSplitArity i)) he

end EnvelopingIsomorphism.Deformation.MixedGraphActionSplits
