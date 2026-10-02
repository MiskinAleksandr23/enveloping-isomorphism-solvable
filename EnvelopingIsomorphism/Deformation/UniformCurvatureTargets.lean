import EnvelopingIsomorphism.Deformation.UniformCurvatureSplits

/-! Literal target formulas for uniform curvature splits in native binary slots. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.UniformCurvatureTargets
open KontsevichGraph.General KontsevichGraph.General.TwoVertexContraction
open UniformBinaryGraphs UniformCurvatureSplits
open scoped Classical
variable {n : ℕ} (i : Fin (n + 1))
abbrev Arity := Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i

theorem outsideArity (v : Fin (n + 1)) (hv : v ≠ i) : Arity i v = 2 := by
  simp [Arity, Gauge.PlacedMixedGraphTaylorCoefficients.arities, hv]

def uniformSplit (Γ : Gauge.PlacedMixedGraphTaylorCoefficients.Graph 3 i)
    (Θ : Graph bivectorArity 3) (χ : Γ.VertexSplitChoices i) : BinaryGraph (n + 2) 3 :=
  castGraph (vertexSplitArity_two i) (Γ.vertexSplit Θ i (selectedArity i).symm χ)

variable (Γ : Gauge.PlacedMixedGraphTaylorCoefficients.Graph 3 i)
    (Θ : Graph bivectorArity 3) (χ : Γ.VertexSplitChoices i)

theorem target_child (c s : Fin 2) :
    (uniformSplit i Γ Θ χ).target ⟨vertexSplitChild i c,s⟩ =
      Γ.vertexSplitTemplateVertex i (selectedArity i).symm (Θ.target ⟨c,s⟩) := by
  rw [uniformSplit, castGraph_target]
  have he : (⟨vertexSplitChild i c, Fin.cast (congrFun (vertexSplitArity_two i) _).symm s⟩ :
      Edge (vertexSplitArity (Arity i) bivectorArity i)) = vertexSplitLocalEdge (Arity i) bivectorArity i ⟨c,s⟩ := by
    apply Sigma.ext (vertexSplitLocalEdge_source (Arity i) bivectorArity i ⟨c,s⟩).symm
    apply heq_of_eq
    apply Fin.ext
    exact (vertexSplitLocalEdge_slot_val (Arity i) bivectorArity i ⟨c,s⟩).symm
  rw [he, Graph.vertexSplit_target_local]

theorem target_outside (v : Fin (n + 1)) (hv : v ≠ i) (s : Fin 2) :
    (uniformSplit i Γ Θ χ).target ⟨vertexSplitOldEmbedding i v,s⟩ =
      Γ.vertexSplitOutsideTarget i χ ⟨⟨v,Fin.cast (outsideArity i v hv).symm s⟩,hv⟩ := by
  rw [uniformSplit, castGraph_target]
  let e : VertexSplitOutsideEdge (Arity i) i := ⟨⟨v,Fin.cast (outsideArity i v hv).symm s⟩,hv⟩
  have he : (⟨vertexSplitOldEmbedding i v, Fin.cast (congrFun (vertexSplitArity_two i) _).symm s⟩ :
      Edge (vertexSplitArity (Arity i) bivectorArity i)) = vertexSplitOutsideEdge (Arity i) bivectorArity i e := by
    apply Sigma.ext (vertexSplitOutsideEdge_source (Arity i) bivectorArity i e).symm
    apply heq_of_eq
    apply Fin.ext
    exact (vertexSplitOutsideEdge_slot_val (Arity i) bivectorArity i e).symm
  rw [he, Graph.vertexSplit_target_outside]

end EnvelopingIsomorphism.Deformation.UniformCurvatureTargets
