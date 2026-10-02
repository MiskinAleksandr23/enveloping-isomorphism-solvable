import EnvelopingIsomorphism.Deformation.MixedScalarBoundaryAssembly
import EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeightRelabel
import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointFaceRelabelling
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCommonRealDensity

/-! Actual one-vector edge arrays and pair-face integrals under internal
labels. The one odd outgoing block produces no internal permutation sign. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedPairedEdgeRelabelling
open Kontsevich KontsevichGraph.General MixedGraphProfileCarrier MixedGraphAveraging
open MixedScalarBoundaryAssembly InteriorGraphFaceCoordinates
open scoped Classical BigOperators
variable {N : ℕ}

private def canonicalEdges {q : Fin (N+1) → ℕ} (G : Graph q 2)
    (hc : ∑ v, q v = GraphForms.dimension N 1) :
    Fin (GraphForms.dimension N 1) → GraphForms.Edge N 2 :=
  fun j => let e := GeometricWeights.canonicalOrder hc j; ⟨e.1,G.target e⟩

private theorem canonicalEdges_castProfile {q q' : Fin (N+1) → ℕ} (h : q = q')
    (G : Graph q 2) (hc : ∑ v, q v = GraphForms.dimension N 1)
    (hc' : ∑ v, q' v = GraphForms.dimension N 1) :
    canonicalEdges (Graph.castProfileEquiv h 2 G) hc' = canonicalEdges G hc := by
  subst q'
  rfl

def rows (H : VectorGraph N 2) (σ : Equiv.Perm (Fin (N+1))) :
    Equiv.Perm (Fin (GraphForms.dimension N 1)) :=
  GeometricWeights.canonicalProfileRows (Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 1 H.vertex) σ

theorem rows_sign (H : VectorGraph N 2) (σ : Equiv.Perm (Fin (N+1))) :
    (rows H σ).sign = 1 := by
  rw [rows, GeometricWeights.canonicalProfileRows_sign]
  apply profileRowPerm_sign_eq_one_of_even_off _ σ H.vertex
  intro v hv
  simp [Gauge.PlacedMixedGraphTaylorCoefficients.arities, hv]

theorem mixedEdges_internalGraphEquiv (H : VectorGraph N 2)
    (σ : Equiv.Perm (Fin (N+1))) :
    mixedEdges (internalGraphEquiv σ 2 H) =
      fun j => GeometricWeights.relabelEdge σ (mixedEdges H (rows H σ j)) := by
  change canonicalEdges
    (Graph.castProfileEquiv (profileArity_placed H.vertex σ) 2
      (H.graph.permuteProfile σ)) _ = _
  rw [canonicalEdges_castProfile (profileArity_placed H.vertex σ) (H.graph.permuteProfile σ)
    ((profileArity_sum _ σ).trans (Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 1 H.vertex))
    (Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 1 (σ H.vertex))]
  funext j
  have ho := congrArg (fun e => e j)
    (GeometricWeights.canonicalOrder_permuteProfile
      (Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 1 H.vertex) σ)
  unfold canonicalEdges
  rw [ho]
  change (⟨_, _⟩ : GraphForms.Edge N 2) = ⟨_, _⟩
  congr 1
  exact H.graph.permuteProfile_target σ _

variable {i a b : Fin (N+1)} {S : Finset (Fin (N+1))}
  (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hi : i ∈ S → a = i)

include ha hb hba hi in
theorem nativeDegree_eq : shapeDegree a b S + coarseDegree i a S 2 =
    GraphForms.dimension N 1 := by
  rw [totalDegree_eq ha hb hba hi]
  dsimp [GraphForms.dimension]
  omega

def nativeEdges (H : VectorGraph N 2) :
    Fin (shapeDegree a b S + coarseDegree i a S 2) → Edge (N+1) 2 :=
  fun j => let e := mixedEdges H (finCongr (nativeDegree_eq ha hb hba hi) j)
    (e.source,e.target)

theorem nativeEdges_noLoops (H : VectorGraph N 2)
    (j : Fin (shapeDegree a b S + coarseDegree i a S 2)) :
    (nativeEdges ha hb hba hi H j).2 ≠ Sum.inl (nativeEdges ha hb hba hi H j).1 :=
  mixedEdges_noLoops H _

def nativeRows (H : VectorGraph N 2) (σ : Equiv.Perm (Fin (N+1))) :
    Equiv.Perm (Fin (shapeDegree a b S + coarseDegree i a S 2)) :=
  (finCongr (nativeDegree_eq ha hb hba hi)).symm.permCongr (rows H σ)

theorem nativeRows_sign (H : VectorGraph N 2) (σ : Equiv.Perm (Fin (N+1))) :
    (nativeRows ha hb hba hi H σ).sign = 1 := by
  rw [nativeRows, Equiv.Perm.sign_permCongr, rows_sign]

variable (σ : Equiv.Perm (Fin (N+1))) {T : Finset (Fin (N+1))}
    (hST : ∀ j, σ j ∈ T ↔ j ∈ S)

include hi hST in
theorem anchor_relabel : σ i ∈ T → σ a = σ i := fun h => congrArg σ (hi ((hST i).mp h))

theorem nativeEdges_relabel (H : VectorGraph N 2) :
    nativeEdges ((hST a).mpr ha) ((hST b).mpr hb) (σ.injective.ne hba)
      (anchor_relabel hi σ hST) (internalGraphEquiv σ 2 H) =
    TwoPointFaceRelabelling.edges σ hST
      (fun j => nativeEdges ha hb hba hi H (nativeRows ha hb hba hi H σ j)) := by
  funext j
  unfold nativeEdges
  rw [mixedEdges_internalGraphEquiv]
  unfold TwoPointFaceRelabelling.edges InteriorFaceLabelRelabelling.relabelEdge
    nativeRows Equiv.permCongr
  dsimp only [Equiv.trans_apply]
  congr 2

include ha hb hba hi in
theorem integral_nativeEdges_relabel (H : VectorGraph N 2) (hS : S.card = 2) :
    TwoPointFaceRelabelling.integral
      (nativeEdges ((hST a).mpr ha) ((hST b).mpr hb) (σ.injective.ne hba)
        (anchor_relabel hi σ hST) (internalGraphEquiv σ 2 H)) =
      TwoPointFaceRelabelling.integral (nativeEdges ha hb hba hi H) := by
  rw [nativeEdges_relabel ha hb hba hi σ hST H,
    TwoPointFaceRelabelling.integral_edges σ hST _ ha hb hba hS
      (fun j => nativeEdges_noLoops ha hb hba hi H _),
    TwoPointFaceRelabelling.integral_permute, nativeRows_sign, Units.val_one, Int.cast_one, one_mul]

def normalization (H : VectorGraph N 2) : ℝ :=
  GeometricWeights.outgoingFactor (Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 H.vertex) *
    ((2 * Real.pi) ^ (GraphForms.dimension N 1))⁻¹

theorem normalization_relabel (H : VectorGraph N 2) (σ : Equiv.Perm (Fin (N+1))) :
    normalization (internalGraphEquiv σ 2 H) = normalization H := by
  unfold normalization
  rw [internalGraphEquiv_vertex, ← profileArity_placed H.vertex σ]
  rw [show profileArity (Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 H.vertex) σ =
    (fun v => Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 H.vertex (σ.symm v)) from rfl,
    GeometricWeights.outgoingFactor_relabel]

def normalized (H : VectorGraph N 2) : ℝ :=
  normalization H * TwoPointFaceRelabelling.integral (nativeEdges ha hb hba hi H)

include ha hb hba hi in
theorem normalized_relabel (H : VectorGraph N 2) (hS : S.card = 2) :
    normalized ((hST a).mpr ha) ((hST b).mpr hb) (σ.injective.ne hba)
      (anchor_relabel hi σ hST) (internalGraphEquiv σ 2 H) = normalized ha hb hba hi H := by
  unfold normalized
  rw [normalization_relabel, integral_nativeEdges_relabel ha hb hba hi σ hST H hS]

theorem nativeEdges_eq_common (H : VectorGraph N 2)
    {a b : Fin (N+1)} {S : Finset (Fin (N+1))}
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hi : (0 : Fin (N+1)) ∈ S → a = 0) :
    nativeEdges ha hb hba hi H =
      PairedForestCommonRealDensity.edges (mixed_dimension N) ha hb hba hi (mixedEdges H) := rfl

end EnvelopingIsomorphism.Deformation.MixedPairedEdgeRelabelling
