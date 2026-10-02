import EnvelopingIsomorphism.Deformation.Gauge.PlacedMixedGraphTaylorCoefficients
import EnvelopingIsomorphism.Deformation.Gauge.GraphFirstCoefficient

/-! Actual first unary coefficient for the all-distinguished-position graph family.
The unique graph and its canonical integral are computed in this family's own graph type.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge.PlacedMixedFirstCoefficient

open MvPolynomial KontsevichGraph.General Kontsevich.GeometricWeights
open PlacedMixedGraphTaylorCoefficients
open scoped BigOperators

variable {k : Type*} [CommRing k] {d : ℕ}

abbrev G := PlacedMixedGraphTaylorCoefficients.Graph 1 (0 : Fin 1)

def graph : G where
  target _ := Sum.inr 0
  noLoops := by intros; simp
  distinctTargets v := by
    rw [Fin.eq_zero v]
    intro a b _
    exact @Subsingleton.elim (Fin 1) inferInstance a b

theorem edge_eq (e : Edge (arities 1 (0 : Fin 1))) : e = ⟨0, (0 : Fin 1)⟩ := by
  rcases e with ⟨v, a⟩
  rcases Fin.eq_zero v with rfl
  have ha : a = (0 : Fin 1) := Fin.eq_zero a
  subst a
  rfl

theorem graph_unique (Γ : G) : Γ = graph := by
  apply Graph.ext
  funext e
  rw [edge_eq e]
  have hn := Γ.noLoops 0 (0 : Fin 1)
  rcases ht : Γ.target ⟨0, (0 : Fin 1)⟩ with v | j
  · exact (hn (by rw [ht, Fin.eq_zero v])).elim
  · rw [Fin.eq_zero j]
    rfl

@[simp] theorem incoming_internal (v : Fin 1) : graph.incoming (Sum.inl v) = ∅ := by
  classical
  ext e
  simp [Graph.incoming, graph]

@[simp] theorem incoming_external (j : Fin 1) : graph.incoming (Sum.inr j) = {⟨0, (0 : Fin 1)⟩} := by
  classical
  ext e
  rw [edge_eq e, Fin.eq_zero j]
  simp [Graph.incoming, graph]

def labelEquiv (d : ℕ) : (Edge (arities 1 (0 : Fin 1)) → Fin d) ≃ Fin d where
  toFun lab := lab ⟨0, (0 : Fin 1)⟩
  invFun i _ := i
  left_inv lab := by funext e; rw [edge_eq e]
  right_inv _ := rfl

theorem graphCoefficient_apply (D : Multiderivation k (MvPolynomial (Fin d) k) 1)
    (f : Fin 1 → MvPolynomial (Fin d) k) :
    graphCoefficient 0 graph Fin.elim0 D f =
      ∑ i : Fin d, D (fun _ ↦ X i) * pderiv i (f 0) := by
  classical
  letI : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
  have hempty : (Fin.elim0 : Fin 0 → Multiderivation k (MvPolynomial (Fin d) k) 2) = fun _ ↦ 0 :=
    Subsingleton.elim _ _
  rw [hempty, graphCoefficient_diagonal, Graph.cochainOperator_apply]
  simp only [Graph.vertexDerivative, incoming_internal, incoming_external,
    Finset.toList_empty, List.map_nil, iteratedPDeriv, LinearMap.id_apply,
    Fin.prod_univ_one, Finset.toList_singleton, List.map_singleton,
    LinearMap.coe_comp, Function.comp_apply]
  apply Fintype.sum_equiv (labelEquiv d)
  intro lab
  congr 1
  rw [Fintype.prod_unique]
  change D (fun i : Fin 1 ↦ X (lab ⟨0, i⟩)) = D (fun _ ↦ X (lab ⟨0, (0 : Fin 1)⟩))
  congr 1
  funext i
  rw [Fin.eq_zero i]

theorem graphCoefficient_eq_raw (D : Multiderivation k (MvPolynomial (Fin d) k) 1) :
    graphCoefficient 0 graph Fin.elim0 D = D.val.toMultilinearMap := by
  classical
  apply MultilinearMap.ext
  intro f
  rw [graphCoefficient_apply]
  change (∑ i : Fin d, D (fun _ ↦ X i) * pderiv i (f 0)) = D f
  rw [Multiderivation.apply_coordinate_expansion 1 D f]
  apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin d)).symm
  intro i
  simp only [Fin.prod_univ_one]
  rfl

theorem orderedEdges_eq_canonical
    (order : Fin (Kontsevich.GraphForms.dimension 0 1) ≃ Edge (arities 1 (0 : Fin 1))) :
    orderedEdges graph order = canonicalOneVertexEdges 1 := by
  funext a
  simp only [orderedEdges, graph, canonicalOneVertexEdges]
  rw [Fin.eq_zero (order a).1, Fin.eq_zero ((zeroIndex 1).symm a)]

theorem canonicalWeight_eq_one (Γ : G) : canonicalWeight Γ (edgeCount 1 0) = 1 := by
  rw [graph_unique Γ, canonicalWeight, geometricWeight, orderedEdges_eq_canonical,
    rawIntegral_canonical_oneVertex ⟨1, by decide⟩]
  change (∏ v : Fin 1, ((arities 1 (0 : Fin 1) v).factorial : ℝ)⁻¹) *
    ((2 * Real.pi) ^ Kontsevich.GraphForms.dimension 0 1)⁻¹ * Kontsevich.oneVertexRawIntegral 1 = 1
  rw [Fin.prod_univ_one, Kontsevich.oneVertexRawIntegral_one]
  simp [arities, Kontsevich.GraphForms.dimension]
  field_simp [Real.pi_ne_zero]

@[simp] theorem canonicalEffectiveWeight_eq_one (Γ : G) :
    canonicalEffectiveWeight Γ (edgeCount 1 0) = 1 := by
  rw [canonicalEffectiveWeight, Kontsevich.effectiveMCWeight_one, canonicalWeight_eq_one]

section Canonical

variable {K : Type*} [Field K] [Algebra ℝ K]

/-- The actual all-position family has the raw unary coefficient at zero bivector inputs. -/
theorem canonicalFamily_zero
    (s : (n : ℕ) → (i : Fin (n + 1)) → Finset (PlacedMixedGraphTaylorCoefficients.Graph 1 i))
    (hs : s 0 0 = Finset.univ) (D : Multiderivation K (MvPolynomial (Fin d) K) 1) :
    canonicalFamily s 0 Fin.elim0 D = D.val.toMultilinearMap := by
  classical
  letI : Unique G := ⟨⟨graph⟩, graph_unique⟩
  rw [canonicalFamily_apply, Fin.sum_univ_one, hs, Fintype.sum_unique]
  rw [show (default : G) = graph from rfl, canonicalEffectiveWeight_eq_one, map_one, one_smul]
  exact graphCoefficient_eq_raw D

/-- Converting the actual raw coefficient gives the native derivation linear map. -/
theorem canonicalFamily_zero_cochainOne
    (s : (n : ℕ) → (i : Fin (n + 1)) → Finset (PlacedMixedGraphTaylorCoefficients.Graph 1 i))
    (hs : s 0 0 = Finset.univ) (D : Multiderivation K (MvPolynomial (Fin d) K) 1) :
    cochainOneEquiv K (MvPolynomial (Fin d) K) (canonicalFamily s 0 Fin.elim0 D) =
      (Multiderivation.oneEquiv D).toLinearMap := by
  rw [canonicalFamily_zero s hs]
  exact GraphFirstCoefficient.Velocity.cochainOne_raw D

theorem mapOutput_canonicalFamily_zero
    (s : (n : ℕ) → (i : Fin (n + 1)) → Finset (PlacedMixedGraphTaylorCoefficients.Graph 1 i))
    (hs : s 0 0 = Finset.univ) (D : Multiderivation K (MvPolynomial (Fin d) K) 1) :
    mapOutput (cochainOneEquiv K (MvPolynomial (Fin d) K)).toLinearMap
      (canonicalFamily s) 0 Fin.elim0 D = (Multiderivation.oneEquiv D).toLinearMap :=
  canonicalFamily_zero_cochainOne s hs D

/-- The h-zero coefficient of the actual all-position base operator is the native vector field. -/
theorem baseOperatorSeries_zero
    (s : (n : ℕ) → (i : Fin (n + 1)) → Finset (PlacedMixedGraphTaylorCoefficients.Graph 1 i))
    (hs : s 0 0 = Finset.univ) (π₀ : Multiderivation K (MvPolynomial (Fin d) K) 2)
    (D : Multiderivation K (MvPolynomial (Fin d) K) 1) :
    FormalSeries.PowerSeriesModule.coeffV 0
      (MixedGraphTaylorCoefficients.baseOperatorSeries
        (mapOutput (cochainOneEquiv K (MvPolynomial (Fin d) K)).toLinearMap
          (canonicalFamily s)) π₀) D = (Multiderivation.oneEquiv D).toLinearMap := by
  change mapOutput (cochainOneEquiv K (MvPolynomial (Fin d) K)).toLinearMap
    (canonicalFamily s) 0 (fun _ ↦ π₀) D = _
  have hempty : (fun _ : Fin 0 ↦ π₀) = Fin.elim0 := Subsingleton.elim _ _
  rw [hempty]
  exact mapOutput_canonicalFamily_zero s hs D

end Canonical

end EnvelopingIsomorphism.Deformation.Gauge.PlacedMixedFirstCoefficient
