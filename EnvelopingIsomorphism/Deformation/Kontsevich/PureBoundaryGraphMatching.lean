import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryGraphDomain

/-! The two-point pure-external face, including its actual outgoing factorials,
matched to the geometric weight of the literal collapsed quotient graph. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryGraphMatching
open scoped Classical BigOperators
open PureBoundaryGraphQuotient PureBoundaryGraphIntegral BoundaryGraphFaceFactorization
variable {n m : ℕ} {l u : Fin (m + 1)} {q : Fin (n+1) → ℕ}
variable (hlu : l ≤ u) (Γ : KontsevichGraph.General.Graph q m)

def quotientTarget (e : KontsevichGraph.General.Edge q) :
    KontsevichGraph.General.Vertex (n+1) (outsideM l u + 1) :=
  Sum.map id (collapsedBoundary hlu) (Γ.target e)

def QuotientDistinct : Prop := ∀ v, Function.Injective (fun j ↦ quotientTarget hlu Γ ⟨v,j⟩)

def quotientGraph (hd : QuotientDistinct hlu Γ) :
    KontsevichGraph.General.Graph q (outsideM l u + 1) where
  target := quotientTarget hlu Γ
  noLoops v j := by
    intro h
    apply Γ.noLoops v j
    cases he : Γ.target ⟨v,j⟩ with
    | inl w => simpa [quotientTarget, he] using h
    | inr w => simp [quotientTarget, he] at h
  distinctTargets := hd

def originalEdges
    (order : Fin (Degree (n := n) (l := l) (u := u)) ≃ KontsevichGraph.General.Edge q)
    (j : Fin (Degree (n := n) (l := l) (u := u))) : GraphForms.Edge n m :=
  ⟨(order j).1, Γ.target (order j)⟩

theorem quotientEdges_eq_orderedEdges
    (order : Fin (Degree (n := n) (l := l) (u := u)) ≃ KontsevichGraph.General.Edge q)
    (hd : QuotientDistinct hlu Γ) :
    (fun j ↦ quotientEdge hlu (originalEdges Γ order j)) =
      GeometricWeights.orderedEdges (quotientGraph hlu Γ hd) order := rfl

/-- Failure of quotient admissibility kills the actual quotient density by
repeated outgoing edge rows. -/
theorem quotientDensity_eq_zero_of_not_distinct
    (order : Fin (Degree (n := n) (l := l) (u := u)) ≃ KontsevichGraph.General.Edge q)
    (hd : ¬ QuotientDistinct hlu Γ) :
    GeometricWeights.realDensity (fun j ↦ quotientEdge hlu (originalEdges Γ order j)) = 0 := by
  obtain ⟨v, j, k, he, hjk⟩ : ∃ v, ∃ j k : Fin (q v),
      quotientTarget hlu Γ ⟨v,j⟩ = quotientTarget hlu Γ ⟨v,k⟩ ∧ j ≠ k := by
    simpa only [QuotientDistinct, Function.Injective, not_forall, exists_prop] using hd
  apply GeometricWeights.realDensity_eq_zero_of_duplicate _ (order.symm ⟨v,j⟩) (order.symm ⟨v,k⟩)
  · intro h
    have h' := order.symm.injective h
    exact hjk (eq_of_heq (Sigma.mk.inj h').2)
  · simp only [originalEdges, Equiv.apply_symm_apply, quotientEdge]
    congr 1

theorem quotientDistinct_of_density_ne_zero
    (order : Fin (Degree (n := n) (l := l) (u := u)) ≃ KontsevichGraph.General.Edge q)
    (x : Fin (Degree (n := n) (l := l) (u := u)) → ℝ)
    (hne : GeometricWeights.realDensity (fun j ↦ quotientEdge hlu (originalEdges Γ order j)) x ≠ 0) :
    QuotientDistinct hlu Γ := by
  by_contra hd
  exact hne (congrFun (quotientDensity_eq_zero_of_not_distinct hlu Γ order hd) x)

variable (a b : Fin m)
    (ha : a ∈ boundaryClusterBlock l u) (hb : b ∈ boundaryClusterBlock l u)
    (hab : a ≠ b) (hcard : (boundaryClusterBlock l u).card = 2)

theorem normalized_outwardIntegral_eq_quotientWeight
    (order : Fin (Degree (n := n) (l := l) (u := u)) ≃ KontsevichGraph.General.Edge q)
    (hd : QuotientDistinct hlu Γ) :
    GeometricWeights.outgoingFactor q * ((2 * Real.pi) ^ Degree (n := n) (l := l) (u := u))⁻¹ *
      outwardIntegral hlu a b ha hb hab hcard (originalEdges Γ order) =
      -GeometricWeights.geometricWeight (quotientGraph hlu Γ hd) order := by
  rw [outwardIntegral_eq_quotient, quotientEdges_eq_orderedEdges hlu Γ order hd]
  simp only [GeometricWeights.geometricWeight, mul_neg]

theorem normalized_outwardIntegral_eq_quotientWeight_of_nonzero
    (order : Fin (Degree (n := n) (l := l) (u := u)) ≃ KontsevichGraph.General.Edge q)
    (x : Fin (Degree (n := n) (l := l) (u := u)) → ℝ)
    (hne : BoxStokes.facePullback (radialForm hlu a b ha hb hab hcard (originalEdges Γ order))
      0 0 x (BoxStokes.standardBasis _) ≠ 0) :
    let hd := quotientDistinct_of_density_ne_zero hlu Γ order x
      (by rwa [facePullback_radialForm] at hne)
    GeometricWeights.outgoingFactor q * ((2 * Real.pi) ^ Degree (n := n) (l := l) (u := u))⁻¹ *
      outwardIntegral hlu a b ha hb hab hcard (originalEdges Γ order) =
      -GeometricWeights.geometricWeight (quotientGraph hlu Γ hd) order := by
  exact normalized_outwardIntegral_eq_quotientWeight hlu Γ a b ha hb hab hcard order _

/-- With the same canonical vertex-major edge order on both sides, no row
permutation remains in the two-point pure-boundary contribution. -/
theorem normalized_outwardIntegral_eq_canonicalQuotientWeight
    (hq : ∑ v, q v = GraphForms.dimension n (outsideM l u + 1))
    (hd : QuotientDistinct hlu Γ) :
    GeometricWeights.outgoingFactor q * ((2 * Real.pi) ^ Degree (n := n) (l := l) (u := u))⁻¹ *
      outwardIntegral hlu a b ha hb hab hcard (originalEdges Γ (GeometricWeights.canonicalOrder hq)) =
      -GeometricWeights.canonicalWeight (quotientGraph hlu Γ hd) hq :=
  normalized_outwardIntegral_eq_quotientWeight hlu Γ a b ha hb hab hcard _ hd

end EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryGraphMatching
