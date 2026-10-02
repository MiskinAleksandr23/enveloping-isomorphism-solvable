import EnvelopingIsomorphism.Deformation.GeneralGraphGraftExtraction
import EnvelopingIsomorphism.Deformation.GeneralGraphMixedProfiles

/-! Actual graph pullback under explicit internal and external finite label
equivalences, and its specialization to the outer/inner graft label order. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General
open scoped Classical

variable {n N m M : ℕ} {q : Fin n → ℕ}

def reindexEdgeEquiv (q : Fin n → ℕ) (e : Fin N ≃ Fin n) :
    Edge (fun v ↦ q (e v)) ≃ Edge q :=
  Equiv.sigmaCongrLeft (β := fun v ↦ Fin (q v)) e

@[simp] theorem reindexEdgeEquiv_apply (e : Fin N ≃ Fin n)
    (v : Fin N) (j : Fin (q (e v))) : reindexEdgeEquiv q e ⟨v, j⟩ = ⟨e v, j⟩ := rfl

namespace Graph

/-- Pull back the original graph by actual finite label bijections. Ordered
outgoing slots are unchanged; external ordering is encoded by the supplied eB. -/
def reindex (Γ : Graph q m) (e : Fin N ≃ Fin n) (eB : Fin M ≃ Fin m) :
    Graph (fun v ↦ q (e v)) M where
  target f := (Equiv.sumCongr e.symm eB.symm) (Γ.target (reindexEdgeEquiv q e f))
  noLoops v j h := by
    have hh := congrArg (Equiv.sumCongr e eB) h
    have ht : Γ.target ⟨e v, j⟩ = Sum.inl (e v) := by simpa using hh
    exact Γ.noLoops (e v) j ht
  distinctTargets v j t h := by
    apply Γ.distinctTargets (e v)
    have hh := (Equiv.sumCongr e.symm eB.symm).injective h
    exact hh

@[simp] theorem reindex_target (Γ : Graph q m) (e : Fin N ≃ Fin n) (eB : Fin M ≃ Fin m)
    (f : Edge (fun v ↦ q (e v))) :
    (Γ.reindex e eB).target f =
      (Equiv.sumCongr e.symm eB.symm) (Γ.target (reindexEdgeEquiv q e f)) := rfl

theorem reindex_injective (e : Fin N ≃ Fin n) (eB : Fin M ≃ Fin m) :
    Function.Injective (fun Γ : Graph q m ↦ Γ.reindex e eB) := by
  intro Γ Δ he
  apply Graph.ext
  funext f
  apply (Equiv.sumCongr e.symm eB.symm).injective
  have h := congrArg (fun G : Graph (fun v ↦ q (e v)) M ↦
    G.target ((reindexEdgeEquiv q e).symm f)) he
  simpa only [reindex_target, Equiv.apply_symm_apply] using h

theorem castProfileEquiv_target {q' : Fin n → ℕ} (h : q = q') (Γ : Graph q m)
    (v : Fin n) (j : Fin (q' v)) :
    (castProfileEquiv h m Γ).target ⟨v, j⟩ =
      Γ.target ⟨v, Fin.cast (congrFun h v).symm j⟩ := by
  cases h
  rfl

end Graph

variable {a b : ℕ}

def pulledOuterArity (q : Fin n → ℕ) (e : Fin (a + b) ≃ Fin n) : Fin a → ℕ :=
  fun v ↦ q (e (Fin.castAdd b v))

def pulledInnerArity (q : Fin n → ℕ) (e : Fin (a + b) ≃ Fin n) : Fin b → ℕ :=
  fun v ↦ q (e (Fin.natAdd a v))

theorem graftArity_pulled (q : Fin n → ℕ) (e : Fin (a + b) ≃ Fin n) :
    graftArity (pulledOuterArity q e) (pulledInnerArity q e) = fun v ↦ q (e v) := by
  funext v
  refine Fin.addCases (fun v ↦ ?_) (fun v ↦ ?_) v <;> simp [pulledOuterArity, pulledInnerArity]

namespace Graph
variable {o l : ℕ}

/-- The original graph in the exact concatenated arity profile required by
the graft constructor. Both reindexing equivalences remain explicit. -/
def reindexForGraft (Γ : Graph q m) (e : Fin (a + b) ≃ Fin n)
    (eB : Fin (o + l + 1) ≃ Fin m) :
    Graph (graftArity (pulledOuterArity q e) (pulledInnerArity q e)) (o + l + 1) :=
  castProfileEquiv (graftArity_pulled q e).symm _ (Γ.reindex e eB)

theorem reindexForGraft_injective (e : Fin (a + b) ≃ Fin n)
    (eB : Fin (o + l + 1) ≃ Fin m) :
    Function.Injective (fun Γ : Graph q m ↦ Γ.reindexForGraft e eB) :=
  (castProfileEquiv (graftArity_pulled q e).symm _).injective.comp (reindex_injective e eB)

theorem reindexForGraft_target_outer (Γ : Graph q m) (e : Fin (a + b) ≃ Fin n)
    (eB : Fin (o + l + 1) ≃ Fin m) (v : Fin a) (j : Fin (pulledOuterArity q e v)) :
    (Γ.reindexForGraft e eB).target
        (graftOuterEdge (pulledOuterArity q e) (pulledInnerArity q e) ⟨v, j⟩) =
      (Equiv.sumCongr e.symm eB.symm) (Γ.target ⟨e (Fin.castAdd b v), j⟩) := by
  rw [graftOuterEdge_mk, reindexForGraft, castProfileEquiv_target, reindex_target, reindexEdgeEquiv_apply]
  apply congrArg (Equiv.sumCongr e.symm eB.symm)
  apply congrArg Γ.target
  apply Sigma.ext rfl
  apply heq_of_eq
  apply Fin.ext
  rfl

theorem reindexForGraft_target_inner (Γ : Graph q m) (e : Fin (a + b) ≃ Fin n)
    (eB : Fin (o + l + 1) ≃ Fin m) (v : Fin b) (j : Fin (pulledInnerArity q e v)) :
    (Γ.reindexForGraft e eB).target
        (graftInnerEdge (pulledOuterArity q e) (pulledInnerArity q e) ⟨v, j⟩) =
      (Equiv.sumCongr e.symm eB.symm) (Γ.target ⟨e (Fin.natAdd a v), j⟩) := by
  rw [graftInnerEdge_mk, reindexForGraft, castProfileEquiv_target, reindex_target, reindexEdgeEquiv_apply]
  apply congrArg (Equiv.sumCongr e.symm eB.symm)
  apply congrArg Γ.target
  apply Sigma.ext rfl
  apply heq_of_eq
  apply Fin.ext
  rfl

/-- Reconstruction of the explicitly relabelled original graph. Geometry
supplies the physical cluster equivalences and derives the two admissibility
properties by actual face nonvanishing. -/
theorem reindexed_graph_eq_extracted_graft (Γ : Graph q m) (e : Fin (a + b) ≃ Fin n)
    (eB : Fin (o + l + 1) ≃ Fin m) (r : Fin (o + 1))
    (hc : (Γ.reindexForGraft e eB).InnerClosed r)
    (hd : (Γ.reindexForGraft e eB).CoarseDistinct r) :
    Γ.reindexForGraft e eB =
      ((Γ.reindexForGraft e eB).extractedOuter r hd).graft
        ((Γ.reindexForGraft e eB).extractedInner r hc) r
        ((Γ.reindexForGraft e eB).extractedChoices r hd) :=
  ((Γ.reindexForGraft e eB).graft_extracted r hc hd).symm

end Graph
end EnvelopingIsomorphism.Deformation.KontsevichGraph.General
