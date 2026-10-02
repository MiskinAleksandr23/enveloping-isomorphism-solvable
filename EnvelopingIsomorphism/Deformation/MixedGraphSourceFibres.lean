import EnvelopingIsomorphism.Deformation.GeneralGraphVertexSplitFibres
import EnvelopingIsomorphism.Deformation.MixedGraphSourceProfiles

/-! Exact weighted fibres of the three actual mixed source split templates.
These retain the signed forward-minus-backward-plus-backward convention. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
namespace EnvelopingIsomorphism.Deformation.MixedGraphActionSplits
open scoped BigOperators Classical
open KontsevichGraph.General KontsevichGraph.General.TwoVertexContraction
open MixedGraphProfileCarrier UniformBinaryGraphs SchoutenGraphContraction
open GraphCoefficientProfiles
variable {n : ℕ}

abbrev SourceSplitData (i : Fin (n + 1)) :=
  Graph.VertexSplitData (fun _ : Fin (n + 1) => 2) 2 i

def forwardDataGraph (i : Fin (n + 1)) (D : SourceSplitData i) : VectorGraph (n + 1) 2 :=
  splitForward D.1 i D.2

def backwardDataGraph (i : Fin (n + 1)) (ρ : Equiv.Perm (Fin 2))
    (D : SourceSplitData i) : VectorGraph (n + 1) 2 := splitBackward D.1 i ρ D.2

private theorem ofProfile_injective {q : Fin (n + 1) → ℕ} {m : ℕ} (i : Fin (n + 1))
    (h : q = Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i) :
    Function.Injective (ofProfile (m := m) i h) := by
  subst q
  intro Γ Δ he
  exact (Sigma.mk.inj he).2.eq

theorem forwardDataGraph_injective (i : Fin (n + 1)) :
    Function.Injective (forwardDataGraph i) := by
  intro D E h
  apply Graph.vertexSplitDataGraph_injective vectorBivectorForward vectorBivectorForwardLeg
    (fun _ => rfl) i rfl
  exact ofProfile_injective _ (actionSplitArity i) h

theorem backwardDataGraph_injective (i : Fin (n + 1)) (ρ : Equiv.Perm (Fin 2)) :
    Function.Injective (backwardDataGraph i ρ) := by
  intro D E h
  have hleg (j : Fin 2) : (vectorBivectorBackward ρ).target (vectorBivectorBackwardLeg ρ j) =
      Sum.inr j := by
    obtain ⟨j, rfl⟩ := ρ.surjective j
    fin_cases j <;> simp [vectorBivectorBackwardLeg, vectorBivectorBackward]
  apply Graph.vertexSplitDataGraph_injective (vectorBivectorBackward ρ)
    (vectorBivectorBackwardLeg ρ) hleg i rfl
  exact ofProfile_injective _ (actionSplitArity i) h

variable {k : Type*} [Field k]

def forwardTemplateProfile (i : Fin (n + 1)) (w : BinaryGraph (n + 1) 2 → k) :
    VectorGraph (n + 1) 2 → k := pushforward (forwardDataGraph i) (fun D => w D.1)

def backwardTemplateProfile (i : Fin (n + 1)) (ρ : Equiv.Perm (Fin 2))
    (w : BinaryGraph (n + 1) 2 → k) : VectorGraph (n + 1) 2 → k :=
  pushforward (backwardDataGraph i ρ) (fun D => w D.1)

private theorem pushforward_at_injective {I A : Type*} [Fintype I]
    (f : I → A) (hf : Function.Injective f) (w : I → k) (i : I) :
    pushforward f w (f i) = w i := by
  simp only [pushforward, hf.eq_iff]
  simp

/-- Each forward boundary graph contributes exactly its recovered quotient weight. -/
theorem forwardTemplateProfile_split (i : Fin (n + 1)) (w : BinaryGraph (n + 1) 2 → k)
    (Θ : BinaryGraph (n + 1) 2) (χ : SplitChoices Θ i) :
    forwardTemplateProfile i w (splitForward Θ i χ) = w Θ :=
  pushforward_at_injective _ (forwardDataGraph_injective i) _ ⟨Θ, χ⟩

/-- Each backward leg order likewise has true fibre multiplicity one. -/
theorem backwardTemplateProfile_split (i : Fin (n + 1)) (ρ : Equiv.Perm (Fin 2))
    (w : BinaryGraph (n + 1) 2 → k) (Θ : BinaryGraph (n + 1) 2) (χ : SplitChoices Θ i) :
    backwardTemplateProfile i ρ w (splitBackward Θ i ρ χ) = w Θ :=
  pushforward_at_injective _ (backwardDataGraph_injective i ρ) _ ⟨Θ, χ⟩

/-- The original source scalar table is exactly the signed sum of these
reconstructed template fibres, with every original binary vertex retained. -/
theorem sourceActionProfile_eq_templateProfiles (w : BinaryGraph (n + 1) 2 → k) :
    sourceActionProfile w = ∑ i : Fin (n + 1),
      (forwardTemplateProfile i w - backwardTemplateProfile i 1 w +
        backwardTemplateProfile i (Equiv.swap 0 1) w) := by
  rw [sourceActionProfile, Finset.sum_comm]
  funext H
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul,
    actionSplitProfile, forwardTemplateProfile, backwardTemplateProfile, pushforward_apply,
    Fintype.sum_sigma, mul_add, mul_sub, Finset.mul_sum, mul_ite, mul_one, mul_zero,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, forwardDataGraph, backwardDataGraph]

end EnvelopingIsomorphism.Deformation.MixedGraphActionSplits
