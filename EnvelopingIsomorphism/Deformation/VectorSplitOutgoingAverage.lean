import EnvelopingIsomorphism.Deformation.VectorSplitOutgoingCovariance
import EnvelopingIsomorphism.Deformation.GeneralGraphOutgoingAverage
import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointTemplateAdmissibility

/-! The actual forward-minus-twice-backward source profile has normalized
split coefficients plus one and minus one. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.VectorSplitOutgoingAverage
open scoped Classical BigOperators
open KontsevichGraph.General KontsevichGraph.General.Graph
open KontsevichGraph.General.TwoVertexContraction
open SchoutenGraphContraction
open VectorSplitOutgoingCovariance GeneralGraphOutgoingAverage GraphCoefficientProfiles
open Kontsevich.MixedTwoPointTemplateWeight
variable {n m : ℕ} {q : Fin (n+1) → ℕ} (r : Fin (n+1)) (hq : q r = 2)

abbrev splitGraph (a : Fin 2) := vertexSplitDataGraph (template a) r hq (m := m)
abbrev SplitOutgoing := Group (vertexSplitArity q vectorBivectorArity r)

def profile (w : Graph q m → ℝ) (a : Fin 2) : Graph (vertexSplitArity q vectorBivectorArity r) m → ℝ :=
  pushforward (splitGraph r hq a) (fun D ↦ w D.1)

def pairProfile (w : Graph q m → ℝ) : Graph (vertexSplitArity q vectorBivectorArity r) m → ℝ :=
  profile r hq w 0 - (2 : ℝ) • profile r hq w 1

theorem splitGraph_injective (a : Fin 2) : Function.Injective (splitGraph r hq (m := m) a) := by
  fin_cases a
  · exact vertexSplitDataGraph_injective (Θ := vectorBivectorForward)
      (leg := vectorBivectorForwardLeg) (fun j ↦ (vectorForward_leg _ j).mpr rfl) r hq
  · exact vertexSplitDataGraph_injective (Θ := vectorBivectorBackward 1)
      (leg := vectorBivectorBackwardLeg 1) (fun j ↦ (vectorBackward_leg 1 _ j).mpr rfl) r hq

theorem profile_split (w : Graph q m → ℝ) (a : Fin 2) (D : VertexSplitData q m r) :
    profile r hq w a (splitGraph r hq a D) = w D.1 := by
  simp only [profile, pushforward, (splitGraph_injective r hq a).eq_iff]
  simp

theorem profile_outgoing (w : Graph q m → ℝ)
    (hw : ∀ Γ σ, w (Γ.permuteOutgoing σ) = sign σ * w Γ)
    (a : Fin 2) (τ : SplitOutgoing (q := q) r)
    (hτ : a ≠ 0 → childOutgoing r τ 1 = Equiv.refl _)
    (H : Graph (vertexSplitArity q vectorBivectorArity r) m) :
    profile r hq w a (H.permuteOutgoing τ) = sign τ * profile r hq w a H := by
  unfold profile pushforward
  rw [← Equiv.sum_comp (dataEquiv r hq τ a), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D _
  dsimp only [splitGraph]
  simp only [dataGraph_outgoing r hq τ a hτ]
  have hinj : Function.Injective
      (fun H : Graph (vertexSplitArity q vectorBivectorArity r) m ↦ H.permuteOutgoing τ) :=
    (Graph.outgoingGraphEquiv (vertexSplitArity q vectorBivectorArity r) m τ).injective
  rw [hinj.eq_iff]
  change (if _ then w (D.1.permuteOutgoing (quotientOutgoing r hq τ a)) else 0) = _
  rw [hw]
  have hs : sign (quotientOutgoing r hq τ a) = sign τ := quotientOutgoing_sign r hq τ a hτ
  rw [hs]
  split_ifs <;> simp

def internalEdge (a : Fin 2) : Edge vectorBivectorArity :=
  if a = 0 then ⟨0,0⟩ else ⟨1,0⟩

def receiver (a : Fin 2) : Fin 2 := if a = 0 then 1 else 0

theorem template_internal (a : Fin 2) :
    (template a).target (internalEdge a) = Sum.inl (receiver a) := by
  fin_cases a <;> rfl

theorem profile_zero (w : Graph q m → ℝ) (a : Fin 2)
    (H : Graph (vertexSplitArity q vectorBivectorArity r) m)
    (hH : H.target (vertexSplitLocalEdge q vectorBivectorArity r (internalEdge a)) ≠
      Sum.inl (vertexSplitChild r (receiver a))) : profile r hq w a H = 0 := by
  apply Finset.sum_eq_zero
  intro D _
  apply if_neg
  intro he
  apply hH
  rw [← he]
  change (D.1.vertexSplit (template a) r hq D.2).target _ = _
  rw [vertexSplit_target_local, template_internal]
  rfl

theorem profile_other_zero (w : Graph q m → ℝ) (a : Fin 2) (D : VertexSplitData q m r)
    (τ : SplitOutgoing (q := q) r) :
    profile r hq w (receiver a) ((splitGraph r hq a D).permuteOutgoing τ) = 0 := by
  apply profile_zero r hq w (receiver a)
  change (D.1.vertexSplit (template a) r hq D.2).target
    (outgoingEdgePerm τ (vertexSplitLocalEdge q vectorBivectorArity r (internalEdge (receiver a)))) ≠ _
  rw [outgoing_localEdge, outgoingEdgePerm_apply, vertexSplit_target_local]
  fin_cases a
  · change vertexSplitOldVertex r (D.1.target ⟨r, Fin.cast hq.symm (childOutgoing r τ 1 0)⟩) ≠
      Sum.inl (vertexSplitChild r 0)
    exact vertexSplitOldVertex_ne_child r _ (D.1.noLoops r _) _
  · have hh : childOutgoing r τ 0 0 = 0 := by
      exact @Subsingleton.elim (Fin 1) inferInstance _ _
    change D.1.vertexSplitTemplateVertex r hq
      ((vectorBivectorBackward 1).target ⟨0,childOutgoing r τ 0 0⟩) ≠ _
    rw [hh]
    exact vertexSplitOldVertex_ne_child r _ (D.1.noLoops r _) _

theorem profile_sender_swap_zero (w : Graph q m → ℝ) (D : VertexSplitData q m r)
    (τ : SplitOutgoing (q := q) r) (hτ : childOutgoing r τ 1 0 = 1) :
    profile r hq w 1 ((splitGraph r hq 1 D).permuteOutgoing τ) = 0 := by
  apply profile_zero r hq w 1
  change (D.1.vertexSplit (template 1) r hq D.2).target
    (outgoingEdgePerm τ (vertexSplitLocalEdge q vectorBivectorArity r ⟨1,0⟩)) ≠ _
  rw [outgoing_localEdge, outgoingEdgePerm_apply, hτ, vertexSplit_target_local]
  exact vertexSplitOldVertex_ne_child r _ (D.1.noLoops r _) _

theorem childOutgoing_refl_iff (τ : SplitOutgoing (q := q) r) :
    childOutgoing r τ 1 = Equiv.refl _ ↔ τ (vertexSplitChild r 1) = Equiv.refl _ := by
  unfold childOutgoing BinarySplitOutgoingCovariance.slotCast
  constructor
  · intro h
    apply Equiv.ext
    intro j
    have he := congrArg (fun e ↦ e (Fin.cast (vertexSplitArity_child q vectorBivectorArity r 1) j)) h
    apply Fin.ext
    simpa using congrArg Fin.val he
  · intro h
    rw [h]
    exact Equiv.ext (fun _ ↦ rfl)

theorem weighted_pairProfile_forward (w : Graph q m → ℝ)
    (hw : ∀ Γ σ, w (Γ.permuteOutgoing σ) = sign σ * w Γ)
    (D : VertexSplitData q m r) (τ : SplitOutgoing (q := q) r) :
    sign τ * pairProfile r hq w
      ((splitGraph r hq 0 D).permuteOutgoing (fun v ↦ (τ v).symm)) = w D.1 := by
  have hz := profile_other_zero r hq w 0 D (fun v ↦ (τ v).symm)
  change profile r hq w 1 _ = 0 at hz
  simp only [pairProfile, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hz, mul_zero, sub_zero]
  rw [profile_outgoing r hq w hw 0 _ (fun h ↦ (h rfl).elim), profile_split,
    sign_symm, ← mul_assoc, sign_sq, one_mul]

theorem weighted_pairProfile_backward (w : Graph q m → ℝ)
    (hw : ∀ Γ σ, w (Γ.permuteOutgoing σ) = sign σ * w Γ)
    (D : VertexSplitData q m r) (τ : SplitOutgoing (q := q) r) :
    sign τ * pairProfile r hq w
      ((splitGraph r hq 1 D).permuteOutgoing (fun v ↦ (τ v).symm)) =
        if τ (vertexSplitChild r 1) = Equiv.refl _ then -2 * w D.1 else 0 := by
  have hz := profile_other_zero r hq w 1 D (fun v ↦ (τ v).symm)
  change profile r hq w 0 _ = 0 at hz
  simp only [pairProfile, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hz, zero_sub]
  have hsym : childOutgoing r (fun v ↦ (τ v).symm) 1 = (childOutgoing r τ 1).symm := rfl
  by_cases ht : τ (vertexSplitChild r 1) = Equiv.refl _
  · have hc : childOutgoing r (fun v ↦ (τ v).symm) 1 = Equiv.refl _ := by
      rw [hsym, (childOutgoing_refl_iff r τ).mpr ht]
      rfl
    rw [if_pos ht, profile_outgoing r hq w hw 1 _ (fun _ ↦ hc), profile_split, sign_symm]
    calc
      _ = -2 * ((sign τ * sign τ) * w D.1) := by ring
      _ = _ := by rw [sign_sq, one_mul]
  · have hc : childOutgoing r τ 1 ≠ Equiv.refl _ := mt (childOutgoing_refl_iff r τ).mp ht
    have hp : (childOutgoing r τ 1).symm 0 = 1 := by
      have hh : ∀ σ : Equiv.Perm (Fin 2), σ ≠ Equiv.refl _ → σ.symm 0 = 1 := by decide
      exact hh _ hc
    rw [if_neg ht, profile_sender_swap_zero r hq w D _ (hsym ▸ hp)]
    ring

theorem average_pairProfile_forward (w : Graph q m → ℝ)
    (hw : ∀ Γ σ, w (Γ.permuteOutgoing σ) = sign σ * w Γ) (D : VertexSplitData q m r) :
    average (pairProfile r hq w) (splitGraph r hq 0 D) = w D.1 := by
  rw [average]
  simp only [weighted_pairProfile_forward r hq w hw D, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← mul_assoc]
  rw [inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

theorem average_pairProfile_backward (w : Graph q m → ℝ)
    (hw : ∀ Γ σ, w (Γ.permuteOutgoing σ) = sign σ * w Γ) (D : VertexSplitData q m r) :
    average (pairProfile r hq w) (splitGraph r hq 1 D) = -w D.1 := by
  rw [average]
  simp only [weighted_pairProfile_backward r hq w hw D]
  have hs : (∑ τ : SplitOutgoing (q := q) r,
      if τ (vertexSplitChild r 1) = Equiv.refl _ then -2 * w D.1 else 0) =
      Fintype.card {τ : SplitOutgoing (q := q) r // τ (vertexSplitChild r 1) = Equiv.refl _} * (-2 * w D.1) := by
    simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 1
    congr 1
    exact (Fintype.card_subtype _).symm
  rw [hs, ← mul_assoc, stabilizer_ratio_binary _ (vertexSplitArity_child q vectorBivectorArity r 1)]
  ring

end EnvelopingIsomorphism.Deformation.VectorSplitOutgoingAverage
