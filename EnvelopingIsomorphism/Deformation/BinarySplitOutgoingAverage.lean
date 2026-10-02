import EnvelopingIsomorphism.Deformation.BinarySplitOutgoingCovariance
import EnvelopingIsomorphism.Deformation.GeneralGraphOutgoingAverage
import EnvelopingIsomorphism.Deformation.MixedGraphCorrectionFibres

/-! Exact outgoing half-factor for a binary split with arbitrary outside
arities. In particular an exterior one-slot vector row is retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.BinarySplitOutgoingAverage
open scoped Classical BigOperators
open KontsevichGraph.General KontsevichGraph.General.Graph
open KontsevichGraph.General.TwoVertexContraction BinaryVertexContraction
open BinarySplitOutgoingCovariance GeneralGraphOutgoingAverage
open GraphCoefficientProfiles SchoutenGraphContraction
open UniformCurvatureOutgoing (receiver)
variable {n m : ℕ} {q : Fin (n + 1) → ℕ} (r : Fin (n + 1)) (hq : q r = 3)

abbrev splitGraph (a : Fin 2) := vertexSplitDataGraph (canonicalTemplate a) r hq (m := m)
abbrev SplitOutgoing := Group (vertexSplitArity q bivectorArity r)

def profile (w : Graph q m → ℝ) (a : Fin 2) : Graph (vertexSplitArity q bivectorArity r) m → ℝ :=
  pushforward (splitGraph r hq a) (fun D => w D.1)

def pairProfile (w : Graph q m → ℝ) : Graph (vertexSplitArity q bivectorArity r) m → ℝ :=
  ∑ a : Fin 2, profile r hq w a

theorem splitGraph_injective (a : Fin 2) : Function.Injective (splitGraph r hq (m := m) a) := by
  fin_cases a
  · apply vertexSplitDataGraph_injective (Θ := bivectorForward (cyclicPermutation 0))
      (leg := bivectorForwardLeg (cyclicPermutation 0))
    intro j
    have hm : bivectorForwardLeg (cyclicPermutation 0) j ∈
        (bivectorForward (cyclicPermutation 0)).incoming (Sum.inr j) := by
      rw [bivectorForward_incoming_leg]; simp
    simpa only [Graph.incoming, Finset.mem_filter, Finset.mem_univ, true_and] using hm
  · apply vertexSplitDataGraph_injective (Θ := bivectorReverse (cyclicPermutation 0))
      (leg := bivectorReverseLeg (cyclicPermutation 0))
    intro j
    have hm : bivectorReverseLeg (cyclicPermutation 0) j ∈
        (bivectorReverse (cyclicPermutation 0)).incoming (Sum.inr j) := by
      rw [bivectorReverse_incoming_leg]; simp
    simpa only [Graph.incoming, Finset.mem_filter, Finset.mem_univ, true_and] using hm

theorem profile_split (w : Graph q m → ℝ) (a : Fin 2) (D : VertexSplitData q m r) :
    profile r hq w a (splitGraph r hq a D) = w D.1 := by
  simp only [profile, pushforward, (splitGraph_injective r hq a).eq_iff]
  simp

theorem profile_outgoing (w : Graph q m → ℝ)
    (hw : ∀ Γ σ, w (Γ.permuteOutgoing σ) = sign σ * w Γ)
    (a : Fin 2) (τ : SplitOutgoing (q := q) r) (hτ : childOutgoing r τ a = Equiv.refl _)
    (H : Graph (vertexSplitArity q bivectorArity r) m) :
    profile r hq w a (H.permuteOutgoing τ) = sign τ * profile r hq w a H := by
  unfold profile pushforward
  rw [← Equiv.sum_comp (dataEquiv r hq τ a), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D _
  dsimp only [splitGraph]
  simp only [dataGraph_outgoing r hq τ a hτ]
  have hinj : Function.Injective (fun H : Graph (vertexSplitArity q bivectorArity r) m => H.permuteOutgoing τ) :=
    (Graph.outgoingGraphEquiv (vertexSplitArity q bivectorArity r) m τ).injective
  rw [hinj.eq_iff]
  change (if _ then w (D.1.permuteOutgoing (quotientOutgoing r hq τ a)) else 0) = _
  rw [hw]
  have hs : sign (quotientOutgoing r hq τ a) = sign τ := quotientOutgoing_sign r hq τ a hτ
  rw [hs]
  split_ifs <;> simp

theorem profile_zero (w : Graph q m → ℝ) (a : Fin 2)
    (H : Graph (vertexSplitArity q bivectorArity r) m)
    (hH : H.target (vertexSplitLocalEdge q bivectorArity r ⟨a,0⟩) ≠
      Sum.inl (vertexSplitChild r (receiver a))) : profile r hq w a H = 0 := by
  apply Finset.sum_eq_zero
  intro D _
  apply if_neg
  intro he
  apply hH
  rw [← he]
  change (D.1.vertexSplit (canonicalTemplate a) r hq D.2).target _ = _
  rw [vertexSplit_target_local, UniformCurvatureOutgoing.canonicalTemplate_sender_zero]
  rfl

theorem profile_sender_swap_zero (w : Graph q m → ℝ) (a : Fin 2) (D : VertexSplitData q m r)
    (τ : SplitOutgoing (q := q) r) (hτ : childOutgoing r τ a 0 = 1) :
    profile r hq w a ((splitGraph r hq a D).permuteOutgoing τ) = 0 := by
  apply profile_zero r hq w a
  change (D.1.vertexSplit (canonicalTemplate a) r hq D.2).target
    (outgoingEdgePerm τ (vertexSplitLocalEdge q bivectorArity r ⟨a,0⟩)) ≠ _
  rw [outgoing_localEdge, outgoingEdgePerm_apply, hτ, vertexSplit_target_local,
    UniformCurvatureOutgoing.canonicalTemplate_sender_one, vertexSplitTemplateVertex_leg]
  exact vertexSplitOldVertex_ne_child r _ (D.1.noLoops r _) _

theorem profile_other_zero (w : Graph q m → ℝ) (a : Fin 2) (D : VertexSplitData q m r)
    (τ : SplitOutgoing (q := q) r) :
    profile r hq w (receiver a) ((splitGraph r hq a D).permuteOutgoing τ) = 0 := by
  apply profile_zero r hq w (receiver a)
  change (D.1.vertexSplit (canonicalTemplate a) r hq D.2).target
    (outgoingEdgePerm τ (vertexSplitLocalEdge q bivectorArity r ⟨receiver a,0⟩)) ≠ _
  rw [outgoing_localEdge, outgoingEdgePerm_apply, vertexSplit_target_local,
    UniformCurvatureOutgoing.canonicalTemplate_receiver, vertexSplitTemplateVertex_leg]
  exact vertexSplitOldVertex_ne_child r _ (D.1.noLoops r _) _

private theorem childOutgoing_symm (τ : SplitOutgoing (q := q) r) (a : Fin 2) :
    childOutgoing r (fun v => (τ v).symm) a = (childOutgoing r τ a).symm := rfl

private theorem childOutgoing_refl_iff (τ : SplitOutgoing (q := q) r) (a : Fin 2) :
    childOutgoing r τ a = Equiv.refl _ ↔ τ (vertexSplitChild r a) = Equiv.refl _ := by
  unfold childOutgoing slotCast
  constructor
  · intro h
    apply Equiv.ext
    intro j
    have he := congrArg (fun e => e (Fin.cast (vertexSplitArity_child q bivectorArity r a) j)) h
    apply Fin.ext
    simpa using congrArg Fin.val he
  · intro h
    rw [h]
    exact Equiv.ext (fun _ => rfl)

theorem weighted_pairProfile_split (w : Graph q m → ℝ)
    (hw : ∀ Γ σ, w (Γ.permuteOutgoing σ) = sign σ * w Γ)
    (a : Fin 2) (D : VertexSplitData q m r) (τ : SplitOutgoing (q := q) r) :
    sign τ * pairProfile r hq w ((splitGraph r hq a D).permuteOutgoing (fun v => (τ v).symm)) =
      if τ (vertexSplitChild r a) = Equiv.refl _ then w D.1 else 0 := by
  have hp : pairProfile r hq w ((splitGraph r hq a D).permuteOutgoing (fun v => (τ v).symm)) =
      profile r hq w a ((splitGraph r hq a D).permuteOutgoing (fun v => (τ v).symm)) := by
    rw [pairProfile, Finset.sum_apply]
    apply Finset.sum_eq_single a
    · intro b _ hba
      have hb : b = receiver a := by fin_cases a <;> fin_cases b <;> simp_all [receiver]
      rw [hb]
      exact profile_other_zero r hq w a D _
    · intro h
      exact (h (Finset.mem_univ a)).elim
  rw [hp]
  by_cases hτ : τ (vertexSplitChild r a) = Equiv.refl _
  · rw [if_pos hτ]
    have hf : childOutgoing r (fun v => (τ v).symm) a = Equiv.refl _ := by
      rw [childOutgoing_symm, (childOutgoing_refl_iff r τ a).mpr hτ]
      rfl
    rw [profile_outgoing r hq w hw a _ hf, profile_split, sign_symm,
      ← mul_assoc, sign_sq, one_mul]
  · rw [if_neg hτ]
    have hn : childOutgoing r τ a ≠ Equiv.refl _ := mt (childOutgoing_refl_iff r τ a).mp hτ
    have hf : (childOutgoing r τ a).symm 0 = 1 := by
      have hh : ∀ σ : Equiv.Perm (Fin 2), σ ≠ Equiv.refl _ → σ.symm 0 = 1 := by decide
      exact hh _ hn
    rw [profile_sender_swap_zero r hq w a D _ (by rwa [childOutgoing_symm]), mul_zero]

/-- The binary sender stabilizer has precisely half of all outgoing families,
regardless of the outside row arities. -/
theorem average_pairProfile_split (w : Graph q m → ℝ)
    (hw : ∀ Γ σ, w (Γ.permuteOutgoing σ) = sign σ * w Γ)
    (a : Fin 2) (D : VertexSplitData q m r) :
    average (pairProfile r hq w) (splitGraph r hq a D) = (1 / 2 : ℝ) * w D.1 := by
  rw [average]
  simp only [weighted_pairProfile_split r hq w hw a D]
  have hs : (∑ τ : SplitOutgoing (q := q) r,
      if τ (vertexSplitChild r a) = Equiv.refl _ then w D.1 else 0) =
      Fintype.card {τ : SplitOutgoing (q := q) r // τ (vertexSplitChild r a) = Equiv.refl _} * w D.1 := by
    simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 1
    congr 1
    exact (Fintype.card_subtype _).symm
  rw [hs, ← mul_assoc, stabilizer_ratio_binary _ (vertexSplitArity_child q bivectorArity r a)]

end EnvelopingIsomorphism.Deformation.BinarySplitOutgoingAverage
