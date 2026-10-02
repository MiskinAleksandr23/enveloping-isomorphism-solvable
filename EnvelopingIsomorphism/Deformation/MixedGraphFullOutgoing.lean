import EnvelopingIsomorphism.Deformation.MixedGraphAveraging
import EnvelopingIsomorphism.Deformation.MixedGraphBlockRelabelling

/-! The mixed outgoing average in actual vertex-indexed dependent arities.
The vector's one-slot permutation is uniquely fixed; every binary row retains
its original outgoing permutation and sign. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
namespace EnvelopingIsomorphism.Deformation.MixedGraphAveraging
open scoped BigOperators Classical
open KontsevichGraph.General MixedGraphProfileCarrier
variable {n m : ℕ}

abbrev FullOutgoing (i : Fin (n + 1)) :=
  (v : Fin (n + 1)) → Equiv.Perm (Fin (Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i v))

theorem backgroundArity (i : Fin (n + 1)) (j : Fin n) :
    Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i (placementEquiv i (Sum.inl j)) = 2 :=
  if_neg (placementEquiv_inl_ne i j)

def outgoingRestrict (i : Fin (n + 1)) (τ : FullOutgoing i) : OutgoingGroup n :=
  fun j => (finCongr (backgroundArity i j)).permCongr (τ (placementEquiv i (Sum.inl j)))

private theorem outside_index (i : Fin (n + 1)) (j : Fin n) :
    (outsideEquiv i).symm ⟨placementEquiv i (Sum.inl j), placementEquiv_inl_ne i j⟩ = j := by
  exact (outsideEquiv i).symm_apply_apply j

/-- Actual equivalence from the existing background-indexed group to every
vertex's native outgoing-slot group, including the unique vector row. -/
def outgoingAtEquiv (i : Fin (n + 1)) : OutgoingGroup n ≃ FullOutgoing i where
  toFun := outgoingAt i
  invFun := outgoingRestrict i
  left_inv τ := by
    funext j
    simp only [outgoingRestrict, outgoingAt, dif_neg (placementEquiv_inl_ne i j), outside_index]
    exact (finCongr (backgroundArity i j)).permCongr.apply_symm_apply (τ j)
  right_inv τ := by
    funext v
    obtain ⟨v,rfl⟩ := (placementEquiv i).surjective v
    cases v with
    | inl j =>
      simp only [outgoingAt, dif_neg (placementEquiv_inl_ne i j)]
      rw [outside_index]
      simp only [outgoingRestrict]
      exact (finCongr (backgroundArity i j)).permCongr.symm_apply_apply _
    | inr j =>
      rw [placementEquiv_inr]
      haveI : Subsingleton (Fin (Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i i)) := by
        simpa [Gauge.PlacedMixedGraphTaylorCoefficients.arities] using (inferInstance : Subsingleton (Fin 1))
      exact Subsingleton.elim _ _

def fullOutgoingSymm (i : Fin (n + 1)) : Equiv.Perm (FullOutgoing i) where
  toFun τ v := (τ v).symm
  invFun τ v := (τ v).symm
  left_inv τ := by funext v; rfl
  right_inv τ := by funext v; rfl

@[simp] theorem outgoingGraphEquiv_symm_carrier (τ : OutgoingGroup n) (H : VectorGraph n m) :
    (outgoingGraphEquiv τ m).symm H =
      ⟨H.vertex,H.graph.permuteOutgoing (fun v => (outgoingAt H.vertex τ v).symm)⟩ := rfl

variable {k : Type*} [Field k]

/-- The full native sign is exactly the original mixed outgoing sign. -/
theorem outgoingAtEquiv_sign (i : Fin (n + 1)) (τ : OutgoingGroup n) :
    (∏ v, permutationSign (R := k) (outgoingAtEquiv i τ v)) = outgoingSign τ :=
  outgoingAt_sign_prod i τ

theorem fullOutgoing_sign_symm (i : Fin (n + 1)) (τ : FullOutgoing i) :
    (∏ v, permutationSign (R := k) ((τ v).symm)) = ∏ v, permutationSign (R := k) (τ v) := by
  simp [permutationSign]

/-- Literal signed average over the graph's full native outgoing arities. -/
theorem outgoingAverage_eq_full (c : VectorGraph n 2 → k) (H : VectorGraph n 2) :
    outgoingAverage c H = ((2 : k)^n)⁻¹ *
      ∑ τ : FullOutgoing H.vertex, (∏ v, permutationSign (R := k) (τ v)) *
        c ⟨H.vertex,H.graph.permuteOutgoing (fun v => (τ v).symm)⟩ := by
  rw [outgoingAverage_apply]
  congr 1
  apply Fintype.sum_equiv (outgoingAtEquiv H.vertex)
  intro τ
  rw [outgoingAtEquiv_sign, outgoingGraphEquiv_symm_carrier]
  rfl

/-- Inverting every row removes the inverse convention without changing any
sign, so actual outgoing covariance lemmas can be applied directly. -/
theorem outgoingAverage_eq_full_forward (c : VectorGraph n 2 → k) (H : VectorGraph n 2) :
    outgoingAverage c H = ((2 : k)^n)⁻¹ *
      ∑ τ : FullOutgoing H.vertex, (∏ v, permutationSign (R := k) (τ v)) *
        c ⟨H.vertex,H.graph.permuteOutgoing τ⟩ := by
  rw [outgoingAverage_eq_full]
  congr 1
  apply Fintype.sum_equiv (fullOutgoingSymm H.vertex)
  intro τ
  change (∏ v, permutationSign (R := k) (τ v)) *
      c ⟨H.vertex,H.graph.permuteOutgoing (fun v => (τ v).symm)⟩ =
    (∏ v, permutationSign (R := k) ((τ v).symm)) *
      c ⟨H.vertex,H.graph.permuteOutgoing (fun v => (τ v).symm)⟩
  rw [fullOutgoing_sign_symm]


theorem card_fullOutgoing (i : Fin (n + 1)) : Fintype.card (FullOutgoing i) = 2 ^ n := by
  rw [← Fintype.card_congr (outgoingAtEquiv i)]
  simp [OutgoingGroup, Fintype.card_perm]

theorem outgoingAverage_eq_full_card (c : VectorGraph n 2 → k) (H : VectorGraph n 2) :
    outgoingAverage c H = (Fintype.card (FullOutgoing H.vertex) : k)⁻¹ *
      ∑ τ : FullOutgoing H.vertex, (∏ v, permutationSign (R := k) (τ v)) *
        c ⟨H.vertex,H.graph.permuteOutgoing (fun v => (τ v).symm)⟩ := by
  simpa only [card_fullOutgoing, Nat.cast_pow, Nat.cast_ofNat] using outgoingAverage_eq_full c H

/-- Native arity casts preserve the literal full-family average. This applies
in particular to a two-child split profile with an outside retained vector. -/
theorem outgoingAverage_ofProfile {q : Fin (n + 1) → ℕ} (i : Fin (n + 1))
    (h : q = Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i)
    (c : VectorGraph n 2 → k) (Γ : Graph q 2) :
    outgoingAverage c (ofProfile i h Γ) =
      (Fintype.card ((v : Fin (n + 1)) → Equiv.Perm (Fin (q v))) : k)⁻¹ *
        ∑ τ : (v : Fin (n + 1)) → Equiv.Perm (Fin (q v)),
          (∏ v, permutationSign (R := k) (τ v)) *
            c (ofProfile i h (Γ.permuteOutgoing (fun v => (τ v).symm))) := by
  subst q
  exact outgoingAverage_eq_full_card c ⟨i,Γ⟩

end EnvelopingIsomorphism.Deformation.MixedGraphAveraging
