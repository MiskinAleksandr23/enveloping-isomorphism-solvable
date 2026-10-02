import EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeights
import EnvelopingIsomorphism.Deformation.GeneralGraphPermutations
import Mathlib.GroupTheory.Perm.Sign

/-! Actual geometric weights under permutations of outgoing edge slots. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeightOutgoing

open KontsevichGraph.General
open scoped Classical BigOperators

theorem outgoingEdgePerm_sign {N : ℕ} (q : Fin N → ℕ)
    (τ : (v : Fin N) → Equiv.Perm (Fin (q v))) :
    Equiv.Perm.sign (outgoingEdgePerm τ) = ∏ v, Equiv.Perm.sign (τ v) := by
  induction N with
  | zero =>
    have he : outgoingEdgePerm τ = 1 := by
      apply Equiv.ext
      intro e
      exact Fin.elim0 e.1
    rw [he]
    simp
  | succ N ih =>
    let tail : (v : Fin N) → Equiv.Perm (Fin (q v.succ)) := fun v => τ v.succ
    have he : ((edgeHeadTailEquiv q).trans (outgoingEdgePerm τ)).trans
        (edgeHeadTailEquiv q).symm = Equiv.sumCongr (τ 0) (outgoingEdgePerm tail) := by
      ext e
      cases e with
      | inl j => rfl
      | inr e => cases e; rfl
    rw [← Equiv.Perm.sign_trans_trans_symm (outgoingEdgePerm τ) (edgeHeadTailEquiv q),
      he, Equiv.Perm.sign_sumCongr, ih, Fin.prod_univ_succ]

variable {n m : ℕ} {q : Fin (n + 1) → ℕ}

def orderPermutation
    (order : Fin (GraphForms.dimension n m) ≃ Edge q)
    (τ : (v : Fin (n + 1)) → Equiv.Perm (Fin (q v))) :
    Equiv.Perm (Fin (GraphForms.dimension n m)) :=
  (order.trans (outgoingEdgePerm τ)).trans order.symm

theorem orderPermutation_sign
    (order : Fin (GraphForms.dimension n m) ≃ Edge q)
    (τ : (v : Fin (n + 1)) → Equiv.Perm (Fin (q v))) :
    Equiv.Perm.sign (orderPermutation order τ) = ∏ v, Equiv.Perm.sign (τ v) := by
  rw [orderPermutation, Equiv.Perm.sign_trans_trans_symm, outgoingEdgePerm_sign]

theorem geometricWeight_permuteOutgoing (Γ : Graph q m)
    (order : Fin (GraphForms.dimension n m) ≃ Edge q)
    (τ : (v : Fin (n + 1)) → Equiv.Perm (Fin (q v))) :
    GeometricWeights.geometricWeight (Γ.permuteOutgoing τ) order =
      (∏ v, permutationSign (R := ℝ) (τ v)) * GeometricWeights.geometricWeight Γ order := by
  have he : GeometricWeights.orderedEdges (Γ.permuteOutgoing τ) order =
      GeometricWeights.orderedEdges Γ ((orderPermutation order τ).trans order) := by
    funext j
    simp [GeometricWeights.orderedEdges, orderPermutation, Graph.permuteOutgoing,
      outgoingEdgePerm]
  rw [GeometricWeights.geometricWeight, he]
  change GeometricWeights.geometricWeight Γ ((orderPermutation order τ).trans order) = _
  rw [GeometricWeights.geometricWeight_permute, orderPermutation_sign]
  let h : ℤˣ →* ℝ := (Int.castRingHom ℝ).toMonoidHom.comp (Units.coeHom ℤ)
  change h (∏ v, Equiv.Perm.sign (τ v)) * _ = (∏ v, h (Equiv.Perm.sign (τ v))) * _
  rw [map_prod]

theorem canonicalWeight_permuteOutgoing (Γ : Graph q m)
    (hq : ∑ v, q v = GraphForms.dimension n m)
    (τ : (v : Fin (n + 1)) → Equiv.Perm (Fin (q v))) :
    GeometricWeights.canonicalWeight (Γ.permuteOutgoing τ) hq =
      (∏ v, permutationSign (R := ℝ) (τ v)) * GeometricWeights.canonicalWeight Γ hq :=
  geometricWeight_permuteOutgoing Γ (GeometricWeights.canonicalOrder hq) τ

theorem canonicalEffectiveWeight_permuteOutgoing (Γ : Graph q m)
    (hq : ∑ v, q v = GraphForms.dimension n m)
    (τ : (v : Fin (n + 1)) → Equiv.Perm (Fin (q v))) :
    GeometricWeights.canonicalEffectiveWeight (Γ.permuteOutgoing τ) hq =
      (∏ v, permutationSign (R := ℝ) (τ v)) * GeometricWeights.canonicalEffectiveWeight Γ hq := by
  rw [GeometricWeights.canonicalEffectiveWeight, canonicalWeight_permuteOutgoing]
  simp only [GeometricWeights.canonicalEffectiveWeight, effectiveMCWeight]
  exact (mul_smul_comm (((n + 1).factorial : ℚ)⁻¹)
    (∏ v, permutationSign (R := ℝ) (τ v)) (GeometricWeights.canonicalWeight Γ hq)).symm

end EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeightOutgoing
