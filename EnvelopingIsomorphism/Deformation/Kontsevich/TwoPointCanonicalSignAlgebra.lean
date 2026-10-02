import EnvelopingIsomorphism.Deformation.Kontsevich.MixedSourceFaceSign

/-! Finite permutation algebra for canonical two-point face orders. -/
noncomputable section
namespace EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointCanonicalSignAlgebra
open KontsevichGraph.General
open scoped Classical BigOperators

theorem rootEdge_sign {N p : ℕ} {q : Fin (N + 1) → ℕ}
    (v : Fin (N + 1)) (hv : q v = p) (ρ : Equiv.Perm (Fin p)) :
    (Equiv.Perm.sign (outgoingEdgePerm (rootOutgoing v hv ρ)) : ℝ) = permutationSign (R := ℝ) ρ := by
  rw [GeometricWeightOutgoing.outgoingEdgePerm_sign]
  let f : ℤˣ →* ℝ := (Int.castRingHom ℝ).toMonoidHom.comp (Units.coeHom ℤ)
  change f (∏ w, Equiv.Perm.sign (rootOutgoing v hv ρ w)) = _
  rw [map_prod]
  exact rootOutgoing_sign v hv ρ

theorem sign_comp_conjugates {A B X : Type*} [Fintype A] [Fintype B] [Fintype X]
    [DecidableEq A] [DecidableEq B] [DecidableEq X]
    (E : A ≃ B) (P : Equiv.Perm A) (T : Equiv.Perm X) (Z : B ≃ X) :
    Equiv.Perm.sign ((E.permCongr P).trans ((Z.trans T).trans Z.symm)) = T.sign * P.sign := by
  rw [Equiv.Perm.sign_trans, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_trans_trans_symm]

theorem block_sign {r q N : ℕ} (hr : r = 1) (hq : q = N)
    (ht : r + q = N + 1) (B : Equiv.Perm (Fin (r + q)))
    (C : Equiv.Perm (Fin (N + 1))) (Q : Fin q ≃ Fin N)
    (hl : ∀ j : Fin r, finCongr ht (B (finSumFinEquiv (Sum.inl j))) = C 0)
    (he : ∀ j : Fin q, finCongr ht (B (finSumFinEquiv (Sum.inr j))) = C (Q j).succ) :
    B.sign = C.sign * Equiv.Perm.sign ((finCongr hq).symm.trans Q) := by
  subst r
  subst q
  change B.sign = C.sign * Equiv.Perm.sign Q
  let E := finCongr ht
  let Z : Fin 1 ⊕ Fin N ≃ Fin (N + 1) := finSumFinEquiv.trans E
  have hz0 (j : Fin 1) : Z (Sum.inl j) = 0 := by
    apply Fin.ext
    have hj := j.isLt
    change j.val = 0
    omega
  have hzs (j : Fin N) : Z (Sum.inr j) = j.succ := by
    apply Fin.ext
    change 1 + j.val = j.val + 1
    omega
  have hh : E.permCongr B = (Z.permCongr (Equiv.sumCongr (Equiv.refl (Fin 1)) Q)).trans C := by
    apply Equiv.ext
    intro x
    obtain ⟨z,rfl⟩ := Z.surjective x
    change E (B (E.symm (Z z))) =
      C (Z ((Equiv.sumCongr (Equiv.refl (Fin 1)) Q) (Z.symm (Z z))))
    rw [Equiv.symm_apply_apply]
    have hEZ : E.symm (Z z) = finSumFinEquiv z := by
      change E.symm (E (finSumFinEquiv z)) = _
      exact E.symm_apply_apply _
    rw [hEZ]
    rcases z with z | z
    · change E (B (finSumFinEquiv (Sum.inl z))) = C (Z (Sum.inl z))
      rw [hz0]
      exact hl z
    · change E (B (finSumFinEquiv (Sum.inr z))) = C (Z (Sum.inr (Q z)))
      rw [hzs]
      exact he z
  have hs := congrArg Equiv.Perm.sign hh
  simpa only [Equiv.Perm.sign_permCongr, Equiv.Perm.sign_trans, Equiv.Perm.sign_sumCongr,
    Equiv.Perm.sign_refl, one_mul] using hs

end EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointCanonicalSignAlgebra
