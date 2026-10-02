import EnvelopingIsomorphism.Deformation.MainRealPhysicalFaces

/-! The surviving proper real faces are precisely a nonempty proper physical
internal subset and one of the two actual ordered boundary insertion slots. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainRealPhysicalIndex
open Kontsevich Configuration MainRealPhysicalFaces
open scoped Classical BigOperators

abbrev ProperSubset (n : ℕ) := {S : Finset (Fin (n+2)) // S.Nonempty ∧ Sᶜ.Nonempty}

theorem key_endpoint_cases {n : ℕ} (K : Key n) :
    (K.l = 0 ∧ K.u = 2) ∨ (K.l = 1 ∧ K.u = 3) := by
  have h : ∀ l u : Fin 4, l ≤ u → (boundaryClusterBlock l u).card = 2 →
      (l = 0 ∧ u = 2) ∨ (l = 1 ∧ u = 3) := by decide
  exact h K.l K.u K.property.2.2.1 K.property.2.2.2

def slot {n : ℕ} (K : Key n) : Fin 2 :=
  ⟨K.l.val, by rcases key_endpoint_cases K with h | h <;> rw [h.1] <;> decide⟩

def key {n : ℕ} (S : ProperSubset n) (r : Fin 2) : Key n :=
  ⟨⟨S.val,Fin.castAdd 2 r,Fin.natAdd 2 r⟩,S.property.1,S.property.2,by
    change r.val ≤ 2 + r.val
    omega,by
    change (boundaryClusterBlock (Fin.castAdd 2 r) (Fin.natAdd 2 r)).card = 2
    fin_cases r <;> decide⟩

def keyEquiv (n : ℕ) : Key n ≃ ProperSubset n × Fin 2 where
  toFun K := (⟨K.S,K.property.1,K.property.2.1⟩,slot K)
  invFun p := key p.1 p.2
  left_inv K := by
    apply Subtype.ext
    change (K.S,Fin.castAdd 2 (slot K),Fin.natAdd 2 (slot K)) = K.val
    refine Prod.ext rfl ?_
    apply Prod.ext
    · exact Fin.ext rfl
    · apply Fin.ext
      change 2 + K.l.val = K.u.val
      rcases key_endpoint_cases K with h | h <;> rw [h.1,h.2] <;> decide
  right_inv p := by
    apply Prod.ext
    · exact Subtype.ext rfl
    · exact Fin.ext rfl

@[simp] theorem keyEquiv_symm_apply {n : ℕ} (S : ProperSubset n) (r : Fin 2) :
    (keyEquiv n).symm (S,r) = key S r := rfl

theorem sum_key_eq_sum_subsets_slots {n : ℕ} (f : Key n → ℝ) :
    (∑ K : Key n, f K) = ∑ S : ProperSubset n, (f (key S 0) + f (key S 1)) := by
  rw [← Equiv.sum_comp (keyEquiv n).symm]
  simp only [Fintype.sum_prod_type, keyEquiv_symm_apply, Fin.sum_univ_two]

/-- The global original proper-real Stokes contribution, indexed by the
physical subset and the two actual boundary slots, each exactly once. -/
theorem nativeKind_properReal_eq_subsets {n : ℕ} {H : UniformBinaryGraphs.BinaryGraph (n+2) 3}
    (P : MainScalarBoundaryAssembly.MainPartition H) :
    MainScalarBoundaryAssembly.nativeKindBoundary P .properReal =
      ∑ S : ProperSubset n, (physicalValue H (key S 0) + physicalValue H (key S 1)) := by
  rw [nativeKind_properReal_eq_sum_physicalValue, sum_key_eq_sum_subsets_slots]

/-- Empty, full, and proper nonempty subsets exhaust the physical index,
with each of the two nullary endpoint subsets occurring exactly once. -/
theorem sum_subsets_eq_endpoints {n : ℕ} (f : Finset (Fin (n+2)) → ℝ) :
    (∑ S : Finset (Fin (n+2)), f S) =
      f ∅ + f Finset.univ + ∑ S : ProperSubset n, f S.val := by
  have he : (∅ : Finset (Fin (n+2))) ≠ Finset.univ := by
    intro h
    have hz : (0 : Fin (n+2)) ∈ (∅ : Finset (Fin (n+2))) := h.symm ▸ Finset.mem_univ _
    simpa using hz
  have hp (S : Finset (Fin (n+2))) :
      f S = (if S = ∅ then f ∅ else 0) + (if S = Finset.univ then f Finset.univ else 0) +
        (if S.Nonempty ∧ Sᶜ.Nonempty then f S else 0) := by
    by_cases h0 : S = ∅
    · subst S
      simp [he]
    · by_cases h1 : S = Finset.univ
      · subst S
        simp [he.symm]
      · have hS : S.Nonempty ∧ Sᶜ.Nonempty := by
          refine ⟨Finset.nonempty_iff_ne_empty.mpr h0,Finset.nonempty_iff_ne_empty.mpr ?_⟩
          intro hc
          apply h1
          have h := congrArg (fun T : Finset (Fin (n+2)) => Tᶜ) hc
          simpa only [compl_compl,Finset.compl_empty] using h
        simp only [if_neg h0,if_neg h1,if_pos hS,zero_add]
  have hs : (∑ S : ProperSubset n, f S.val) =
      ∑ S : Finset (Fin (n+2)), if S.Nonempty ∧ Sᶜ.Nonempty then f S else 0 := by
    apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
    · intro S hS
      apply if_neg
      intro hp
      exact hS ⟨⟨S,hp⟩,rfl⟩
    · intro S
      exact (if_pos S.property).symm
  calc
    _ = ∑ S : Finset (Fin (n+2)),
        ((if S = ∅ then f ∅ else 0) + (if S = Finset.univ then f Finset.univ else 0) +
          (if S.Nonempty ∧ Sᶜ.Nonempty then f S else 0)) := Finset.sum_congr rfl (fun S _ => hp S)
    _ = _ := by
      simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      rw [← hs]

end EnvelopingIsomorphism.Deformation.MainRealPhysicalIndex
