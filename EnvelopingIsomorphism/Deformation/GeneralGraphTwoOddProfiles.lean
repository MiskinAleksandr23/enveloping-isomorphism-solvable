import EnvelopingIsomorphism.Deformation.GeneralGraphMixedProfiles
import EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeightRelabel

/-! Dependent profiles with one vector and one trivector. Their two odd outgoing
blocks contribute the relative-order sign; the remaining binary blocks are even.
Independent background tensors are transported along the actual vertex permutation.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General

open scoped BigOperators Classical

variable {n m d : ℕ}

def twoOddArity (i j : Fin n) (v : Fin n) : ℕ := if v = i then 1 else if v = j then 3 else 2

@[simp] theorem twoOddArity_vector (i j : Fin n) : twoOddArity i j i = 1 := by simp [twoOddArity]

theorem twoOddArity_trivector (i j : Fin n) (hji : j ≠ i) : twoOddArity i j j = 3 := by
  simp [twoOddArity, hji]

theorem twoOddArity_binary (i j v : Fin n) (hvi : v ≠ i) (hvj : v ≠ j) :
    twoOddArity i j v = 2 := by simp [twoOddArity, hvi, hvj]

theorem profileArity_twoOdd (i j : Fin n) (σ : Equiv.Perm (Fin n)) :
    profileArity (twoOddArity i j) σ = twoOddArity (σ i) (σ j) := by
  funext v
  simp only [profileArity, twoOddArity, Equiv.symm_apply_eq]

section Tensors

variable {R : Type*} [CommRing R]

/-- All ordinary tensors remain independent; values of B at the distinguished slots are unused. -/
def twoOddTensors (i j : Fin n) (hji : j ≠ i)
    (X : Tensor 1 d R) (Q : Tensor 3 d R) (B : Fin n → Tensor 2 d R)
    (v : Fin n) : Tensor (twoOddArity i j v) d R :=
  if hvi : v = i then by simpa [twoOddArity, hvi] using X
  else if hvj : v = j then by simpa [twoOddArity, hvi, hvj, hji] using Q
  else by simpa [twoOddArity, hvi, hvj] using B v

theorem twoOddTensors_vector_heq (i j : Fin n) (hji : j ≠ i)
    (X : Tensor 1 d R) (Q : Tensor 3 d R) (B : Fin n → Tensor 2 d R) :
    HEq (twoOddTensors i j hji X Q B i) X := by simp [twoOddTensors]

theorem twoOddTensors_trivector_heq (i j : Fin n) (hji : j ≠ i)
    (X : Tensor 1 d R) (Q : Tensor 3 d R) (B : Fin n → Tensor 2 d R) :
    HEq (twoOddTensors i j hji X Q B j) Q := by simp [twoOddTensors, hji]

theorem twoOddTensors_binary_heq (i j : Fin n) (hji : j ≠ i)
    (X : Tensor 1 d R) (Q : Tensor 3 d R) (B : Fin n → Tensor 2 d R)
    (v : Fin n) (hvi : v ≠ i) (hvj : v ≠ j) :
    HEq (twoOddTensors i j hji X Q B v) (B v) := by simp [twoOddTensors, hvi, hvj]

private theorem transportTwoOddTensors_heq {q q' : Fin n → ℕ} (h : q = q')
    (T : (v : Fin n) → Tensor (q v) d R) (v : Fin n) :
    HEq ((h ▸ T : (w : Fin n) → Tensor (q' w) d R) v) (T v) := by
  subst q'
  rfl

/-- Actual dependent transport carries X, Q and each separate binary argument to its new slot. -/
theorem profileTensors_twoOdd (i j : Fin n) (hji : j ≠ i) (σ : Equiv.Perm (Fin n))
    (X : Tensor 1 d R) (Q : Tensor 3 d R) (B : Fin n → Tensor 2 d R) :
    (profileArity_twoOdd i j σ ▸ profileTensors (twoOddArity i j) σ
      (twoOddTensors i j hji X Q B) :
        (v : Fin n) → Tensor (twoOddArity (σ i) (σ j) v) d R) =
      twoOddTensors (σ i) (σ j) (σ.injective.ne hji) X Q (B ∘ σ.symm) := by
  funext v
  apply eq_of_heq
  refine (transportTwoOddTensors_heq (profileArity_twoOdd i j σ) _ v).trans ?_
  change HEq (twoOddTensors i j hji X Q B (σ.symm v)) _
  by_cases hvi : v = σ i
  · subst v
    rw [σ.symm_apply_apply]
    exact (twoOddTensors_vector_heq i j hji X Q B).trans
      (twoOddTensors_vector_heq (σ i) (σ j) (σ.injective.ne hji) X Q _).symm
  · have hi : σ.symm v ≠ i := fun h => hvi ((σ.symm_apply_eq).mp h)
    by_cases hvj : v = σ j
    · subst v
      rw [σ.symm_apply_apply]
      exact (twoOddTensors_trivector_heq i j hji X Q B).trans
        (twoOddTensors_trivector_heq (σ i) (σ j) (σ.injective.ne hji) X Q _).symm
    · have hj : σ.symm v ≠ j := fun h => hvj ((σ.symm_apply_eq).mp h)
      exact (twoOddTensors_binary_heq i j hji X Q B (σ.symm v) hi hj).trans
        (twoOddTensors_binary_heq (σ i) (σ j) (σ.injective.ne hji) X Q (B ∘ σ.symm) v hvi hvj).symm

namespace Graph

def twoOddGraphEquiv (i j : Fin n) (σ : Equiv.Perm (Fin n)) (m : ℕ) :
    Graph (twoOddArity i j) m ≃ Graph (twoOddArity (σ i) (σ j)) m :=
  (profileGraphEquiv (twoOddArity i j) m σ).trans (castProfileEquiv (profileArity_twoOdd i j σ) m)

theorem cochainOperator_twoOddGraphEquiv (i j : Fin n) (hji : j ≠ i)
    (σ : Equiv.Perm (Fin n)) (Γ : Graph (twoOddArity i j) m)
    (X : Tensor 1 d R) (Q : Tensor 3 d R) (B : Fin n → Tensor 2 d R) :
    (twoOddGraphEquiv i j σ m Γ).cochainOperator
      (twoOddTensors (σ i) (σ j) (σ.injective.ne hji) X Q (B ∘ σ.symm)) =
        Γ.cochainOperator (twoOddTensors i j hji X Q B) := by
  rw [← profileTensors_twoOdd i j hji σ X Q B]
  exact (cochainOperator_castProfile (profileArity_twoOdd i j σ) (Γ.permuteProfile σ) _).trans
    (cochainOperator_permuteProfile Γ σ _)

/-- The labelled identity uses the genuine dependent edge-label equivalence. -/
theorem labelledOperator_permuteProfile_twoOdd (i j : Fin n) (hji : j ≠ i)
    (Γ : Graph (twoOddArity i j) m) (σ : Equiv.Perm (Fin n))
    (lab : Edge (profileArity (twoOddArity i j) σ) → Fin d)
    (X : Tensor 1 d R) (Q : Tensor 3 d R) (B : Fin n → Tensor 2 d R)
    (f : Fin m → Polynomial d R) :
    ((Γ.permuteProfile σ).labelledOperator lab).currySum
      (profileTensors (twoOddArity i j) σ (twoOddTensors i j hji X Q B)) f =
      (Γ.labelledOperator (profileLabelEquiv (twoOddArity i j) σ d lab)).currySum
        (twoOddTensors i j hji X Q B) f :=
  labelledOperator_permuteProfile Γ σ lab _ f

end Graph
end Tensors

/-- Only the relative order of the two odd blocks contributes to this placement sign. -/
def twoOddPlacementSign (i j : Fin n) : ℤˣ := if i < j then 1 else -1

theorem twoOddPlacementSign_sq (i j : Fin n) : twoOddPlacementSign i j * twoOddPlacementSign i j = 1 := by
  unfold twoOddPlacementSign
  split_ifs <;> norm_num

/-- The weighted inversion product has just one potentially negative factor. -/
theorem profileRowPerm_sign_two_odd_of_lt (q : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
    (i j : Fin n) (hij : i < j) (hi : Odd (q i)) (hj : Odd (q j))
    (heven : ∀ v, v ≠ i → v ≠ j → Even (q v)) :
    (profileRowPerm q σ).sign = if σ i < σ j then 1 else -1 := by
  have hfactor (v w : Fin n) (hnot : ¬ (v = i ∧ w = j)) :
      (if v < w ∧ σ w < σ v then (-1 : ℤˣ) ^ (q v * q w) else 1) = 1 := by
    split_ifs with h
    · have hp : Even (q v * q w) := by
        by_cases hvi : v = i
        · have hwi : w ≠ i := fun hw => h.1.ne (hvi.trans hw.symm)
          have hwj : w ≠ j := fun hw => hnot ⟨hvi, hw⟩
          exact (heven w hwi hwj).mul_left _
        · by_cases hvj : v = j
          · have hwi : w ≠ i := by
              intro hw
              exact hij.not_gt (hvj ▸ hw ▸ h.1)
            have hwj : w ≠ j := fun hw => h.1.ne (hvj.trans hw.symm)
            exact (heven w hwi hwj).mul_left _
          · exact (heven v hvi hvj).mul_right _
      exact hp.neg_one_pow
    · rfl
  rw [profileRowPerm_sign]
  rw [Finset.prod_eq_single i]
  · rw [Finset.prod_eq_single j]
    · have hs : σ i ≠ σ j := σ.injective.ne hij.ne
      have hlt : σ j < σ i ↔ ¬ σ i < σ j := by omega
      simp only [hij, true_and, (hi.mul hj).neg_one_pow, hlt]
      split_ifs <;> rfl
    · intro w _ hw
      exact hfactor i w (by simpa using hw)
    · simp
  · intro v _ hv
    apply Finset.prod_eq_one
    intro w _
    exact hfactor v w (fun h => hv h.1)
  · simp

/-- Exact canonical edge-block sign, with both odd placements retained. -/
theorem profileRowPerm_sign_twoOdd (i j : Fin n) (hji : j ≠ i) (σ : Equiv.Perm (Fin n)) :
    (profileRowPerm (twoOddArity i j) σ).sign =
      twoOddPlacementSign i j * twoOddPlacementSign (σ i) (σ j) := by
  have heven (v : Fin n) (hvi : v ≠ i) (hvj : v ≠ j) : Even (twoOddArity i j v) := by
    simp [twoOddArity, hvi, hvj]
  rcases lt_or_gt_of_ne hji.symm with hij | hji'
  · rw [profileRowPerm_sign_two_odd_of_lt _ σ i j hij (by simp [twoOddArity])
      (by rw [twoOddArity_trivector _ _ hji]; exact ⟨1, rfl⟩) heven]
    simp [twoOddPlacementSign, hij]
  · rw [profileRowPerm_sign_two_odd_of_lt _ σ j i hji' (by rw [twoOddArity_trivector _ _ hji]; exact ⟨1, rfl⟩)
      (by simp [twoOddArity]) (fun v hvj hvi => heven v hvi hvj)]
    have hs : σ i ≠ σ j := σ.injective.ne hji.symm
    rcases lt_or_gt_of_ne hs with h | h
    · simp [twoOddPlacementSign, hji'.not_gt, h, h.not_gt]
    · simp [twoOddPlacementSign, hji'.not_gt, h, h.not_gt]

/-- For fixed ordered arguments X,Q,B..., the sign is positive exactly when
the vector remains before the trivector in the new placement. -/
theorem profileRowPerm_sign_twoOdd_ordered (i j : Fin n) (hij : i < j) (σ : Equiv.Perm (Fin n)) :
    (profileRowPerm (twoOddArity i j) σ).sign = twoOddPlacementSign (σ i) (σ j) := by
  rw [profileRowPerm_sign_twoOdd i j hij.ne.symm σ]
  simp [twoOddPlacementSign, hij]

theorem twoOddArity_sum (i j : Fin n) (hji : j ≠ i) : ∑ v, twoOddArity i j v = n * 2 := by
  have hv (v : Fin n) : twoOddArity i j v + (if v = i then 1 else 0) =
      2 + (if v = j then 1 else 0) := by
    by_cases hvi : v = i
    · subst v
      simp [twoOddArity, hji.symm]
    · by_cases hvj : v = j <;> simp [twoOddArity, hvi, hvj, hji]
  have h := congrArg (fun f : Fin n → ℕ => ∑ v, f v) (funext hv)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  omega

open EnvelopingIsomorphism.Deformation.Kontsevich

/-- Genuine canonical weights have exactly the two-odd placement covariance. -/
theorem canonicalWeight_twoOddGraphEquiv_sign (i j : Fin (n + 1)) (hji : j ≠ i)
    (σ : Equiv.Perm (Fin (n + 1))) (Γ : Graph (twoOddArity i j) m)
    (hq : ∑ v, twoOddArity i j v = GraphForms.dimension n m)
    (hq' : ∑ v, twoOddArity (σ i) (σ j) v = GraphForms.dimension n m) :
    GeometricWeights.canonicalWeight (Graph.twoOddGraphEquiv i j σ m Γ) hq' =
      ((twoOddPlacementSign i j * twoOddPlacementSign (σ i) (σ j) : ℤˣ) : ℝ) *
        GeometricWeights.canonicalWeight Γ hq := by
  change GeometricWeights.canonicalWeight
    (Graph.castProfileEquiv (profileArity_twoOdd i j σ) m (Γ.permuteProfile σ)) hq' = _
  rw [GeometricWeights.canonicalWeight_castProfile (profileArity_twoOdd i j σ)
    (Γ.permuteProfile σ) ((profileArity_sum (twoOddArity i j) σ).trans hq) hq',
    GeometricWeights.canonicalWeight_permuteProfile_sign, profileRowPerm_sign_twoOdd i j hji σ]

/-- MC normalization keeps the same total-vertex factorial and the same two-odd sign. -/
theorem canonicalEffectiveWeight_twoOddGraphEquiv_sign (i j : Fin (n + 1)) (hji : j ≠ i)
    (σ : Equiv.Perm (Fin (n + 1))) (Γ : Graph (twoOddArity i j) m)
    (hq : ∑ v, twoOddArity i j v = GraphForms.dimension n m)
    (hq' : ∑ v, twoOddArity (σ i) (σ j) v = GraphForms.dimension n m) :
    GeometricWeights.canonicalEffectiveWeight (Graph.twoOddGraphEquiv i j σ m Γ) hq' =
      ((twoOddPlacementSign i j * twoOddPlacementSign (σ i) (σ j) : ℤˣ) : ℝ) *
        GeometricWeights.canonicalEffectiveWeight Γ hq := by
  unfold GeometricWeights.canonicalEffectiveWeight
  rw [canonicalWeight_twoOddGraphEquiv_sign i j hji σ Γ hq hq']
  unfold effectiveMCWeight
  exact (mul_smul_comm _ _ _).symm

/-- Weighting by the fixed X,Q ordering sign compensates precisely the actual
canonical block sign. An unsigned placement sum would not have this covariance. -/
theorem signed_canonicalEffectiveWeight_twoOddGraphEquiv (i j : Fin (n + 1)) (hji : j ≠ i)
    (σ : Equiv.Perm (Fin (n + 1))) (Γ : Graph (twoOddArity i j) m)
    (hq : ∑ v, twoOddArity i j v = GraphForms.dimension n m)
    (hq' : ∑ v, twoOddArity (σ i) (σ j) v = GraphForms.dimension n m) :
    (twoOddPlacementSign (σ i) (σ j) : ℝ) *
        GeometricWeights.canonicalEffectiveWeight (Graph.twoOddGraphEquiv i j σ m Γ) hq' =
      (twoOddPlacementSign i j : ℝ) * GeometricWeights.canonicalEffectiveWeight Γ hq := by
  rw [canonicalEffectiveWeight_twoOddGraphEquiv_sign i j hji σ Γ hq hq']
  have hs : (twoOddPlacementSign (σ i) (σ j) : ℝ) * (twoOddPlacementSign (σ i) (σ j) : ℝ) = 1 := by
    unfold twoOddPlacementSign
    split_ifs <;> norm_num
  push_cast
  calc
    _ = ((twoOddPlacementSign (σ i) (σ j) : ℝ) * (twoOddPlacementSign (σ i) (σ j) : ℝ)) *
        ((twoOddPlacementSign i j : ℝ) * GeometricWeights.canonicalEffectiveWeight Γ hq) := by ring
    _ = _ := by rw [hs, one_mul]

end EnvelopingIsomorphism.Deformation.KontsevichGraph.General
