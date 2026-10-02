import EnvelopingIsomorphism.Deformation.MixedRealPhysicalFaces

/-! Mixed proper-real faces have one output and two input chambers for each
nonempty physical binary subset disjoint from the distinguished vector. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedRealPhysicalIndex
open Kontsevich Configuration MixedRealPhysicalFaces
open scoped Classical BigOperators

abbrev BinarySubset {N : ℕ} (v : Fin (N+1)) := {S : Finset (Fin (N+1)) // S.Nonempty ∧ v ∉ S}

variable {N : ℕ} {v : Fin (N+1)}

def outputKey (T : BinarySubset v) : Key N v :=
  ⟨⟨T.val,0,2⟩,T.property.1,⟨v,Finset.mem_compl.mpr T.property.2⟩,by change (0 : Fin 3) ≤ 2; decide,by
    change (boundaryClusterBlock (0 : Fin 3) 2).card = if v ∈ T.val then 1 else 2
    rw [if_neg T.property.2]
    decide⟩

def inputKey (T : BinarySubset v) (r : Fin 2) : Key N v :=
  ⟨⟨T.valᶜ,Fin.castAdd 1 r,Fin.natAdd 1 r⟩,
    ⟨v,Finset.mem_compl.mpr T.property.2⟩,by simpa only [compl_compl] using T.property.1,
    by change r.val ≤ 1 + r.val; omega,by
    change (boundaryClusterBlock (Fin.castAdd 1 r) (Fin.natAdd 1 r)).card = if v ∈ T.valᶜ then 1 else 2
    rw [if_pos (Finset.mem_compl.mpr T.property.2)]
    fin_cases r <;> decide⟩

theorem input_endpoint_cases (K : Key N v) (hv : v ∈ K.S) :
    (K.l = 0 ∧ K.u = 1) ∨ (K.l = 1 ∧ K.u = 2) := by
  have h : ∀ l u : Fin 3, l ≤ u → (boundaryClusterBlock l u).card = 1 →
      (l = 0 ∧ u = 1) ∨ (l = 1 ∧ u = 2) := by decide
  exact h K.l K.u K.property.2.2.1 (by simpa only [if_pos hv] using K.property.2.2.2)

theorem output_endpoints (K : Key N v) (hv : v ∉ K.S) : K.l = 0 ∧ K.u = 2 := by
  have h : ∀ l u : Fin 3, l ≤ u → (boundaryClusterBlock l u).card = 2 → l = 0 ∧ u = 2 := by decide
  exact h K.l K.u K.property.2.2.1 (by simpa only [if_neg hv] using K.property.2.2.2)

def inputSlot (K : Key N v) (hv : v ∈ K.S) : Fin 2 :=
  ⟨K.l.val,by rcases input_endpoint_cases K hv with h | h <;> rw [h.1] <;> decide⟩

def faceIndex (K : Key N v) : BinarySubset v × Option (Fin 2) :=
  if hv : v ∈ K.S then (⟨K.Sᶜ,K.property.2.1,by simpa only [Finset.mem_compl,not_not] using hv⟩,some (inputSlot K hv))
  else (⟨K.S,K.property.1,hv⟩,none)

def keyOfIndex (p : BinarySubset v × Option (Fin 2)) : Key N v :=
  match p.2 with
  | none => outputKey p.1
  | some r => inputKey p.1 r

theorem keyOfIndex_faceIndex (K : Key N v) : keyOfIndex (faceIndex K) = K := by
  unfold faceIndex
  split_ifs with hv
  · apply Subtype.ext
    change (K.Sᶜᶜ,Fin.castAdd 1 (inputSlot K hv),Fin.natAdd 1 (inputSlot K hv)) = K.val
    refine Prod.ext (compl_compl _) (Prod.ext (Fin.ext rfl) ?_)
    apply Fin.ext
    change 1 + K.l.val = K.u.val
    rcases input_endpoint_cases K hv with h | h <;> rw [h.1,h.2] <;> decide
  · apply Subtype.ext
    exact Prod.ext rfl (Prod.ext (output_endpoints K hv).1.symm (output_endpoints K hv).2.symm)

theorem faceIndex_keyOfIndex (p : BinarySubset v × Option (Fin 2)) : faceIndex (keyOfIndex p) = p := by
  rcases p with ⟨T,r⟩
  cases r with
  | none =>
    unfold keyOfIndex faceIndex
    rw [dif_neg (show v ∉ (outputKey T).S from T.property.2)]
    exact Prod.ext (Subtype.ext rfl) rfl
  | some r =>
    change faceIndex (inputKey T r) = (T,some r)
    unfold faceIndex
    rw [dif_pos (show v ∈ (inputKey T r).S from Finset.mem_compl.mpr T.property.2)]
    apply Prod.ext
    · exact Subtype.ext (compl_compl _)
    · apply congrArg some
      exact Fin.ext rfl

def keyEquiv (v : Fin (N+1)) : Key N v ≃ BinarySubset v × Option (Fin 2) where
  toFun := faceIndex
  invFun := keyOfIndex
  left_inv := keyOfIndex_faceIndex
  right_inv := faceIndex_keyOfIndex

theorem sum_key_eq_output_inputs (f : Key N v → ℝ) :
    (∑ K : Key N v, f K) =
      ∑ T : BinarySubset v, (f (outputKey T) + f (inputKey T 0) + f (inputKey T 1)) := by
  rw [← Equiv.sum_comp (keyEquiv v).symm]
  simp only [Fintype.sum_prod_type,Fintype.sum_option,Fin.sum_univ_two]
  apply Finset.sum_congr rfl
  intro T _
  change f (outputKey T) + (f (inputKey T 0) + f (inputKey T 1)) = _
  ring

theorem nativeKind_properReal_eq_binarySubsets {H : MixedGraphProfileCarrier.VectorGraph N 2}
    (P : MixedScalarBoundaryAssembly.MixedPartition H) :
    MixedScalarBoundaryAssembly.nativeKindBoundary P .properReal =
      ∑ T : BinarySubset H.vertex,
        (physicalValue H (outputKey T) + physicalValue H (inputKey T 0) + physicalValue H (inputKey T 1)) := by
  rw [nativeKind_properReal_eq_sum_physicalValue,sum_key_eq_output_inputs]

end EnvelopingIsomorphism.Deformation.MixedRealPhysicalIndex
