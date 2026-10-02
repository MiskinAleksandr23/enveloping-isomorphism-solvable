import EnvelopingIsomorphism.Deformation.Kontsevich.MixedTwoPointTemplateWeight
import EnvelopingIsomorphism.Deformation.Kontsevich.BlockPermutationSign

/-! Literal vertex-major positions of the three mixed source templates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.MixedSourceCanonicalOrder
open KontsevichGraph.General KontsevichGraph.General.Graph
open KontsevichGraph.General.TwoVertexContraction MixedTwoPointTemplateWeight
open scoped Classical BigOperators
variable {n : ℕ} (v : Fin (n + 1))

abbrev splitArity := vertexSplitArity (fun _ : Fin (n + 1) => 2) vectorBivectorArity v

theorem splitArity_def (w : Fin (n + 2)) :
    splitArity v w = if w = vertexSplitChild v 0 then 1 else 2 := by
  have h := congrFun (MixedGraphActionSplits.actionSplitArity v) w
  exact h

theorem splitArity_add_indicator (w : Fin (n + 2)) :
    splitArity v w + (if w = vertexSplitChild v 0 then 1 else 0) = 2 := by
  rw [splitArity_def]
  split_ifs <;> omega

theorem splitArity_sum : ∑ w, splitArity v w = 2 * n + 3 := by
  have h := congrArg (fun f : Fin (n + 2) → ℕ => ∑ w, f w) (funext (splitArity_add_indicator v))
  simp only [Finset.sum_add_distrib, Fintype.sum_ite_eq', Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  omega

theorem edgePrefix_split (w : Fin (n + 2)) :
    edgePrefix (splitArity v) w + (if vertexSplitChild v 0 < w then 1 else 0) = 2 * w.val := by
  have h (u : Fin (n + 2)) :
      (if u < w then splitArity v u else 0) +
        (if u = vertexSplitChild v 0 then (if vertexSplitChild v 0 < w then 1 else 0) else 0) =
      if u < w then 2 else 0 := by
    by_cases hu : u = vertexSplitChild v 0
    · subst u
      rw [splitArity_def]
      split_ifs <;> omega
    · rw [splitArity_def]
      split_ifs <;> omega
  have hh := congrArg (fun f : Fin (n + 2) → ℕ => ∑ u, f u) (funext h)
  simpa only [edgePrefix, Finset.sum_add_distrib, Fintype.sum_ite_eq',
    ← edgePrefix_constant 2 w] using hh

def splitOrder : Fin (2 * n + 3) ≃ KontsevichGraph.General.Edge (splitArity v) :=
  (finCongr (splitArity_sum v).symm).trans (vertexMajorEdgeEquiv _)

def quotientOrder : Fin (2 * n + 2) ≃ KontsevichGraph.General.Edge (fun _ : Fin (n + 1) => 2) :=
  (finCongr (by simp; omega)).trans (vertexMajorEdgeEquiv _)

theorem quotientOrder_symm_val (e : KontsevichGraph.General.Edge (fun _ : Fin (n + 1) => 2)) :
    ((quotientOrder (n := n)).symm e).val = 2 * e.1.val + e.2.val := by
  change ((vertexMajorEdgeEquiv _).symm e).val = _
  rw [← Sigma.eta e, vertexMajorEdgeEquiv_symm_val, edgePrefix_constant]

theorem splitOrder_symm_val (e : KontsevichGraph.General.Edge (splitArity v)) :
    ((splitOrder v).symm e).val + (if vertexSplitChild v 0 < e.1 then 1 else 0) =
      2 * e.1.val + e.2.val := by
  change ((vertexMajorEdgeEquiv _).symm e).val + _ = _
  rw [← Sigma.eta e, vertexMajorEdgeEquiv_symm_val]
  simp only [Sigma.fst, Sigma.snd]
  have h := edgePrefix_split v e.1
  omega

def internalEdge (c : Fin 3) : KontsevichGraph.General.Edge vectorBivectorArity :=
  if c = 0 then ⟨0,0⟩ else ⟨1,0⟩

theorem source_internal_iff (c : Fin 3) (e : KontsevichGraph.General.Edge vectorBivectorArity) :
    (∃ a, (sourceTemplate c).target e = Sum.inl a) ↔ e = internalEdge c := by
  rcases e with ⟨w,s⟩
  fin_cases c <;> fin_cases w <;> fin_cases s <;> decide

def internalIndex (c : Fin 3) : Fin (2 * n + 3) :=
  (splitOrder v).symm (vertexSplitLocalEdge (fun _ : Fin (n + 1) => 2) vectorBivectorArity v (internalEdge c))

theorem internalIndex_val (c : Fin 3) :
    (internalIndex v c).val = 2 * v.val + if c = 0 then 0 else 1 := by
  have hh := splitOrder_symm_val v
    (vertexSplitLocalEdge (fun _ : Fin (n + 1) => 2) vectorBivectorArity v (internalEdge c))
  simp only [vertexSplitLocalEdge_slot_val, vertexSplitLocalEdge_source] at hh
  change (internalIndex v c).val + _ = _ at hh
  fin_cases c <;> simp [internalEdge, vertexSplitChild, splitExternalVertex, Fin.lt_def] at hh ⊢ <;>
    omega

def rootIndex (j : Fin 2) : Fin (2 * n + 2) := ⟨2 * v.val + j.val, by omega⟩

def legPermutation (c : Fin 3) : Equiv.Perm (Fin (2 * n + 2)) :=
  if c = 2 then Equiv.swap (rootIndex v 0) (rootIndex v 1) else Equiv.refl _

def fullLegPermutation (c : Fin 3) : Equiv.Perm (Fin (2 * n + 3)) :=
  if c = 2 then Equiv.swap (rootIndex v 0).succ (rootIndex v 1).succ else Equiv.refl _

theorem fullLegPermutation_zero (c : Fin 3) : fullLegPermutation v c 0 = 0 := by
  have hz (j : Fin (2 * n + 2)) : (0 : Fin (2 * n + 3)) ≠ j.succ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  by_cases hc : c = 2 <;> simp [fullLegPermutation, hc, Equiv.swap_apply_def, hz]

theorem fullLegPermutation_succ (c : Fin 3) (j : Fin (2 * n + 2)) :
    fullLegPermutation v c j.succ = (legPermutation v c j).succ := by
  by_cases hc : c = 2 <;> simp [fullLegPermutation, legPermutation, hc, Equiv.swap_apply_def]
  split_ifs <;> rfl

def canonicalPermutation (c : Fin 3) : Equiv.Perm (Fin (2 * n + 3)) :=
  (fullLegPermutation v c).trans (Fin.cycleRange (internalIndex v c)).symm

theorem canonicalPermutation_zero (c : Fin 3) : canonicalPermutation v c 0 = internalIndex v c := by
  simp [canonicalPermutation, fullLegPermutation_zero]

theorem canonicalPermutation_succ (c : Fin 3) (j : Fin (2 * n + 2)) :
    canonicalPermutation v c j.succ = (internalIndex v c).succAbove (legPermutation v c j) := by
  simp [canonicalPermutation, fullLegPermutation_succ]

/-- The three fixed source templates have the actual signs plus, minus,
plus in the native source-major ordering. -/
theorem canonicalPermutation_sign (c : Fin 3) :
    (canonicalPermutation v c).sign = if c = 1 then (-1 : ℤˣ) else 1 := by
  have hne : (rootIndex v 0).succ ≠ (rootIndex v 1).succ := by
    simp [Fin.ext_iff, rootIndex]
  rw [canonicalPermutation, Equiv.Perm.sign_trans, Equiv.Perm.sign_symm, Fin.sign_cycleRange,
    internalIndex_val, pow_add, pow_mul]
  fin_cases c <;> simp [fullLegPermutation, Equiv.Perm.sign_swap hne]

def templateEmbedding (c : Fin 3) :
    KontsevichGraph.General.Edge (fun _ : Fin (n + 1) => 2) ↪ KontsevichGraph.General.Edge (splitArity v) :=
  (sourceTemplate c).vertexSplitOldEdge (sourceLeg c) (fun j => (source_leg c _ j).mpr rfl)
    (fun _ : Fin (n + 1) => 2) v rfl

@[simp] theorem templateEmbedding_outside (c : Fin 3)
    (e : VertexSplitOutsideEdge (fun _ : Fin (n + 1) => 2) v) :
    templateEmbedding v c e.val = vertexSplitOutsideEdge _ _ v e :=
  vertexSplitOldEdge_outside _ _ _ e

@[simp] theorem templateEmbedding_root (c : Fin 3) (j : Fin 2) :
    templateEmbedding v c ⟨v,j⟩ = vertexSplitLocalEdge _ _ v (sourceLeg c j) :=
  vertexSplitOldEdge_root _ _ _ j

private theorem legPermutation_outside (c : Fin 3)
    (e : VertexSplitOutsideEdge (fun _ : Fin (n + 1) => 2) v) :
    legPermutation v c ((quotientOrder (n := n)).symm e.val) =
      (quotientOrder (n := n)).symm e.val := by
  have hne (j : Fin 2) : (quotientOrder (n := n)).symm e.val ≠ rootIndex v j := by
    intro he
    have hh := congrArg Fin.val he
    rw [quotientOrder_symm_val] at hh
    have hv : e.val.1.val ≠ v.val := fun h => e.property (Fin.ext h)
    have hs := e.val.2.isLt
    have hj := j.isLt
    dsimp [rootIndex] at hh
    omega
  by_cases hc : c = 2 <;> simp [legPermutation, hc, Equiv.swap_apply_def, hne]

private theorem canonicalPermutation_outside (c : Fin 3)
    (e : VertexSplitOutsideEdge (fun _ : Fin (n + 1) => 2) v) :
    canonicalPermutation v c ((quotientOrder (n := n)).symm e.val).succ =
      (splitOrder v).symm (templateEmbedding v c e.val) := by
  rw [canonicalPermutation_succ, legPermutation_outside, templateEmbedding_outside]
  apply Fin.ext
  have hh := splitOrder_symm_val v (vertexSplitOutsideEdge _ _ v e)
  simp only [vertexSplitOutsideEdge_slot_val, vertexSplitOutsideEdge_source] at hh
  have hv : e.val.1.val ≠ v.val := fun h => e.property (Fin.ext h)
  have hs : e.val.2.val < 2 := e.val.2.isLt
  simp only [Fin.succAbove, apply_ite Fin.val, Fin.val_castSucc,
    internalIndex_val, quotientOrder_symm_val, Fin.val_succ, Fin.lt_def,
    vertexSplitChild, splitExternalVertex, vertexSplitOldEmbedding,
    splitExternalEmbedding, Fin.val_cast] at hh ⊢
  split_ifs at hh ⊢ <;> omega

private theorem legPermutation_root (c : Fin 3) (j : Fin 2) :
    legPermutation v c (rootIndex v j) = rootIndex v (if c = 2 then Equiv.swap 0 1 j else j) := by
  have hr (a b : Fin 2) : rootIndex v a = rootIndex v b ↔ a = b := by
    simp [rootIndex, Fin.ext_iff]
  fin_cases c <;> fin_cases j <;> simp [legPermutation, Equiv.swap_apply_def, hr]

private theorem canonicalPermutation_root (c : Fin 3) (j : Fin 2) :
    canonicalPermutation v c ((quotientOrder (n := n)).symm ⟨v,j⟩).succ =
      (splitOrder v).symm (templateEmbedding v c ⟨v,j⟩) := by
  have hj : (quotientOrder (n := n)).symm ⟨v,j⟩ = rootIndex v j := by
    apply Fin.ext
    rw [quotientOrder_symm_val]
    rfl
  rw [hj, canonicalPermutation_succ, legPermutation_root, templateEmbedding_root]
  apply Fin.ext
  have hh := splitOrder_symm_val v (vertexSplitLocalEdge _ _ v (sourceLeg c j))
  simp only [vertexSplitLocalEdge_slot_val, vertexSplitLocalEdge_source] at hh
  have hsource : (sourceLeg c j).1.val = if c = 0 then 1 else if j.val = (if c = 2 then 1 else 0) then 0 else 1 := by
    fin_cases c <;> fin_cases j <;> decide
  have hslot : (sourceLeg c j).2.val = if c = 0 then j.val else if j.val = (if c = 2 then 1 else 0) then 0 else 1 := by
    fin_cases c <;> fin_cases j <;> decide
  have hchild (a : Fin 2) : (vertexSplitChild v a).val = v.val + a.val := by
    fin_cases a <;> simp [vertexSplitChild, splitExternalVertex]
  have hroot (k : Fin 2) : (rootIndex v k).val = 2 * v.val + k.val := rfl
  simp only [Fin.succAbove, apply_ite Fin.val, Fin.val_castSucc, Fin.val_succ,
    Fin.lt_def, hroot, internalIndex_val]
  simp only [Fin.lt_def, hchild, hsource, hslot] at hh
  fin_cases c <;> fin_cases j <;>
    norm_num [rootIndex, Fin.ext_iff] at hh ⊢ <;> first | omega | (rw [hh]; ring)

/-- This permutation really enumerates the internal arrow first, followed
by all original quotient slots in canonical vertex-major order. -/
theorem canonicalPermutation_embedding (c : Fin 3) (j : Fin (2 * n + 2)) :
    splitOrder v (canonicalPermutation v c j.succ) =
      templateEmbedding v c (quotientOrder j) := by
  apply (splitOrder v).symm.injective
  rw [Equiv.symm_apply_apply]
  let e := quotientOrder j
  have hj : j = (quotientOrder (n := n)).symm e := (Equiv.symm_apply_apply _ _).symm
  rw [hj]
  obtain ⟨f,hf⟩ := (vertexSplitOldEdgeEquiv (fun _ : Fin (n + 1) => 2) v rfl).symm.surjective e
  rw [← hf]
  rcases f with f | k
  · simpa only [vertexSplitOldEdgeEquiv_symm_outside, Equiv.apply_symm_apply] using
      canonicalPermutation_outside v c f
  · simpa only [vertexSplitOldEdgeEquiv_symm_root, Equiv.apply_symm_apply, Fin.cast_eq_self] using
      canonicalPermutation_root v c k

end EnvelopingIsomorphism.Deformation.Kontsevich.MixedSourceCanonicalOrder
