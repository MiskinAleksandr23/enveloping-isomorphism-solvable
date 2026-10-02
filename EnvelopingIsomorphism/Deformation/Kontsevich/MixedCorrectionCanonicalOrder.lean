import EnvelopingIsomorphism.Deformation.Kontsevich.MixedSourceCanonicalOrder
import EnvelopingIsomorphism.Deformation.Kontsevich.MixedProfileEdgePrefixes

/-! Canonical edge order for the two-bivector correction with its retained
exterior vector. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.MixedCorrectionCanonicalOrder
open KontsevichGraph.General KontsevichGraph.General.Graph
open KontsevichGraph.General.TwoVertexContraction MixedGraphCorrectionProfiles
open BinaryVertexContraction
open scoped Classical BigOperators
private theorem offset_cancel {x y z b : ℕ} (hx : x + b = 2 * z)
    (hy : y + b = 2 * (z + 1) + 1) : x + 2 + 1 = y := by omega

variable {n : ℕ} (p : Placement n)

abbrev dim := GraphForms.dimension (n + 1) 2
abbrev arity := twoOddArity p.1 p.2
abbrev expandedArity := vertexSplitArity (arity p) bivectorArity p.2

theorem expandedArity_sum : ∑ w, expandedArity p w = dim (n := n) + 1 := by
  rw [show expandedArity p = Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 (expandedVector p) from splitArity p]
  have h := Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 1 (expandedVector p)
  exact h.trans (by dsimp [dim, GraphForms.dimension]; omega)

def splitOrder : Fin (dim (n := n) + 1) ≃ KontsevichGraph.General.Edge (expandedArity p) :=
  (finCongr (expandedArity_sum p).symm).trans (vertexMajorEdgeEquiv _)

def quotientOrder : Fin (dim (n := n)) ≃ KontsevichGraph.General.Edge (arity p) :=
  GeometricWeights.canonicalOrder (edgeCount p)

def rootIndex (j : Fin 3) : Fin (dim (n := n)) :=
  (quotientOrder p).symm ⟨p.2.val, Fin.cast (selectedArity p) j⟩

theorem quotientOrder_symm_val_add (e : KontsevichGraph.General.Edge (arity p)) :
    ((quotientOrder p).symm e).val + (if p.1 < e.1 then 1 else 0) =
      2 * e.1.val + (if p.2.val < e.1 then 1 else 0) + e.2.val :=
  MixedProfileEdgePrefixes.twoOddOrder_symm_val_add p.1 p.2.val p.2.property e

theorem rootIndex_val (j : Fin 3) :
    (rootIndex p j).val = edgePrefix (arity p) p.2.val + j.val := by
  change ((vertexMajorEdgeEquiv (arity p)).symm ⟨p.2.val,Fin.cast (selectedArity p) j⟩).val = _
  rw [vertexMajorEdgeEquiv_symm_val]
  rfl

theorem splitOrder_symm_val_add (e : KontsevichGraph.General.Edge (expandedArity p)) :
    ((splitOrder p).symm e).val + (if expandedVector p < e.1 then 1 else 0) =
      2 * e.1.val + e.2.val := by
  change ((vertexMajorEdgeEquiv (expandedArity p)).symm e).val + _ = _
  rw [← Sigma.eta e, vertexMajorEdgeEquiv_symm_val]
  simp only [Sigma.fst, Sigma.snd]
  have hpref : edgePrefix (expandedArity p) e.1 + (if expandedVector p < e.1 then 1 else 0) = 2 * e.1.val := by
    have heq := congrArg (fun q : Fin (n + 3) → ℕ => edgePrefix q e.1) (splitArity p)
    change edgePrefix (expandedArity p) e.1 = _ at heq
    rw [heq]
    exact MixedProfileEdgePrefixes.edgePrefix_vector_add (expandedVector p) e.1
  omega

theorem rootIndex_injective : Function.Injective (rootIndex p) := by
  intro j k h
  have he := (quotientOrder p).symm.injective h
  have hh := congrArg (fun e : KontsevichGraph.General.Edge (arity p) => e.2.val) he
  exact Fin.ext hh

def legPermutation (c : Fin 2) : Equiv.Perm (Fin (dim (n := n))) :=
  if c = 0 then (Equiv.swap (rootIndex p 0) (rootIndex p 1)).trans
    (Equiv.swap (rootIndex p 0) (rootIndex p 2)) else Equiv.refl _

def fullLegPermutation (c : Fin 2) : Equiv.Perm (Fin (dim (n := n) + 1)) :=
  if c = 0 then (Equiv.swap (rootIndex p 0).succ (rootIndex p 1).succ).trans
    (Equiv.swap (rootIndex p 0).succ (rootIndex p 2).succ) else Equiv.refl _

theorem fullLegPermutation_zero (c : Fin 2) : fullLegPermutation p c 0 = 0 := by
  have hz (j : Fin (dim (n := n))) : (0 : Fin (dim (n := n) + 1)) ≠ j.succ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  by_cases hc : c = 0 <;> simp [fullLegPermutation, hc, Equiv.swap_apply_def, hz]

theorem fullLegPermutation_succ (c : Fin 2) (j : Fin (dim (n := n))) :
    fullLegPermutation p c j.succ = (legPermutation p c j).succ := by
  have hswap (a b k : Fin (dim (n := n))) :
      Equiv.swap a.succ b.succ k.succ = (Equiv.swap a b k).succ := by
    simp only [Equiv.swap_apply_def, Fin.succ_inj]
    split_ifs <;> rfl
  by_cases hc : c = 0
  · simp only [fullLegPermutation, legPermutation, if_pos hc, Equiv.trans_apply, hswap]
  · simp only [fullLegPermutation, legPermutation, if_neg hc, Equiv.refl_apply]

theorem fullLegPermutation_sign (c : Fin 2) : (fullLegPermutation p c).sign = 1 := by
  have h01 : (rootIndex p 0).succ ≠ (rootIndex p 1).succ := by
    intro he
    exact (by decide : (0 : Fin 3) ≠ 1) (rootIndex_injective p (Fin.succ_inj.mp he))
  have h02 : (rootIndex p 0).succ ≠ (rootIndex p 2).succ := by
    intro he
    exact (by decide : (0 : Fin 3) ≠ 2) (rootIndex_injective p (Fin.succ_inj.mp he))
  by_cases hc : c = 0 <;>
    simp [fullLegPermutation, hc, Equiv.Perm.sign_trans, Equiv.Perm.sign_swap h01, Equiv.Perm.sign_swap h02]

def internalIndex (c : Fin 2) : Fin (dim (n := n) + 1) :=
  (splitOrder p).symm (vertexSplitLocalEdge (arity p) bivectorArity p.2 ⟨c,0⟩)

def canonicalPermutation (c : Fin 2) : Equiv.Perm (Fin (dim (n := n) + 1)) :=
  (fullLegPermutation p c).trans (Fin.cycleRange (internalIndex p c)).symm

theorem canonicalPermutation_zero (c : Fin 2) : canonicalPermutation p c 0 = internalIndex p c := by
  simp [canonicalPermutation, fullLegPermutation_zero]

theorem canonicalPermutation_succ (c : Fin 2) (j : Fin (dim (n := n))) :
    canonicalPermutation p c j.succ = (internalIndex p c).succAbove (legPermutation p c j) := by
  simp [canonicalPermutation, fullLegPermutation_succ]

theorem canonicalPermutation_sign_index (c : Fin 2) :
    (canonicalPermutation p c).sign = (-1 : ℤˣ) ^ (internalIndex p c).val := by
  rw [canonicalPermutation, Equiv.Perm.sign_trans, fullLegPermutation_sign, mul_one,
    Equiv.Perm.sign_symm, Fin.sign_cycleRange]

theorem oldEmbedding_val (w : Fin (n + 2)) :
    (vertexSplitOldEmbedding p.2.val w).val = if w < p.2.val then w.val else w.val + 1 := by
  simp only [vertexSplitOldEmbedding, splitExternalEmbedding, Fin.succAbove, apply_ite Fin.val,
    Fin.val_castSucc, Fin.val_succ, Fin.lt_def]

theorem child_val (c : Fin 2) : (vertexSplitChild p.2.val c).val = p.2.val.val + c.val := by
  fin_cases c <;> simp [vertexSplitChild, splitExternalVertex]

theorem expandedVector_lt_child (c : Fin 2) : expandedVector p < vertexSplitChild p.2.val c ↔ p.1 < p.2.val := by
  have hv : p.1.val ≠ p.2.val.val := fun h => p.2.property.symm (Fin.ext h)
  change (vertexSplitOldEmbedding p.2.val p.1).val < (vertexSplitChild p.2.val c).val ↔ p.1.val < p.2.val.val
  rw [oldEmbedding_val, child_val]
  simp only [Fin.lt_def]
  have hc := c.isLt
  split_ifs <;> omega

theorem internalIndex_val (c : Fin 2) :
    (internalIndex p c).val = edgePrefix (arity p) p.2.val + 2 * c.val := by
  have hh := splitOrder_symm_val_add p (vertexSplitLocalEdge (arity p) bivectorArity p.2.val ⟨c,0⟩)
  simp only [vertexSplitLocalEdge_slot_val, vertexSplitLocalEdge_source] at hh
  simp only [expandedVector_lt_child] at hh
  have hpref := MixedProfileEdgePrefixes.twoOdd_rootPrefix_add p.1 p.2.val p.2.property
  have hchild : (vertexSplitChild p.2.val c).val = p.2.val.val + c.val := by
    fin_cases c <;> simp [vertexSplitChild, splitExternalVertex]
  simp only [hchild] at hh
  change (internalIndex p c).val + _ = _ at hh
  change edgePrefix (arity p) p.2.val + _ = _ at hpref
  have hz : (0 : Fin (bivectorArity c)).val = 0 := rfl
  simp only [hz, add_zero] at hh
  omega

/-- The retained vector contributes its actual odd prefix. -/
theorem canonicalPermutation_sign (c : Fin 2) :
    (canonicalPermutation p c).sign = -twoOddPlacementSign p.1 p.2.val := by
  rw [canonicalPermutation_sign_index, internalIndex_val, pow_add, pow_mul]
  norm_num only [even_two, Even.neg_pow, one_pow, mul_one]
  exact MixedProfileEdgePrefixes.twoOdd_rootPrefix_sign p.1 p.2.val p.2.property

def templateEmbedding (c : Fin 2) :
    KontsevichGraph.General.Edge (arity p) ↪ KontsevichGraph.General.Edge (expandedArity p) :=
  (canonicalTemplate c).vertexSplitOldEdge (canonicalLeg c)
    (fun j => (MixedTwoPointTemplateWeight.correction_leg c _ j).mpr rfl)
    (arity p) p.2.val (selectedArity p).symm

@[simp] theorem templateEmbedding_outside (c : Fin 2) (e : VertexSplitOutsideEdge (arity p) p.2.val) :
    templateEmbedding p c e.val = vertexSplitOutsideEdge _ _ p.2.val e :=
  vertexSplitOldEdge_outside _ _ _ e

@[simp] theorem templateEmbedding_root (c : Fin 2) (j : Fin 3) :
    templateEmbedding p c ⟨p.2.val,Fin.cast (selectedArity p) j⟩ =
      vertexSplitLocalEdge _ _ p.2.val (canonicalLeg c j) :=
  vertexSplitOldEdge_root _ _ _ j

theorem legPermutation_outside (c : Fin 2) (e : VertexSplitOutsideEdge (arity p) p.2.val) :
    legPermutation p c ((quotientOrder p).symm e.val) = (quotientOrder p).symm e.val := by
  have hne (j : Fin 3) : (quotientOrder p).symm e.val ≠ rootIndex p j := by
    intro he
    have hh := (quotientOrder p).symm.injective he
    exact e.property (congrArg Sigma.fst hh)
  by_cases hc : c = 0 <;> simp [legPermutation, hc, Equiv.swap_apply_def, hne]

def rootRotate (c : Fin 2) (j : Fin 3) : Fin 3 := if c = 0 then ![1,2,0] j else j

theorem legPermutation_root (c : Fin 2) (j : Fin 3) :
    legPermutation p c (rootIndex p j) = rootIndex p (rootRotate c j) := by
  have hr (a b : Fin 3) : rootIndex p a = rootIndex p b ↔ a = b := (rootIndex_injective p).eq_iff
  fin_cases c <;> fin_cases j <;> simp [legPermutation, rootRotate, Equiv.swap_apply_def, hr]

theorem expandedVector_lt_old (w : Fin (n + 2)) :
    expandedVector p < vertexSplitOldEmbedding p.2.val w ↔ p.1 < w := by
  change (vertexSplitOldEmbedding p.2.val p.1).val < (vertexSplitOldEmbedding p.2.val w).val ↔ p.1.val < w.val
  rw [oldEmbedding_val, oldEmbedding_val]
  simp only [Fin.lt_def]
  split_ifs <;> omega

private theorem canonicalPermutation_outside (c : Fin 2) (e : VertexSplitOutsideEdge (arity p) p.2.val) :
    canonicalPermutation p c ((quotientOrder p).symm e.val).succ =
      (splitOrder p).symm (templateEmbedding p c e.val) := by
  rw [canonicalPermutation_succ, legPermutation_outside, templateEmbedding_outside]
  apply Fin.ext
  have hh := splitOrder_symm_val_add p (vertexSplitOutsideEdge (arity p) bivectorArity p.2.val e)
  simp only [vertexSplitOutsideEdge_slot_val, vertexSplitOutsideEdge_source, expandedVector_lt_old,
    oldEmbedding_val] at hh
  have he := quotientOrder_symm_val_add p e.val
  have hpref := MixedProfileEdgePrefixes.twoOdd_rootPrefix_add p.1 p.2.val p.2.property
  change edgePrefix (arity p) p.2.val + _ = _ at hpref
  have hv : e.val.1.val ≠ p.2.val.val := fun h => e.property (Fin.ext h)
  have hs : e.val.2.val < 2 := by
    have h := e.val.2.isLt
    simp only [arity, twoOddArity, if_neg e.property] at h
    split_ifs at h <;> omega
  have hs' : e.val.2.val < if e.val.1.val = p.1.val then 1 else 2 := by
    have h := e.val.2.isLt
    simpa only [arity, twoOddArity, Fin.ext_iff, if_neg hv] using h
  have hc := c.isLt
  simp only [Fin.succAbove, apply_ite Fin.val, Fin.val_castSucc, Fin.val_succ,
    internalIndex_val, Fin.lt_def] at hh he hpref ⊢
  split_ifs at hh he hpref hs' ⊢ <;> omega

private theorem canonicalPermutation_root (c : Fin 2) (j : Fin 3) :
    canonicalPermutation p c (rootIndex p j).succ =
      (splitOrder p).symm (templateEmbedding p c ⟨p.2.val,Fin.cast (selectedArity p) j⟩) := by
  rw [canonicalPermutation_succ, legPermutation_root, templateEmbedding_root]
  apply Fin.ext
  have hh := splitOrder_symm_val_add p (vertexSplitLocalEdge (arity p) bivectorArity p.2.val (canonicalLeg c j))
  simp only [vertexSplitLocalEdge_slot_val, vertexSplitLocalEdge_source,
    expandedVector_lt_child, child_val] at hh
  have hpref := MixedProfileEdgePrefixes.twoOdd_rootPrefix_add p.1 p.2.val p.2.property
  change edgePrefix (arity p) p.2.val + _ = _ at hpref
  have hs : (canonicalLeg c j).1.val = if j = 2 then c.val else 1 - c.val := by
    fin_cases c <;> fin_cases j <;> decide
  have ht : (canonicalLeg c j).2.val = if j = 0 then 0 else 1 := by
    fin_cases c <;> fin_cases j <;> decide
  simp only [hs, ht] at hh
  simp only [Fin.succAbove, apply_ite Fin.val, Fin.val_castSucc, Fin.val_succ,
    internalIndex_val, rootIndex_val, Fin.lt_def]
  fin_cases c <;> fin_cases j <;>
    norm_num [rootRotate, Fin.ext_iff] at hh ⊢ <;> first | omega | exact offset_cancel hpref hh

/-- Actual internal-first enumeration with the receiver's two quotient
slots and the sender's remaining slot in canonical order. -/
theorem canonicalPermutation_embedding (c : Fin 2) (j : Fin (dim (n := n))) :
    splitOrder p (canonicalPermutation p c j.succ) = templateEmbedding p c (quotientOrder p j) := by
  apply (splitOrder p).symm.injective
  rw [Equiv.symm_apply_apply]
  let e := quotientOrder p j
  have hj : j = (quotientOrder p).symm e := (Equiv.symm_apply_apply _ _).symm
  rw [hj]
  obtain ⟨f,hf⟩ := (vertexSplitOldEdgeEquiv (arity p) p.2.val (selectedArity p).symm).symm.surjective e
  rw [← hf]
  rcases f with f | k
  · simpa only [vertexSplitOldEdgeEquiv_symm_outside, Equiv.apply_symm_apply] using
      canonicalPermutation_outside p c f
  · simpa only [vertexSplitOldEdgeEquiv_symm_root, Equiv.apply_symm_apply, rootIndex] using
      canonicalPermutation_root p c k

end EnvelopingIsomorphism.Deformation.Kontsevich.MixedCorrectionCanonicalOrder
