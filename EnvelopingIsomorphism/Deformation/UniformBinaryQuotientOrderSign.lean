import EnvelopingIsomorphism.Deformation.UniformBinaryQuotientEdges
import EnvelopingIsomorphism.Deformation.Kontsevich.BlockPermutationSign

/-! Canonical source-major ordering of the one-arrow binary contraction.
The internal-first ordering has precisely the original sender-slot sign. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.UniformBinaryQuotientOrderSign
open KontsevichGraph.General KontsevichGraph.General.Graph
open KontsevichGraph.General.TwoVertexContraction UniformBinaryGraphs UniformCurvatureSplits
open UniformBinaryContraction BinaryVertexContraction UniformBinaryQuotientEdges
open Kontsevich
open scoped Classical BigOperators
variable {n : ℕ} (v : Fin (n + 1))

abbrev D := GraphForms.dimension n 3

def binaryOrder : Fin (D (n := n) + 1) ≃ Edge (fun _ : Fin (n + 2) => 2) :=
  (finCongr (by simp [D, GraphForms.dimension]; omega)).trans (vertexMajorEdgeEquiv _)

def quotientCanonicalOrder : Fin (D (n := n)) ≃ Edge (Arity v) :=
  GeometricWeights.canonicalOrder (Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 3 v)

theorem binaryOrder_symm_val (w : Fin (n + 2)) (j : Fin 2) :
    ((binaryOrder (n := n)).symm ⟨w,j⟩).val = 2 * w.val + j.val := by
  change ((vertexMajorEdgeEquiv (fun _ : Fin (n + 2) => 2)).symm ⟨w,j⟩).val = _
  rw [vertexMajorEdgeEquiv_symm_val, edgePrefix_constant]

theorem edgePrefix_curvature (w : Fin (n + 1)) :
    edgePrefix (Arity v) w = 2 * w.val + if v < w then 1 else 0 := by
  have hq (u : Fin (n + 1)) : Arity v u = 2 + if u = v then 1 else 0 := by
    by_cases hu : u = v <;> simp [Arity, Gauge.PlacedMixedGraphTaylorCoefficients.arities, hu]
  have ht (u : Fin (n + 1)) :
      (if u < w then Arity v u else 0) =
        (if u < w then 2 else 0) + (if u = v then (if v < w then 1 else 0) else 0) := by
    by_cases huv : u = v
    · subst u
      by_cases hvw : v < w <;> simp [hq, hvw]
    · simp [hq, huv]
  simp only [edgePrefix, ht, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact congrArg (fun t => t + if v < w then 1 else 0) (edgePrefix_constant 2 w)

theorem quotientCanonicalOrder_symm_val (e : Edge (Arity v)) :
    ((quotientCanonicalOrder v).symm e).val = 2 * e.1.val + (if v < e.1 then 1 else 0) + e.2.val := by
  change ((vertexMajorEdgeEquiv (Arity v)).symm e).val = _
  rw [← Sigma.eta e, vertexMajorEdgeEquiv_symm_val, edgePrefix_curvature]

/-- The three quotient root slots occupy this consecutive block. -/
def rootIndex (j : Fin 3) : Fin (D (n := n)) := ⟨2 * v.val + j.val, by
  have hv := v.isLt
  have hj := j.isLt
  dsimp [D, GraphForms.dimension]
  omega⟩

def legPermutation (c : Fin 2) : Equiv.Perm (Fin (D (n := n))) :=
  if c = 0 then (Equiv.swap (rootIndex v 0) (rootIndex v 1)).trans
    (Equiv.swap (rootIndex v 0) (rootIndex v 2)) else Equiv.refl _

def fullLegPermutation (c : Fin 2) : Equiv.Perm (Fin (D (n := n) + 1)) :=
  if c = 0 then (Equiv.swap (rootIndex v 0).succ (rootIndex v 1).succ).trans
    (Equiv.swap (rootIndex v 0).succ (rootIndex v 2).succ) else Equiv.refl _

@[simp] theorem fullLegPermutation_zero (c : Fin 2) : fullLegPermutation v c 0 = 0 := by
  have hz (j : Fin (D (n := n))) : (0 : Fin (D (n := n) + 1)) ≠ j.succ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  by_cases hc : c = 0 <;> simp [fullLegPermutation, hc, Equiv.swap_apply_def, hz]

@[simp] theorem fullLegPermutation_succ (c : Fin 2) (j : Fin (D (n := n))) :
    fullLegPermutation v c j.succ = (legPermutation v c j).succ := by
  have hswap (p q k : Fin (D (n := n))) :
      Equiv.swap p.succ q.succ k.succ = (Equiv.swap p q k).succ := by
    simp only [Equiv.swap_apply_def, Fin.succ_inj]
    split_ifs <;> rfl
  by_cases hc : c = 0
  · simp only [fullLegPermutation, legPermutation, if_pos hc, Equiv.trans_apply, hswap]
  · simp only [fullLegPermutation, legPermutation, if_neg hc, Equiv.refl_apply]

theorem fullLegPermutation_sign (c : Fin 2) : (fullLegPermutation v c).sign = 1 := by
  have h01 : (rootIndex v 0).succ ≠ (rootIndex v 1).succ := by
    intro h
    have := congrArg Fin.val h
    simp [rootIndex] at this
  have h02 : (rootIndex v 0).succ ≠ (rootIndex v 2).succ := by
    intro h
    have := congrArg Fin.val h
    simp [rootIndex] at this
  by_cases hc : c = 0 <;>
    simp [fullLegPermutation, hc, Equiv.Perm.sign_trans, Equiv.Perm.sign_swap h01, Equiv.Perm.sign_swap h02]

def internalIndex (c s : Fin 2) : Fin (D (n := n) + 1) :=
  (binaryOrder (n := n)).symm ⟨vertexSplitChild v c,s⟩

def canonicalPermutation (c s : Fin 2) : Equiv.Perm (Fin (D (n := n) + 1)) :=
  (fullLegPermutation v c).trans (Fin.cycleRange (internalIndex v c s)).symm

@[simp] theorem canonicalPermutation_zero (c s : Fin 2) :
    canonicalPermutation v c s 0 = internalIndex v c s := by
  simp [canonicalPermutation]

@[simp] theorem canonicalPermutation_succ (c s : Fin 2) (j : Fin (D (n := n))) :
    canonicalPermutation v c s j.succ = (internalIndex v c s).succAbove (legPermutation v c j) := by
  simp [canonicalPermutation]

/-- Moving the internal edge first crosses an even number of complete
binary source slots; the receiver/sender root reordering is an even 3-cycle. -/
theorem canonicalPermutation_sign (c s : Fin 2) :
    (canonicalPermutation v c s).sign = (-1 : ℤˣ) ^ s.val := by
  rw [canonicalPermutation, Equiv.Perm.sign_trans, fullLegPermutation_sign, mul_one,
    Equiv.Perm.sign_symm, Fin.sign_cycleRange]
  rw [internalIndex, binaryOrder_symm_val, pow_add, pow_mul]
  norm_num

variable (H : BinaryGraph (n + 2) 3) (c s : Fin 2)
  (hi : UniqueInternalAt v H c s) (hd : CoarseDistinct v H) (hx : ExitsDistinctAt v H c s)

theorem originalSlots_outside (e : VertexSplitOutsideEdge (Arity v) v) :
    originalSlots v c s (vertexSplitOutsideEdge (Arity v) bivectorArity v e) =
      ⟨vertexSplitOldEmbedding v e.val.1,
        Fin.cast (by simp [Arity, Gauge.PlacedMixedGraphTaylorCoefficients.arities, e.property]) e.val.2⟩ := by
  apply Sigma.ext (vertexSplitOutsideEdge_source (Arity v) bivectorArity v e)
  apply heq_of_eq
  change (slotPermutation v c s (vertexSplitOutsideEdge (Arity v) bivectorArity v e).1)
    (Fin.cast (congrFun (vertexSplitArity_two v) (vertexSplitOutsideEdge (Arity v) bivectorArity v e).1)
      (vertexSplitOutsideEdge (Arity v) bivectorArity v e).2) = _
  have hslot : Fin.cast (congrFun (vertexSplitArity_two v) (vertexSplitOutsideEdge (Arity v) bivectorArity v e).1)
      (vertexSplitOutsideEdge (Arity v) bivectorArity v e).2 =
      Fin.cast (by simp [Arity, Gauge.PlacedMixedGraphTaylorCoefficients.arities, e.property]) e.val.2 := by
    apply Fin.ext
    exact vertexSplitOutsideEdge_slot_val (Arity v) bivectorArity v e
  rw [hslot, vertexSplitOutsideEdge_source]
  simp only [slotPermutation, if_neg (vertexSplitOld_ne_child v e.val.1 e.property c), Equiv.refl_apply]

@[simp] theorem embedding_outside (e : VertexSplitOutsideEdge (Arity v) v) :
    embedding v H c s hi hd hx e.val =
      ⟨vertexSplitOldEmbedding v e.val.1,
        Fin.cast (by simp [Arity, Gauge.PlacedMixedGraphTaylorCoefficients.arities, e.property]) e.val.2⟩ := by
  change originalSlots v c s (splitEmbedding v H c s hi hd hx e.val) = _
  rw [splitEmbedding_outside, originalSlots_outside]

@[simp] theorem embedding_root (j : Fin 3) :
    embedding v H c s hi hd hx ⟨v, Fin.cast (selectedArity v) j⟩ =
      ⟨vertexSplitChild v (localEdgePermutation c s (canonicalLeg c j)).1,
        (localEdgePermutation c s (canonicalLeg c j)).2⟩ := by
  change originalSlots v c s (splitEmbedding v H c s hi hd hx _) = _
  rw [splitEmbedding_root, originalSlots_local]

private theorem legPermutation_outside (e : VertexSplitOutsideEdge (Arity v) v) :
    legPermutation v c ((quotientCanonicalOrder v).symm e.val) =
      (quotientCanonicalOrder v).symm e.val := by
  have hslot : e.val.2.val < 2 := by
    have := e.val.2.isLt
    simpa [Arity, Gauge.PlacedMixedGraphTaylorCoefficients.arities, e.property] using this
  have hne (j : Fin 3) : (quotientCanonicalOrder v).symm e.val ≠ rootIndex v j := by
    intro h
    have hh := congrArg Fin.val h
    rw [quotientCanonicalOrder_symm_val] at hh
    have hv : e.val.1.val ≠ v.val := fun h => e.property (Fin.ext h)
    have hj := j.isLt
    dsimp [rootIndex] at hh
    split_ifs at hh <;> simp only [Fin.lt_def] at * <;> omega
  by_cases hc : c = 0 <;> simp [legPermutation, hc, Equiv.swap_apply_def, hne]

private theorem canonicalPermutation_outside (e : VertexSplitOutsideEdge (Arity v) v) :
    canonicalPermutation v c s ((quotientCanonicalOrder v).symm e.val).succ =
      (binaryOrder (n := n)).symm (embedding v H c s hi hd hx e.val) := by
  rw [canonicalPermutation_succ, legPermutation_outside, embedding_outside]
  apply Fin.ext
  rw [binaryOrder_symm_val]
  have hslot : e.val.2.val < 2 := by
    have := e.val.2.isLt
    simpa [Arity, Gauge.PlacedMixedGraphTaylorCoefficients.arities, e.property] using this
  have hv : e.val.1.val ≠ v.val := fun h => e.property (Fin.ext h)
  have hs := s.isLt
  simp only [Fin.succAbove, apply_ite, Fin.lt_def, Fin.val_castSucc, internalIndex,
    binaryOrder_symm_val, vertexSplitOldEmbedding, splitExternalEmbedding,
    quotientCanonicalOrder_symm_val, vertexSplitChild, splitExternalVertex,
    Fin.val_succ, Fin.val_cast]
  split_ifs <;> omega

private def rootRotate (c : Fin 2) (j : Fin 3) : Fin 3 :=
  if c = 0 then ![1,2,0] j else j

private theorem legPermutation_root (j : Fin 3) :
    legPermutation v c (rootIndex v j) = rootIndex v (rootRotate c j) := by
  have hr (k l : Fin 3) : rootIndex v k = rootIndex v l ↔ k = l := by
    constructor
    · intro h
      apply Fin.ext
      have := congrArg Fin.val h
      dsimp [rootIndex] at this
      omega
    · rintro rfl; rfl
  fin_cases c <;> fin_cases j <;> simp [legPermutation, rootRotate, Equiv.swap_apply_def, hr]

private theorem canonicalPermutation_root (j : Fin 3) :
    canonicalPermutation v c s ((quotientCanonicalOrder v).symm ⟨v, Fin.cast (selectedArity v) j⟩).succ =
      (binaryOrder (n := n)).symm (embedding v H c s hi hd hx ⟨v, Fin.cast (selectedArity v) j⟩) := by
  have hr : (quotientCanonicalOrder v).symm ⟨v, Fin.cast (selectedArity v) j⟩ = rootIndex v j := by
    apply Fin.ext
    simp [quotientCanonicalOrder_symm_val, rootIndex]
  rw [hr, canonicalPermutation_succ, legPermutation_root, embedding_root]
  apply Fin.ext
  have hcval (k : Fin 2) : (vertexSplitChild v k).val = v.val + k.val := by
    fin_cases k <;> simp [vertexSplitChild, splitExternalVertex]
  have hsource : (localEdgePermutation c s (canonicalLeg c j)).1.val =
      if j = 2 then c.val else 1 - c.val := by
    fin_cases c <;> fin_cases s <;> fin_cases j <;> decide
  have hslot : (localEdgePermutation c s (canonicalLeg c j)).2.val =
      if j = 0 then 0 else if j = 1 then 1 else 1 - s.val := by
    fin_cases c <;> fin_cases s <;> fin_cases j <;> decide
  rw [binaryOrder_symm_val, hcval, hsource, hslot]
  have hint : (internalIndex v c s).val = 2 * (v.val + c.val) + s.val := by
    rw [internalIndex, binaryOrder_symm_val, hcval]
  rw [Fin.succAbove, apply_ite Fin.val]
  change (if (rootIndex v (rootRotate c j)).val < (internalIndex v c s).val
    then (rootIndex v (rootRotate c j)).val else (rootIndex v (rootRotate c j)).val + 1) = _
  rw [hint]
  fin_cases c <;> fin_cases s <;> fin_cases j <;>
    norm_num [rootRotate, rootIndex, Fin.ext_iff, Nat.mul_add] <;> omega

/-- The explicit permutation is the actual original edge array with its
internal arrow first and its extracted quotient arrows in canonical order. -/
theorem canonicalPermutation_embedding (j : Fin (D (n := n))) :
    binaryOrder (canonicalPermutation v c s j.succ) =
      embedding v H c s hi hd hx (quotientCanonicalOrder v j) := by
  apply (binaryOrder (n := n)).symm.injective
  rw [Equiv.symm_apply_apply]
  let e := quotientCanonicalOrder v j
  have hj : j = (quotientCanonicalOrder v).symm e := (Equiv.symm_apply_apply _ _).symm
  rw [hj]
  obtain ⟨f,hf⟩ := (vertexSplitOldEdgeEquiv (Arity v) v (selectedArity v).symm).symm.surjective e
  rw [← hf]
  rcases f with f | k
  · simpa only [vertexSplitOldEdgeEquiv_symm_outside, Equiv.apply_symm_apply] using
      canonicalPermutation_outside v H c s hi hd hx f
  · simpa only [vertexSplitOldEdgeEquiv_symm_root, Equiv.apply_symm_apply] using
      canonicalPermutation_root v H c s hi hd hx k

end EnvelopingIsomorphism.Deformation.UniformBinaryQuotientOrderSign
