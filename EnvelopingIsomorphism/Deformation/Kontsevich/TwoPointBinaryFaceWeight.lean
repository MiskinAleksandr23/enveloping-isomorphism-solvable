import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointQuotientEdgeOrder
import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointActualFaceIntegral
import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointCurvatureNormalization
import EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeightRelabel
import EnvelopingIsomorphism.Deformation.GraphCurvaturePhysicalPairs
import EnvelopingIsomorphism.Deformation.UniformBinaryQuotientOrderSign

/-! Genuine two-point simple-face coefficients of binary graphs, matched to
the actual extracted curvature quotient and retaining every ordering sign. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointBinaryFaceWeight
open KontsevichGraph.General UniformBinaryGraphs UniformBinaryContraction
open InteriorGraphFaceCoordinates TwoPointBinaryFaceAdmissibility
open TwoPointQuotientCoarseLabels TwoPointQuotientEdgeOrder
open Set MeasureTheory
open scoped Classical

private theorem block_sign {r q N : ℕ} (hr : r = 1) (hq : q = N)
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

private def relabelBetween {n k m : ℕ} (σ : Fin (n + 1) ≃ Fin (k + 1))
    (e : GraphForms.Edge n m) : GraphForms.Edge k m := ⟨σ e.source, Sum.map σ id e.target⟩

private theorem rawIntegral_between {n k m : ℕ} (h : k = n)
    (σ : Fin (n + 1) ≃ Fin (k + 1))
    (es : Fin (GraphForms.dimension k m) → GraphForms.Edge k m)
    (fs : Fin (GraphForms.dimension n m) → GraphForms.Edge n m)
    (he : ∀ j, es j = relabelBetween σ (fs (finCongr (congrArg (fun t => GraphForms.dimension t m) h) j))) :
    GeometricWeights.rawIntegral es = GeometricWeights.rawIntegral fs := by
  subst k
  have hfun : es = fun j => GeometricWeights.relabelEdge σ (fs j) := by
    funext j
    exact he j
  rw [hfun, GeometricWeights.rawIntegral_relabel]

variable {n : ℕ} (v : Fin (n + 1)) (H : BinaryGraph (n + 2) 3)
  {i a b : Fin (n + 2)}
  (ha : a ∈ cluster v) (hb : b ∈ cluster v) (hba : b ≠ a)
  (hanchor : i ∈ cluster v → a = i)
  (order : Fin (shapeDegree a b (cluster v) + coarseDegree i a (cluster v) 3) ≃
    KontsevichGraph.General.Edge (fun _ : Fin (n + 2) => 2))
  (hcount : Fintype.card {j // IsInternal (cluster v) (TwoPointBinaryFaceAdmissibility.orderedEdges H order j)} =
    shapeDegree a b (cluster v))
  (c s : Fin 2) (hi : UniqueInternalAt v H c s) (hd : CoarseDistinct v H) (hx : ExitsDistinctAt v H c s)

/-- The exact native external-arrow order, transported only by the proved
numerical equality of native coarse dimensions. -/
def inducedOrder : Fin (GraphForms.dimension n 3) ≃ KontsevichGraph.General.Edge (Arity v) :=
  (finCongr (congrArg (fun t => GraphForms.dimension t 3) (coarseN_eq v ha hanchor))).symm.trans
    (quotientOrder v H c s hi hd hx order hcount)

theorem rawIntegral_coarse_eq_quotient :
    GeometricWeights.rawIntegral
      (coarseEdges (i := i) (a := a) (TwoPointBinaryFaceAdmissibility.orderedEdges H order) hcount) =
    GeometricWeights.rawIntegral (GeometricWeights.orderedEdges (curvatureGraph v H c s hi hd hx)
      (inducedOrder v H ha hanchor order hcount c s hi hd hx)) := by
  apply rawIntegral_between (coarseN_eq v ha hanchor) (quotientLabelEquiv v ha hanchor)
  intro j
  have h := coarseEdges_eq_quotient_order v H c s hi hd hx ha hanchor order hcount j
  convert h using 1
  simp only [GeometricWeights.orderedEdges, inducedOrder, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

include hb hba

/-- The integral is a genuine two-point circle factor times the actual
curvature quotient weight. Outgoing factorials contribute the explicit 3/2. -/
theorem normalized_integral_eq_quotient :
    GeometricWeights.outgoingFactor (fun _ : Fin (n + 2) => 2) *
      (((2 * Real.pi) ^ (shapeDegree a b (cluster v) + coarseDegree i a (cluster v) 3))⁻¹ *
        ∫ x in InteriorFiberAngleSplit.integrationRegion (shapeN a b (cluster v)) ×ˢ
          GeometricWeights.realDomain (coarseN i a (cluster v)) 3,
          realFaceDensity (TwoPointBinaryFaceAdmissibility.orderedEdges H order) x) =
      (3 / 2 : ℝ) *
        (Equiv.Perm.sign (edgeBlockPermutation (TwoPointBinaryFaceAdmissibility.orderedEdges H order) hcount).symm : ℝ) *
        GeometricWeights.geometricWeight (curvatureGraph v H c s hi hd hx)
          (inducedOrder v H ha hanchor order hcount c s hi hd hx) := by
  have hloop : ∀ q, (TwoPointBinaryFaceAdmissibility.orderedEdges H order q).2 ≠
      Sum.inl (TwoPointBinaryFaceAdmissibility.orderedEdges H order q).1 :=
    fun q => H.noLoops (order q).1 (order q).2
  rw [(TwoPointActualFaceIntegral.integral_realFaceDensity
    (TwoPointBinaryFaceAdmissibility.orderedEdges H order) hcount ha hb hba (cluster_card v) hloop).2,
    rawIntegral_coarse_eq_quotient v H ha hanchor order hcount c s hi hd hx]
  have hdeg : shapeDegree a b (cluster v) + coarseDegree i a (cluster v) 3 = GraphForms.dimension n 3 + 1 := by
    rw [shapeDegree_eq ha hb hba, cluster_card]
    change 1 + GraphForms.dimension (coarseN i a (cluster v)) 3 = _
    rw [coarseN_eq v ha hanchor]
    omega
  have hpow := congrArg (fun d : ℕ => ((2 * Real.pi) ^ d)⁻¹) hdeg
  rw [hpow, TwoPointCurvatureNormalization.binary_curvature_factor v, GeometricWeights.geometricWeight]
  have hc := TwoPointGraphWeightProduct.circle_normalization (GraphForms.dimension n 3)
  calc
    _ = (3 / 2 : ℝ) *
        (Equiv.Perm.sign (edgeBlockPermutation (TwoPointBinaryFaceAdmissibility.orderedEdges H order) hcount).symm : ℝ) *
        (GeometricWeights.outgoingFactor (Arity v) *
          ((((2 * Real.pi) ^ (GraphForms.dimension n 3 + 1))⁻¹ * (2 * Real.pi)) *
            GeometricWeights.rawIntegral (GeometricWeights.orderedEdges (curvatureGraph v H c s hi hd hx)
              (inducedOrder v H ha hanchor order hcount c s hi hd hx)))) := by ring
    _ = _ := by rw [hc]; ring

/-- The literal normalized native face integral, before any edge-order sign
is simplified. -/
def normalizedIntegral : ℝ :=
  GeometricWeights.outgoingFactor (fun _ : Fin (n + 2) => 2) *
    (((2 * Real.pi) ^ (shapeDegree a b (cluster v) + coarseDegree i a (cluster v) 3))⁻¹ *
      ∫ x in InteriorFiberAngleSplit.integrationRegion (shapeN a b (cluster v)) ×ˢ
        GeometricWeights.realDomain (coarseN i a (cluster v)) 3,
        realFaceDensity (TwoPointBinaryFaceAdmissibility.orderedEdges H order) x)

/-- The exact permutation converting the native quotient array to the
canonical source-major quotient array. -/
def quotientOrderPermutation : Equiv.Perm (Fin (GraphForms.dimension n 3)) :=
  (inducedOrder v H ha hanchor order hcount c s hi hd hx).trans
    (UniformBinaryQuotientOrderSign.quotientCanonicalOrder v).symm

omit hb hba in
theorem inducedWeight_eq_signed_rawWeight :
    GeometricWeights.geometricWeight (curvatureGraph v H c s hi hd hx)
      (inducedOrder v H ha hanchor order hcount c s hi hd hx) =
    (Equiv.Perm.sign (quotientOrderPermutation v H ha hanchor order hcount c s hi hd hx) : ℝ) *
      GraphCurvatureExtractedCoefficient.rawWeight v (curvatureGraph v H c s hi hd hx) := by
  have h := GeometricWeights.geometricWeight_permute (curvatureGraph v H c s hi hd hx)
    (UniformBinaryQuotientOrderSign.quotientCanonicalOrder v)
    (quotientOrderPermutation v H ha hanchor order hcount c s hi hd hx)
  have he : (quotientOrderPermutation v H ha hanchor order hcount c s hi hd hx).trans
      (UniformBinaryQuotientOrderSign.quotientCanonicalOrder v) =
      inducedOrder v H ha hanchor order hcount c s hi hd hx := by
    apply Equiv.ext
    intro j
    simp only [quotientOrderPermutation, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [he] at h
  exact h

/-- Both independent ordering signs remain visible in the actual integral. -/
theorem normalized_integral_eq_signed_rawWeight :
    normalizedIntegral v H order =
      (3 / 2 : ℝ) *
        (Equiv.Perm.sign (edgeBlockPermutation (TwoPointBinaryFaceAdmissibility.orderedEdges H order) hcount).symm : ℝ) *
        (Equiv.Perm.sign (quotientOrderPermutation v H ha hanchor order hcount c s hi hd hx) : ℝ) *
        GraphCurvatureExtractedCoefficient.rawWeight v (curvatureGraph v H c s hi hd hx) := by
  unfold normalizedIntegral
  rw [normalized_integral_eq_quotient v H ha hb hba hanchor order hcount c s hi hd hx,
    inducedWeight_eq_signed_rawWeight]
  ring

/-- The residual orientation relative to the extracted sender-slot convention.
It is an explicit product of permutation signs, never an order invariance assumption. -/
def faceOrderingSign : ℝ :=
  (Equiv.Perm.sign (edgeBlockPermutation (TwoPointBinaryFaceAdmissibility.orderedEdges H order) hcount).symm : ℝ) *
    (Equiv.Perm.sign (quotientOrderPermutation v H ha hanchor order hcount c s hi hd hx) : ℝ) *
    (-1 : ℝ) ^ s.val

theorem normalized_integral_eq_extractedCoefficient :
    normalizedIntegral v H order =
      (3 / 2 : ℝ) * faceOrderingSign v H ha hanchor order hcount c s hi hd hx *
        GraphCurvatureExtractedCoefficient.coefficient v H := by
  rw [normalized_integral_eq_signed_rawWeight v H ha hb hba hanchor order hcount c s hi hd hx,
    GraphCurvatureExtractedCoefficient.coefficient_eq_extracted v H c s hi hd hx]
  unfold faceOrderingSign
  have hs : (-1 : ℝ) ^ s.val * (-1 : ℝ) ^ s.val = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    _ = (3 / 2 : ℝ) *
        (Equiv.Perm.sign (edgeBlockPermutation (TwoPointBinaryFaceAdmissibility.orderedEdges H order) hcount).symm : ℝ) *
        (Equiv.Perm.sign (quotientOrderPermutation v H ha hanchor order hcount c s hi hd hx) : ℝ) *
        GraphCurvatureExtractedCoefficient.rawWeight v (curvatureGraph v H c s hi hd hx) *
        ((-1 : ℝ) ^ s.val * (-1 : ℝ) ^ s.val) := by rw [hs, mul_one]
    _ = _ := by ring

/-- Physical-pair matching in the identity labelling. General physical
labellings use this theorem on the corresponding permuted binary graph. -/
theorem normalized_integral_eq_physicalCoefficient :
    normalizedIntegral v H order =
      (3 / 2 : ℝ) * faceOrderingSign v H ha hanchor order hcount c s hi hd hx *
        GraphCurvaturePhysicalPairs.physicalCoefficient H
          (GraphCurvatureLabelCounting.movedPair v (Equiv.refl _)) := by
  rw [normalized_integral_eq_extractedCoefficient v H ha hb hba hanchor order hcount c s hi hd hx]
  have h := GraphCurvaturePhysicalPairs.coefficient_eq_physical H
    (GraphCurvatureLabelCounting.movedPair v (Equiv.refl _)) ⟨(v, Equiv.refl _), rfl⟩
  simpa only [Equiv.refl_symm, KontsevichGraph.General.Graph.permuteInternal_refl] using
    congrArg (fun z => (3 / 2 : ℝ) * faceOrderingSign v H ha hanchor order hcount c s hi hd hx * z) h

include ha hanchor in
/-- Native face dimensions agree with the source-major binary edge count. -/
theorem nativeDegree_eq :
    shapeDegree a b (cluster v) + coarseDegree i a (cluster v) 3 = GraphForms.dimension n 3 + 1 := by
  rw [shapeDegree_eq ha hb hba, cluster_card]
  change 1 + GraphForms.dimension (coarseN i a (cluster v)) 3 = _
  rw [coarseN_eq v ha hanchor]
  omega

/-- The canonical binary edge order, with only the actual native dimension cast. -/
def sourceMajorOrder : Fin (shapeDegree a b (cluster v) + coarseDegree i a (cluster v) 3) ≃
    KontsevichGraph.General.Edge (fun _ : Fin (n + 2) => 2) :=
  (finCongr (nativeDegree_eq v ha hb hba hanchor)).trans UniformBinaryQuotientOrderSign.binaryOrder

/-- Exact cancellation of the arbitrary intermediate enumeration against the
canonical quotient order. The remaining sender-slot sign is proved, not assumed. -/
theorem faceOrderingSign_sourceMajor
    (horder : order = sourceMajorOrder v ha hb hba hanchor) :
    faceOrderingSign v H ha hanchor order hcount c s hi hd hx = 1 := by
  let B := edgeBlockPermutation (TwoPointBinaryFaceAdmissibility.orderedEdges H order) hcount
  let C := UniformBinaryQuotientOrderSign.canonicalPermutation v c s
  let Q := (quotientOrder v H c s hi hd hx order hcount).trans
    (UniformBinaryQuotientOrderSign.quotientCanonicalOrder v).symm
  have hr : shapeDegree a b (cluster v) = 1 := by
    rw [shapeDegree_eq ha hb hba, cluster_card]
  have hq : coarseDegree i a (cluster v) 3 = GraphForms.dimension n 3 :=
    congrArg (fun t => GraphForms.dimension t 3) (coarseN_eq v ha hanchor)
  have ho (j) : order j = UniformBinaryQuotientOrderSign.binaryOrder
      (finCongr (nativeDegree_eq v ha hb hba hanchor) j) := by
    rw [horder]
    rfl
  have hleft (j : Fin (shapeDegree a b (cluster v))) :
      finCongr (nativeDegree_eq v ha hb hba hanchor) (B (finSumFinEquiv (Sum.inl j))) = C 0 := by
    apply UniformBinaryQuotientOrderSign.binaryOrder.injective
    rw [← ho]
    change order (edgeBlockPermutation _ _ (finSumFinEquiv (Sum.inl j))) =
      UniformBinaryQuotientOrderSign.binaryOrder (UniformBinaryQuotientOrderSign.canonicalPermutation v c s 0)
    rw [edgeBlockPermutation_inl, UniformBinaryQuotientOrderSign.canonicalPermutation_zero]
    simp only [UniformBinaryQuotientOrderSign.internalIndex, Equiv.apply_symm_apply]
    exact (isInternal_iff_slot v H c s hi _).mp ((internalEnum
      (TwoPointBinaryFaceAdmissibility.orderedEdges H order) hcount).symm j).property
  have hright (j : Fin (coarseDegree i a (cluster v) 3)) :
      finCongr (nativeDegree_eq v ha hb hba hanchor) (B (finSumFinEquiv (Sum.inr j))) = C (Q j).succ := by
    apply UniformBinaryQuotientOrderSign.binaryOrder.injective
    rw [← ho]
    change order (edgeBlockPermutation _ _ (finSumFinEquiv (Sum.inr j))) =
      UniformBinaryQuotientOrderSign.binaryOrder (UniformBinaryQuotientOrderSign.canonicalPermutation v c s (Q j).succ)
    rw [edgeBlockPermutation_inr, UniformBinaryQuotientOrderSign.canonicalPermutation_embedding v H c s hi hd hx]
    simp only [Q, Equiv.trans_apply, Equiv.apply_symm_apply]
    exact (embedding_quotientOrder v H c s hi hd hx order hcount j).symm
  have hsign := block_sign hr hq (nativeDegree_eq v ha hb hba hanchor) B C Q hleft hright
  change B.sign = C.sign * Equiv.Perm.sign
    (quotientOrderPermutation v H ha hanchor order hcount c s hi hd hx) at hsign
  change B.sign = (UniformBinaryQuotientOrderSign.canonicalPermutation v c s).sign * _ at hsign
  rw [UniformBinaryQuotientOrderSign.canonicalPermutation_sign] at hsign
  unfold faceOrderingSign
  change (Equiv.Perm.sign B.symm : ℝ) *
    (Equiv.Perm.sign (quotientOrderPermutation v H ha hanchor order hcount c s hi hd hx) : ℝ) *
    (-1 : ℝ) ^ s.val = 1
  rw [Equiv.Perm.sign_symm, hsign]
  rcases Int.units_eq_one_or (Equiv.Perm.sign
    (quotientOrderPermutation v H ha hanchor order hcount c s hi hd hx)) with hp | hp <;>
    rw [hp] <;> fin_cases s <;> norm_num

include hcount hi hd hx in
/-- Source-major native two-point face integral equals the actual extracted
physical-pair coefficient, with the outgoing factorial ratio 3/2. -/
theorem normalized_integral_sourceMajor_eq_physicalCoefficient
    (horder : order = sourceMajorOrder v ha hb hba hanchor) :
    normalizedIntegral v H order = (3 / 2 : ℝ) *
      GraphCurvaturePhysicalPairs.physicalCoefficient H
        (GraphCurvatureLabelCounting.movedPair v (Equiv.refl _)) := by
  rw [normalized_integral_eq_physicalCoefficient v H ha hb hba hanchor order hcount c s hi hd hx,
    faceOrderingSign_sourceMajor v H ha hb hba hanchor order hcount c s hi hd hx horder, mul_one]

end EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointBinaryFaceWeight
