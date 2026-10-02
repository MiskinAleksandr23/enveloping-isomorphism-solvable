import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointSplitFaceContraction
import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointActualFaceIntegral
import EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeightRelabel
import EnvelopingIsomorphism.Deformation.Kontsevich.VertexSplitOutgoingFactor

/-! Actual two-point face integrals for arbitrary split arities. The quotient
is extracted from nonzero density and every native/canonical edge sign remains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointSplitFaceWeight
open KontsevichGraph.General KontsevichGraph.General.Graph
open InteriorGraphFaceCoordinates TwoPointBinaryFaceAdmissibility TwoPointQuotientCoarseLabels
open TwoPointSplitFaceContraction
open scoped Classical BigOperators
open Set MeasureTheory
variable {n m p : ℕ} {q : Fin (n + 1) → ℕ} {qLocal : Fin 2 → ℕ}
variable (v : Fin (n + 1)) (hq : q v = p) (H : Graph (vertexSplitArity q qLocal v) m)
  (hp : Fintype.card (KontsevichGraph.General.Edge qLocal) = p + 1) (D : Data v H)
variable {i a b : Fin (n + 2)} (ha : a ∈ cluster v) (hanchor : i ∈ cluster v → a = i)

private def relabelBetween {n k m : ℕ} (σ : Fin (n + 1) ≃ Fin (k + 1))
    (e : GraphForms.Edge n m) : GraphForms.Edge k m := ⟨σ e.source, Sum.map σ id e.target⟩

private theorem rawIntegral_between {n k m : ℕ} (h : k = n)
    (σ : Fin (n + 1) ≃ Fin (k + 1))
    (es : Fin (GraphForms.dimension k m) → GraphForms.Edge k m)
    (fs : Fin (GraphForms.dimension n m) → GraphForms.Edge n m)
    (he : ∀ j, es j = relabelBetween σ (fs (finCongr (congrArg (fun t => GraphForms.dimension t m) h) j))) :
    GeometricWeights.rawIntegral es = GeometricWeights.rawIntegral fs := by
  subst k
  have hfun : es = fun j => GeometricWeights.relabelEdge σ (fs j) := funext he
  rw [hfun, GeometricWeights.rawIntegral_relabel]

def relabelEdge (e : GraphForms.Edge n m) : GraphForms.Edge (coarseN i a (cluster v)) m :=
  relabelBetween (quotientLabelEquiv v ha hanchor) e

theorem coarseTarget_eq_map_collapse (t : Vertex (n + 2) m) :
    coarseTarget (i := i) (a := a) (S := cluster v) t =
      Sum.map (quotientLabelEquiv v ha hanchor) id (vertexSplitCollapseVertex v t) := by
  rcases t with t | t
  · exact congrArg Sum.inl (coarseLabel_eq_quotientLabel v t)
  · rfl

theorem coarseEdge_embedding (e : KontsevichGraph.General.Edge q) :
    coarseEdge (i := i) (a := a) (S := cluster v)
      ((embedding v hq H hp D e).1, H.target (embedding v hq H hp D e)) =
      relabelEdge v ha hanchor ⟨e.1, (quotient v hq H hp D).target e⟩ := by
  unfold coarseEdge relabelEdge relabelBetween
  congr 1
  · rw [coarseLabel_eq_quotientLabel, embedding_source]
    rfl
  · rw [coarseTarget_eq_map_collapse, ← quotient_target]

variable {s t : ℕ}
  (order : Fin (s + t) ≃ KontsevichGraph.General.Edge (vertexSplitArity q qLocal v))
  (hcount : Fintype.card {j // IsInternal (cluster v)
    (TwoPointSplitFaceAdmissibility.orderedEdges v H order j)} = s)

def quotientOrder : Fin t ≃ KontsevichGraph.General.Edge q :=
  ((externalEnum (TwoPointSplitFaceAdmissibility.orderedEdges v H order) hcount).symm.trans
    (order.subtypeEquiv (fun _ => Iff.rfl))).trans (externalEquiv v hq H hp D).symm

theorem embedding_quotientOrder (j : Fin t) :
    embedding v hq H hp D (quotientOrder v hq H hp D order hcount j) =
      order (externalIndex (TwoPointSplitFaceAdmissibility.orderedEdges v H order) hcount j) := by
  change ((externalEquiv v hq H hp D) ((externalEquiv v hq H hp D).symm _)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem coarseEdges_eq_quotient_order (j : Fin t) :
    coarseEdges (i := i) (a := a) (TwoPointSplitFaceAdmissibility.orderedEdges v H order) hcount j =
      relabelEdge v ha hanchor
        ⟨(quotientOrder v hq H hp D order hcount j).1,
          (quotient v hq H hp D).target (quotientOrder v hq H hp D order hcount j)⟩ := by
  have h := coarseEdge_embedding v hq H hp D ha hanchor (quotientOrder v hq H hp D order hcount j)
  rw [embedding_quotientOrder] at h
  exact h

variable
  (order : Fin (shapeDegree a b (cluster v) + coarseDegree i a (cluster v) m) ≃
    KontsevichGraph.General.Edge (vertexSplitArity q qLocal v))
  (hcount : Fintype.card {j // IsInternal (cluster v)
    (TwoPointSplitFaceAdmissibility.orderedEdges v H order j)} = shapeDegree a b (cluster v))

def inducedOrder : Fin (GraphForms.dimension n m) ≃ KontsevichGraph.General.Edge q :=
  (finCongr (congrArg (fun t => GraphForms.dimension t m) (coarseN_eq v ha hanchor))).symm.trans
    (quotientOrder v hq H hp D order hcount)

/-- The quotient has top degree because its edges are the actual external
rows of the face; no degree certificate is imported as a matching premise. -/
theorem quotient_edgeCount (A : Fin (GraphForms.dimension n m) ≃ KontsevichGraph.General.Edge q) :
    ∑ w, q w = GraphForms.dimension n m := by
  have hc := Fintype.card_congr A
  simpa only [Fintype.card_fin, Fintype.card_sigma] using hc.symm

theorem rawIntegral_coarse_eq_quotient :
    GeometricWeights.rawIntegral (coarseEdges (i := i) (a := a)
      (TwoPointSplitFaceAdmissibility.orderedEdges v H order) hcount) =
    GeometricWeights.rawIntegral (GeometricWeights.orderedEdges (quotient v hq H hp D)
      (inducedOrder v hq H hp D ha hanchor order hcount)) := by
  apply rawIntegral_between (coarseN_eq v ha hanchor) (quotientLabelEquiv v ha hanchor)
  intro j
  have h := coarseEdges_eq_quotient_order v hq H hp D ha hanchor order hcount j
  convert h using 1
  simp only [GeometricWeights.orderedEdges, inducedOrder, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

def quotientOrderPermutation : Equiv.Perm (Fin (GraphForms.dimension n m)) :=
  (inducedOrder v hq H hp D ha hanchor order hcount).trans
    (GeometricWeights.canonicalOrder (quotient_edgeCount (inducedOrder v hq H hp D ha hanchor order hcount))).symm

theorem inducedWeight_eq_signed_canonical :
    GeometricWeights.geometricWeight (quotient v hq H hp D)
      (inducedOrder v hq H hp D ha hanchor order hcount) =
      (Equiv.Perm.sign (quotientOrderPermutation v hq H hp D ha hanchor order hcount) : ℝ) *
        GeometricWeights.canonicalWeight (quotient v hq H hp D)
          (quotient_edgeCount (inducedOrder v hq H hp D ha hanchor order hcount)) := by
  have h := GeometricWeights.geometricWeight_permute (quotient v hq H hp D)
    (GeometricWeights.canonicalOrder (quotient_edgeCount (inducedOrder v hq H hp D ha hanchor order hcount)))
    (quotientOrderPermutation v hq H hp D ha hanchor order hcount)
  have he : (quotientOrderPermutation v hq H hp D ha hanchor order hcount).trans
      (GeometricWeights.canonicalOrder (quotient_edgeCount (inducedOrder v hq H hp D ha hanchor order hcount))) =
      inducedOrder v hq H hp D ha hanchor order hcount := by
    apply Equiv.ext
    intro j
    simp only [quotientOrderPermutation, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [he] at h
  exact h

def normalizedIntegral : ℝ :=
  GeometricWeights.outgoingFactor (vertexSplitArity q qLocal v) *
    (((2 * Real.pi) ^ (shapeDegree a b (cluster v) + coarseDegree i a (cluster v) m))⁻¹ *
      ∫ x in InteriorFiberAngleSplit.integrationRegion (shapeN a b (cluster v)) ×ˢ
        GeometricWeights.realDomain (coarseN i a (cluster v)) m,
        realFaceDensity (TwoPointSplitFaceAdmissibility.orderedEdges v H order) x)

variable (hb : b ∈ cluster v) (hba : b ≠ a)
include hb hba

/-- Literal integral matching for the extracted quotient with every native
ordering sign. The outgoing factor ratio is explicit and never assumed. -/
theorem normalized_integral_eq_quotient :
    normalizedIntegral v H order =
      (GeometricWeights.outgoingFactor (vertexSplitArity q qLocal v) /
        GeometricWeights.outgoingFactor q) *
      (Equiv.Perm.sign (edgeBlockPermutation (TwoPointSplitFaceAdmissibility.orderedEdges v H order) hcount).symm : ℝ) *
        GeometricWeights.geometricWeight (quotient v hq H hp D)
          (inducedOrder v hq H hp D ha hanchor order hcount) := by
  have hloop : ∀ j, (TwoPointSplitFaceAdmissibility.orderedEdges v H order j).2 ≠
      Sum.inl (TwoPointSplitFaceAdmissibility.orderedEdges v H order j).1 :=
    fun j => H.noLoops (order j).1 (order j).2
  unfold normalizedIntegral
  rw [(TwoPointActualFaceIntegral.integral_realFaceDensity
    (TwoPointSplitFaceAdmissibility.orderedEdges v H order) hcount ha hb hba (cluster_card v) hloop).2,
    rawIntegral_coarse_eq_quotient v hq H hp D ha hanchor order hcount]
  have hdeg : shapeDegree a b (cluster v) + coarseDegree i a (cluster v) m = GraphForms.dimension n m + 1 := by
    rw [shapeDegree_eq ha hb hba, cluster_card]
    change 1 + GraphForms.dimension (coarseN i a (cluster v)) m = _
    rw [coarseN_eq v ha hanchor]
    omega
  have hpow := congrArg (fun d : ℕ => ((2 * Real.pi) ^ d)⁻¹) hdeg
  rw [hpow, GeometricWeights.geometricWeight]
  have hf : GeometricWeights.outgoingFactor q ≠ 0 := by
    unfold GeometricWeights.outgoingFactor
    apply Finset.prod_ne_zero_iff.mpr
    intro w _
    exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (q w))
  have hc := TwoPointGraphWeightProduct.circle_normalization (GraphForms.dimension n m)
  calc
    _ = GeometricWeights.outgoingFactor (vertexSplitArity q qLocal v) *
      (Equiv.Perm.sign (edgeBlockPermutation (TwoPointSplitFaceAdmissibility.orderedEdges v H order) hcount).symm : ℝ) *
        ((((2 * Real.pi) ^ (GraphForms.dimension n m + 1))⁻¹ * (2 * Real.pi)) *
          GeometricWeights.rawIntegral (GeometricWeights.orderedEdges (quotient v hq H hp D)
            (inducedOrder v hq H hp D ha hanchor order hcount))) := by ring
    _ = _ := by rw [hc]; field_simp

theorem normalized_integral_eq_signed_canonical :
    normalizedIntegral v H order =
      (GeometricWeights.outgoingFactor (vertexSplitArity q qLocal v) /
        GeometricWeights.outgoingFactor q) *
      (Equiv.Perm.sign (edgeBlockPermutation (TwoPointSplitFaceAdmissibility.orderedEdges v H order) hcount).symm : ℝ) *
      (Equiv.Perm.sign (quotientOrderPermutation v hq H hp D ha hanchor order hcount) : ℝ) *
        GeometricWeights.canonicalWeight (quotient v hq H hp D)
          (quotient_edgeCount (inducedOrder v hq H hp D ha hanchor order hcount)) := by
  rw [normalized_integral_eq_quotient v hq H hp D ha hanchor order hcount hb hba,
    inducedWeight_eq_signed_canonical]
  ring

/-- The actual native face ordering sign relative to the canonical quotient
slots. Both permutations are constructed from the original edge array. -/
def faceSign : ℝ :=
  (Equiv.Perm.sign (edgeBlockPermutation (TwoPointSplitFaceAdmissibility.orderedEdges v H order) hcount).symm : ℝ) *
    (Equiv.Perm.sign (quotientOrderPermutation v hq H hp D ha hanchor order hcount) : ℝ)

omit hb hba in
theorem faceSign_sq : faceSign v hq H hp D ha hanchor order hcount *
    faceSign v hq H hp D ha hanchor order hcount = 1 := by
  unfold faceSign
  have hs (σ : Equiv.Perm (Fin (shapeDegree a b (cluster v) + coarseDegree i a (cluster v) m))) :
      (σ.sign : ℝ) * (σ.sign : ℝ) = 1 := by simp [← Int.cast_mul, ← Units.val_mul]
  have ht (σ : Equiv.Perm (Fin (GraphForms.dimension n m))) :
      (σ.sign : ℝ) * (σ.sign : ℝ) = 1 := by simp [← Int.cast_mul, ← Units.val_mul]
  calc
    _ = ((Equiv.Perm.sign (edgeBlockPermutation (TwoPointSplitFaceAdmissibility.orderedEdges v H order) hcount).symm : ℝ) ^ 2) *
      ((Equiv.Perm.sign (quotientOrderPermutation v hq H hp D ha hanchor order hcount) : ℝ) ^ 2) := by ring
    _ = 1 := by rw [pow_two, pow_two, hs, ht, one_mul]

include ha
omit D hcount in
/-- The required internal-row count follows from one actual nonzero face
value and the two-point geometry. -/
theorem count_of_nonzero
    (y : RealProductCoordinates i a b (cluster v) m)
    (hy : y ∈ InteriorFiberAngleSplit.integrationRegion (shapeN a b (cluster v)) ×ˢ
      GeometricWeights.realDomain (coarseN i a (cluster v)) m)
    (h : realFaceDensity (TwoPointSplitFaceAdmissibility.orderedEdges v H order) y ≠ 0) :
    Fintype.card {j // IsInternal (cluster v)
      (TwoPointSplitFaceAdmissibility.orderedEdges v H order j)} = shapeDegree a b (cluster v) := by
  have hs : shapeDegree a b (cluster v) = 1 := by rw [shapeDegree_eq ha hb hba, cluster_card]
  exact (InteriorFaceNonzeroAdmissibility.internal_count_eq_one_of_density_ne_zero
    (TwoPointSplitFaceAdmissibility.orderedEdges v H order) y ha hb hba (cluster_card v) hy
    (fun j => H.noLoops (order j).1 (order j).2) h).trans hs.symm

omit D hcount in
/-- Full actual coefficient matching with all discrete quotient hypotheses
discharged from nonzero density, rather than supplied as matching premises. -/
theorem normalized_integral_of_nonzero
    (y : RealProductCoordinates i a b (cluster v) m)
    (hy : y ∈ InteriorFiberAngleSplit.integrationRegion (shapeN a b (cluster v)) ×ˢ
      GeometricWeights.realDomain (coarseN i a (cluster v)) m)
    (h : realFaceDensity (TwoPointSplitFaceAdmissibility.orderedEdges v H order) y ≠ 0) :
    let D := ofNonzero v H order ha hb hba y hy h
    let hc := count_of_nonzero v H ha order hb hba y hy h
    normalizedIntegral v H order =
      (GeometricWeights.outgoingFactor (vertexSplitArity q qLocal v) / GeometricWeights.outgoingFactor q) *
        faceSign v hq H hp D ha hanchor order hc *
          GeometricWeights.canonicalWeight (quotient v hq H hp D)
            (quotient_edgeCount (inducedOrder v hq H hp D ha hanchor order hc)) := by
  dsimp only
  rw [normalized_integral_eq_signed_canonical v hq H hp
    (ofNonzero v H order ha hb hba y hy h) ha hanchor order
    (count_of_nonzero v H ha order hb hba y hy h) hb hba]
  unfold faceSign
  ring

end EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointSplitFaceWeight
