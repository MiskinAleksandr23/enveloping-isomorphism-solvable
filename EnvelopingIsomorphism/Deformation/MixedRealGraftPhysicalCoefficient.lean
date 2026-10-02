import EnvelopingIsomorphism.Deformation.MixedRealUnconditionalWeight
import EnvelopingIsomorphism.Deformation.MixedGraphClusterSums
import EnvelopingIsomorphism.Deformation.MixedGraphGraftFibres
import EnvelopingIsomorphism.Deformation.Kontsevich.MainRealGraftPhysicalCoefficient

/-! The actual native one-vector graft coefficients in the retained-vector
carrier, including graphs with empty graft fibres. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace EnvelopingIsomorphism.Deformation.MixedRealGraftPhysicalCoefficient
open Kontsevich KontsevichGraph.General MixedGraphProfileCarrier MixedGraphTargetProfiles
open MixedGraphAveraging MixedGraphClusterSums GraphCoefficientProfiles UniformBinaryGraphs
open scoped Classical BigOperators
variable {a b : ℕ}

private theorem pushforward_injective {k I A : Type*} [CommRing k] [Fintype I]
    (f : I → A) (hf : Function.Injective f) (w : I → k) (i : I) :
    pushforward f w (f i) = w i := by
  simp only [pushforward, hf.eq_iff]
  simp

theorem outputCarrier_injective : Function.Injective
    (fun D : (i : Fin (a+1)) × Graph (graftArity (vectorArity i) (fun _ : Fin b ↦ 2)) 2 ↦
      outputCarrier D.1 D.2) := by
  rintro ⟨i,H⟩ ⟨j,G⟩ he
  have hij : i = j := (vectorEmbedding a b).injective (congrArg VectorGraph.vertex he)
  subst j
  have hg := transportGraph_injective (outputCount a b) (outputVertexEquiv a b)
    (ofProfile_injective _ (outputArity i) he)
  exact congrArg (Sigma.mk i) hg

theorem inputCarrier_injective : Function.Injective
    (fun D : (i : Fin (a+1)) × Graph (graftArity (fun _ : Fin b ↦ 2) (vectorArity i)) 2 ↦
      inputCarrier D.1 D.2) := by
  rintro ⟨i,H⟩ ⟨j,G⟩ he
  have hij : i = j := (vectorEmbedding a b).injective (congrArg VectorGraph.vertex he)
  subst j
  have hg := transportGraph_injective (inputCount a b) (inputVertexEquiv a b)
    (ofProfile_injective _ (inputArity i) he)
  exact congrArg (Sigma.mk i) hg

theorem outputProfile_carrier {k : Type*} [CommRing k]
    (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k) (i : Fin (a+1))
    (H : Graph (graftArity (vectorArity i) (fun _ : Fin b ↦ 2)) 2) :
    outputProfile w v (outputCarrier i H) =
      GraphGeneralWeightedGraft.graftProfile (m := 0) (l := 1) 0 (fun G ↦ w ⟨i,G⟩) v H := by
  have he : outputProfile w v = pushforward
      (fun D : (i : Fin (a+1)) × Graph (graftArity (vectorArity i) (fun _ : Fin b ↦ 2)) 2 ↦
        outputCarrier D.1 D.2)
      (fun D ↦ GraphGeneralWeightedGraft.graftProfile (m := 0) (l := 1) 0
        (fun G ↦ w ⟨D.1,G⟩) v D.2) := by
    rw [outputProfile_eq_native]
    funext G
    simp [pushforward, Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro L _
    split_ifs <;> rfl
  rw [he]
  exact pushforward_injective _ outputCarrier_injective _ ⟨i,H⟩

theorem inputProfile_carrier {k : Type*} [CommRing k]
    (r : Fin 2) (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k) (i : Fin (a+1))
    (H : Graph (graftArity (fun _ : Fin b ↦ 2) (vectorArity i)) 2) :
    inputProfile r w v (inputCarrier i H) =
      GraphGeneralWeightedGraft.graftProfile (m := 1) (l := 0) r v (fun G ↦ w ⟨i,G⟩) H := by
  have he : inputProfile r w v = pushforward
      (fun D : (i : Fin (a+1)) × Graph (graftArity (fun _ : Fin b ↦ 2) (vectorArity i)) 2 ↦
        inputCarrier D.1 D.2)
      (fun D ↦ GraphGeneralWeightedGraft.graftProfile (m := 1) (l := 0) r
        v (fun G ↦ w ⟨D.1,G⟩) D.2) := by
    rw [inputProfile_eq_native]
    funext G
    simp [pushforward, Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro L _
    split_ifs <;> rfl
  rw [he]
  exact pushforward_injective _ inputCarrier_injective _ ⟨i,H⟩


open GraphCanonicalBinaryWeights
open Kontsevich.BoundaryGraphFaceFactorization Kontsevich.BoundaryGraphOrderedCoordinates
open Kontsevich.BoundaryGraphCanonicalFibreMatching Kontsevich.BoundaryGraphGraftReconstruction
open Kontsevich.BoundaryGraphValenceSelection

/-- Only equality casts of arities and external counts; all incidences remain. -/
def castGraph {n m M : ℕ} {q p : Fin n → ℕ} (hq : q = p) (hm : m = M)
    (G : Graph q m) : Graph p M := by
  subst p
  subst M
  exact G

@[simp] theorem castGraph_refl {n m : ℕ} {q : Fin n → ℕ} (G : Graph q m) :
    castGraph rfl rfl G = G := rfl

theorem canonicalWeight_eq_rawVelocity_cast {A M : ℕ} {q : Fin (A+1) → ℕ}
    (i : Fin (A+1)) (hq : q = vectorArity i) (hM : M = 1)
    (G : Graph q M) (hD : ∑ v, q v = GraphForms.dimension A M) :
    GeometricWeights.canonicalWeight G hD = rawVelocityWeight A ⟨i,castGraph hq hM G⟩ := by
  subst q
  subst M
  rfl

theorem canonicalWeight_eq_rawBinary_cast {A M : ℕ} {q : Fin (A+1) → ℕ}
    (hq : q = fun _ ↦ 2) (hM : M = 2)
    (G : Graph q M) (hD : ∑ v, q v = GraphForms.dimension A M) :
    GeometricWeights.canonicalWeight G hD = rawBinaryWeight (A+1) (castGraph hq hM G) := by
  subst q
  subst M
  rfl

/-- The arity/external-count casts commute with the genuine finite graft fibre. -/
theorem graftProfile_cast {A B O I O' I' : ℕ}
    {q q' : Fin A → ℕ} {p p' : Fin B → ℕ}
    (hq : q = q') (hp : p = p') (hO : O = O') (hI : I = I')
    (r : Fin (O+1)) (w : Graph q (O+1) → ℝ) (v : Graph p (I+1) → ℝ)
    (w' : Graph q' (O'+1) → ℝ) (v' : Graph p' (I'+1) → ℝ)
    (hw : ∀ G, w G = w' (castGraph hq (by omega) G))
    (hv : ∀ G, v G = v' (castGraph hp (by omega) G))
    (H : Graph (graftArity q p) (O+I+1)) :
    GraphGeneralWeightedGraft.graftProfile r w v H =
      GraphGeneralWeightedGraft.graftProfile (Fin.cast (by omega) r) w' v'
        (castGraph (by rw [hq,hp]) (by omega) H) := by
  subst q'
  subst p'
  subst O'
  subst I'
  have hw' : w = w' := funext hw
  have hv' : v = v' := funext hv
  rw [hw',hv']
  rfl

/-- Arbitrary dependent native output coefficients give the actual output
profile, including the empty-fibre case. -/
theorem graftProfile_eq_outputProfile {A B O I : ℕ}
    {q : Fin (A+1) → ℕ} {p : Fin B → ℕ}
    (i : Fin (A+1)) (hq : q = vectorArity i) (hp : p = fun _ ↦ 2)
    (hO : O = 0) (hI : I = 1) (r : Fin (O+1))
    (w : Graph q (O+1) → ℝ) (v : Graph p (I+1) → ℝ)
    (hw : ∀ G, w G = rawVelocityWeight A ⟨i,castGraph hq (by omega) G⟩)
    (hv : ∀ G, v G = rawBinaryWeight B (castGraph hp (by omega) G))
    (H : Graph (graftArity q p) (O+I+1)) :
    GraphGeneralWeightedGraft.graftProfile r w v H =
      outputProfile (rawVelocityWeight A) (rawBinaryWeight B)
        (outputCarrier i (castGraph (by rw [hq,hp]) (by omega) H)) := by
  rw [graftProfile_cast hq hp hO hI r w v
    (fun G ↦ rawVelocityWeight A ⟨i,G⟩) (rawBinaryWeight B) hw hv]
  have hr : Fin.cast (show O+1=0+1 by omega) r = 0 := by
    apply Fin.ext
    have hr := r.isLt
    simp only [Fin.val_cast,Fin.val_zero]
    omega
  rw [hr,outputProfile_carrier]

/-- Input faces use the actual input profile at their original external slot. -/
theorem graftProfile_eq_inputProfile {A B O I : ℕ}
    {q : Fin B → ℕ} {p : Fin (A+1) → ℕ}
    (i : Fin (A+1)) (hq : q = fun _ ↦ 2) (hp : p = vectorArity i)
    (hO : O = 1) (hI : I = 0) (r : Fin (O+1))
    (w : Graph q (O+1) → ℝ) (v : Graph p (I+1) → ℝ)
    (hw : ∀ G, w G = rawBinaryWeight B (castGraph hq (by omega) G))
    (hv : ∀ G, v G = rawVelocityWeight A ⟨i,castGraph hp (by omega) G⟩)
    (H : Graph (graftArity q p) (O+I+1)) :
    GraphGeneralWeightedGraft.graftProfile r w v H =
      inputProfile (Fin.cast (by omega) r) (rawVelocityWeight A) (rawBinaryWeight B)
        (inputCarrier i (castGraph (by rw [hq,hp]) (by omega) H)) := by
  rw [graftProfile_cast hq hp hO hI r w v
    (rawBinaryWeight B) (fun G ↦ rawVelocityWeight A ⟨i,G⟩) hw hv]
  rw [inputProfile_carrier]


section Physical
variable {N : ℕ} {i a : Fin (N+1)} {S : Finset (Fin (N+1))}
variable (H : VectorGraph N 2) (ha : a ∈ S) (hi : i ∉ S)

def outputVectorIndex (hv : H.vertex ∉ S) : Fin (coarseN i S+1) :=
  coarseSourceEquiv hi ⟨H.vertex,hv⟩

def inputVectorIndex (hv : H.vertex ∈ S) : Fin (shapeN a S+1) :=
  shapeSourceEquiv ha ⟨H.vertex,hv⟩

theorem outputOuterArity (hv : H.vertex ∉ S) :
    pulledOuterArity (vectorArity H.vertex) (anchoredPartitionEquiv ha hi) =
      vectorArity (outputVectorIndex H hi hv) := by
  funext v
  have he : ((coarseSourceEquiv hi).symm v).val = H.vertex ↔ v = outputVectorIndex H hi hv := by
    constructor
    · intro h
      apply (coarseSourceEquiv hi).symm.injective
      simpa only [outputVectorIndex,Equiv.symm_apply_apply] using (Subtype.ext h :
        (coarseSourceEquiv hi).symm v = ⟨H.vertex,hv⟩)
    · intro h
      rw [h]
      simp [outputVectorIndex]
  simp only [pulledOuterArity,anchoredPartition_outer,vectorArity,
    Gauge.PlacedMixedGraphTaylorCoefficients.arities,he]

theorem outputInnerArity (hv : H.vertex ∉ S) :
    pulledInnerArity (vectorArity H.vertex) (anchoredPartitionEquiv ha hi) = fun _ ↦ 2 := by
  funext v
  have he : ((shapeSourceEquiv ha).symm v).val ≠ H.vertex := by
    intro he
    exact hv (he ▸ ((shapeSourceEquiv ha).symm v).property)
  simp only [pulledInnerArity,anchoredPartition_inner,vectorArity,
    Gauge.PlacedMixedGraphTaylorCoefficients.arities,if_neg he]

theorem inputOuterArity (hv : H.vertex ∈ S) :
    pulledOuterArity (vectorArity H.vertex) (anchoredPartitionEquiv ha hi) = fun _ ↦ 2 := by
  funext v
  have he : ((coarseSourceEquiv hi).symm v).val ≠ H.vertex := by
    intro he
    exact ((coarseSourceEquiv hi).symm v).property (he.symm ▸ hv)
  simp only [pulledOuterArity,anchoredPartition_outer,vectorArity,
    Gauge.PlacedMixedGraphTaylorCoefficients.arities,if_neg he]

theorem inputInnerArity (hv : H.vertex ∈ S) :
    pulledInnerArity (vectorArity H.vertex) (anchoredPartitionEquiv ha hi) =
      vectorArity (inputVectorIndex H ha hv) := by
  funext v
  have he : ((shapeSourceEquiv ha).symm v).val = H.vertex ↔ v = inputVectorIndex H ha hv := by
    constructor
    · intro h
      apply (shapeSourceEquiv ha).symm.injective
      simpa only [inputVectorIndex,Equiv.symm_apply_apply] using (Subtype.ext h :
        (shapeSourceEquiv ha).symm v = ⟨H.vertex,hv⟩)
    · intro h
      rw [h]
      simp [inputVectorIndex]
  simp only [pulledInnerArity,anchoredPartition_inner,vectorArity,
    Gauge.PlacedMixedGraphTaylorCoefficients.arities,he]

end Physical


theorem castGraph_reindex_boundary {n m M L : ℕ} {q p : Fin n → ℕ}
    (hq : q = p) (hm : m = L) (hM : M = L) (e : Fin M ≃ Fin m)
    (he : ∀ j, (e j).val = j.val) (G : Graph q m) :
    castGraph hq hM (G.reindex (Equiv.refl _) e) = castGraph hq hm G := by
  subst M
  subst m
  have he' : e = Equiv.refl _ := by ext j; exact he j
  subst e
  rw [MainRealGraftPhysicalCoefficient.reindex_refl]

section Actual
variable {N : ℕ} {i a : Fin (N+1)} {S : Finset (Fin (N+1))} {l u : Fin 3}
variable (H : VectorGraph N 2) (ha : a ∈ S) (hi : i ∉ S)

theorem outputOutsideM (hs : shapeM l u = 2) : outsideM l u = 0 := by
  have hh := boundary_card_sum (l := l) (u := u)
  omega

theorem inputOutsideM (hs : shapeM l u = 1) : outsideM l u = 1 := by
  have hh := boundary_card_sum (l := l) (u := u)
  omega

def outputPhysicalCarrier (hv : H.vertex ∉ S) (hlt : l < u) (hs : shapeM l u = 2) :
    VectorGraph (coarseN i S + (shapeN a S+1)) 2 :=
  outputCarrier (outputVectorIndex H hi hv)
    (castGraph (by rw [outputOuterArity H ha hi hv,outputInnerArity H ha hi hv])
      (by have hh := outputOutsideM hs; omega) (orderedGraph H.graph ha hi hlt))

def inputPhysicalCarrier (hv : H.vertex ∈ S) (hlt : l < u) (hs : shapeM l u = 1) :
    VectorGraph (shapeN a S + (coarseN i S+1)) 2 :=
  inputCarrier (inputVectorIndex H ha hv)
    (castGraph (by rw [inputOuterArity H ha hi hv,inputInnerArity H ha hi hv])
      (by have hh := inputOutsideM hs; omega) (orderedGraph H.graph ha hi hlt))

def physicalInputSlot (hlt : l < u) (hs : shapeM l u = 1) : Fin 2 :=
  Fin.cast (by rw [inputOutsideM hs]) (centerSlot hlt.le)

variable (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃
    KontsevichGraph.General.Edge (vectorArity H.vertex))
    (hc : Fintype.card {j // (graphEdges H.graph order j).1 ∈ S} = shapeDegree a S l u)

theorem canonical_graft_eq_outputProfile (hv : H.vertex ∉ S) (hlt : l < u)
    (hs : shapeM l u = 2) :
    GraphGeneralWeightedGraft.graftProfile (centerSlot hlt.le)
      (outerCoefficient H.graph ha hi order hc) (innerCoefficient H.graph ha hi order hc hlt)
      (orderedGraph H.graph ha hi hlt) =
    outputProfile (rawVelocityWeight (coarseN i S)) (rawBinaryWeight (shapeN a S+1))
      (outputPhysicalCarrier H ha hi hv hlt hs) := by
  apply graftProfile_eq_outputProfile (outputVectorIndex H hi hv)
    (outputOuterArity H ha hi hv) (outputInnerArity H ha hi hv) (outputOutsideM hs) (by omega)
  · intro G
    exact canonicalWeight_eq_rawVelocity_cast _ _ (by rw [outputOutsideM hs]) G _
  · intro G
    unfold innerCoefficient
    rw [canonicalWeight_eq_rawBinary_cast (outputInnerArity H ha hi hv) hs]
    congr 1
    apply castGraph_reindex_boundary
    intro j
    rfl

theorem canonical_graft_eq_inputProfile (hv : H.vertex ∈ S) (hlt : l < u)
    (hs : shapeM l u = 1) :
    GraphGeneralWeightedGraft.graftProfile (centerSlot hlt.le)
      (outerCoefficient H.graph ha hi order hc) (innerCoefficient H.graph ha hi order hc hlt)
      (orderedGraph H.graph ha hi hlt) =
    inputProfile (physicalInputSlot hlt hs) (rawVelocityWeight (shapeN a S))
      (rawBinaryWeight (coarseN i S+1)) (inputPhysicalCarrier H ha hi hv hlt hs) := by
  apply graftProfile_eq_inputProfile (inputVectorIndex H ha hv)
    (inputOuterArity H ha hi hv) (inputInnerArity H ha hi hv) (inputOutsideM hs) (by omega)
  · intro G
    exact canonicalWeight_eq_rawBinary_cast _ (by rw [inputOutsideM hs]) G _
  · intro G
    unfold innerCoefficient
    rw [canonicalWeight_eq_rawVelocity_cast _ (inputInnerArity H ha hi hv) hs]
    congr 2
    apply castGraph_reindex_boundary
    intro j
    rfl

end Actual


section PhysicalValue
open MixedRealPhysicalFaces MixedRealUnconditionalWeight
variable {N : ℕ} (H : VectorGraph N 2) (K : Key N H.vertex)

theorem outputShapeM (hv : H.vertex ∉ K.S) : shapeM K.l K.u = 2 := by
  rw [show shapeM K.l K.u = (boundaryClusterBlock K.l K.u).card from Fintype.card_coe _]
  simpa only [if_neg hv] using K.property.2.2.2

theorem inputShapeM (hv : H.vertex ∈ K.S) : shapeM K.l K.u = 1 := by
  rw [show shapeM K.l K.u = (boundaryClusterBlock K.l K.u).card from Fintype.card_coe _]
  simpa only [if_pos hv] using K.property.2.2.2

/-- A physical output face is exactly its individual output coefficient. -/
theorem normalized_physicalValue_eq_outputProfile (hv : H.vertex ∉ K.S) :
    MixedPairedEdgeRelabelling.normalization H * physicalValue H K =
      outputProfile (rawVelocityWeight (coarseN K.outside K.S))
        (rawBinaryWeight (shapeN K.inside K.S+1))
        (outputPhysicalCarrier H K.inside_mem K.outside_not_mem hv K.block_lt (outputShapeM H K hv)) := by
  rw [normalized_physicalValue_eq_graftProfile,fibreSign_key,if_neg hv,one_mul]
  exact canonical_graft_eq_outputProfile H K.inside_mem K.outside_not_mem
    (edgeOrder H K) (internal_count H K) hv K.block_lt (outputShapeM H K hv)

/-- The two input chambers carry the negative of their individual input
coefficient. This does not replace a face by the three-term action profile. -/
theorem normalized_physicalValue_eq_neg_inputProfile (hv : H.vertex ∈ K.S) :
    MixedPairedEdgeRelabelling.normalization H * physicalValue H K =
      -inputProfile (physicalInputSlot K.block_lt (inputShapeM H K hv))
        (rawVelocityWeight (shapeN K.inside K.S))
        (rawBinaryWeight (coarseN K.outside K.S+1))
        (inputPhysicalCarrier H K.inside_mem K.outside_not_mem hv K.block_lt (inputShapeM H K hv)) := by
  rw [normalized_physicalValue_eq_graftProfile,fibreSign_key,if_pos hv,neg_one_mul]
  rw [canonical_graft_eq_inputProfile H K.inside_mem K.outside_not_mem
    (edgeOrder H K) (internal_count H K) hv K.block_lt (inputShapeM H K hv)]

end PhysicalValue

end EnvelopingIsomorphism.Deformation.MixedRealGraftPhysicalCoefficient
