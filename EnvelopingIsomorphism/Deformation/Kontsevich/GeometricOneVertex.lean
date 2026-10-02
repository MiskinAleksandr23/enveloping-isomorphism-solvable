import EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeights
import EnvelopingIsomorphism.Deformation.Kontsevich.OneVertexMeasureCoordinates

/-! Identify the genuine general-coordinate integral with the already evaluated
one-vertex integrals, preserving the explicit real-coordinate orientation. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeights

open MeasureTheory
open scoped BigOperators

variable {m : ℕ}

/-- The arithmetic cast from external labels to the complete zero-interior coordinate labels. -/
def zeroIndex (m : ℕ) : Fin m ≃ Fin (GraphForms.dimension 0 m) :=
  finCongr (by simp [GraphForms.dimension])

@[simp] theorem externalBasisIndex_zero (j : Fin m) :
    GraphForms.externalBasisIndex 0 j = zeroIndex m j := by
  apply Fin.ext
  simp [GraphForms.externalBasisIndex, GraphForms.coordinateIndexEquiv, zeroIndex]

/-- Renaming the finite real-coordinate indices preserves the actual product Lebesgue measure. -/
def zeroMeasureChart (m : ℕ) : (Fin m → ℝ) ≃ᵐ (Fin (GraphForms.dimension 0 m) → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin (GraphForms.dimension 0 m) ↦ ℝ) (zeroIndex m)

@[simp] theorem zeroMeasureChart_apply (x : Fin m → ℝ) (j : Fin m) :
    zeroMeasureChart m x (zeroIndex m j) = x j :=
  MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin (GraphForms.dimension 0 m) ↦ ℝ)
    (zeroIndex m) x j

theorem zeroMeasureChart_preserving (m : ℕ) : MeasurePreserving (zeroMeasureChart m) :=
  volume_measurePreserving_piCongrLeft (fun _ : Fin (GraphForms.dimension 0 m) ↦ ℝ) (zeroIndex m)

theorem realCoordinates_zero (x : GraphForms.Coordinates 0 m) (j : Fin m) :
    GraphForms.realCoordinates 0 m x (zeroIndex m j) = x.2 j := by
  simpa only [externalBasisIndex_zero] using GraphForms.realCoordinates_external x j

theorem realCoordinates_zero_symm (x : Fin m → ℝ) :
    (GraphForms.realCoordinates 0 m).symm (zeroMeasureChart m x) = (0, x) := by
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · funext j
    rw [← realCoordinates_zero, (GraphForms.realCoordinates 0 m).apply_symm_apply]
    exact zeroMeasureChart_apply x j

theorem realDomain_zero_preimage (m : ℕ) :
    zeroMeasureChart m ⁻¹' realDomain 0 m = {x : Fin m → ℝ | StrictMono x} := by
  ext x
  simp only [realDomain, Set.mem_preimage, GraphForms.admissibleSet,
    Set.mem_setOf_eq, realCoordinates_zero_symm, GraphForms.admissible_zero_iff]

/-- Canonical outgoing order: the j-th edge goes to external vertex j. -/
def canonicalOneVertexEdges (m : ℕ) : Fin (GraphForms.dimension 0 m) → GraphForms.Edge 0 m :=
  fun j ↦ ⟨0, Sum.inr ((zeroIndex m).symm j)⟩

@[simp] theorem canonicalOneVertexEdges_index (j : Fin m) :
    canonicalOneVertexEdges m (zeroIndex m j) = ⟨0, Sum.inr j⟩ := by
  simp [canonicalOneVertexEdges]

theorem canonicalOneVertexEdgeForm (x v : Fin m → ℝ) (j : Fin m) :
    GraphForms.edgeForm (canonicalOneVertexEdges m (zeroIndex m j)) (0, x)
        (fun _ : Fin 1 ↦ (0, v)) =
      oneVertexEdgeForm j x (fun _ : Fin 1 ↦ v) := by
  rw [canonicalOneVertexEdges_index]
  rfl

theorem realDensity_canonical_oneVertex (x : Fin m → ℝ) :
    realDensity (canonicalOneVertexEdges m) (zeroMeasureChart m x) =
      oneVertexTopForm x (fun i ↦ Pi.single i 1) := by
  rw [realDensity, realCoordinates_zero_symm, GraphForms.topDensity,
    GraphForms.topForm_apply, oneVertexTopForm_apply]
  rw [← Matrix.det_submatrix_equiv_self (zeroIndex m)]
  congr 1
  funext i j
  simp only [Matrix.submatrix_apply]
  have hi : GraphForms.realBasis 0 m (zeroIndex m i) = GraphForms.externalTangent i := by
    simpa only [externalBasisIndex_zero] using GraphForms.realBasis_external (n := 0) i
  rw [hi]
  exact canonicalOneVertexEdgeForm x (Pi.single i 1) j

theorem rawIntegral_canonical_oneVertex (m : Fin 4) :
    rawIntegral (canonicalOneVertexEdges m.val) = oneVertexRawIntegral m := by
  have h := (zeroMeasureChart_preserving m.val).setIntegral_preimage_emb
    (zeroMeasureChart m.val).measurableEmbedding
    (realDensity (canonicalOneVertexEdges m.val)) (realDomain 0 m.val)
  rw [realDomain_zero_preimage] at h
  simp only [realDensity_canonical_oneVertex] at h
  rw [rawIntegral, ← h]
  exact integral_strictMono_eq_oneVertexChartIntegral m _

theorem absolutelyIntegrable_canonical_oneVertex (m : Fin 4) :
    AbsolutelyIntegrable (canonicalOneVertexEdges m.val) := by
  have h := (zeroMeasureChart_preserving m.val).integrableOn_comp_preimage
    (zeroMeasureChart m.val).measurableEmbedding
    (f := realDensity (canonicalOneVertexEdges m.val)) (s := realDomain 0 m.val)
  rw [realDomain_zero_preimage] at h
  simp only [Function.comp_def, realDensity_canonical_oneVertex] at h
  apply h.mp
  apply (integrableOn_strictMono_iff_oneVertexChartIntegrable m _).mpr
  exact oneVertexChartIntegrable_topForm m

/-- The one-vertex graph corresponding to an outgoing permutation. -/
def oneVertexGraph (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    KontsevichGraph.General.Graph (fun _ : Fin 1 ↦ m) m where
  target e := Sum.inr (σ e.2)
  noLoops := by intros; simp
  distinctTargets _ := Sum.inr_injective.comp σ.injective

theorem oneVertex_edgeCount (m : ℕ) :
    ∑ _ : Fin 1, m = GraphForms.dimension 0 m := by simp [GraphForms.dimension]

/-- Explicit one-vertex edge order, including the real-coordinate arithmetic cast. -/
def oneVertexOrder (m : ℕ) :
    Fin (GraphForms.dimension 0 m) ≃ KontsevichGraph.General.Edge (fun _ : Fin 1 ↦ m) where
  toFun a := ⟨0, (zeroIndex m).symm a⟩
  invFun e := zeroIndex m e.2
  left_inv a := (zeroIndex m).apply_symm_apply a
  right_inv e := by
    rcases e with ⟨v, a⟩
    have hv : v = 0 := Subsingleton.elim _ _
    subst v
    simp

theorem canonicalOrder_oneVertex (m : ℕ) :
    canonicalOrder (oneVertex_edgeCount m) = oneVertexOrder m := by
  apply Equiv.symm_bijective.injective
  apply Equiv.ext
  rintro ⟨v, a⟩
  apply Fin.ext
  change ((vertexMajorEdgeEquiv (fun _ : Fin 1 ↦ m)).symm ⟨v, a⟩).val = a.val
  rw [vertexMajorEdgeEquiv_symm_val]
  have hv : v = 0 := by omega
  subst v
  simp [edgePrefix]

theorem orderedEdges_oneVertex (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    orderedEdges (oneVertexGraph m σ) (oneVertexOrder m) =
      fun a ↦ canonicalOneVertexEdges m ((Equiv.permCongr (zeroIndex m) σ) a) := by
  funext a
  simp [orderedEdges, oneVertexGraph, oneVertexOrder, canonicalOneVertexEdges,
    Equiv.permCongr_apply]

theorem rawIntegral_oneVertex (m : Fin 4) (σ : Equiv.Perm (Fin m.val)) :
    rawIntegral (orderedEdges (oneVertexGraph m.val σ) (oneVertexOrder m.val)) =
      labelledOneVertexRawIntegral m σ := by
  rw [orderedEdges_oneVertex, rawIntegral_permute, rawIntegral_canonical_oneVertex,
    Equiv.Perm.sign_permCongr, labelledOneVertexRawIntegral_eq]

/-- The general actual geometric weight is exactly the previously evaluated
labelled one-vertex weight, with both factorial conventions preserved. -/
theorem canonicalWeight_oneVertex (m : Fin 4) (σ : Equiv.Perm (Fin m.val)) :
    canonicalWeight (oneVertexGraph m.val σ) (oneVertex_edgeCount m.val) =
      labelledOneVertexWeight m σ := by
  rw [canonicalWeight, canonicalOrder_oneVertex, geometricWeight, rawIntegral_oneVertex]
  simp only [outgoingFactor, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one,
    GraphForms.dimension, Nat.zero_mul, Nat.zero_add, labelledOneVertexWeight]

theorem canonicalEffectiveWeight_oneVertex (m : Fin 4) (σ : Equiv.Perm (Fin m.val)) :
    canonicalEffectiveWeight (oneVertexGraph m.val σ) (oneVertex_edgeCount m.val) =
      labelledOneVertexWeight m σ := by
  rw [canonicalEffectiveWeight, canonicalWeight_oneVertex, effectiveMCWeight_one]

end EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeights
