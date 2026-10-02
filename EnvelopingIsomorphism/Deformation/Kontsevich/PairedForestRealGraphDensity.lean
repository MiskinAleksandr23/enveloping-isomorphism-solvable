import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestProductGraphDensity
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestWeightedSignedChange
import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFacePartitionReassembly

/-! Exact equality of the graph density used in native paired change of
variables and the real product density used in whole-face integration. The
simultaneous frame/edge reindexing contributes no extra sign. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestRealGraphDensity
open PairedForestSimpleCluster PairedForestProductGraphDensity
open InteriorGraphFaceCoordinates BoxStokes GraphFormProduct
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : ForestRadialFaceClassification.kind 0 x o = .paired)

private theorem toProduct_faceFrame
    (j : Fin (shapeDegree (anchor x o ho) (reference x o ho) (S x o ho) +
      coarseDegree (0 : Fin (n+1)) (anchor x o ho) (S x o ho) m)) :
    toProduct (faceFrame j) =
      PairedForestCartesianChange.cartesian hdim x o ho (standardBasis r (frameIndex hdim x o ho j)) := by
  rw [cartesian_frame]
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases j with
  | inl j => simp [faceFrame, productVectors, toProduct]
  | inr j =>
    simp only [faceFrame, productVectors, Equiv.symm_apply_apply, Sum.elim_inr]
    apply Prod.ext
    · rfl
    · exact ForestGraphIntegrability.nativeCoordinates_symm_basis j

/-- Both integration endpoints use the literal same graph coefficient, not
merely proportional forms or independently chosen determinant signs. -/
theorem productDensity_toProduct (edges : Fin r → GraphForms.Edge n m)
    (y : RealProductCoordinates (0 : Fin (n+1)) (anchor x o ho) (reference x o ho) (S x o ho) m) :
    productDensity hdim x o ho edges (toProduct y) =
      realFaceDensity (framedEdges hdim x o ho edges) y := by
  unfold realFaceDensity toAngularReal
  rw [fderiv_comp y (contDiff_toAngular.differentiable (by simp)).differentiableAt
    toProduct.differentiableAt, toProduct.fderiv]
  change Matrix.det (fun i j : Fin r ↦
      faceCovector (rawEdges edges j) (toProduct y)
        (PairedForestCartesianChange.cartesian hdim x o ho (standardBasis r i))) =
    Matrix.det (fun i j ↦ faceCovector (rawEdges edges (frameIndex hdim x o ho j)) (toProduct y)
      (toProduct (faceFrame i)))
  simp_rw [toProduct_faceFrame hdim x o ho]
  exact (Matrix.det_submatrix_equiv_self (frameIndex hdim x o ho) _).symm

open InteriorFacePartitionReassembly

/-- The native paired cutoff in real product coordinates is exactly the
weight used by finite whole-face partition reassembly. -/
theorem productCutoff_toProduct_eq_weight {J : Type*} [Fintype J]
    (ρ : Partition J (0 : Fin (n+1)) m) (j : J)
    (y : RealProductCoordinates (0 : Fin (n+1)) (anchor x o ho) (reference x o ho) (S x o ho) m)
    (hy : y ∈ FaceRegion (0 : Fin (n+1)) (anchor x o ho) (reference x o ho) (S x o ho) m) :
    PairedForestOverlapJacobian.productCutoff x o ho (ρ j) (toProduct y) =
      weight ρ (anchor_mem x o ho) (reference_mem x o ho) (reference_ne_anchor x o ho)
        (anchor_global x o ho) j y := by
  rw [weight_eq ρ (anchor_mem x o ho) (reference_mem x o ho) (reference_ne_anchor x o ho)
    (anchor_global x o ho) j y hy]
  unfold PairedForestOverlapJacobian.productCutoff CompactDRAmbientPartition.cutoff
    CompactDRCoordinates.embedding
  rw [InteriorFaceDRCoordinates.ambient_eq_boundaryPoint (anchor_mem x o ho) (reference_mem x o ho)
    (anchor_global x o ho) (toProduct y)
    (openConditions_toAngular (anchor_mem x o ho) (reference_ne_anchor x o ho) (toProduct y) hy.1.2 hy.2)]
  rfl

/-- The entire weighted density in native paired CV agrees literally with
the weighted density in the real simple-face integral endpoint. -/
theorem localizedDensity_eq {J : Type*} [Fintype J]
    (ρ : Partition J (0 : Fin (n+1)) m) (j : J) (edges : Fin r → GraphForms.Edge n m)
    (y : RealProductCoordinates (0 : Fin (n+1)) (anchor x o ho) (reference x o ho) (S x o ho) m)
    (hy : y ∈ FaceRegion (0 : Fin (n+1)) (anchor x o ho) (reference x o ho) (S x o ho) m) :
    PairedForestOverlapJacobian.productCutoff x o ho (ρ j) (toProduct y) *
      productDensity hdim x o ho edges (toProduct y) =
    localizedDensity ρ (anchor_mem x o ho) (reference_mem x o ho) (reference_ne_anchor x o ho)
      (anchor_global x o ho) (framedEdges hdim x o ho edges) j y := by
  rw [productCutoff_toProduct_eq_weight x o ho ρ j y hy, productDensity_toProduct]
  rfl

/-- Original finite forest cutoffs reassemble pointwise on the full simple
face, with no assumed weighted matching identity. -/
theorem sum_weightedDensity {J : Type*} [Fintype J]
    (ρ : Partition J (0 : Fin (n+1)) m) (edges : Fin r → GraphForms.Edge n m)
    (y : RealProductCoordinates (0 : Fin (n+1)) (anchor x o ho) (reference x o ho) (S x o ho) m)
    (hy : y ∈ FaceRegion (0 : Fin (n+1)) (anchor x o ho) (reference x o ho) (S x o ho) m) :
    (∑ j, PairedForestOverlapJacobian.productCutoff x o ho (ρ j) (toProduct y) *
      productDensity hdim x o ho edges (toProduct y)) =
      realFaceDensity (framedEdges hdim x o ho edges) y := by
  simp_rw [localizedDensity_eq hdim x o ho ρ _ edges y hy]
  exact sum_localizedDensity ρ (anchor_mem x o ho) (reference_mem x o ho)
    (reference_ne_anchor x o ho) (anchor_global x o ho) (framedEdges hdim x o ho edges) y hy

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestRealGraphDensity
