import EnvelopingIsomorphism.Deformation.Kontsevich.SimpleFaceChartPoint
import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFaceDomainConverse

/-! Actual simple-face graph densities are invariant under the integer angle
translations used in the native atlas. No scalar invariance is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestPeriodicDensity
open InteriorGraphFaceCoordinates InteriorFiberAngleSplit SimpleProductPhaseIdentification
open PairedForestProductGraphDensity
open scoped Classical
variable {n m : ℕ} {i a b : Fin n} {T : Finset (Fin n)}

/-- Rotating the entire planar shape by an integral turn preserves the actual
pulled-back angular edge form. -/
theorem rotatedEdgeForm_shift {N : ℕ} (s t : Point N) (hst : s ≠ t)
    (p : Parameters N) (hp : p.2 ∈ shapeConfiguration N) (k : ℤ) :
    rotatedEdgeForm s t (p.1 + k * (2 * Real.pi),p.2) = rotatedEdgeForm s t p := by
  exact (rotatedEdgeForm_split_on_configuration (p.1 + k * (2 * Real.pi),p.2) hp s t hst).trans
    (rotatedEdgeForm_split_on_configuration p hp s t hst).symm

/-- The covectors used in graph factorization are unchanged by a full turn,
including every original edge and outgoing position. -/
theorem faceCovector_shift (ha : a ∈ T) (hb : b ∈ T) (hba : b ≠ a)
    (hg : i ∈ T → a = i) (p : ProductCoordinates i a b T m)
    (hp : (toAngular p).toFree.OpenConditions) (k : ℤ) (e : Edge n m)
    (hne : e.2 ≠ Sum.inl e.1) : faceCovector e (shift k p) = faceCovector e p := by
  have hsc := shape_coarse_of_openConditions_toAngular ha hb hba hg p hp
  have hp' := openConditions_toAngular ha hba (shift k p) hsc.1 hsc.2
  by_cases hint : IsInternal T e
  · rw [faceCovector_internal hba (shift k p) hp' e hint hne,
      faceCovector_internal hba p hp e hint hne]
    congr 1
    exact congrArg formLinear (rotatedEdgeForm_shift (planarEdge e hint).1 (planarEdge e hint).2
      (planarEdge_nonloop e hint hne) p.1 hsc.1 k)
  · rw [faceCovector_external (shift k p) hp' e hint,faceCovector_external p hp e hint]
    rfl

variable {N r : ℕ} (hdim : GraphForms.dimension N m = r+1)
  (x : Compactification (0 : Fin (N+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : ForestRadialFaceClassification.kind 0 x o = .paired)

theorem productDensity_shift (es : Fin r → GraphForms.Edge N m)
    (hne : ∀ q, (es q).target ≠ Sum.inl (es q).source)
    (p : PairedForestSmoothProduct.Product x o ho)
    (hp : (toAngular p).toFree.OpenConditions) (k : ℤ) :
    productDensity hdim x o ho es (shift k p) = productDensity hdim x o ho es p := by
  change Matrix.det (fun i j : Fin r ↦ faceCovector (rawEdges es j) (shift k p)
      (PairedForestCartesianChange.cartesian hdim x o ho (BoxStokes.standardBasis r i))) =
    Matrix.det (fun i j : Fin r ↦ faceCovector (rawEdges es j) p
      (PairedForestCartesianChange.cartesian hdim x o ho (BoxStokes.standardBasis r i)))
  congr 1
  funext i j
  rw [faceCovector_shift (PairedForestSimpleCluster.anchor_mem x o ho)
    (PairedForestSimpleCluster.reference_mem x o ho) (PairedForestSimpleCluster.reference_ne_anchor x o ho)
    (PairedForestSimpleCluster.anchor_global x o ho) p hp k (rawEdges es j) (hne j)]

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestPeriodicDensity
