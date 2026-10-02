import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCartesianChange
import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarCoarseCartesianBasis
import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceIntegral

/-! Actual simple graph forms and their coefficients in the explicitly
volume-preserving Cartesian product frame used by native paired-face CV. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestProductGraphDensity
open PairedForestSimpleCluster PairedForestSmoothProduct PairedForestProductChart
open InteriorGraphFaceCoordinates BoxStokes ContinuousAlternatingMap OrientedFormChangeVariables
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : ForestRadialFaceClassification.kind 0 x o = .paired)

abbrev rawEdges (edges : Fin r → GraphForms.Edge n m) : Fin r → InteriorGraphFaceCoordinates.Edge (n + 1) m :=
  fun j ↦ ((edges j).source, (edges j).target)

def productForm (edges : Fin r → GraphForms.Edge n m) (p : Product x o ho) :
    Product x o ho [⋀^Fin r]→L[ℝ] ℝ :=
  (InteriorGraphFaceCoordinates.graphForm (rawEdges edges) (toAngular p)).compContinuousLinearMap
    (fderiv ℝ toAngular p)

def productDensity (edges : Fin r → GraphForms.Edge n m) (p : Product x o ho) : ℝ :=
  productForm x o ho edges p (fun j ↦ PairedForestCartesianChange.cartesian hdim x o ho (standardBasis r j))

/-- Exact coefficient transformation under the actual native local chart. -/
theorem pullback_density (edges : Fin r → GraphForms.Edge n m) (z₀ : Source hdim x o)
    {w : Coord r} (hw : w ∈ (localChart hdim x o ho z₀).source) :
    (productForm x o ho edges (localChart hdim x o ho z₀ w)).compContinuousLinearMap
        (fderiv ℝ (localChart hdim x o ho z₀) w) (standardBasis r) =
      PairedForestCartesianChange.jacobian hdim x o ho z₀ w * productDensity hdim x o ho edges (localChart hdim x o ho z₀ w) := by
  let C := PairedForestCartesianChange.cartesian hdim x o ho
  let e := PairedForestCartesianChange.chart hdim x o ho z₀
  have hD := (C.hasFDerivAt.comp w
    ((PairedForestCartesianChange.chart_contDiffAt hdim x o ho z₀
      ((PairedForestCartesianChange.chart_source hdim x o ho z₀).symm ▸ hw)).differentiableAt (by simp)).hasFDerivAt).fderiv
  have he : C ∘ e = localChart hdim x o ho z₀ := funext (PairedForestCartesianChange.cartesian_chart hdim x o ho z₀)
  rw [he] at hD
  rw [hD]
  exact topForm_linear_change
    ((productForm x o ho edges (localChart hdim x o ho z₀ w)).compContinuousLinearMap C.toContinuousLinearMap)
    (fderiv ℝ e w)

include hdim

/-- Exact total degree in the fixed planar/coarse frame. -/
theorem frameDegree_eq : shapeDegree (anchor x o ho) (reference x o ho) (S x o ho) +
    coarseDegree (0 : Fin (n + 1)) (anchor x o ho) (S x o ho) m = r := by
  rw [totalDegree_eq (anchor_mem x o ho) (reference_mem x o ho) (reference_ne_anchor x o ho) (anchor_global x o ho)]
  have hpos := hdim
  unfold GraphForms.dimension at hpos
  omega

/-- The only change to the original edge order is the proved equality of its length. -/
def frameIndex : Fin (shapeDegree (anchor x o ho) (reference x o ho) (S x o ho) +
    coarseDegree (0 : Fin (n + 1)) (anchor x o ho) (S x o ho) m) ≃ Fin r :=
  finCongr (frameDegree_eq hdim x o ho)

def framedEdges (edges : Fin r → GraphForms.Edge n m) := fun j ↦ rawEdges edges (frameIndex hdim x o ho j)

theorem cartesian_frame (j : Fin (shapeDegree (anchor x o ho) (reference x o ho) (S x o ho) +
    coarseDegree (0 : Fin (n + 1)) (anchor x o ho) (S x o ho) m)) :
    PairedForestCartesianChange.cartesian hdim x o ho (standardBasis r (frameIndex hdim x o ho j)) =
      GraphFormProduct.productVectors (InteriorFiberAngleSplit.fiberFrame (shapeN (anchor x o ho) (reference x o ho) (S x o ho)))
        (GraphForms.realBasis (coarseN 0 (anchor x o ho) (S x o ho)) m) j := by
  have hcast : (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin r ↦ ℝ)
      (finCongr (PairedForestCartesianChange.dimension_eq hdim x o ho))).symm
      (standardBasis r (frameIndex hdim x o ho j)) =
    standardBasis _ (PlanarCoarseCartesian.productIndex _ _ _ j) := by
    ext k
    change standardBasis r (frameIndex hdim x o ho j)
      (finCongr (PairedForestCartesianChange.dimension_eq hdim x o ho) k) = _
    simp [standardBasis, Pi.single_apply, frameIndex, PlanarCoarseCartesian.productIndex, Fin.ext_iff]

  unfold PairedForestCartesianChange.cartesian
  rw [ContinuousLinearEquiv.trans_apply, hcast]
  exact PlanarCoarseCartesian.cartesian_standardBasis _ _ _ j

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestProductGraphDensity
