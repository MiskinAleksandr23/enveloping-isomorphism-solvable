import EnvelopingIsomorphism.Deformation.MainPurePhysicalFace
import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryGraphMatching

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.MainPurePhysicalIntegral
open Kontsevich MainPurePhysicalFace BoundaryGraphFaceFactorization
open PureBoundaryGraphQuotient PureBoundaryGraphIntegral
open OrientedFormChangeVariables MeasureTheory BoxStokes
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1) (F : FaceData m)

/-- The actual physical form is the increasing-coordinate quotient density. -/
theorem integral_eq_rawIntegral (es : Fin r → GraphForms.Edge n m) :
    (∫ y in region hdim F, density (form hdim F es) y) =
      GeometricWeights.rawIntegral (fun j ↦ quotientEdge F.ordered
        (es (finCongr (degree_eq hdim F) j))) := by
  have he := degree_eq hdim F
  subst r
  have hreg : region hdim F = GeometricWeights.realDomain n (outsideM F.l F.u + 1) := by
    rw [PureBoundaryGraphDomain.realDomain_eq_native_preimage F.ordered F.left_mem F.right_mem
      F.endpoints F.card_eq F.left_eq F.right_eq]
    rfl
  rw [hreg]
  unfold GeometricWeights.rawIntegral
  apply setIntegral_congr_fun (GeometricWeights.measurableSet_realDomain _ _)
  intro y hy
  change PureBoundaryClusterForms.faceGraphForm _ F.a F.b es
      ((faceCoordinates F.ordered F.a F.b F.left_mem F.right_mem F.endpoints.ne F.card_eq).symm y)
      (fun j ↦ (faceCoordinates F.ordered F.a F.b F.left_mem F.right_mem F.endpoints.ne F.card_eq).symm (Pi.single j 1)) = _
  rw [twoPoint_faceGraphForm_eq_quotient F.ordered F.a F.b F.left_mem F.right_mem F.endpoints.ne F.card_eq]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,faceCoordinates,
    ContinuousLinearEquiv.symm_trans_apply,ContinuousLinearEquiv.apply_symm_apply,
    Function.comp_def,ContinuousLinearEquiv.coe_coe]
  change GraphForms.topForm _ ((GraphForms.realCoordinates _ _).symm y)
      (fun j ↦ (GraphForms.realCoordinates _ _).symm (Pi.single j 1)) = _
  have hb (j : Fin (Degree (n := n) (l := F.l) (u := F.u))) :
      (GraphForms.realCoordinates n (outsideM F.l F.u + 1)).symm (Pi.single j (1 : ℝ)) =
        GraphForms.realBasis n (outsideM F.l F.u + 1) j := by
    simp [GraphForms.realCoordinates,Module.Basis.equivFun_symm_apply]
  simp_rw [hb]
  rfl

open PureBoundaryGraphMatching

/-- Source-major graph edges in any proved face degree. -/
def edges {q : Fin (n+1) → ℕ} (G : KontsevichGraph.General.Graph q m)
    (hq : ∑ v, q v = r) : Fin r → GraphForms.Edge n m := fun j ↦
  let e := ((finCongr hq.symm).trans (vertexMajorEdgeEquiv q)) j
  ⟨e.1,G.target e⟩

theorem normalized_integral_eq_quotientWeight {q : Fin (n+1) → ℕ}
    (G : KontsevichGraph.General.Graph q m) (hq : ∑ v, q v = r)
    (hd : QuotientDistinct F.ordered G) :
    GeometricWeights.outgoingFactor q * ((2 * Real.pi)^r)⁻¹ *
      (∫ y in region hdim F, density (form hdim F (edges G hq)) y) =
      GeometricWeights.canonicalWeight (quotientGraph F.ordered G hd)
        (hq.trans (degree_eq hdim F).symm) := by
  rw [integral_eq_rawIntegral]
  have he := degree_eq hdim F
  cases he
  rfl

theorem integral_eq_zero_of_not_distinct {q : Fin (n+1) → ℕ}
    (G : KontsevichGraph.General.Graph q m) (hq : ∑ v, q v = r)
    (hd : ¬ QuotientDistinct F.ordered G) :
    (∫ y in region hdim F, density (form hdim F (edges G hq)) y) = 0 := by
  rw [integral_eq_rawIntegral]
  have he := degree_eq hdim F
  cases he
  change GeometricWeights.rawIntegral (fun j ↦ quotientEdge F.ordered
    (originalEdges G (GeometricWeights.canonicalOrder hq) j)) = 0
  unfold GeometricWeights.rawIntegral
  rw [quotientDensity_eq_zero_of_not_distinct F.ordered G _ hd]
  simp

end EnvelopingIsomorphism.Deformation.MainPurePhysicalIntegral
