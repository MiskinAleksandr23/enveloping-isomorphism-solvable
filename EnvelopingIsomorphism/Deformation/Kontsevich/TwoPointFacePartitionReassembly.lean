import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFacePartitionReassembly
import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointBinaryFaceWeight

/-! Reassembly of the original ambient partition on the surviving simple
interior face. Its L1 estimate and whole-face integral are proved; no weighted
integral identity is assumed. Identification with native chart-image fibres
remains separate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointFacePartitionReassembly
open InteriorFacePartitionReassembly InteriorGraphFaceCoordinates InteriorFiberAngleSplit
open Set MeasureTheory
open scoped Classical
variable {n m : ℕ} {i a b : Fin (n+1)} {S : Finset (Fin (n+1))}
variable {J : Type*} [Fintype J]
variable (ρ : Partition J i m) (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i)
variable (edges : Fin (shapeDegree a b S + coarseDegree i a S m) → Edge (n+1) m)

/-- The original cutoff is bounded by one, so any proved whole-face L1 bound
passes to every localized density. This works for small as well as large faces. -/
theorem integrableOn_localizedDensity_of_integrable
    (hi : IntegrableOn (realFaceDensity edges) (FaceRegion i a b S m)) (j : J) :
    IntegrableOn (localizedDensity ρ ha hb hba hanchor edges j) (FaceRegion i a b S m) :=
  hi.bdd_mul (measurable_weight ρ ha hb hba hanchor j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (weight_nonneg ρ ha hb hba hanchor j x)]
      exact weight_le_one ρ ha hb hba hanchor j x)

/-- Exact finite reassembly from the original partition of unity. -/
theorem sum_integral_localizedDensity_of_integrable
    (hi : IntegrableOn (realFaceDensity edges) (FaceRegion i a b S m)) :
    (∑ j, ∫ x in FaceRegion i a b S m, localizedDensity ρ ha hb hba hanchor edges j x) =
      ∫ x in FaceRegion i a b S m, realFaceDensity edges x := by
  rw [← integral_finsetSum _ (fun j _ ↦
    integrableOn_localizedDensity_of_integrable ρ ha hb hba hanchor edges hi j)]
  exact setIntegral_congr_fun measurableSet_faceRegion
    (sum_localizedDensity ρ ha hb hba hanchor edges)

variable (hcount : Fintype.card {q // IsInternal S (edges q)} = shapeDegree a b S)
variable (hS : S.card = 2) (hne : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1)

include hS hne in
/-- Genuine small-face reassembly, including its circle factor and actual
coarse integral. Both weighted L1 and the value are unconditional. -/
theorem sum_integral_localizedDensity_twoPoint :
    (∀ j, IntegrableOn (localizedDensity ρ ha hb hba hanchor edges j) (FaceRegion i a b S m)) ∧
    (∑ j, ∫ x in FaceRegion i a b S m, localizedDensity ρ ha hb hba hanchor edges j x) =
      (Equiv.Perm.sign (edgeBlockPermutation edges hcount).symm : ℝ) *
        ((2 * Real.pi) * GeometricWeights.rawIntegral (coarseEdges edges hcount)) := by
  have h := TwoPointActualFaceIntegral.integral_realFaceDensity edges hcount ha hb hba hS hne
  exact ⟨integrableOn_localizedDensity_of_integrable ρ ha hb hba hanchor edges h.1,
    (sum_integral_localizedDensity_of_integrable ρ ha hb hba hanchor edges h.1).trans h.2⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointFacePartitionReassembly

namespace EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointFacePartitionReassembly
open UniformBinaryGraphs UniformBinaryContraction
open InteriorGraphFaceCoordinates InteriorFacePartitionReassembly
open TwoPointBinaryFaceAdmissibility TwoPointBinaryFaceWeight
open MeasureTheory
open scoped Classical
variable {n : ℕ} (v : Fin (n+1)) (H : BinaryGraph (n+2) 3)
  {i a b : Fin (n+2)}
  (ha : a ∈ cluster v) (hb : b ∈ cluster v) (hba : b ≠ a)
  (hanchor : i ∈ cluster v → a = i)
  (order : Fin (shapeDegree a b (cluster v) + coarseDegree i a (cluster v) 3) ≃
    KontsevichGraph.General.Edge (fun _ : Fin (n+2) ↦ 2))
  (hcount : Fintype.card {j // IsInternal (cluster v) (orderedEdges H order j)} = shapeDegree a b (cluster v))
  (c s : Fin 2) (hi : UniqueInternalAt v H c s) (hd : CoarseDistinct v H) (hx : ExitsDistinctAt v H c s)
  {J : Type*} [Fintype J] (ρ : Partition J i 3)

/-- The actual finite weighted partition sum gives the physical-pair scalar
with every edge-order sign retained. All partition and analytic inputs are
constructed; the only premises describe the selected admissible graph pair. -/
theorem normalized_sum_eq_physicalCoefficient :
    GeometricWeights.outgoingFactor (fun _ : Fin (n+2) ↦ 2) *
      (((2 * Real.pi) ^ (shapeDegree a b (cluster v) + coarseDegree i a (cluster v) 3))⁻¹ *
        ∑ j, ∫ x in FaceRegion i a b (cluster v) 3,
          localizedDensity ρ ha hb hba hanchor (orderedEdges H order) j x) =
      (3 / 2 : ℝ) * faceOrderingSign v H ha hanchor order hcount c s hi hd hx *
        GraphCurvaturePhysicalPairs.physicalCoefficient H
          (GraphCurvatureLabelCounting.movedPair v (Equiv.refl _)) := by
  have hL := (TwoPointActualFaceIntegral.integral_realFaceDensity
    (orderedEdges H order) hcount ha hb hba (cluster_card v)
    (fun q ↦ H.noLoops (order q).1 (order q).2)).1
  rw [sum_integral_localizedDensity_of_integrable ρ ha hb hba hanchor (orderedEdges H order) hL]
  exact normalized_integral_eq_physicalCoefficient v H ha hb hba hanchor order hcount c s hi hd hx

include hcount hi hd hx in
/-- For canonical source-major edges the two independently constructed edge
order signs cancel, leaving precisely the physical-pair coefficient. -/
theorem normalized_sum_sourceMajor_eq_physicalCoefficient
    (horder : order = sourceMajorOrder v ha hb hba hanchor) :
    GeometricWeights.outgoingFactor (fun _ : Fin (n+2) ↦ 2) *
      (((2 * Real.pi) ^ (shapeDegree a b (cluster v) + coarseDegree i a (cluster v) 3))⁻¹ *
        ∑ j, ∫ x in FaceRegion i a b (cluster v) 3,
          localizedDensity ρ ha hb hba hanchor (orderedEdges H order) j x) =
      (3 / 2 : ℝ) * GraphCurvaturePhysicalPairs.physicalCoefficient H
        (GraphCurvatureLabelCounting.movedPair v (Equiv.refl _)) := by
  rw [normalized_sum_eq_physicalCoefficient v H ha hb hba hanchor order hcount c s hi hd hx ρ,
    faceOrderingSign_sourceMajor v H ha hb hba hanchor order hcount c s hi hd hx horder, mul_one]

end EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointFacePartitionReassembly
