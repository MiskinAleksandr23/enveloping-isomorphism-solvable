import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFaceNonzeroAdmissibility
import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointFacePartitionReassembly

/-! Whole-face L1 and large-face zero without an internal-degree premise.
Wrong-degree graph densities vanish pointwise; surviving degrees use the
proved planar/coarse integration endpoints. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFaceFullIntegrability
open InteriorGraphFaceCoordinates InteriorFacePartitionReassembly MeasureTheory
open scoped Classical
variable {n m : ℕ} {i a b : Fin (n+1)} {S : Finset (Fin (n+1))}
  (edges : Fin (shapeDegree a b S + coarseDegree i a S m) → Edge (n+1) m)
  (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
  (hne : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1)

include ha hba hne in
theorem density_zero_of_wrong_count
    (hcount : Fintype.card {q // IsInternal S (edges q)} ≠ shapeDegree a b S)
    (y : RealProductCoordinates i a b S m) (hy : y ∈ FaceRegion i a b S m) :
    realFaceDensity edges y = 0 := by
  by_contra h
  exact hcount (InteriorFaceNonzeroAdmissibility.internal_count_eq_of_density_ne_zero edges y ha hba hy hne h)

include ha hb hba hne in
/-- All actual full simple-face graph coefficients are L1. No edge-count
hypothesis is supplied; the wrong count has proved zero density. -/
theorem integrableOn_realFaceDensity :
    IntegrableOn (realFaceDensity edges) (FaceRegion i a b S m) := by
  by_cases hcount : Fintype.card {q // IsInternal S (edges q)} = shapeDegree a b S
  · by_cases hS : S.card = 2
    · exact (TwoPointActualFaceIntegral.integral_realFaceDensity edges hcount ha hb hba hS hne).1
    · exact (integral_realFaceDensity_eq_zero edges hcount ha hb hba
        (by have hc := cluster_card_ge_two ha hb hba; omega) hne).1
  · exact (integrableOn_zero : IntegrableOn (fun _ : RealProductCoordinates i a b S m ↦ (0 : ℝ)) _).congr_fun
      (fun y hy ↦ (density_zero_of_wrong_count edges ha hba hne hcount y hy).symm) measurableSet_faceRegion

include ha hb hba hne in
/-- The full large-face integral vanishes also in every wrong edge degree. -/
theorem integral_realFaceDensity_zero (hlarge : 3 ≤ S.card) :
    (∫ y in FaceRegion i a b S m, realFaceDensity edges y) = 0 := by
  by_cases hcount : Fintype.card {q // IsInternal S (edges q)} = shapeDegree a b S
  · exact (integral_realFaceDensity_eq_zero edges hcount ha hb hba hlarge hne).2
  · rw [setIntegral_congr_fun measurableSet_faceRegion
      (density_zero_of_wrong_count edges ha hba hne hcount)]
    simp

include ha hb hba hne in
/-- Every member of the original finite ambient partition is L1 on this full
face, without any extra integrability or degree premise. -/
theorem integrableOn_localizedDensity {J : Type*} [Fintype J]
    (ρ : Partition J i m) (hanchor : i ∈ S → a = i) (j : J) :
    IntegrableOn (localizedDensity ρ ha hb hba hanchor edges j) (FaceRegion i a b S m) :=
  TwoPointFacePartitionReassembly.integrableOn_localizedDensity_of_integrable
    ρ ha hb hba hanchor edges (integrableOn_realFaceDensity edges ha hb hba hne) j

end EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFaceFullIntegrability
