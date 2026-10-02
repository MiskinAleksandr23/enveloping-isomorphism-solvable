import EnvelopingIsomorphism.Deformation.Kontsevich.ForestOrthantLocalization
import EnvelopingIsomorphism.Deformation.Kontsevich.CompactOrthantStokes
import EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestDimension

/-! Literal lower-face integrals of compact forest forms, in coordinates that
put the free radial variables first and preserve the actual corner orthant. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestOrthantStokes

open Set MeasureTheory ContinuousAlternatingMap ForestOrthantRealization
open ForestOrthantCharts ForestOrthantLocalization BoxStokes CompactOrthantStokes
open scoped Topology Classical

variable {n m : ℕ} (i : Fin (n + 1)) (x : Compactification i m)

abbrev coordinateCount := R i x + (C i x + Q i x)

/-- The literal ordering is radial coordinates, then angles, then real shapes. -/
def flatCoordinates : Ambient i x ≃L[ℝ] Coord (coordinateCount i x) :=
  ((LinearEquiv.sumArrowLequivProdArrow (Fin (R i x)) (Fin (C i x + Q i x)) ℝ ℝ).symm.trans
    (LinearEquiv.piCongrLeft ℝ (fun _ : Fin (coordinateCount i x) => ℝ) finSumFinEquiv)).toContinuousLinearEquiv

def radialIndex (j : Fin (R i x)) : Fin (coordinateCount i x) := finSumFinEquiv (Sum.inl j)

theorem flatCoordinates_radial (z : Ambient i x) (j : Fin (R i x)) :
    flatCoordinates i x z (radialIndex i x j) = z.1 j := by
  simp [flatCoordinates, radialIndex, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft']
  rfl

def radialIndices : Finset (Fin (coordinateCount i x)) := Finset.univ.image (radialIndex i x)

theorem flatCoordinates_mem_orthant (z : Ambient i x) :
    flatCoordinates i x z ∈ orthant (radialIndices i x) ↔ ∀ j, 0 ≤ z.1 j := by
  simp only [mem_orthant, radialIndices, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hz j
    simpa only [flatCoordinates_radial] using hz (radialIndex i x j) ⟨j, rfl⟩
  · rintro hz _ ⟨j, rfl⟩
    simpa only [flatCoordinates_radial] using hz j

theorem flatCoordinates_image_orthant :
    flatCoordinates i x '' {z : Ambient i x | ∀ j, 0 ≤ z.1 j} = orthant (radialIndices i x) := by
  apply Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    exact (flatCoordinates_mem_orthant i x z).mpr hz
  · intro y hy
    refine ⟨(flatCoordinates i x).symm y, ?_, (flatCoordinates i x).apply_symm_apply y⟩
    apply (flatCoordinates_mem_orthant i x _).mp
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hy

theorem coordinateCount_eq : coordinateCount i x = GraphForms.dimension n m := by
  have h := ExtractedForestDimension.total_dimension_add_two i x
  change ExtractedForestShapeCoordinates.radialCount i x +
    (ExtractedForestShapeCoordinates.circleCount i x + ExtractedForestShapeCoordinates.realCount i x) = n * 2 + m
  omega

variable {r : ℕ}

def coordinateForm (η : Ambient i x → Ambient i x [⋀^Fin r]→L[ℝ] ℝ) :
    Coord (coordinateCount i x) → Coord (coordinateCount i x) [⋀^Fin r]→L[ℝ] ℝ :=
  fun z => (η ((flatCoordinates i x).symm z)).compContinuousLinearMap
    (flatCoordinates i x).symm.toContinuousLinearMap

theorem contDiff_coordinateForm
    (η : Ambient i x → Ambient i x [⋀^Fin r]→L[ℝ] ℝ) (hη : ContDiff ℝ 1 η) :
    ContDiff ℝ 1 (coordinateForm i x η) := by
  let L : (Ambient i x [⋀^Fin r]→L[ℝ] ℝ) →L[ℝ]
      (Coord (coordinateCount i x) [⋀^Fin r]→L[ℝ] ℝ) :=
    compContinuousLinearMapCLM (flatCoordinates i x).symm.toContinuousLinearMap
  change ContDiff ℝ 1 (L ∘ η ∘ (flatCoordinates i x).symm)
  exact L.contDiff.comp (hη.comp (flatCoordinates i x).symm.contDiff)

theorem hasCompactSupport_coordinateForm
    (η : Ambient i x → Ambient i x [⋀^Fin r]→L[ℝ] ℝ) (hη : HasCompactSupport η) :
    HasCompactSupport (coordinateForm i x η) := by
  let L : (Ambient i x [⋀^Fin r]→L[ℝ] ℝ) →L[ℝ]
      (Coord (coordinateCount i x) [⋀^Fin r]→L[ℝ] ℝ) :=
    compContinuousLinearMapCLM (flatCoordinates i x).symm.toContinuousLinearMap
  exact (hη.comp_homeomorph (flatCoordinates i x).symm.toHomeomorph).comp_left
    (g := L) (map_zero L)

/-- This is Stokes for the actual finite radial orthant. Every boundary
summand is a genuine coordinate lower-face integral with its standard sign. -/
theorem integral_extDeriv_eq_lower_faces
    (hcount : coordinateCount i x = r + 1)
    (η : Ambient i x → Ambient i x [⋀^Fin r]→L[ℝ] ℝ)
    (hη : ContDiff ℝ 1 η) (hcpt : HasCompactSupport η) :
    let E : Ambient i x ≃L[ℝ] Coord (r + 1) := hcount ▸ flatCoordinates i x
    let S : Finset (Fin (r + 1)) := hcount ▸ radialIndices i x
    let θ : Form r := fun z => (η (E.symm z)).compContinuousLinearMap E.symm.toContinuousLinearMap
    (∫ z in orthant S, extDeriv θ z (standardBasis (r + 1))) =
      ∑ j ∈ S, -((-1 : ℝ) ^ j.val) •
        ∫ z in orthant (faceIndices S j), facePullback θ j 0 z (standardBasis r) := by
  dsimp only
  let E : Ambient i x ≃L[ℝ] Coord (r + 1) := hcount ▸ flatCoordinates i x
  let L : (Ambient i x [⋀^Fin r]→L[ℝ] ℝ) →L[ℝ] (Coord (r + 1) [⋀^Fin r]→L[ℝ] ℝ) :=
    compContinuousLinearMapCLM E.symm.toContinuousLinearMap
  apply CompactOrthantStokes.integral_extDeriv_eq_lower_faces
  · change ContDiff ℝ 1 (L ∘ η ∘ E.symm)
    exact L.contDiff.comp (hη.comp E.symm.contDiff)
  · exact (hcpt.comp_homeomorph E.symm.toHomeomorph).comp_left (g := L) (map_zero L)

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestOrthantStokes
