import EnvelopingIsomorphism.Deformation.MainSimplePairedChartTransfer
import EnvelopingIsomorphism.Deformation.Kontsevich.SingleStaticCollisionZeroNodeLabels

/-! Reverse source transfer for a single reflection-stable coarse collision
fiber, using the actual inverse of a specified native chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.MainStaticCollisionChartTransfer

open Kontsevich Configuration MainPairedChartTransfer MainSimplePairedChartTransfer
open ExtractedForestParameters ExtractedForestChildShapes ExtractedForestFrames
open ForestDirectionRatioCoordinates ForestOrthantRealization
open ReflectedRadiusCoordinates ForestRadialFaceClassification ForestRadialFaceReconstruction
open SingleStaticCollisionZeroNodeLabels
open scoped Classical

variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x q : Compactification (0 : Fin (n + 1)) m)
  (C : Finset (DoubledLabel (n + 1) m)) (B V : DoubledLabel (n + 1) m → ℂ)

/-- One primitive stable collision fiber produces a strict native source in
every containing chart. Both the mask and represented point are literal. -/
theorem exists_source_of_static_collision
    (hB : ∀ p : DoubledPair (n + 1) m, B p.val.2 - B p.val.1 = 0 ↔ p.val.1 ∈ C ∧ p.val.2 ∈ C)
    (hV : ∀ p : DoubledPair (n + 1) m, B p.val.2 - B p.val.1 = 0 → V p.val.2 - V p.val.1 ≠ 0)
    (hC : 1 < C.card) (hproper : C ≠ Finset.univ) (hstable : C.image doubledReflection = C)
    (hqDR : projectDR q.val = projectDR (linearCollisionCoordinates B V))
    (hq : q ∈ (ForestOrthantCharts.chart 0 x).target) :
    ∃ (o : ForestRadialFaceClassification.Orbit 0 x)
      (z : ForestRadialFaceLocalization.source hdim x o),
      (representative 0 x o).val.val = C ∧
      reflection 0 x (representative 0 x o).val = (representative 0 x o).val ∧
      PairedForestSimpleOverlap.facePoint hdim x o z = q := by
  let p := decodedParameters x q hq
  have hDR : doubledCoordinates (tree 0 x) (canonicalLeaf 0 x) p =
      projectDR (linearCollisionCoordinates B V) := (decodedParameters_fullDR x q hq).trans hqDR
  obtain ⟨u,hu,hzero,hpos⟩ := exists_unique_zero_node C B V hB hV x p hDR hC hproper
  have hfix : reflection 0 x u.val = u.val := node_fixed_of_mask C x hstable u hu
  let o := orbitClass (tree 0 x) (reflection 0 x) (reflection_reflection 0 x) u
  have hrep : representative 0 x o = u := by
    have he := (orbitClass_eq_iff _ _ _ u (representative 0 x o)).mp
      (representative_orbit 0 x o).symm
    rcases he with he | he
    · exact he.symm
    · have hrefl : reflect (tree 0 x) (reflection 0 x) u = u := Subtype.ext hfix
      rw [hrefl] at he
      exact he.symm
  have hz : (decodedAmbient x q).1 (orbitEquiv 0 x o) = 0 :=
    (decodedParameters_radius x q hq u).symm.trans hzero
  have hp : ∀ o' : ForestRadialFaceClassification.Orbit 0 x, o' ≠ o →
      0 < (decodedAmbient x q).1 (orbitEquiv 0 x o') := by
    intro o' hne
    have hne' : representative 0 x o' ≠ u := by
      intro he
      apply hne
      rw [← representative_orbit 0 x o', he]
    have hh := hpos (representative 0 x o') hne'
    rw [decodedParameters_radius x q hq, representative_orbit] at hh
    exact hh
  have hchart : ForestPositiveChartSmooth.ofAmbient 0 x (decodedAmbient x q) ∈
      (ForestOrthantCharts.chart 0 x).source := by
    rw [decodedAmbient, ForestPositiveChartSmooth.ofAmbient_includeOrthant]
    exact (ForestOrthantCharts.chart 0 x).map_target hq
  obtain ⟨z,hz',_⟩ := existsUnique_source_parameter hdim x o (decodedAmbient x q) hz hp hchart
  refine ⟨o,z,hrep ▸ hu,?_,?_⟩
  · rw [hrep]
    exact hfix
  · rw [PairedForestSimpleOverlap.facePoint, hz', decodedAmbient,
      ForestPositiveChartSmooth.ofAmbient_includeOrthant, (ForestOrthantCharts.chart 0 x).right_inv hq]

end EnvelopingIsomorphism.Deformation.MainStaticCollisionChartTransfer
