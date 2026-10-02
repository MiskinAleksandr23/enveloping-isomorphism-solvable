import EnvelopingIsomorphism.Deformation.Kontsevich.ForestOriginalCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestOrthantRealization
import EnvelopingIsomorphism.Deformation.Kontsevich.VariableAffineForms

/-! Literal positive forest positions normalized to native original graph coordinates.
The scale and translation vary with the forest parameters and their derivatives
are retained through the actual affine-pair identity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestPositiveChartSmooth

open Configuration ExtractedForestParameters ExtractedForestFrames ExtractedForestChildShapes
open ForestOrthantRealization ComplexConjugate Filter
open scoped Classical Topology ContDiff

variable {n m : ℕ} (i : Fin (n + 1)) (x : Compactification i m)

def leafPositions (z : Ambient i x) (v : DoubledLabel (n + 1) m) : ℂ :=
  ForestInsertionDifference.position (tree i x) (realization i x z).1 (realization i x z).2 (canonicalLeaf i x v)

theorem contDiff_leafPositions {ν : ℕ∞ω} : ContDiff ℝ ν (leafPositions i x) := by
  apply contDiff_pi.mpr
  intro v
  exact ((ForestInsertionDifference.contDiff_position (tree i x) (canonicalLeaf i x v)).of_le le_top).comp
    (contDiff_realization i x)

theorem leafPositions_reflection (z : Ambient i x) (v : DoubledLabel (n + 1) m) :
    leafPositions i x z (doubledReflection v) = conj (leafPositions i x z v) := by
  unfold leafPositions
  rw [← canonicalLeaf_reflect]
  exact ReflectedForestInsertion.position_reflect (tree i x) (reflection i x)
    (radiusArray i x z) (radiusArray_reflection i x z) (shapeArray i x z)
    (shapeArray_constraints i x z).2.1 (canonicalLeaf i x v)

theorem leafPositions_boundary_real (z : Ambient i x) (j : Fin m) :
    leafPositions i x z (Sum.inl (Sum.inr j)) = ((leafPositions i x z (Sum.inl (Sum.inr j))).re : ℂ) := by
  have h := Complex.conj_eq_iff_im.mp (leafPositions_reflection i x z (Sum.inl (Sum.inr j))).symm
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using h

def anchorPoint (z : Ambient i x) : ℂ := leafPositions i x z (Sum.inl (Sum.inl i))
def normalizationScale (z : Ambient i x) : ℝ := (anchorPoint i x z).im⁻¹
def normalizationShift (z : Ambient i x) : ℝ := -(anchorPoint i x z).re / (anchorPoint i x z).im

def forwardCoordinates (z : Ambient i x) : GraphForms.Coordinates n m :=
  (fun j => (leafPositions i x z (Sum.inl (Sum.inl (Equiv.swap 0 i j.succ))) - ((anchorPoint i x z).re : ℂ)) /
      ((anchorPoint i x z).im : ℂ),
    fun j => ((leafPositions i x z (Sum.inl (Sum.inr j))).re - (anchorPoint i x z).re) / (anchorPoint i x z).im)

theorem contDiff_anchorPoint {ν : ℕ∞ω} : ContDiff ℝ ν (anchorPoint i x) :=
  contDiff_pi.mp (contDiff_leafPositions i x) _

theorem contDiffAt_normalizationScale (z : Ambient i x) (hz : (anchorPoint i x z).im ≠ 0) {ν : ℕ∞ω} :
    ContDiffAt ℝ ν (normalizationScale i x) z :=
  (Complex.imCLM.contDiff.contDiffAt.comp z (contDiff_anchorPoint i x).contDiffAt).inv hz

theorem contDiffAt_normalizationShift (z : Ambient i x) (hz : (anchorPoint i x z).im ≠ 0) {ν : ℕ∞ω} :
    ContDiffAt ℝ ν (normalizationShift i x) z :=
  ((Complex.reCLM.contDiff.contDiffAt.comp z (contDiff_anchorPoint i x).contDiffAt).neg).div
    (Complex.imCLM.contDiff.contDiffAt.comp z (contDiff_anchorPoint i x).contDiffAt) hz

theorem contDiffAt_forwardCoordinates (z : Ambient i x) (hz : (anchorPoint i x z).im ≠ 0) {ν : ℕ∞ω} :
    ContDiffAt ℝ ν (forwardCoordinates i x) z := by
  have hp (v : DoubledLabel (n + 1) m) := (contDiff_pi.mp (contDiff_leafPositions (ν := ν) i x) v).contDiffAt (x := z)
  have ha := (contDiff_anchorPoint (ν := ν) i x).contDiffAt (x := z)
  have hr : ContDiffAt ℝ ν (fun z => (anchorPoint i x z).re) z := Complex.reCLM.contDiff.contDiffAt.comp z ha
  have hi : ContDiffAt ℝ ν (fun z => (anchorPoint i x z).im) z := Complex.imCLM.contDiff.contDiffAt.comp z ha
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro j
    simp only [div_eq_mul_inv]
    exact ((hp (Sum.inl (Sum.inl (Equiv.swap 0 i j.succ)))).sub
      (Complex.ofRealCLM.contDiff.contDiffAt.comp z hr)).mul
        ((Complex.ofRealCLM.contDiff.contDiffAt.comp z hi).inv (Complex.ofReal_ne_zero.mpr hz))
  · apply contDiffAt_pi.mpr
    intro j
    exact ((Complex.reCLM.contDiff.contDiffAt.comp z (hp _)).sub hr).div hi hz

theorem interiorPoint_forwardCoordinates (z : Ambient i x) (hz : (anchorPoint i x z).im ≠ 0)
    (j : Fin (n + 1)) :
    GraphForms.interiorPoint j (forwardCoordinates i x z) =
      (leafPositions i x z (Sum.inl (Sum.inl (Equiv.swap 0 i j))) - ((anchorPoint i x z).re : ℂ)) /
        ((anchorPoint i x z).im : ℂ) := by
  cases j using Fin.cases with
  | zero =>
    simp only [GraphForms.interiorPoint_zero, Equiv.swap_apply_left]
    change Complex.I = (anchorPoint i x z - ((anchorPoint i x z).re : ℂ)) / ((anchorPoint i x z).im : ℂ)
    apply Complex.ext <;> simp [hz]
  | succ j => rfl

theorem vertexPoint_forwardCoordinates (z : Ambient i x) (hz : (anchorPoint i x z).im ≠ 0)
    (v : Fin (n + 1) ⊕ Fin m) :
    GraphForms.vertexPoint v (forwardCoordinates i x z) =
      (leafPositions i x z (Sum.inl (Sum.map (Equiv.swap 0 i) id v)) - ((anchorPoint i x z).re : ℂ)) /
        ((anchorPoint i x z).im : ℂ) := by
  cases v with
  | inl j => exact interiorPoint_forwardCoordinates i x z hz j
  | inr j =>
    change ((((leafPositions i x z (Sum.inl (Sum.inr j))).re - (anchorPoint i x z).re) /
      (anchorPoint i x z).im : ℝ) : ℂ) =
      (leafPositions i x z (Sum.inl (Sum.inr j)) - ((anchorPoint i x z).re : ℂ)) /
        ((anchorPoint i x z).im : ℂ)
    conv_rhs => rw [leafPositions_boundary_real]
    push_cast
    rfl

def leafEdgeMap (e : GraphForms.Edge n m) (z : Ambient i x) : ℂ × ℂ :=
  (leafPositions i x z (Sum.inl (Sum.inl (Equiv.swap 0 i e.source))),
    leafPositions i x z (Sum.inl (Sum.map (Equiv.swap 0 i) id e.target)))

/-- Exact variable-affine endpoint equality, including normalization of the fixed first point. -/
theorem edgeMap_forwardCoordinates (e : GraphForms.Edge n m) (z : Ambient i x)
    (hz : (anchorPoint i x z).im ≠ 0) :
    GraphForms.edgeMap e (forwardCoordinates i x z) =
      variableAffinePair (leafEdgeMap i x e) (normalizationScale i x) (normalizationShift i x) z := by
  apply Prod.ext
  · rw [GraphForms.edgeMap, interiorPoint_forwardCoordinates i x z hz]
    simp only [variableAffinePair, leafEdgeMap, normalizationScale, normalizationShift,
      Prod.smul_fst, Prod.fst_add, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
    push_cast
    ring
  · rw [GraphForms.edgeMap, vertexPoint_forwardCoordinates i x z hz]
    simp only [variableAffinePair, leafEdgeMap, normalizationScale, normalizationShift,
      Prod.smul_snd, Prod.snd_add, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
    push_cast
    ring

theorem edgeMap_forwardCoordinates_eventuallyEq (e : GraphForms.Edge n m) (z : Ambient i x)
    (hz : (anchorPoint i x z).im ≠ 0) :
    (GraphForms.edgeMap e ∘ forwardCoordinates i x) =ᶠ[𝓝 z]
      variableAffinePair (leafEdgeMap i x e) (normalizationScale i x) (normalizationShift i x) := by
  have hc : ContinuousAt (fun y : Ambient i x => (anchorPoint i x y).im) z :=
    (Complex.continuous_im.comp (contDiff_anchorPoint (ν := 1) i x).continuous).continuousAt
  filter_upwards [hc.eventually_ne hz] with y hy
  exact edgeMap_forwardCoordinates i x e y hy

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestPositiveChartSmooth
