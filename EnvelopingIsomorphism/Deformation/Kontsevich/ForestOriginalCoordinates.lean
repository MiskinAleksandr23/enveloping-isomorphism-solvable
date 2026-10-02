import EnvelopingIsomorphism.Deformation.Kontsevich.AnchorChangeSmooth
import EnvelopingIsomorphism.Deformation.Kontsevich.Compactification

/-! Native original graph coordinates at any selected interior anchor.
All raw doubled coordinates are actual affine and conjugate-affine maps. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestPositiveChartSmooth
open Configuration ComplexConjugate Set Topology Filter
open scoped Classical ContDiff
variable {n m : ℕ} (i : Fin (n + 1))

/-- Original normalized graph coordinates, with the fixed label zero moved to the chosen anchor. -/
def toNormalized (q : GraphForms.CoordinateDomain n m) : Configuration.Normalized i m :=
  ⟨Configuration.relabelInterior (Equiv.swap 0 i) (GraphForms.toConfiguration q), by
    apply UpperHalfPlane.ext
    simp⟩

def fromNormalized (c : Configuration.Normalized i m) : GraphForms.Coordinates n m :=
  (fun j => (c.val.interior (Equiv.swap 0 i j.succ) : ℂ), c.val.boundary)

theorem fromNormalized_admissible (c : Configuration.Normalized i m) :
    GraphForms.Admissible (fromNormalized i c) := by
  let c₀ : Configuration.Normalized (0 : Fin (n + 1)) m :=
    ⟨Configuration.relabelInterior (Equiv.swap 0 i) c.val, by simpa using c.property⟩
  exact GraphForms.fromNormalized_admissible c₀

@[simp] theorem fromNormalized_toNormalized (q : GraphForms.CoordinateDomain n m) :
    fromNormalized i (toNormalized i q) = q.val := by
  ext j <;> simp [fromNormalized, toNormalized]

@[simp] theorem toNormalized_fromNormalized (c : Configuration.Normalized i m) :
    toNormalized i ⟨fromNormalized i c, fromNormalized_admissible i c⟩ = c := by
  apply Subtype.ext
  apply Configuration.ext
  · funext j
    apply UpperHalfPlane.ext
    change GraphForms.interiorPoint (Equiv.swap 0 i j) (fromNormalized i c) = (c.val.interior j : ℂ)
    have h (v : Fin (n + 1)) :
        GraphForms.interiorPoint v (fromNormalized i c) = (c.val.interior (Equiv.swap 0 i v) : ℂ) := by
      cases v using Fin.cases with
      | zero => simpa using (congrArg (fun z : UpperHalfPlane => (z : ℂ)) c.property).symm
      | succ v => rfl
    rw [h]
    simp
  · rfl

/-- The doubled coordinate map is globally affine over the reals, including the conjugate labels. -/
def doubledRaw (q : GraphForms.Coordinates n m) : DoubledLabel (n + 1) m → ℂ
  | Sum.inl (Sum.inl j) => GraphForms.interiorPoint (Equiv.swap 0 i j) q
  | Sum.inl (Sum.inr j) => (q.2 j : ℂ)
  | Sum.inr j => conj (GraphForms.interiorPoint (Equiv.swap 0 i j) q)

theorem doubledRaw_eq (q : GraphForms.CoordinateDomain n m) :
    doubledRaw i q.val = (toNormalized i q).val.doubledPoint := by
  funext v
  rcases v with (j | j) | j <;> rfl

theorem contDiff_doubledRaw {ν : ℕ∞ω} : ContDiff ℝ ν (doubledRaw (m := m) i) := by
  apply contDiff_pi.mpr
  intro v
  rcases v with (j | j) | j
  · exact (GraphForms.contDiff_interiorPoint _).of_le le_top
  · exact Complex.ofRealCLM.contDiff.comp (by fun_prop)
  · exact Complex.conjCLE.contDiff.comp ((GraphForms.contDiff_interiorPoint _).of_le le_top)

theorem continuous_toNormalized : Continuous (toNormalized (m := m) i) := by
  apply Continuous.subtype_mk
  apply Configuration.isEmbedding_vertexCoordinates.isInducing.continuous_iff.mpr
  apply continuous_pi
  intro v
  cases v with
  | inl j => exact (GraphForms.contDiff_interiorPoint (Equiv.swap 0 i j)).continuous.comp continuous_subtype_val
  | inr j => exact Complex.ofRealCLM.continuous.comp ((continuous_apply j).comp
      (continuous_snd.comp continuous_subtype_val))

theorem continuous_fromNormalized : Continuous (fromNormalized (m := m) i) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro j
    exact (Configuration.continuous_vertexCoordinate (Sum.inl (Equiv.swap 0 i j.succ))).comp continuous_subtype_val
  · apply continuous_pi
    intro j
    exact Complex.continuous_re.comp ((Configuration.continuous_vertexCoordinate (Sum.inr j)).comp continuous_subtype_val)

def originalEmbedding (q : GraphForms.CoordinateDomain n m) : Compactification i m :=
  compactificationEmbedding i (toNormalized i q)

theorem continuous_originalEmbedding : Continuous (originalEmbedding (m := m) i) :=
  (isEmbedding_compactificationEmbedding i).continuous.comp (continuous_toNormalized i)


end EnvelopingIsomorphism.Deformation.Kontsevich.ForestPositiveChartSmooth
