import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestSimpleCluster
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFaceImmersion

/-! The simple real-cluster coordinates are an explicit smooth map of the
literal native Stokes face coordinates, with genuine source membership. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealForestSimpleCoordinates
open Configuration ExtractedForestParameters ExtractedForestChildShapes ForestOrthantRealization
open ForestRadialFaceClassification ForestRadialClusterLabels ForestInsertionDifference
open RealForestCoarsePositions (node labelsSet)
open RealForestSimpleCluster (normalize normalizeReal lower upper)
open BoxStokes
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (a b : Fin (n+1))

def ambientParameters (y : Coord r) : ForestDirectionRatioCoordinates.Parameters (tree 0 x) :=
  realization 0 x (faceAmbient hdim x o y)

def coarsePosition (j : DoubledLabel (n+1) m) (y : Coord r) : ℂ :=
  position (tree 0 x) (ambientParameters hdim x o y).1 (ambientParameters hdim x o y).2
    (canonicalLeaf 0 x j)

def shapePosition (j : DoubledLabel (n+1) m) (y : Coord r) : ℂ :=
  branchUnit (tree 0 x) (ambientParameters hdim x o y).1 (ambientParameters hdim x o y).2
    (node x o) (canonicalLeaf 0 x j)

def centerPosition (y : Coord r) : ℝ :=
  (position (tree 0 x) (ambientParameters hdim x o y).1 (ambientParameters hdim x o y).2 (node x o)).re

def coordinates (y : Coord r) : BoundaryClusterFreeCoordinates.FaceCoordinates b a (labelsSet x o) m :=
  (fun j ↦ normalize (coarsePosition hdim x o (Sum.inl (Sum.inl b)) y)
      (coarsePosition hdim x o (Sum.inl (Sum.inl j.val)) y),
    fun j ↦ normalize (shapePosition hdim x o (Sum.inl (Sum.inl a)) y)
      (shapePosition hdim x o (Sum.inl (Sum.inl j.val)) y),
    fun j ↦ if j ∈ boundaryClusterBlock (lower x o) (upper x o) then
      normalizeReal (shapePosition hdim x o (Sum.inl (Sum.inl a)) y)
        (shapePosition hdim x o (Sum.inl (Sum.inr j)) y).re
      else normalizeReal (coarsePosition hdim x o (Sum.inl (Sum.inl b)) y)
        (coarsePosition hdim x o (Sum.inl (Sum.inr j)) y).re,
    normalizeReal (coarsePosition hdim x o (Sum.inl (Sum.inl b)) y) (centerPosition hdim x o y))

theorem contDiff_ambientParameters : ContDiff ℝ ⊤ (ambientParameters hdim x o) :=
  (contDiff_realization 0 x).comp (ForestRadialFaceImmersion.contDiff_faceAmbient hdim x o)

theorem contDiff_coarsePosition (j : DoubledLabel (n+1) m) :
    ContDiff ℝ ⊤ (coarsePosition hdim x o j) :=
  (contDiff_position (tree 0 x) (canonicalLeaf 0 x j)).comp (contDiff_ambientParameters hdim x o)

theorem contDiff_shapePosition (j : DoubledLabel (n+1) m) :
    ContDiff ℝ ⊤ (shapePosition hdim x o j) :=
  (contDiff_branchUnit (tree 0 x) (node x o) (canonicalLeaf 0 x j)).comp
    (contDiff_ambientParameters hdim x o)

theorem contDiff_centerPosition : ContDiff ℝ ⊤ (centerPosition hdim x o) :=
  Complex.reCLM.contDiff.comp ((contDiff_position (tree 0 x) (node x o)).comp
    (contDiff_ambientParameters hdim x o))

theorem smooth_normalize {d : ℕ} {f g : Coord d → ℂ} {y : Coord d}
    (hf : ContDiffAt ℝ ⊤ f y) (hg : ContDiffAt ℝ ⊤ g y) (hp : 0 < (f y).im) :
    ContDiffAt ℝ ⊤ (fun z ↦ normalize (f z) (g z)) y := by
  have hn : ContDiffAt ℝ ⊤ (fun z ↦ g z - ((f z).re : ℂ)) y :=
    hg.sub (Complex.ofRealCLM.contDiff.contDiffAt.comp y
      (Complex.reCLM.contDiff.contDiffAt.comp y hf))
  have hd : ContDiffAt ℝ ⊤ (fun z ↦ ((f z).im : ℂ)) y :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp y (Complex.imCLM.contDiff.contDiffAt.comp y hf)
  simpa only [RealForestSimpleCluster.normalize, div_eq_mul_inv, Pi.inv_apply] using
    hn.mul (hd.inv (Complex.ofReal_ne_zero.mpr hp.ne'))

theorem smooth_normalizeReal {d : ℕ} {f : Coord d → ℂ} {g : Coord d → ℝ} {y : Coord d}
    (hf : ContDiffAt ℝ ⊤ f y) (hg : ContDiffAt ℝ ⊤ g y) (hp : 0 < (f y).im) :
    ContDiffAt ℝ ⊤ (fun z ↦ normalizeReal (f z) (g z)) y := by
  unfold normalizeReal
  exact (hg.sub (Complex.reCLM.contDiff.contDiffAt.comp y hf)).div
    (Complex.imCLM.contDiff.contDiffAt.comp y hf) hp.ne'

variable (ho : RealForestCoarsePositions.IsFixed x o)
  (ha : a ∈ labelsSet x o) (hb : b ∉ labelsSet x o)
  (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)
  (z : ForestRadialFaceLocalization.source hdim x o)

include ho ha hb in
/-- Smoothness comes from insertion polynomials and division only by the two
proved strictly positive anchor heights. -/
theorem contDiffAt_coordinates : ContDiffAt ℝ ⊤ (coordinates hdim x o a b) z.val := by
  have hc := (contDiff_coarsePosition hdim x o (Sum.inl (Sum.inl b))).contDiffAt (x := z.val)
  have hs := (contDiff_shapePosition hdim x o (Sum.inl (Sum.inl a))).contDiffAt (x := z.val)
  have hcpos : 0 < (coarsePosition hdim x o (Sum.inl (Sum.inl b)) z.val).im :=
    RealForestSimpleCluster.coarseAnchor_pos hdim x o ho b hb z
  have hspos : 0 < (shapePosition hdim x o (Sum.inl (Sum.inl a)) z.val).im :=
    RealForestSimpleCluster.shapeAnchor_pos hdim x o ho a ha z
  unfold coordinates
  refine (contDiffAt_pi.mpr fun j ↦ smooth_normalize hc
    (contDiff_coarsePosition hdim x o _).contDiffAt hcpos).prodMk ?_
  refine (contDiffAt_pi.mpr fun j ↦ smooth_normalize hs
    (contDiff_shapePosition hdim x o _).contDiffAt hspos).prodMk ?_
  refine (contDiffAt_pi.mpr fun j ↦ ?_).prodMk
    (smooth_normalizeReal hc (contDiff_centerPosition hdim x o).contDiffAt hcpos)
  split_ifs
  · exact smooth_normalizeReal hs
      (Complex.reCLM.contDiff.contDiffAt.comp _ (contDiff_shapePosition hdim x o _).contDiffAt) hspos
  · exact smooth_normalizeReal hc
      (Complex.reCLM.contDiff.contDiffAt.comp _ (contDiff_coarsePosition hdim x o _).contDiffAt) hcpos

/-- On the exact forest face source, the smooth formula is the actual
constructed simple chart datum, not only a map with matching dimensions. -/
theorem coordinates_eq_freeDomain :
    BoundaryClusterFreeCoordinates.faceEmbedding (coordinates hdim x o a b z.val) =
      (RealForestSimpleCluster.freeDomain hdim x o ho a b ha hb hne z).val := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext j
      change RealForestSimpleCluster.normalize _ _ = RealForestSimpleCluster.velocity hdim x o a z j.val
      rw [RealForestSimpleCluster.velocity, if_pos j.property.1]
      rfl
    · apply Prod.ext
      · funext j
        change (if j ∈ boundaryClusterBlock (lower x o) (upper x o) then _ else _) =
          (if j ∈ boundaryClusterBlock (lower x o) (upper x o) then
            RealForestSimpleCluster.boundaryVelocity hdim x o a z j
          else RealForestSimpleCluster.boundaryBase hdim x o b z j)
        by_cases hj : j ∈ boundaryClusterBlock (lower x o) (upper x o)
        · rw [if_pos hj, if_pos hj, RealForestSimpleCluster.boundaryVelocity, if_pos hj]
          rfl
        · rw [if_neg hj, if_neg hj]
          rfl
      · rfl

include ho ha hb hne in
/-- Every nonempty-block proper fixed native face lands in the original
strict simple-cluster source at scale zero. -/
theorem coordinates_mem_source :
    (BoundaryClusterFreeCoordinates.faceEmbedding (coordinates hdim x o a b z.val)).OpenConditions
      (lower x o) (upper x o) := by
  rw [coordinates_eq_freeDomain hdim x o a b ho ha hb hne z]
  exact (RealForestSimpleCluster.freeDomain hdim x o ho a b ha hb hne z).property.2

end EnvelopingIsomorphism.Deformation.Kontsevich.RealForestSimpleCoordinates
