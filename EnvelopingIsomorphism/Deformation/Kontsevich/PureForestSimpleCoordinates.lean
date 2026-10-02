import EnvelopingIsomorphism.Deformation.Kontsevich.PureForestResolvedCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryGraphDomain

/-! Explicit smooth native-forest-to-pure-face coordinate map, landing in the
same actual primitive-data face used by the geometric-weight integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PureForestSimpleCoordinates
open Configuration ForestRadialFaceClassification
open RealForestSimpleCoordinates (coarsePosition shapePosition centerPosition contDiff_coarsePosition contDiff_shapePosition contDiff_centerPosition)
open PureForestSimpleCluster (lower upper)
open BoxStokes
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (a b : Fin m)

def fineCoordinate (j : Fin m) (y : Coord r) : ℝ :=
  ((shapePosition hdim x o (Sum.inl (Sum.inr j)) y).re -
      (shapePosition hdim x o (Sum.inl (Sum.inr a)) y).re) /
    ((shapePosition hdim x o (Sum.inl (Sum.inr b)) y).re -
      (shapePosition hdim x o (Sum.inl (Sum.inr a)) y).re)

def coordinates (y : Coord r) : PureBoundaryClusterForms.Face n
    (boundaryClusterBlock (lower x o) (upper x o)) a b :=
  ((fun j ↦ RealForestSimpleCluster.normalize (coarsePosition hdim x o (Sum.inl (Sum.inl 0)) y)
      (coarsePosition hdim x o (Sum.inl (Sum.inl j.succ)) y),
    RealForestSimpleCluster.normalizeReal (coarsePosition hdim x o (Sum.inl (Sum.inl 0)) y)
      (centerPosition hdim x o y),
    fun j ↦ RealForestSimpleCluster.normalizeReal (coarsePosition hdim x o (Sum.inl (Sum.inl 0)) y)
      (coarsePosition hdim x o (Sum.inl (Sum.inr j.val)) y).re),
    fun j ↦ fineCoordinate hdim x o a b j.val y)

variable (ho : kind 0 x o = .pureBoundary)
  (hl : a.val = (lower x o).val) (hu : b.val + 1 = (upper x o).val) (hab : a < b)
  (z : ForestRadialFaceLocalization.source hdim x o)

include ho hl hu hab in
theorem contDiffAt_fineCoordinate (j : Fin m) :
    ContDiffAt ℝ ⊤ (fineCoordinate hdim x o a b j) z.val := by
  apply ContDiffAt.div
  · exact (Complex.reCLM.contDiff.contDiffAt.comp _ (contDiff_shapePosition hdim x o _).contDiffAt).sub
      (Complex.reCLM.contDiff.contDiffAt.comp _ (contDiff_shapePosition hdim x o _).contDiffAt)
  · exact (Complex.reCLM.contDiff.contDiffAt.comp _ (contDiff_shapePosition hdim x o _).contDiffAt).sub
      (Complex.reCLM.contDiff.contDiffAt.comp _ (contDiff_shapePosition hdim x o _).contDiffAt)
  · exact (PureForestSimpleCluster.gap_pos hdim x o ho a b hl hu hab z).ne'

include ho hl hu hab in
theorem contDiffAt_coordinates : ContDiffAt ℝ ⊤ (coordinates hdim x o a b) z.val := by
  have hc := (contDiff_coarsePosition hdim x o (Sum.inl (Sum.inl 0))).contDiffAt (x := z.val)
  have hp : 0 < (coarsePosition hdim x o (Sum.inl (Sum.inl 0)) z.val).im :=
    PureForestSimpleCluster.anchor_pos hdim x o ho z
  unfold coordinates
  refine ContDiffAt.prodMk ?_ (contDiffAt_pi.mpr fun j ↦ contDiffAt_fineCoordinate hdim x o a b ho hl hu hab z j.val)
  refine ContDiffAt.prodMk (contDiffAt_pi.mpr fun j ↦ RealForestSimpleCoordinates.smooth_normalize hc
    (contDiff_coarsePosition hdim x o _).contDiffAt hp) ?_
  exact (RealForestSimpleCoordinates.smooth_normalizeReal hc (contDiff_centerPosition hdim x o).contDiffAt hp).prodMk
    (contDiffAt_pi.mpr fun j ↦ RealForestSimpleCoordinates.smooth_normalizeReal hc
      (Complex.reCLM.contDiff.contDiffAt.comp _ (contDiff_coarsePosition hdim x o _).contDiffAt) hp)

theorem coordinates_eq_datum :
    coordinates hdim x o a b z.val =
      (PureBoundaryClusterForms.dataCoarse (PureForestSimpleCluster.datum hdim x o ho a b hl hu hab z),
       PureBoundaryClusterForms.dataShape (PureForestSimpleCluster.datum hdim x o ho a b hl hu hab z)) := by
  apply Prod.ext
  · rfl
  · funext j
    have hj : j.val ∈ boundaryClusterBlock (lower x o) (upper x o) :=
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase j.property)
    change _ = PureForestSimpleCluster.velocity hdim x o a b z j.val
    rw [PureForestSimpleCluster.velocity, if_pos hj]
    rfl

include ho hl hu hab in
theorem coordinates_mem_nativeDomain :
    coordinates hdim x o a b z.val ∈ PureBoundaryGraphDomain.nativeDomain
      (n := n) (l := lower x o) (u := upper x o) a b := by
  exact ⟨PureForestSimpleCluster.datum hdim x o ho a b hl hu hab z,
    (coordinates_eq_datum hdim x o a b ho hl hu hab z).symm⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.PureForestSimpleCoordinates
