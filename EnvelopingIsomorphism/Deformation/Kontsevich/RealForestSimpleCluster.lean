import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestShapePositions
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterFreeChart

/-! A genuine simple real-cluster source point constructed from the actual
proper fixed native forest face. All geometric inequalities are proved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealForestSimpleCluster
open Configuration ExtractedForestParameters ForestRadialFaceClassification ForestRadialClusterLabels
open RealForestCoarsePositions (node labelsSet)
open scoped Classical

/-- Positive affine normalization at an arbitrary upper point. -/
def normalize (w q : ℂ) : ℂ := (q - (w.re : ℂ)) / (w.im : ℂ)
def normalizeReal (w : ℂ) (t : ℝ) : ℝ := (t - w.re) / w.im

@[simp] theorem normalize_im (w q : ℂ) : (normalize w q).im = q.im / w.im := by
  simp [normalize]

@[simp] theorem normalize_re (w q : ℂ) : (normalize w q).re = normalizeReal w q.re := by
  simp [normalize, normalizeReal]

theorem normalize_injective (w : ℂ) (hw : 0 < w.im) : Function.Injective (normalize w) := by
  intro p q h
  exact sub_left_inj.mp ((div_left_inj' (Complex.ofReal_ne_zero.mpr hw.ne')).mp h)

theorem normalize_self (w : ℂ) (hw : 0 < w.im) : normalize w w = Complex.I := by
  apply Complex.ext <;> simp [normalize, hw.ne']

theorem normalize_real (w : ℂ) (t : ℝ) : normalize w (t : ℂ) = (normalizeReal w t : ℂ) := by
  apply Complex.ext <;> simp [normalize, normalizeReal]

theorem normalizeReal_strictMono (w : ℂ) (hw : 0 < w.im) : StrictMono (normalizeReal w) :=
  fun _ _ h ↦ (div_lt_div_iff_of_pos_right hw).mpr (sub_lt_sub_right h _)

variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n+1)) m)
  (o : ForestRadialFaceClassification.Orbit 0 x) (ho : RealForestCoarsePositions.IsFixed x o)
  (a b : Fin (n+1)) (ha : a ∈ labelsSet x o) (hb : b ∉ labelsSet x o)
  (hne : (boundaryClusterBlock (blockLower 0 x (node x o)) (blockUpper 0 x (node x o))).Nonempty)
  (z : ForestRadialFaceLocalization.source hdim x o)

abbrev lower := blockLower 0 x (node x o)
abbrev upper := blockUpper 0 x (node x o)

def coarseAnchor : ℂ := PairedForestCoarsePositions.positions hdim x o z (Sum.inl (Sum.inl b))
def shapeAnchor : ℂ := RealForestShapePositions.positions hdim x o z (Sum.inl (Sum.inl a))

include ho hb in
theorem coarseAnchor_pos : 0 < (coarseAnchor hdim x o b z).im :=
  RealForestCoarsePositions.positions_upper_im_pos_off hdim x o ho z b hb

include ho ha in
theorem shapeAnchor_pos : 0 < (shapeAnchor hdim x o a z).im :=
  RealForestShapePositions.positions_upper_im_pos hdim x o ho z a ha

/-- Full normalized coarse positions, retaining the collapsed center at every
inside label. -/
def base (j : Fin (n+1)) : ℂ := normalize (coarseAnchor hdim x o b z)
  (PairedForestCoarsePositions.positions hdim x o z (Sum.inl (Sum.inl j)))

def velocity (j : Fin (n+1)) : ℂ := if j ∈ labelsSet x o then
  normalize (shapeAnchor hdim x o a z)
    (RealForestShapePositions.positions hdim x o z (Sum.inl (Sum.inl j))) else 0

def center : ℝ := normalizeReal (coarseAnchor hdim x o b z) (RealForestCoarsePositions.center hdim x o z)

def boundaryBase (j : Fin m) : ℝ := normalizeReal (coarseAnchor hdim x o b z)
  (PairedForestCoarsePositions.positions hdim x o z (Sum.inl (Sum.inr j))).re

def boundaryVelocity (j : Fin m) : ℝ := if j ∈ boundaryClusterBlock (lower x o) (upper x o) then
  normalizeReal (shapeAnchor hdim x o a z)
    (RealForestShapePositions.positions hdim x o z (Sum.inl (Sum.inr j))).re else 0

/-- Actual native radii, units, and signs supply every field of the simple
cluster data. No factor configuration or source membership is supplied. -/
def datum : BoundaryClusterData b a m (labelsSet x o) (lower x o) (upper x o) where
  center := center hdim x o b z
  base := base hdim x o b z
  velocity := velocity hdim x o a z
  boundaryBase := boundaryBase hdim x o b z
  boundaryVelocity := boundaryVelocity hdim x o a z
  anchor_mem := ha
  normalized_not_mem := hb
  block_order := block_order 0 x (node x o)
  base_eq_center j hj := by
    unfold base center
    rw [RealForestCoarsePositions.positions_inside hdim x o ho z _
      ((mem_interiorLabels 0 x _ _).mp hj), normalize_real]
  base_im_pos_off j hj := by
    rw [base, normalize_im]
    exact div_pos (RealForestCoarsePositions.positions_upper_im_pos_off hdim x o ho z j hj)
      (coarseAnchor_pos hdim x o ho b hb z)
  base_injective_off j k hj hk he := by
    have h := normalize_injective _ (coarseAnchor_pos hdim x o ho b hb z) he
    rcases (RealForestCoarsePositions.positions_eq_iff hdim x o ho z _ _).mp h with h | h
    · exact Sum.inl.inj (Sum.inl.inj h)
    · exact (hj ((mem_interiorLabels 0 x _ _).mpr h.1)).elim
  base_normalized := normalize_self _ (coarseAnchor_pos hdim x o ho b hb z)
  velocity_im_pos j hj := by
    simp only [velocity, if_pos hj, normalize_im]
    exact div_pos (RealForestShapePositions.positions_upper_im_pos hdim x o ho z j hj)
      (shapeAnchor_pos hdim x o ho a ha z)
  velocity_zero_off j hj := by simp [velocity, hj]
  velocity_injective_on j k hj hk he := by
    simp only [velocity, if_pos hj, if_pos hk] at he
    have h := normalize_injective _ (shapeAnchor_pos hdim x o ho a ha z) he
    have hj' := (mem_interiorLabels 0 x _ _).mp hj
    have hk' := (mem_interiorLabels 0 x _ _).mp hk
    exact Sum.inl.inj (Sum.inl.inj
      (RealForestShapePositions.positions_injective_on hdim x o ho z hj' hk' h))
  velocity_anchor := by
    simp only [velocity, if_pos ha]
    exact normalize_self _ (shapeAnchor_pos hdim x o ho a ha z)
  boundaryBase_eq_center j hj := by
    unfold boundaryBase center
    rw [RealForestCoarsePositions.positions_inside hdim x o ho z _
      ((RealForestCoarsePositions.boundary_mem_node_iff x o ho j).mpr hj)]
    rfl
  boundaryBase_lt_center j hj :=
    normalizeReal_strictMono _ (coarseAnchor_pos hdim x o ho b hb z)
      (RealForestCoarsePositions.boundary_lt_center hdim x o ho z hne j hj)
  center_lt_boundaryBase j hj :=
    normalizeReal_strictMono _ (coarseAnchor_pos hdim x o ho b hb z)
      (RealForestCoarsePositions.center_lt_boundary hdim x o ho z hne j hj)
  boundaryBase_lt j k hjk hblock := by
    apply normalizeReal_strictMono _ (coarseAnchor_pos hdim x o ho b hb z)
    apply RealForestCoarsePositions.positions_boundary_lt hdim x o ho z j k hjk
    simpa only [RealForestCoarsePositions.boundary_mem_node_iff x o ho] using hblock
  boundaryVelocity_zero_off j hj := by simp [boundaryVelocity, hj]
  boundaryVelocity_strictMono_on j k hj hk hjk := by
    simp only [boundaryVelocity, if_pos hj, if_pos hk]
    apply normalizeReal_strictMono _ (shapeAnchor_pos hdim x o ho a ha z)
    exact RealForestShapePositions.positions_boundary_lt hdim x o ho z j k hjk
      ((RealForestCoarsePositions.boundary_mem_node_iff x o ho j).mpr hj)
      ((RealForestCoarsePositions.boundary_mem_node_iff x o ho k).mpr hk)

def domain : BoundaryClusterDomain b a m (labelsSet x o) (lower x o) (upper x o) :=
  ⟨(datum hdim x o ho a b ha hb hne z, 0), BoundaryClusterData.admissibleScale_zero _⟩

/-- The actual native face produces a point in the established simple smooth
cluster source, including every strict open condition. -/
def freeDomain : BoundaryClusterFreeDomain b a (labelsSet x o) m (lower x o) (upper x o) :=
  (domain hdim x o ho a b ha hb hne z).toFreeDomain

@[simp] theorem freeDomain_radius :
    (freeDomain hdim x o ho a b ha hb hne z).val.radius = 0 := rfl

end EnvelopingIsomorphism.Deformation.Kontsevich.RealForestSimpleCluster
