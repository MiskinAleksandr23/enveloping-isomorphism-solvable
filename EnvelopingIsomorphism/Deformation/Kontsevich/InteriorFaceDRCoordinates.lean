import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterAngularChart
import EnvelopingIsomorphism.Deformation.Kontsevich.CompactDRCoordinates

/-! Smooth literal full-DR encoding of simple interior coarse/planar product
coordinates at radius zero. Mixed collapsing/noncollapsing ratios are constants. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFaceDRCoordinates
open Configuration InteriorGraphFaceCoordinates ComplexConjugate
open scoped Classical
variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

abbrev Product := ProductCoordinates i a b S m

def base (y : Product (i := i) (a := a) (b := b) (S := S) (m := m)) : DoubledLabel n m → ℂ
  | .inl (.inl j) => (toAngular y).toFree.base j
  | .inl (.inr j) => y.2.2 j
  | .inr j => conj ((toAngular y).toFree.base j)

def velocity (y : Product (i := i) (a := a) (b := b) (S := S) (m := m)) : DoubledLabel n m → ℂ
  | .inl (.inl j) => (toAngular y).toFree.velocity j
  | .inl (.inr _) => 0
  | .inr j => conj ((toAngular y).toFree.velocity j)

def baseDifference (p : DoubledPair n m) (y : Product (i := i) (a := a) (b := b) (S := S) (m := m)) : ℂ :=
  base y p.val.2 - base y p.val.1

def velocityDifference (p : DoubledPair n m) (y : Product (i := i) (a := a) (b := b) (S := S) (m := m)) : ℂ :=
  velocity y p.val.2 - velocity y p.val.1

def unit (p : DoubledPair n m) (y : Product (i := i) (a := a) (b := b) (S := S) (m := m)) : ℂ :=
  if clusterPairCollapses S p then velocityDifference p y else baseDifference p y

theorem contDiff_base (j : DoubledLabel n m) :
    ContDiff ℝ ⊤ (fun y : Product (i := i) (a := a) (b := b) (S := S) (m := m) ↦ base y j) := by
  rcases j with (j | j) | j
  · exact (ClusterAngularCoordinates.contDiff_base j).comp contDiff_toAngular
  · exact Complex.ofRealCLM.contDiff.comp (by fun_prop)
  · exact Complex.conjCLE.contDiff.comp ((ClusterAngularCoordinates.contDiff_base j).comp contDiff_toAngular)

theorem contDiff_velocity (j : DoubledLabel n m) :
    ContDiff ℝ ⊤ (fun y : Product (i := i) (a := a) (b := b) (S := S) (m := m) ↦ velocity y j) := by
  rcases j with (j | j) | j
  · exact (ClusterAngularCoordinates.contDiff_velocity j).comp contDiff_toAngular
  · exact contDiff_const
  · exact Complex.conjCLE.contDiff.comp ((ClusterAngularCoordinates.contDiff_velocity j).comp contDiff_toAngular)

theorem contDiff_unit (p : DoubledPair n m) :
    ContDiff ℝ ⊤ (unit (i := i) (a := a) (b := b) (S := S) p) := by
  unfold unit
  split_ifs
  · exact (contDiff_velocity _).sub (contDiff_velocity _)
  · exact (contDiff_base _).sub (contDiff_base _)

def freeDomain (y : Product (i := i) (a := a) (b := b) (S := S) (m := m))
    (hy : (toAngular y).toFree.OpenConditions) : ClusterFreeDomain i a b S m :=
  ⟨(toAngular y).toFree, le_rfl, hy⟩

variable (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i)
variable (y : Product (i := i) (a := a) (b := b) (S := S) (m := m))
  (hy : (toAngular y).toFree.OpenConditions)

def datum : SingleInteriorCluster i m S := ClusterFreeDomain.datum ha hb hanchor (freeDomain y hy)

theorem datum_base (j : DoubledLabel n m) :
    (datum ha hb hanchor y hy).toInteriorCollisionData.doubledBase j = base y j := by
  rcases j with (j | j) | j
  · exact ClusterFreeDomain.datum_base ha hb hanchor _ j
  · exact congrArg Complex.ofReal (congrFun (ClusterFreeDomain.datum_boundary ha hb hanchor (freeDomain y hy)) j)
  · exact congrArg conj (ClusterFreeDomain.datum_base ha hb hanchor _ j)

theorem datum_velocity (j : DoubledLabel n m) :
    (datum ha hb hanchor y hy).toInteriorCollisionData.doubledVelocity j = velocity y j := by
  rcases j with (j | j) | j
  · exact ClusterFreeDomain.datum_velocity ha hb hanchor _ j
  · rfl
  · exact congrArg conj (ClusterFreeDomain.datum_velocity ha hb hanchor _ j)

theorem datum_pairBase (p : DoubledPair n m) :
    (datum ha hb hanchor y hy).toInteriorCollisionData.pairBase p = baseDifference p y := by
  simp only [InteriorCollisionData.pairBase, datum_base, baseDifference]

theorem datum_pairVelocity (p : DoubledPair n m) :
    (datum ha hb hanchor y hy).toInteriorCollisionData.pairVelocity p = velocityDifference p y := by
  simp only [InteriorCollisionData.pairVelocity, datum_velocity, velocityDifference]

include ha hb hanchor hy in
theorem unit_ne_zero (p : DoubledPair n m) : unit p y ≠ 0 := by
  unfold unit
  split_ifs with h
  · rw [← datum_pairVelocity ha hb hanchor y hy]
    exact (datum ha hb hanchor y hy).pairVelocity_ne_zero_of_clusterPairCollapses p h
  · rw [← datum_pairBase ha hb hanchor y hy]
    exact ((datum ha hb hanchor y hy).pairBase_eq_zero_iff_clusterPairCollapses p).not.mpr h

omit ha hb hba hanchor y hy in
def ratio (t : DoubledTriple n m) (y : Product (i := i) (a := a) (b := b) (S := S) (m := m)) : ℝ :=
  let p : DoubledPair n m := ⟨(t.val.1, t.val.2.1), t.property.1⟩
  let q : DoubledPair n m := ⟨(t.val.1, t.val.2.2), t.property.2⟩
  if clusterPairCollapses S p ∧ ¬clusterPairCollapses S q then 0
  else if ¬clusterPairCollapses S p ∧ clusterPairCollapses S q then 1
  else ‖unit p y‖ / (‖unit p y‖ + ‖unit q y‖)

omit ha hb hba hanchor y hy in
def ambient (y : Product (i := i) (a := a) (b := b) (S := S) (m := m)) : CompactDRCoordinates.Ambient n m :=
  (fun p ↦ unit p y / (‖unit p y‖ : ℂ), fun t ↦ ratio t y)

include ha hb hanchor hy in
theorem contDiffAt_ambient : ContDiffAt ℝ ⊤ (ambient (i := i) (a := a) (b := b) (S := S) (m := m)) y := by
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro p
    have hu := (contDiff_unit (i := i) (a := a) (b := b) (S := S) p).contDiffAt (x := y)
    have hn := hu.norm ℝ (unit_ne_zero ha hb hanchor y hy p)
    have hr := Complex.ofRealCLM.contDiff.contDiffAt.comp y hn
    simpa only [div_eq_mul_inv, Pi.inv_apply, Function.comp_apply, Complex.ofRealCLM_apply] using hu.mul
      (hr.inv (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (unit_ne_zero ha hb hanchor y hy p))))
  · apply contDiffAt_pi.mpr
    intro t
    dsimp only [ratio]
    split_ifs
    · exact contDiffAt_const
    · exact contDiffAt_const
    · exact ((contDiff_unit _).contDiffAt.norm ℝ (unit_ne_zero ha hb hanchor y hy _)).div
        (((contDiff_unit _).contDiffAt.norm ℝ (unit_ne_zero ha hb hanchor y hy _)).add
          ((contDiff_unit _).contDiffAt.norm ℝ (unit_ne_zero ha hb hanchor y hy _)))
        (add_pos (norm_pos_iff.mpr (unit_ne_zero ha hb hanchor y hy _))
          (norm_pos_iff.mpr (unit_ne_zero ha hb hanchor y hy _))).ne'


/-- The smooth formula is the actual compactification encoding of the simple
collision, not a model substituted for its native coordinates. -/
theorem ambient_eq_boundaryPoint : ambient y = CompactDRCoordinates.dataEmbedding
    (projectDR (datum ha hb hanchor y hy).toInteriorCollisionData.boundaryPoint.val) := by
  have hbzero (p : DoubledPair n m) : baseDifference p y = 0 ↔ clusterPairCollapses S p := by
    rw [← datum_pairBase ha hb hanchor y hy]
    exact (datum ha hb hanchor y hy).pairBase_eq_zero_iff_clusterPairCollapses p
  have hbp := (datum ha hb hanchor y hy).toInteriorCollisionData.resolvedCoordinates_zero
  change ambient y = CompactDRCoordinates.dataEmbedding
    (projectDR ((datum ha hb hanchor y hy).toInteriorCollisionData.resolvedCoordinates 0))
  rw [hbp]
  apply Prod.ext
  · funext p
    change unit p y / (‖unit p y‖ : ℂ) =
      (linearPhaseLimit ((datum ha hb hanchor y hy).toInteriorCollisionData.pairBase p)
        ((datum ha hb hanchor y hy).toInteriorCollisionData.pairVelocity p) : ℂ)
    rw [datum_pairBase, datum_pairVelocity]
    rw [← complexPhase_coe (unit_ne_zero ha hb hanchor y hy p)]
    unfold unit linearPhaseLimit
    by_cases h : clusterPairCollapses S p
    · simp [h, (hbzero p).mpr h]
    · simp [h, (hbzero p).not.mpr h]
  · funext t
    let p : DoubledPair n m := ⟨(t.val.1, t.val.2.1), t.property.1⟩
    let q : DoubledPair n m := ⟨(t.val.1, t.val.2.2), t.property.2⟩
    change ratio t y = (linearRatioLimit
      ((datum ha hb hanchor y hy).toInteriorCollisionData.pairBase p)
      ((datum ha hb hanchor y hy).toInteriorCollisionData.pairBase q)
      ((datum ha hb hanchor y hy).toInteriorCollisionData.pairVelocity p)
      ((datum ha hb hanchor y hy).toInteriorCollisionData.pairVelocity q) : ℝ)
    rw [datum_pairBase, datum_pairBase, datum_pairVelocity, datum_pairVelocity]
    have hne (e : DoubledPair n m) (he : ¬clusterPairCollapses S e) : ‖baseDifference e y‖ ≠ 0 :=
      norm_ne_zero_iff.mpr ((hbzero e).not.mpr he)
    by_cases hp : clusterPairCollapses S p <;> by_cases hq : clusterPairCollapses S q
    · simp only [ratio, show clusterPairCollapses S ⟨(t.val.1, t.val.2.1), t.property.1⟩ from hp,
        show clusterPairCollapses S ⟨(t.val.1, t.val.2.2), t.property.2⟩ from hq,
        not_true_eq_false, and_false, false_and, if_false, unit, if_pos,
        linearRatioLimit, (hbzero p).mpr hp, (hbzero q).mpr hq, and_self, normalizedNormRatio]
      rfl
    · have hbp0 := (hbzero p).mpr hp
      simp [ratio, unit, linearRatioLimit, hp, hq, hbp0, (hbzero q).not.mpr hq,
        normalizedNormRatio, p, q] at *
    · have hbq0 := (hbzero q).mpr hq
      simp [ratio, unit, linearRatioLimit, hp, hq, hbq0, (hbzero p).not.mpr hp,
        normalizedNormRatio, hne p hp, p, q] at *
    · simp [ratio, unit, linearRatioLimit, hp, hq, (hbzero p).not.mpr hp,
        (hbzero q).not.mpr hq, normalizedNormRatio, p, q] at *

end EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFaceDRCoordinates
