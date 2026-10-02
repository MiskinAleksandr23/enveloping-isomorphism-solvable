import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterSmoothForms
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterPattern
import EnvelopingIsomorphism.Deformation.Kontsevich.CompactDRCoordinates

/-! Explicit smooth full-DR coordinates on the scale-zero simple real face.
The fixed collision mask removes all appearances of a norm at a zero vector. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterFaceDR
open Configuration ComplexConjugate ForestDirectionRatioCoordinates
open scoped Classical Topology
variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} (l u : Fin (m+1))

abbrev Face := BoundaryClusterFreeCoordinates.FaceCoordinates i a S m

def base (y : Face (m := m) (i := i) (a := a) (S := S)) : DoubledLabel n m → ℂ
  | Sum.inl (Sum.inl j) => (BoundaryClusterFreeCoordinates.faceEmbedding y).base j
  | Sum.inl (Sum.inr j) => (BoundaryClusterFreeCoordinates.faceEmbedding y).boundaryBase l u j
  | Sum.inr j => conj ((BoundaryClusterFreeCoordinates.faceEmbedding y).base j)

def velocity (y : Face (m := m) (i := i) (a := a) (S := S)) : DoubledLabel n m → ℂ
  | Sum.inl (Sum.inl j) => (BoundaryClusterFreeCoordinates.faceEmbedding y).velocity j
  | Sum.inl (Sum.inr j) => (BoundaryClusterFreeCoordinates.faceEmbedding y).boundaryVelocity l u j
  | Sum.inr j => conj ((BoundaryClusterFreeCoordinates.faceEmbedding y).velocity j)

def pairBase (p : DoubledPair n m) (y : Face (m := m) (i := i) (a := a) (S := S)) : ℂ :=
  base l u y p.val.2 - base l u y p.val.1

def pairVelocity (p : DoubledPair n m) (y : Face (m := m) (i := i) (a := a) (S := S)) : ℂ :=
  velocity l u y p.val.2 - velocity l u y p.val.1

theorem contDiff_base (j : DoubledLabel n m) : ContDiff ℝ ⊤ (fun y : Face (m := m) (i := i) (a := a) (S := S) ↦ base l u y j) := by
  rcases j with (j | j) | j
  · exact (BoundaryClusterFreeCoordinates.contDiff_base j).comp BoundaryClusterFreeCoordinates.faceEmbedding.contDiff
  · exact Complex.ofRealCLM.contDiff.comp
      ((BoundaryClusterFreeCoordinates.contDiff_boundaryBase l u j).comp BoundaryClusterFreeCoordinates.faceEmbedding.contDiff)
  · exact Complex.conjCLE.contDiff.comp
      ((BoundaryClusterFreeCoordinates.contDiff_base j).comp BoundaryClusterFreeCoordinates.faceEmbedding.contDiff)

theorem contDiff_velocity (j : DoubledLabel n m) : ContDiff ℝ ⊤ (fun y : Face (m := m) (i := i) (a := a) (S := S) ↦ velocity l u y j) := by
  rcases j with (j | j) | j
  · exact (BoundaryClusterFreeCoordinates.contDiff_velocity j).comp BoundaryClusterFreeCoordinates.faceEmbedding.contDiff
  · exact Complex.ofRealCLM.contDiff.comp
      ((BoundaryClusterFreeCoordinates.contDiff_boundaryVelocity l u j).comp BoundaryClusterFreeCoordinates.faceEmbedding.contDiff)
  · exact Complex.conjCLE.contDiff.comp
      ((BoundaryClusterFreeCoordinates.contDiff_velocity j).comp BoundaryClusterFreeCoordinates.faceEmbedding.contDiff)

theorem contDiff_pairBase (p : DoubledPair n m) : ContDiff ℝ ⊤ (pairBase (i := i) (a := a) (S := S) l u p) :=
  (contDiff_base l u p.val.2).sub (contDiff_base l u p.val.1)

theorem contDiff_pairVelocity (p : DoubledPair n m) : ContDiff ℝ ⊤ (pairVelocity (i := i) (a := a) (S := S) l u p) :=
  (contDiff_velocity l u p.val.2).sub (contDiff_velocity l u p.val.1)

def sourcePoint (y : Face (m := m) (i := i) (a := a) (S := S))
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u) :
    BoundaryClusterFreeDomain i a S m l u := ⟨BoundaryClusterFreeCoordinates.faceEmbedding y, le_rfl, hy⟩

theorem datum_pairBase (y : Face (m := m) (i := i) (a := a) (S := S))
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u) (p : DoubledPair n m) :
    (sourcePoint l u y hy).datum.pairBase p = pairBase l u p y := by
  have hb (j : DoubledLabel n m) : (sourcePoint l u y hy).datum.doubledBase j = base l u y j := by
    rcases j with (j | j) | j
    · exact (sourcePoint l u y hy).datum_base j
    · exact congrArg Complex.ofReal ((sourcePoint l u y hy).datum_boundaryBase j)
    · exact congrArg conj ((sourcePoint l u y hy).datum_base j)
  exact congrArg₂ (· - ·) (hb p.val.2) (hb p.val.1)

theorem datum_pairVelocity (y : Face (m := m) (i := i) (a := a) (S := S))
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u) (p : DoubledPair n m) :
    (sourcePoint l u y hy).datum.pairVelocity p = pairVelocity l u p y := by
  have hv (j : DoubledLabel n m) : (sourcePoint l u y hy).datum.doubledVelocity j = velocity l u y j := by
    rcases j with (j | j) | j
    · exact (sourcePoint l u y hy).datum_velocity j
    · exact congrArg Complex.ofReal ((sourcePoint l u y hy).datum_boundaryVelocity j)
    · exact congrArg conj ((sourcePoint l u y hy).datum_velocity j)
  exact congrArg₂ (· - ·) (hv p.val.2) (hv p.val.1)

theorem pairBase_eq_zero_iff (y : Face (m := m) (i := i) (a := a) (S := S))
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u) (p : DoubledPair n m) :
    pairBase l u p y = 0 ↔ boundaryClusterPairCollapses S l u p := by
  rw [← datum_pairBase l u y hy p]
  exact (sourcePoint l u y hy).datum.pairBase_eq_zero_iff_boundaryClusterPairCollapses p

theorem pairVelocity_ne_zero (y : Face (m := m) (i := i) (a := a) (S := S))
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u) (p : DoubledPair n m)
    (hp : boundaryClusterPairCollapses S l u p) : pairVelocity l u p y ≠ 0 := by
  rw [← datum_pairVelocity l u y hy p]
  exact (sourcePoint l u y hy).datum.pairVelocity_ne_zero_of_boundaryClusterPairCollapses p hp

def direction (p : DoubledPair n m) (y : Face (m := m) (i := i) (a := a) (S := S)) : ℂ :=
  if boundaryClusterPairCollapses S l u p then (complexPhase (pairVelocity l u p y) : ℂ)
  else (complexPhase (pairBase l u p y) : ℂ)

def ratio (q : DoubledTriple n m) (y : Face (m := m) (i := i) (a := a) (S := S)) : ℝ :=
  if boundaryClusterPairCollapses S l u (firstPair q) then
    if boundaryClusterPairCollapses S l u (secondPair q) then
      ‖pairVelocity l u (firstPair q) y‖ /
        (‖pairVelocity l u (firstPair q) y‖ + ‖pairVelocity l u (secondPair q) y‖)
    else 0
  else if boundaryClusterPairCollapses S l u (secondPair q) then 1
    else ‖pairBase l u (firstPair q) y‖ /
      (‖pairBase l u (firstPair q) y‖ + ‖pairBase l u (secondPair q) y‖)

def ambient (y : Face (m := m) (i := i) (a := a) (S := S)) : CompactDRCoordinates.Ambient n m :=
  (fun p ↦ direction l u p y, fun q ↦ ratio l u q y)

private theorem smooth_phase {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} {y : E} (hf : ContDiff ℝ ⊤ f) (h : f y ≠ 0) :
    ContDiffAt ℝ ⊤ (fun z ↦ (complexPhase (f z) : ℂ)) y := by
  have hn := hf.contDiffAt.norm ℝ h
  have hd : ContDiffAt ℝ ⊤ (fun z ↦ (‖f z‖ : ℂ)) y := Complex.ofRealCLM.contDiff.contDiffAt.comp y hn
  have hh : ContDiffAt ℝ ⊤ (fun z ↦ f z / (‖f z‖ : ℂ)) y := by
    simpa only [div_eq_mul_inv, Pi.inv_apply] using
      hf.contDiffAt.mul (hd.inv (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h)))
  have he : ∀ᶠ z in 𝓝 y, f z ≠ 0 := (hf.continuous.isOpen_preimage _ isOpen_compl_singleton).mem_nhds h
  exact hh.congr_of_eventuallyEq (he.mono fun z hz ↦ complexPhase_coe hz)

private theorem smooth_normRatio {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℂ} {y : E} (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g)
    (hfn : f y ≠ 0) (hgn : g y ≠ 0) :
    ContDiffAt ℝ ⊤ (fun z ↦ ‖f z‖ / (‖f z‖ + ‖g z‖)) y := by
  have hF := hf.contDiffAt.norm ℝ hfn
  have hG := hg.contDiffAt.norm ℝ hgn
  exact hF.div (hF.add hG) (ne_of_gt (add_pos (norm_pos_iff.mpr hfn) (norm_pos_iff.mpr hgn)))

/-- Every relevant pair difference is genuinely nonzero. Mixed ratios are
locally constant, so no smoothness of a norm at zero is asserted. -/
theorem contDiffAt_ambient (y : Face (m := m) (i := i) (a := a) (S := S))
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u) :
    ContDiffAt ℝ ⊤ (ambient l u) y := by
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro p
    unfold direction
    split_ifs with hp
    · exact smooth_phase (contDiff_pairVelocity l u p) (pairVelocity_ne_zero l u y hy p hp)
    · exact smooth_phase (contDiff_pairBase l u p) (mt (pairBase_eq_zero_iff l u y hy p).mp hp)
  · apply contDiffAt_pi.mpr
    intro q
    unfold ratio
    split_ifs with hp hq hq
    · exact smooth_normRatio (contDiff_pairVelocity l u (firstPair q))
        (contDiff_pairVelocity l u (secondPair q))
        (pairVelocity_ne_zero l u y hy _ hp) (pairVelocity_ne_zero l u y hy _ hq)
    · exact contDiffAt_const
    · exact contDiffAt_const
    · exact smooth_normRatio (contDiff_pairBase l u (firstPair q))
        (contDiff_pairBase l u (secondPair q))
        (mt (pairBase_eq_zero_iff l u y hy _).mp hp) (mt (pairBase_eq_zero_iff l u y hy _).mp hq)

/-- The smooth ambient formula is exactly the complete DR data of the
original simple-cluster insertion at its genuine scale-zero source. -/
theorem ambient_eq_data (y : Face (m := m) (i := i) (a := a) (S := S))
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u) :
    ambient l u y = CompactDRCoordinates.dataEmbedding
      (projectDR (sourcePoint l u y hy).toDomain.insertion.val) := by
  let D := (sourcePoint l u y hy).datum
  change ambient l u y = CompactDRCoordinates.dataEmbedding (D.resolvedCoordinates 0).2
  apply Prod.ext
  · funext p
    simp only [ambient, CompactDRCoordinates.dataEmbedding, BoundaryClusterData.resolvedCoordinates, apply_ite]
    simp only [BoundaryClusterData.activeDifference, Complex.ofReal_zero, zero_mul, add_zero]
    rw [show D.pairBase p = pairBase l u p y from datum_pairBase l u y hy p,
      show D.pairVelocity p = pairVelocity l u p y from datum_pairVelocity l u y hy p]
    simp only [direction, pairBase_eq_zero_iff l u y hy p]
    split_ifs <;> rfl
  · funext q
    simp only [ambient, CompactDRCoordinates.dataEmbedding, BoundaryClusterData.resolvedCoordinates, apply_ite]
    simp only [BoundaryClusterData.activeDifference, Complex.ofReal_zero, zero_mul, add_zero]
    simp only [show ∀ p, D.pairBase p = pairBase l u p y from datum_pairBase l u y hy,
      show ∀ p, D.pairVelocity p = pairVelocity l u p y from datum_pairVelocity l u y hy]
    change (if pairBase l u (firstPair q) y = 0 ∧ pairBase l u (secondPair q) y = 0 then
      ratio l u q y = (normalizedNormRatio (pairVelocity l u (firstPair q) y)
        (pairVelocity l u (secondPair q) y) : ℝ)
      else ratio l u q y = (normalizedNormRatio (pairBase l u (firstPair q) y)
        (pairBase l u (secondPair q) y) : ℝ))
    by_cases hp : boundaryClusterPairCollapses S l u (firstPair q) <;>
      by_cases hq : boundaryClusterPairCollapses S l u (secondPair q)
    · simp [ratio, hp, hq, (pairBase_eq_zero_iff l u y hy _).mpr hp,
        (pairBase_eq_zero_iff l u y hy _).mpr hq, normalizedNormRatio]
    · have hqn := mt (pairBase_eq_zero_iff l u y hy _).mp hq
      simp [ratio, hp, hq, (pairBase_eq_zero_iff l u y hy _).mpr hp, hqn, normalizedNormRatio]
    · have hpn := mt (pairBase_eq_zero_iff l u y hy _).mp hp
      simp [ratio, hp, hq, (pairBase_eq_zero_iff l u y hy _).mpr hq, hpn, normalizedNormRatio]
    · have hpn := mt (pairBase_eq_zero_iff l u y hy _).mp hp
      simp [ratio, hp, hq, hpn, normalizedNormRatio]

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterFaceDR
