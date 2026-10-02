import EnvelopingIsomorphism.Deformation.Kontsevich.GraphFormsClosed
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestOriginalCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.CompactDRCoordinates

/-! Smooth actual full direction/ratio data in the original normalized configuration coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.OriginalDRSmooth

open Configuration ComplexConjugate Set Filter
open scoped Topology ContDiff

variable {n m : ℕ}

/-- All original and conjugate doubled points, as actual affine real-coordinate functions. -/
def doubledRaw (x : GraphForms.Coordinates n m) : DoubledLabel (n + 1) m → ℂ :=
  ForestPositiveChartSmooth.doubledRaw 0 x

@[simp] theorem doubledRaw_toConfiguration (x : GraphForms.CoordinateDomain n m)
    (v : DoubledLabel (n + 1) m) : doubledRaw x.val v = (GraphForms.toConfiguration x).doubledPoint v := by
  rcases v with (v | v) | v <;>
    simp [doubledRaw, ForestPositiveChartSmooth.doubledRaw, Configuration.doubledPoint,
      GraphForms.toConfiguration, Configuration.vertexPoint]

theorem contDiff_doubledRaw (v : DoubledLabel (n + 1) m) :
    ContDiff ℝ ⊤ (fun x : GraphForms.Coordinates n m => doubledRaw x v) := by
  exact contDiff_pi.mp (ForestPositiveChartSmooth.contDiff_doubledRaw (m := m)
    (ν := ⊤) (0 : Fin (n + 1))) v

def pairDifference (p : DoubledPair (n + 1) m) (x : GraphForms.Coordinates n m) : ℂ :=
  doubledRaw x p.val.2 - doubledRaw x p.val.1

@[simp] theorem pairDifference_toConfiguration (x : GraphForms.CoordinateDomain n m)
    (p : DoubledPair (n + 1) m) : pairDifference p x.val = (GraphForms.toConfiguration x).pairDifference p := by
  simp only [pairDifference, Configuration.pairDifference, doubledRaw_toConfiguration]

theorem contDiff_pairDifference (p : DoubledPair (n + 1) m) : ContDiff ℝ ⊤ (pairDifference p) :=
  (contDiff_doubledRaw p.val.2).sub (contDiff_doubledRaw p.val.1)

theorem pairDifference_ne_zero {x : GraphForms.Coordinates n m} (hx : GraphForms.Admissible x)
    (p : DoubledPair (n + 1) m) : pairDifference p x ≠ 0 := by
  have h := (GraphForms.toConfiguration ⟨x, hx⟩).pairDifference_ne_zero p
  simpa only [← pairDifference_toConfiguration] using h

/-- The original direction is the genuine circle phase; its ambient value is complex. -/
def direction (p : DoubledPair (n + 1) m) (x : GraphForms.Coordinates n m) : ℂ :=
  complexPhase (pairDifference p x)

/-- Original bounded distance ratios include every admissible doubled triple. -/
def ratio (t : DoubledTriple (n + 1) m) (x : GraphForms.Coordinates n m) : ℝ :=
  ‖pairDifference ⟨(t.val.1, t.val.2.1), t.property.1⟩ x‖ /
    (‖pairDifference ⟨(t.val.1, t.val.2.1), t.property.1⟩ x‖ +
      ‖pairDifference ⟨(t.val.1, t.val.2.2), t.property.2⟩ x‖)

theorem contDiffAt_direction (p : DoubledPair (n + 1) m)
    {x : GraphForms.Coordinates n m} (hx : GraphForms.Admissible x) :
    ContDiffAt ℝ ⊤ (direction p) x := by
  have hp := pairDifference_ne_zero hx p
  have hf := (contDiff_pairDifference p).contDiffAt (x := x)
  have hn := hf.norm ℝ hp
  have hd : ContDiffAt ℝ ⊤ (fun y : GraphForms.Coordinates n m => (‖pairDifference p y‖ : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hn
  have hd0 : (‖pairDifference p x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hp)
  have hform : ContDiffAt ℝ ⊤ (fun y => pairDifference p y / (‖pairDifference p y‖ : ℂ)) x := by
    simpa only [div_eq_mul_inv, Pi.inv_apply] using hf.mul (hd.inv hd0)
  have hloc : ∀ᶠ y in 𝓝 x, pairDifference p y ≠ 0 :=
    ((isClosed_eq (contDiff_pairDifference p).continuous continuous_const).isOpen_compl).mem_nhds hp
  exact hform.congr_of_eventuallyEq (hloc.mono fun y hy => complexPhase_coe hy)

theorem contDiffAt_ratio (t : DoubledTriple (n + 1) m)
    {x : GraphForms.Coordinates n m} (hx : GraphForms.Admissible x) : ContDiffAt ℝ ⊤ (ratio t) x := by
  let p : DoubledPair (n + 1) m := ⟨(t.val.1, t.val.2.1), t.property.1⟩
  let q : DoubledPair (n + 1) m := ⟨(t.val.1, t.val.2.2), t.property.2⟩
  have hp := ((contDiff_pairDifference p).contDiffAt (x := x)).norm ℝ (pairDifference_ne_zero hx p)
  have hq := ((contDiff_pairDifference q).contDiffAt (x := x)).norm ℝ (pairDifference_ne_zero hx q)
  exact hp.div (hp.add hq) (ne_of_gt (add_pos
    (norm_pos_iff.mpr (pairDifference_ne_zero hx p)) (norm_pos_iff.mpr (pairDifference_ne_zero hx q))))

def ambient (x : GraphForms.Coordinates n m) : CompactDRCoordinates.Ambient (n + 1) m :=
  (fun p => direction p x, fun t => ratio t x)

def real (x : GraphForms.Coordinates n m) : Fin (CompactDRCoordinates.dimension (n + 1) m) → ℝ :=
  CompactDRCoordinates.realCoordinates (n + 1) m (ambient x)

/-- The extended ambient formula agrees with the actual full native encoder on every original point. -/
theorem ambient_eq_encoder (x : GraphForms.CoordinateDomain n m) :
    ambient x.val = CompactDRCoordinates.dataEmbedding (directionRatioCoordinates (GraphForms.toConfiguration x)) := by
  apply Prod.ext
  · funext p
    simp only [ambient, direction, CompactDRCoordinates.dataEmbedding, directionRatioCoordinates,
      pairDifference_toConfiguration]
  · funext t
    simp only [ambient, ratio, CompactDRCoordinates.dataEmbedding, directionRatioCoordinates,
      Configuration.tripleDistanceRatio, pairDifference_toConfiguration]

/-- The genuine original point in the anchor-zero compactification. -/
def originalPoint (x : GraphForms.CoordinateDomain n m) : Compactification (0 : Fin (n + 1)) m :=
  compactificationEmbedding 0 (GraphForms.toNormalized x)

theorem real_eq_embedding (x : GraphForms.CoordinateDomain n m) :
    real x.val = CompactDRCoordinates.embedding 0 (originalPoint x) := by
  rw [real, ambient_eq_encoder]
  rfl

theorem contDiffAt_ambient {x : GraphForms.Coordinates n m} (hx : GraphForms.Admissible x) :
    ContDiffAt ℝ ⊤ ambient x :=
  (contDiffAt_pi.mpr fun p => contDiffAt_direction p hx).prodMk
    (contDiffAt_pi.mpr fun t => contDiffAt_ratio t hx)

theorem contDiffAt_real {x : GraphForms.Coordinates n m} (hx : GraphForms.Admissible x) :
    ContDiffAt ℝ ⊤ real x :=
  (CompactDRCoordinates.realCoordinates (n + 1) m).contDiff.contDiffAt.comp x (contDiffAt_ambient hx)

theorem contDiffOn_real : ContDiffOn ℝ ⊤ (real (n := n) (m := m)) (GraphForms.admissibleSet n m) :=
  fun _ hx => (contDiffAt_real hx).contDiffWithinAt

end EnvelopingIsomorphism.Deformation.Kontsevich.OriginalDRSmooth
