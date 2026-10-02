import EnvelopingIsomorphism.Deformation.Kontsevich.ForestDirectionRatioCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.ReferenceNormIdentification

/-!
# Marked inverse functions from actual full direction/ratio data

The recovered coordinates are actual relative leaf positions. Only the chosen
finite set of outputs needs finite reference ratios. No injectivity of a
recovered limiting array or identification with free child centers is asserted.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.MarkedDRIdentification

open ForestDirectionRatioCoordinates (Pair Triple Data)
open Configuration Topology Set
open scoped Classical

variable {I : Type*}

def markedPair (a b : I) (hab : a ≠ b) : Pair I := ⟨(a, b), hab⟩

def markedTriple (a j b : I) (haj : a ≠ j) (hab : a ≠ b) : Triple I :=
  ⟨(a, j, b), haj, hab⟩

/-- The literal full direction/ratio encoder for a complex position array. -/
def ofPositions (p : I → ℂ) : Data I :=
  (fun s => complexPhase (p s.val.2 - p s.val.1),
    fun t => normalizedNormRatio (p t.val.2.1 - p t.val.1) (p t.val.2.2 - p t.val.1))

def recoverArray (a b : I) (hab : a ≠ b) (x : Data I) : I → ℂ :=
  fun j => if hja : j = a then 0 else
    recoverRelativePosition (x.1 (markedPair a j (Ne.symm hja)))
      (x.2 (markedTriple a j b (Ne.symm hja) hab))

@[simp] theorem recoverArray_anchor (a b : I) (hab : a ≠ b) (x : Data I) :
    recoverArray a b hab x a = 0 := by simp [recoverArray]

theorem ratio_ofPositions (p : I → ℂ) (a j b : I) (haj : a ≠ j) (hab : a ≠ b) :
    ((ofPositions p).2 (markedTriple a j b haj hab) : ℝ) =
      referenceNormRatio ‖p b - p a‖ (p j - p a) := rfl

/-- Actual original-coordinate identity; only the reference difference must
be nonzero, so other original or limiting marks may coincide. -/
theorem recoverArray_ofPositions (p : I → ℂ) (a b : I) (hab : a ≠ b)
    (href : p a ≠ p b) (j : I) :
    recoverArray a b hab (ofPositions p) j = (p j - p a) / (‖p b - p a‖ : ℂ) := by
  by_cases hja : j = a
  · simp [hja]
  · rw [recoverArray, dif_neg hja]
    change recoverRelativePosition (complexPhase (p j - p a))
      (referenceNormRatio ‖p b - p a‖ (p j - p a)) = _
    have hR : 0 < ‖p b - p a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr href.symm)
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr hR.ne')).mpr
    simpa only [mul_comm] using recoverRelativePosition_referenceNormRatio hR (p j - p a)

def FiniteRegion (S : Finset I) (a b : I) (hab : a ≠ b) : Set (Data I) :=
  {x | ∀ j : S, ∀ hja : j.val ≠ a, (x.2 (markedTriple a j.val b (Ne.symm hja) hab) : ℝ) < 1}

theorem isOpen_finiteRegion (S : Finset I) (a b : I) (hab : a ≠ b) :
    IsOpen (FiniteRegion S a b hab) := by
  simp only [FiniteRegion, setOf_forall]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro hja
  exact isOpen_lt
    (continuous_subtype_val.comp ((continuous_apply _).comp continuous_snd)) continuous_const

theorem ofPositions_mem_finiteRegion (S : Finset I) (p : I → ℂ) (a b : I)
    (hab : a ≠ b) (href : p a ≠ p b) : ofPositions p ∈ FiniteRegion S a b hab := by
  intro j hja
  rw [ratio_ofPositions]
  exact referenceNormRatio_lt_one (norm_pos_iff.mpr (sub_ne_zero.mpr href.symm)) _

private theorem continuousAt_relativeIdentification (θ : Circle) (r : ℝ) (hr : r < 1) :
    ContinuousAt (fun x : Circle × ℝ => recoverRelativePosition x.1 x.2) (θ, r) := by
  have hcont : ContinuousOn (fun x : Circle × ℝ => recoverRelativePosition x.1 x.2)
      {x | x.2 < 1} := by
    apply continuousOn_iff_continuous_restrict.mpr
    exact continuous_recoverRelativePosition.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk fun x => x.property))
  exact (hcont (θ, r) hr).continuousAt
    ((isOpen_lt continuous_snd continuous_const).mem_nhds hr)

theorem continuousAt_recoverArray (a b : I) (hab : a ≠ b) (j : I) (x : Data I)
    (hfinite : ∀ hja : j ≠ a, (x.2 (markedTriple a j b (Ne.symm hja) hab) : ℝ) < 1) :
    ContinuousAt (fun y : Data I => recoverArray a b hab y j) x := by
  by_cases hja : j = a
  · simp only [hja, recoverArray_anchor]
    exact continuousAt_const
  · simp only [recoverArray, dif_neg hja]
    let g : Data I → Circle × ℝ := fun y =>
      (y.1 (markedPair a j (Ne.symm hja)), (y.2 (markedTriple a j b (Ne.symm hja) hab) : ℝ))
    have hg : Continuous g :=
      ((continuous_apply _).comp continuous_fst).prodMk
        (continuous_subtype_val.comp ((continuous_apply _).comp continuous_snd))
    exact (continuousAt_relativeIdentification _ _ (hfinite hja)).comp (f := g) (x := x) hg.continuousAt

def recoverOn (S : Finset I) (a b : I) (hab : a ≠ b) (x : Data I) : S → ℂ :=
  fun j => recoverArray a b hab x j.val

/-- Joint continuity on the actual finite open region, with no conditions
on ratios belonging only to marks outside the requested finite output set. -/
theorem continuousOn_recoverOn (S : Finset I) (a b : I) (hab : a ≠ b) :
    ContinuousOn (recoverOn S a b hab) (FiniteRegion S a b hab) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_pi.mpr
  intro j
  exact continuousAt_recoverArray a b hab j.val x (hx j)

theorem continuous_recoverOn (S : Finset I) (a b : I) (hab : a ≠ b) :
    Continuous (fun x : FiniteRegion S a b hab => recoverOn S a b hab x.val) :=
  (continuousOn_recoverOn S a b hab).restrict

theorem reference_ratio_half_ofPositions (p : I → ℂ) (a b : I) (hab : a ≠ b)
    (href : p a ≠ p b) :
    ((ofPositions p).2 (markedTriple a b b hab hab) : ℝ) = 1 / 2 := by
  change ‖p b - p a‖ / (‖p b - p a‖ + ‖p b - p a‖) = 1 / 2
  have hn : ‖p b - p a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr href.symm)
  field_simp
  ring

theorem recoverArray_reference_of_half (a b : I) (hab : a ≠ b) (x : Data I)
    (hhalf : (x.2 (markedTriple a b b hab hab) : ℝ) = 1 / 2) :
    recoverArray a b hab x b = (x.1 (markedPair a b hab) : ℂ) := by
  rw [recoverArray, dif_neg hab.symm]
  unfold recoverRelativePosition
  rw [hhalf]
  norm_num

theorem norm_recoverArray_reference_of_half (a b : I) (hab : a ≠ b) (x : Data I)
    (hhalf : (x.2 (markedTriple a b b hab hab) : ℝ) = 1 / 2) :
    ‖recoverArray a b hab x b‖ = 1 := by
  rw [recoverArray_reference_of_half a b hab x hhalf, Circle.norm_coe]

def ratioCoefficient (x : Data I) (t : Triple I) : ℝ := (x.2 t : ℝ) / (1 - (x.2 t : ℝ))

theorem ratioCoefficient_ofPositions (p : I → ℂ) (s t c : I) (hst : s ≠ t) (hsc : s ≠ c)
    (hgap : p s ≠ p c) :
    ratioCoefficient (ofPositions p) (markedTriple s t c hst hsc) = ‖p t - p s‖ / ‖p c - p s‖ := by
  have hR : 0 < ‖p c - p s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hgap.symm)
  apply (eq_div_iff hR.ne').mpr
  change (referenceNormRatio ‖p c - p s‖ (p t - p s) /
    (1 - referenceNormRatio ‖p c - p s‖ (p t - p s))) * ‖p c - p s‖ = _
  simpa only [mul_comm] using referenceNormRatio_div hR (p t - p s)

theorem norm_recoverArray_sub_ofPositions (p : I → ℂ) (a b : I) (hab : a ≠ b)
    (href : p a ≠ p b) (s c : I) :
    ‖recoverArray a b hab (ofPositions p) s - recoverArray a b hab (ofPositions p) c‖ =
      ‖p s - p c‖ / ‖p b - p a‖ := by
  rw [recoverArray_ofPositions p a b hab href s, recoverArray_ofPositions p a b hab href c, ← sub_div]
  have hdiff : (p s - p a) - (p c - p a) = p s - p c := by abel
  rw [hdiff, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]

/-- Recover a child/parent scale from the child's internal marked pair and
a common-source reference outside it, measured in recovered parent coordinates. -/
def childScale (a b : I) (hab : a ≠ b) (s t c : I) (hst : s ≠ t) (hsc : s ≠ c)
    (x : Data I) : ℝ :=
  ratioCoefficient x (markedTriple s t c hst hsc) *
    ‖recoverArray a b hab x s - recoverArray a b hab x c‖

/-- Exact original-coordinate child/parent radius ratio. The reference gap
is genuinely nonzero; no scale-ratio identity is supplied as an assumption. -/
theorem childScale_ofPositions (p : I → ℂ) (a b : I) (hab : a ≠ b) (href : p a ≠ p b)
    (s t c : I) (hst : s ≠ t) (hsc : s ≠ c) (hgap : p s ≠ p c) :
    childScale a b hab s t c hst hsc (ofPositions p) = ‖p t - p s‖ / ‖p b - p a‖ := by
  rw [childScale, ratioCoefficient_ofPositions p s t c hst hsc hgap,
    norm_recoverArray_sub_ofPositions p a b hab href s c, norm_sub_rev (p s) (p c)]
  have hG : ‖p c - p s‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hgap.symm)
  have hP : ‖p b - p a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr href.symm)
  field_simp

def ChildRegion (a b : I) (hab : a ≠ b) (s t c : I) (hst : s ≠ t) (hsc : s ≠ c) : Set (Data I) :=
  FiniteRegion {s, c} a b hab ∩ {x | (x.2 (markedTriple s t c hst hsc) : ℝ) < 1}

theorem isOpen_childRegion (a b : I) (hab : a ≠ b) (s t c : I) (hst : s ≠ t) (hsc : s ≠ c) :
    IsOpen (ChildRegion a b hab s t c hst hsc) :=
  (isOpen_finiteRegion {s, c} a b hab).inter (isOpen_lt
    (continuous_subtype_val.comp ((continuous_apply _).comp continuous_snd)) continuous_const)

theorem ofPositions_mem_childRegion (p : I → ℂ) (a b : I) (hab : a ≠ b) (href : p a ≠ p b)
    (s t c : I) (hst : s ≠ t) (hsc : s ≠ c) (hgap : p s ≠ p c) :
    ofPositions p ∈ ChildRegion a b hab s t c hst hsc := by
  refine ⟨ofPositions_mem_finiteRegion {s, c} p a b hab href, ?_⟩
  change ((ofPositions p).2 (markedTriple s t c hst hsc) : ℝ) < 1
  rw [ratio_ofPositions]
  exact referenceNormRatio_lt_one (norm_pos_iff.mpr (sub_ne_zero.mpr hgap.symm)) _

/-- Continuity includes ratio zero and does not require noncollision of the
recovered parent array; the outside gap is multiplied, not divided out. -/
theorem continuousAt_childScale (a b : I) (hab : a ≠ b) (s t c : I) (hst : s ≠ t) (hsc : s ≠ c)
    (x : Data I) (hx : x ∈ ChildRegion a b hab s t c hst hsc) :
    ContinuousAt (childScale a b hab s t c hst hsc) x := by
  have hs := continuousAt_recoverArray a b hab s x (hx.1 ⟨s, by simp⟩)
  have hc := continuousAt_recoverArray a b hab c x (hx.1 ⟨c, by simp⟩)
  have hratio : Continuous (fun y : Data I => (y.2 (markedTriple s t c hst hsc) : ℝ)) :=
    continuous_subtype_val.comp ((continuous_apply _).comp continuous_snd)
  exact (hratio.continuousAt.div (continuousAt_const.sub hratio.continuousAt)
    (ne_of_gt (sub_pos.mpr hx.2))).mul (hs.sub hc).norm

theorem continuousOn_childScale (a b : I) (hab : a ≠ b) (s t c : I) (hst : s ≠ t) (hsc : s ≠ c) :
    ContinuousOn (childScale a b hab s t c hst hsc) (ChildRegion a b hab s t c hst hsc) :=
  fun x hx => (continuousAt_childScale a b hab s t c hst hsc x hx).continuousWithinAt

theorem childScale_nonneg (a b : I) (hab : a ≠ b) (s t c : I) (hst : s ≠ t) (hsc : s ≠ c)
    (x : Data I) (hx : x ∈ ChildRegion a b hab s t c hst hsc) :
    0 ≤ childScale a b hab s t c hst hsc x :=
  mul_nonneg (div_nonneg (x.2 _).property.1 (sub_pos.mpr hx.2).le) (norm_nonneg _)

theorem childScale_eq_zero_of_ratio_zero (a b : I) (hab : a ≠ b)
    (s t c : I) (hst : s ≠ t) (hsc : s ≠ c) (x : Data I)
    (hzero : (x.2 (markedTriple s t c hst hsc) : ℝ) = 0) :
    childScale a b hab s t c hst hsc x = 0 := by
  simp only [childScale, ratioCoefficient, hzero, zero_div, zero_mul]

section ActualData

variable {n m : ℕ}

theorem ofPositions_doubledPoint (c : Configuration n m) :
    ofPositions c.doubledPoint = directionRatioCoordinates c := rfl

theorem recoverArray_configuration (c : Configuration n m) (a b : DoubledLabel n m) (hab : a ≠ b)
    (j : DoubledLabel n m) :
    recoverArray a b hab (directionRatioCoordinates c) j =
      (c.doubledPoint j - c.doubledPoint a) / (‖c.doubledPoint b - c.doubledPoint a‖ : ℂ) := by
  rw [← ofPositions_doubledPoint]
  exact recoverArray_ofPositions _ a b hab (fun h => hab (c.doubledPoint_injective h)) j

theorem childScale_configuration (cfg : Configuration n m) (a b : DoubledLabel n m) (hab : a ≠ b)
    (s t c : DoubledLabel n m) (hst : s ≠ t) (hsc : s ≠ c) :
    childScale a b hab s t c hst hsc (directionRatioCoordinates cfg) =
      ‖cfg.doubledPoint t - cfg.doubledPoint s‖ / ‖cfg.doubledPoint b - cfg.doubledPoint a‖ := by
  rw [← ofPositions_doubledPoint]
  exact childScale_ofPositions _ a b hab (fun h => hab (cfg.doubledPoint_injective h))
    s t c hst hsc (fun h => hsc (cfg.doubledPoint_injective h))

/-- The repeated-target reference ratio remains one half on the actual
compact closure, including collision points. -/
theorem reference_ratio_half_space (a b : DoubledLabel n m) (hab : a ≠ b) (x : DRSpace n m) :
    (x.val.2 (markedTriple a b b hab hab) : ℝ) = 1 / 2 := by
  have hclosed : IsClosed {y : DRData n m | (y.2 (markedTriple a b b hab hab) : ℝ) = 1 / 2} :=
    isClosed_eq (continuous_subtype_val.comp ((continuous_apply _).comp continuous_snd)) continuous_const
  have hsource : Set.range (directionRatioCoordinates : Configuration n m → DRData n m) ⊆
      {y | (y.2 (markedTriple a b b hab hab) : ℝ) = 1 / 2} := by
    rintro _ ⟨c, rfl⟩
    rw [← ofPositions_doubledPoint]
    exact reference_ratio_half_ofPositions _ a b hab (fun h => hab (c.doubledPoint_injective h))
  exact (closure_minimal hsource hclosed) x.property

theorem recoverArray_reference_space (a b : DoubledLabel n m) (hab : a ≠ b) (x : DRSpace n m) :
    recoverArray a b hab x.val b = (x.val.1 (markedPair a b hab) : ℂ) :=
  recoverArray_reference_of_half a b hab x.val (reference_ratio_half_space a b hab x)

theorem norm_recoverArray_reference_space (a b : DoubledLabel n m) (hab : a ≠ b) (x : DRSpace n m) :
    ‖recoverArray a b hab x.val b‖ = 1 :=
  norm_recoverArray_reference_of_half a b hab x.val (reference_ratio_half_space a b hab x)

end ActualData

end EnvelopingIsomorphism.Deformation.Kontsevich.MarkedDRIdentification
