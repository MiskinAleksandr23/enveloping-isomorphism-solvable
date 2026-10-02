import EnvelopingIsomorphism.Deformation.Kontsevich.ForestDRParameterIdentification

/-! The whole finite-tree decoder from actual stored direction/ratio data.
The positive encoder composition is proved; extension across corners and open
image are separate statements. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestDRInverse

open ForestMarkedFrames ForestDRParameterIdentification ForestDirectionRatioCoordinates
open ForestInsertionDifference ForestNormalizationTelescope MarkedDRIdentification
open scoped Classical

variable (T : RootedTree) [Fintype T] {I : Type*} (lab : T → I)

abbrev References := (A : T) → ¬ IsMax A → Reference I

/-- The intended geometric reference labels lie in descendant leaves. The
decoder formulas and their continuity require no additional choice principle. -/
def Located (d : References T (I := I)) : Prop :=
  ∀ A hA, (∃ v, A ≤ v ∧ IsMax v ∧ lab v = (d A hA).a) ∧
    (∃ v, A ≤ v ∧ IsMax v ∧ lab v = (d A hA).b) ∧
    (∀ c, (d A hA).correction = some c → ∃ v, A ≤ v ∧ IsMax v ∧ lab v = c)

def Region (F : Frames T) (d : References T (I := I)) : Set (Data I) :=
  {x | ∀ A hA, x ∈ ForestDRParameterIdentification.Region T lab F A (d A hA)}

theorem isOpen_region (F : Frames T) (d : References T (I := I)) :
    IsOpen (Region T lab F d) := by
  simp only [Region, Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro A
  apply isOpen_iInter_of_finite
  intro hA
  exact ForestDRParameterIdentification.isOpen_region T lab F A (d A hA)

omit [Fintype T] in
theorem pred_internal (B : T) (hB : B ≠ ⊥) : ¬ IsMax (Order.pred B) :=
  not_isMax_of_lt (Order.pred_lt_iff_ne_bot.mpr hB)

def recoveredRadii (F : Frames T) (d : References T (I := I)) (x : Data I) : T → ℝ :=
  fun B => if IsMax B then 1 else if hB : B = ⊥ then 1 else
    childRadius T lab F (Order.pred B) B (d (Order.pred B) (pred_internal T B hB)) x

def recoveredIncrements (F : Frames T) (d : References T (I := I)) (x : Data I) : T → ℂ :=
  fun B => if hB : B = ⊥ then 0 else
    childIncrement T lab F (Order.pred B) B (d (Order.pred B) (pred_internal T B hB)) x

def decode (F : Frames T) (d : References T (I := I)) (x : Data I) : Parameters T :=
  (recoveredRadii T lab F d x, recoveredIncrements T lab F d x)

theorem continuousAt_recoveredRadii (F : Frames T) (d : References T (I := I))
    (x : Data I) (hx : x ∈ Region T lab F d) : ContinuousAt (recoveredRadii T lab F d) x := by
  apply continuousAt_pi.mpr
  intro B
  by_cases hmax : IsMax B
  · simp only [recoveredRadii, if_pos hmax]
    exact continuousAt_const
  · by_cases hB : B = ⊥
    · simp only [recoveredRadii, if_neg hmax, dif_pos hB]
      exact continuousAt_const
    · simp only [recoveredRadii, if_neg hmax, dif_neg hB]
      exact continuousAt_childRadius T lab F _ B _ x (hx _ _)

theorem continuousAt_recoveredIncrements (F : Frames T) (d : References T (I := I))
    (x : Data I) (hx : x ∈ Region T lab F d) : ContinuousAt (recoveredIncrements T lab F d) x := by
  apply continuousAt_pi.mpr
  intro B
  by_cases hB : B = ⊥
  · simp only [recoveredIncrements, dif_pos hB]
    exact continuousAt_const
  · simp only [recoveredIncrements, dif_neg hB]
    exact continuousAt_childIncrement T lab F _ B _ x (hx _ _)

theorem continuousAt_decode (F : Frames T) (d : References T (I := I))
    (x : Data I) (hx : x ∈ Region T lab F d) : ContinuousAt (decode T lab F d) x :=
  (continuousAt_recoveredRadii T lab F d x hx).prodMk
    (continuousAt_recoveredIncrements T lab F d x hx)

theorem continuousOn_decode (F : Frames T) (d : References T (I := I)) :
    ContinuousOn (decode T lab F d) (Region T lab F d) :=
  fun x hx => (continuousAt_decode T lab F d x hx).continuousWithinAt

theorem continuous_decode (F : Frames T) (d : References T (I := I)) :
    Continuous (fun x : Region T lab F d => decode T lab F d x.val) :=
  (continuousOn_decode T lab F d).restrict

def Compatible (F : Frames T) (d : References T (I := I)) (p : I → ℂ) : Prop :=
  ∀ A hA, CompatibleShift T F A ((d A hA).shift p)

def DistinctReferences (d : References T (I := I)) (p : I → ℂ) : Prop :=
  ∀ A hA, p (d A hA).a ≠ p (d A hA).b

/-- Static chart choices: complex-centered references are used only on wholly
complex subtrees; stable references correct using the reflected anchor label. -/
def ReferenceModes (F : Frames T) (d : References T (I := I)) (σ : I → I) : Prop :=
  ∀ A hA, match (d A hA).correction with
    | none => ComplexSubtree T F A
    | some c => c = σ (d A hA).a

omit [Fintype T] in
theorem compatible_of_reflection (F : Frames T) (d : References T (I := I)) (σ : I → I)
    (hd : ReferenceModes T F d σ) (p : I → ℂ) (hp : ∀ i, p (σ i) = star (p i)) :
    Compatible T F d p := by
  intro A hA
  have hm := hd A hA
  cases hc : (d A hA).correction with
  | none =>
    rw [hc] at hm
    exact compatibleShift_complexSubtree T F A hm _
  | some c =>
    rw [hc] at hm
    exact compatibleShift_stable T F A (d A hA) p c hc (by rw [hm, hp])

theorem ofPositions_mem_region (F : Frames T) (d : References T (I := I))
    (p : I → ℂ) (P : T → ℂ) (href : DistinctReferences T d p)
    (hp : ∀ v, IsMax v → p (lab v) = P v) (hz : Compatible T F d p)
    (hpos : P ∈ PositiveGaps T F) : ofPositions p ∈ Region T lab F d := by
  intro A hA
  exact ForestDRParameterIdentification.ofPositions_mem_region T lab F A (d A hA) p P
    (href A hA) (fun v _ hv => hp v hv) (hz A hA) hA (hpos A)

/-- The complete decoder equals the actual marked-frame factory on original
positions, with the unused leaf ratios fixed to one. -/
theorem decode_ofPositions (F : Frames T) (d : References T (I := I))
    (p : I → ℂ) (P : T → ℂ) (href : DistinctReferences T d p)
    (hp : ∀ v, IsMax v → p (lab v) = P v) (hz : Compatible T F d p)
    (hpos : P ∈ PositiveGaps T F) :
    decode T lab F d (ofPositions p) =
      (ForestLeafRadii.fixLeaves T (localRadii T F P), increments T F P) := by
  apply Prod.ext
  · funext B
    by_cases hmax : IsMax B
    · simp [decode, recoveredRadii, ForestLeafRadii.fixLeaves, hmax]
    · by_cases hB : B = ⊥
      · subst B
        simp [decode, recoveredRadii, ForestLeafRadii.fixLeaves, hmax,
          localRadii_root T F P hpos]
      · simp only [decode, recoveredRadii, if_neg hmax, dif_neg hB,
          ForestLeafRadii.fixLeaves]
        rw [childRadius_ofPositions T lab F (Order.pred B) B
          (d _ (pred_internal T B hB)) p P (href _ _) (fun v _ hv => hp v hv)
          (hz _ _) (pred_internal T B hB) (Order.pred_le B) hmax]
        rfl
  · funext B
    by_cases hB : B = ⊥
    · subst B
      simp [decode, recoveredIncrements, increments]
    · simp only [decode, recoveredIncrements, dif_neg hB]
      rw [childIncrement_ofPositions T lab F (Order.pred B) B
        (d _ (pred_internal T B hB)) p P (href _ _) (fun v _ hv => hp v hv)
        (hz _ _) (pred_internal T B hB) (Order.pred_le B)]
      exact (increments_child T F P _ B (Order.pred_covBy_of_not_isMin (not_isMin_iff_ne_bot.mpr hB))).symm

open ForestMarkedFrameInverse AncestorScaleRatios

theorem decode_inserted (F : Frames T) (d : References T (I := I))
    (p : I → ℂ) (r : T → ℝ) (a : T → ℂ) (href : DistinctReferences T d p)
    (hp : ∀ v, IsMax v → p (lab v) = position T r a v) (hz : Compatible T F d p)
    (hr : PositiveInternal T r) (ha : ForestMarkedFrameInverse.Normalized T F r a)
    (hr0 : r ⊥ = 1) (ha0 : a ⊥ = 0) (hleaf : ∀ v, IsMax v → r v = 1) :
    decode T lab F d (ofPositions p) = (r, a) := by
  rw [decode_ofPositions T lab F d p (position T r a) href hp hz
    (positiveGaps_position T F r a hr ha)]
  exact inverse_position T F r a hr ha hr0 ha0 hleaf

variable (leaf : I → T)

/-- Agreement with the genuine full stored encoder is the existing proved
positive-scale factorization, specialized to original leaf positions. -/
theorem resolved_eq_ofPositions (x : Domain T leaf) (hr : ∀ v, 0 < x.val.1 v) :
    resolvedCoordinates T leaf x = ofPositions (fun i => position T x.val.1 x.val.2 (leaf i)) := by
  rw [resolvedCoordinates_eq_raw T leaf x hr]
  rfl

theorem inserted_reference_ne (x : Domain T leaf) (hr : ∀ v, 0 < x.val.1 v)
    (i j : I) (hne : i ≠ j) :
    position T x.val.1 x.val.2 (leaf i) ≠ position T x.val.1 x.val.2 (leaf j) := by
  have hpair : pairDifference T leaf x.val ⟨(i, j), hne⟩ ≠ 0 := by
    rw [pairDifference_factor]
    exact smul_ne_zero (scale_pos x.val.1 hr _).ne' (x.property.2 ⟨(i, j), hne⟩)
  intro heq
  exact hpair (sub_eq_zero.mpr heq.symm)

theorem inserted_distinctReferences (d : References T (I := I)) (x : Domain T leaf)
    (hr : ∀ v, 0 < x.val.1 v) :
    DistinctReferences T d (fun i => position T x.val.1 x.val.2 (leaf i)) := by
  intro A hA
  exact inserted_reference_ne T leaf x hr _ _ (d A hA).ne

/-- All actual full-encoder outputs on this positive normalized locus belong
to the explicit open decoder region. Reference compatibility remains an
explicit chart input (stable reflection or wholly complex subtree). -/
theorem resolved_mem_region (F : Frames T) (d : References T (I := I))
    (hlabel : ∀ v, IsMax v → leaf (lab v) = v)
    (x : Domain T leaf) (hr : ∀ v, 0 < x.val.1 v)
    (ha : ForestMarkedFrameInverse.Normalized T F x.val.1 x.val.2)
    (hz : Compatible T F d (fun i => position T x.val.1 x.val.2 (leaf i))) :
    resolvedCoordinates T leaf x ∈ Region T lab F d := by
  rw [resolved_eq_ofPositions T leaf x hr]
  apply ofPositions_mem_region T lab F d _ (position T x.val.1 x.val.2)
    (inserted_distinctReferences T leaf d x hr) _ hz
    (positiveGaps_position T F x.val.1 x.val.2 (fun v _ => hr v) ha)
  intro v hv
  rw [hlabel v hv]

/-- Literal left composition with the FULL resolved forest encoder, on the
positive normalized parameter locus. The reference gaps are derived from
actual admissibility, not assumed identification data. -/
theorem decode_resolved (F : Frames T) (d : References T (I := I))
    (hlabel : ∀ v, IsMax v → leaf (lab v) = v)
    (x : Domain T leaf) (hr : ∀ v, 0 < x.val.1 v)
    (ha : ForestMarkedFrameInverse.Normalized T F x.val.1 x.val.2)
    (hr0 : x.val.1 ⊥ = 1) (ha0 : x.val.2 ⊥ = 0)
    (hleaf : ∀ v, IsMax v → x.val.1 v = 1)
    (hz : Compatible T F d (fun i => position T x.val.1 x.val.2 (leaf i))) :
    decode T lab F d (resolvedCoordinates T leaf x) = x.val := by
  rw [resolved_eq_ofPositions T leaf x hr]
  apply decode_inserted T lab F d _ x.val.1 x.val.2
    (inserted_distinctReferences T leaf d x hr) _ hz
    (fun v _ => hr v) ha hr0 ha0 hleaf
  intro v hv
  rw [hlabel v hv]

/-- Reflected positive-locus version with reference compatibility discharged
from the fixed reference modes and actual reflected inserted positions. -/
theorem decode_resolved_reflected (F : Frames T) (d : References T (I := I))
    (σ : I → I) (hd : ReferenceModes T F d σ)
    (hlabel : ∀ v, IsMax v → leaf (lab v) = v)
    (x : Domain T leaf) (hr : ∀ v, 0 < x.val.1 v)
    (ha : ForestMarkedFrameInverse.Normalized T F x.val.1 x.val.2)
    (hr0 : x.val.1 ⊥ = 1) (ha0 : x.val.2 ⊥ = 0)
    (hleaf : ∀ v, IsMax v → x.val.1 v = 1)
    (hreflect : ∀ i, position T x.val.1 x.val.2 (leaf (σ i)) =
      star (position T x.val.1 x.val.2 (leaf i))) :
    decode T lab F d (resolvedCoordinates T leaf x) = x.val :=
  decode_resolved T lab leaf F d hlabel x hr ha hr0 ha0 hleaf
    (compatible_of_reflection T F d σ hd _ hreflect)

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestDRInverse
