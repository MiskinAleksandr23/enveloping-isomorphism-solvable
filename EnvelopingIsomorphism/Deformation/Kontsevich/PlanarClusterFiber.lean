import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarClusterInteriorEmbedding
import EnvelopingIsomorphism.Deformation.Kontsevich.CompactificationSequences

/-! Exact characterization of the planar compactification as the closed
all-interior-points-at-I fiber of the genuine upper-half-plane compactification. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PlanarClusterFiber

open Configuration ForestDirectionRatioCoordinates ComplexConjugate Filter Topology Set
open PlanarClusterDoubledData
open scoped Classical

variable {q : ℕ} (a b : Fin q) (hab : a ≠ b)

def originalPoints (c : Configuration q 0) (j : Fin q) : ℂ := c.interior j

theorem originalPoints_injective (c : Configuration q 0) : Function.Injective (originalPoints c) :=
  fun _ _ h => c.interior_injective (UpperHalfPlane.ext h)

def referenceRadius (c : Configuration q 0) : ℝ := ‖originalPoints c b - originalPoints c a‖

include hab in
theorem referenceRadius_pos (c : Configuration q 0) : 0 < referenceRadius a b c :=
  norm_pos_iff.mpr (sub_ne_zero.mpr ((originalPoints_injective c).ne hab.symm))

def planarOfConfiguration (c : Configuration q 0) : PlanarClusterCompactification.Normalized a b :=
  ⟨fun j => (originalPoints c j - originalPoints c a) / (referenceRadius a b c : ℂ), by
    intro i j h
    apply originalPoints_injective c
    have h' := congrArg (fun z : ℂ => z * (referenceRadius a b c : ℂ)) h
    rw [div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (referenceRadius_pos a b hab c).ne'),
      div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (referenceRadius_pos a b hab c).ne')] at h'
    exact sub_left_inj.mp h',
    by simp,
    by rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (referenceRadius_pos a b hab c).le]
       exact div_self (referenceRadius_pos a b hab c).ne'⟩

theorem planarOfConfiguration_encode (c : Configuration q 0) :
    PlanarClusterCompactification.encode a b (planarOfConfiguration a b hab c) = projectUpper (directionRatioCoordinates c) := by
  have hd (i j : Fin q) :
      (planarOfConfiguration a b hab c).val j - (planarOfConfiguration a b hab c).val i =
        (referenceRadius a b c)⁻¹ • (originalPoints c j - originalPoints c i) := by
    change (_ / _) - (_ / _) = _
    rw [← sub_div]
    have he : (originalPoints c j - originalPoints c a) - (originalPoints c i - originalPoints c a) =
        originalPoints c j - originalPoints c i := by abel
    rw [he]
    simp only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]
  have hr := inv_pos.mpr (referenceRadius_pos a b hab c)
  apply Prod.ext
  · funext p
    change complexPhase ((planarOfConfiguration a b hab c).val p.val.2 -
      (planarOfConfiguration a b hab c).val p.val.1) = _
    rw [hd, complexPhase_pos_real_smul hr]
    rfl
  · funext t
    apply Subtype.ext
    change ‖(planarOfConfiguration a b hab c).val t.val.2.1 - (planarOfConfiguration a b hab c).val t.val.1‖ /
      (‖(planarOfConfiguration a b hab c).val t.val.2.1 - (planarOfConfiguration a b hab c).val t.val.1‖ +
        ‖(planarOfConfiguration a b hab c).val t.val.2.2 - (planarOfConfiguration a b hab c).val t.val.1‖) = _
    simp only [hd, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    rw [← mul_add, mul_div_mul_left _ _ hr.ne']
    rfl

include hab in
/-- Every upper DR projection lies in the actual planar closure, including
points outside the collision fiber. -/
theorem projectUpper_mem (x : Compactification a 0) :
    projectUpper (projectDR x.val) ∈ PlanarClusterCompactification.carrier a b := by
  have h := continuous_projectUpper.continuousAt.tendsto.comp (tendsto_normalizedSequence_DR a x)
  apply mem_closure_of_tendsto h
  exact Filter.Eventually.of_forall (fun k =>
    ⟨planarOfConfiguration a b hab (normalizedSequence a x k).val,
      planarOfConfiguration_encode a b hab (normalizedSequence a x k).val⟩)

def projection (x : Compactification a 0) : PlanarClusterCompactification.Space a b :=
  ⟨projectUpper (projectDR x.val), projectUpper_mem a b hab x⟩

theorem continuous_projection : Continuous (projection a b hab) :=
  (continuous_projectUpper.comp (continuous_projectDR.comp continuous_subtype_val)).subtype_mk _

theorem projection_embedding (x : PlanarClusterCompactification.Space a b) :
    projection a b hab (PlanarClusterInteriorEmbedding.embedding a b x) = x :=
  Subtype.ext (PlanarClusterInteriorEmbedding.projectUpper_embedding a b x)

def IsFiber (x : Compactification a 0) : Prop := ∀ j : Fin q, x.val.1 (Sum.inl j) = (Complex.I : OnePoint ℂ)

theorem isClosed_fiber : IsClosed {x : Compactification a 0 | IsFiber a x} := by
  simp only [IsFiber, setOf_forall]
  apply isClosed_iInter
  intro j
  exact isClosed_eq (((continuous_apply (Sum.inl j)).comp continuous_fst).comp continuous_subtype_val) continuous_const

abbrev Fiber := {x : Compactification a 0 // IsFiber a x}

def base (j : DoubledLabel q 0) : ℂ := if lower j then -Complex.I else Complex.I

theorem tendsto_upper (x : Compactification a 0) (hx : IsFiber a x) (j : Fin q) :
    Tendsto (fun k => ((normalizedSequence a x k).val.interior j : ℂ)) atTop (𝓝 Complex.I) := by
  have h := tendsto_normalizedSequence_position a x (Sum.inl j)
  rw [hx j] at h
  exact OnePoint.isOpenEmbedding_coe.isEmbedding.tendsto_nhds_iff.mpr h

theorem tendsto_doubled (x : Compactification a 0) (hx : IsFiber a x) (j : DoubledLabel q 0) :
    Tendsto (fun k => (normalizedSequence a x k).val.doubledPoint j) atTop (𝓝 (base j)) := by
  rcases j with (j | j) | j
  · exact tendsto_upper a x hx j
  · exact Fin.elim0 j
  · simpa only [Function.comp_def, Complex.conj_I, doubledPoint, base, lower_lower, ↓reduceIte] using
      Complex.continuous_conj.continuousAt.tendsto.comp (tendsto_upper a x hx j)

theorem direction_of_base_ne (x : Compactification a 0) (hx : IsFiber a x) (p : DoubledPair q 0)
    (hp : base p.val.2 - base p.val.1 ≠ 0) :
    x.val.2.1 p = complexPhase (base p.val.2 - base p.val.1) :=
  tendsto_nhds_unique (tendsto_normalizedSequence_direction a x p)
    ((continuousAt_complexPhase hp).tendsto.comp ((tendsto_doubled a x hx p.val.2).sub (tendsto_doubled a x hx p.val.1)))

theorem ratio_of_base_ne (x : Compactification a 0) (hx : IsFiber a x) (t : DoubledTriple q 0)
    (ht : ¬(base t.val.2.1 - base t.val.1 = 0 ∧ base t.val.2.2 - base t.val.1 = 0)) :
    x.val.2.2 t = normalizedNormRatio (base t.val.2.1 - base t.val.1) (base t.val.2.2 - base t.val.1) := by
  have h₁ := (tendsto_doubled a x hx t.val.2.1).sub (tendsto_doubled a x hx t.val.1)
  have h₂ := (tendsto_doubled a x hx t.val.2.2).sub (tendsto_doubled a x hx t.val.1)
  exact tendsto_nhds_unique (tendsto_normalizedSequence_ratio a x t)
    ((continuousAt_normalizedNormRatio _ _ ht).tendsto.comp (h₁.prodMk_nhds h₂))

def lowerPair (p : Pair (Fin q)) : DoubledPair q 0 :=
  ⟨(Sum.inr p.val.1, Sum.inr p.val.2), fun h => p.property (Sum.inr.inj h)⟩

def lowerTriple (t : Triple (Fin q)) : DoubledTriple q 0 :=
  ⟨(Sum.inr t.val.1, Sum.inr t.val.2.1, Sum.inr t.val.2.2),
    fun h => t.property.1 (Sum.inr.inj h), fun h => t.property.2 (Sum.inr.inj h)⟩

theorem direction_lower (x : Compactification a 0) (p : Pair (Fin q)) :
    x.val.2.1 (lowerPair p) = (x.val.2.1 (upperPair p))⁻¹ := by
  have h := (tendsto_normalizedSequence_direction a x (upperPair p)).inv
  have he (k : ℕ) : complexPhase ((normalizedSequence a x k).val.pairDifference (lowerPair p)) =
      (complexPhase ((normalizedSequence a x k).val.pairDifference (upperPair p)))⁻¹ := by
    simp only [Configuration.pairDifference, lowerPair, upperPair, doubledPoint,
      vertexPoint, Sum.elim_inl, ← map_sub, complexPhase_conj]
  apply tendsto_nhds_unique (tendsto_normalizedSequence_direction a x (lowerPair p))
  simpa only [← he] using h

theorem ratio_lower (x : Compactification a 0) (t : Triple (Fin q)) :
    x.val.2.2 (lowerTriple t) = x.val.2.2 (upperTriple t) := by
  have he (k : ℕ) : (normalizedSequence a x k).val.tripleDistanceRatio (lowerTriple t) =
      (normalizedSequence a x k).val.tripleDistanceRatio (upperTriple t) := by
    apply Subtype.ext
    simp only [Configuration.tripleDistanceRatio, Configuration.pairDifference, lowerTriple, upperTriple,
      doubledPoint, vertexPoint, Sum.elim_inl, ← map_sub, Complex.norm_conj]
  apply tendsto_nhds_unique (tendsto_normalizedSequence_ratio a x (lowerTriple t))
  simpa only [he] using tendsto_normalizedSequence_ratio a x (upperTriple t)

private theorem phase_doubleI : complexPhase (Complex.I + Complex.I) = complexPhase Complex.I := by
  have h : Complex.I + Complex.I = ((2 : ℝ) : ℂ) * Complex.I := by norm_num; ring
  rw [h, complexPhase_pos_real_mul (by norm_num : (0 : ℝ) < 2)]

private theorem phase_minusDoubleI : complexPhase (-Complex.I - Complex.I) = complexPhase (-Complex.I) := by
  have h : -Complex.I - Complex.I = ((2 : ℝ) : ℂ) * -Complex.I := by norm_num; ring
  rw [h, complexPhase_pos_real_mul (by norm_num : (0 : ℝ) < 2)]

private theorem norm_doubleI : ‖Complex.I + Complex.I‖ = 2 := by
  have h : Complex.I + Complex.I = ((2 : ℝ) : ℂ) * Complex.I := by norm_num; ring
  rw [h, norm_mul]
  norm_num

private theorem norm_minusDoubleI : ‖-Complex.I - Complex.I‖ = 2 := by
  rw [norm_sub_rev]
  simpa only [sub_neg_eq_add] using norm_doubleI

theorem lift_projection_direction (x : Compactification a 0) (hx : IsFiber a x) (p : DoubledPair q 0) :
    (liftDR (projectUpper (projectDR x.val))).1 p = x.val.2.1 p := by
  rcases p with ⟨⟨u, v⟩, hp⟩
  rcases u with (u | u) | u <;> rcases v with (v | v) | v
  all_goals try exact Fin.elim0 u
  all_goals try exact Fin.elim0 v
  · simp [liftDR, PlanarClusterDoubledData.direction, projectUpper, projectDR, withinPair, upperPair]
  · rw [direction_of_base_ne a x hx _ (by
      change base (Sum.inr v) - base (Sum.inl (Sum.inl u)) ≠ 0
      intro h
      have hi := congrArg Complex.im h
      norm_num [base] at hi)]
    simp [liftDR, PlanarClusterDoubledData.direction, base, phase_minusDoubleI]
  · rw [direction_of_base_ne a x hx _ (by
      change base (Sum.inl (Sum.inl v)) - base (Sum.inr u) ≠ 0
      intro h
      have hi := congrArg Complex.im h
      norm_num [base] at hi)]
    simp [liftDR, PlanarClusterDoubledData.direction, base, phase_doubleI]
  · have hne : u ≠ v := fun h => hp (congrArg Sum.inr h)
    simpa [liftDR, PlanarClusterDoubledData.direction, projectUpper, projectDR, withinPair, upperPair, lowerPair] using
      (direction_lower a x ⟨(u, v), hne⟩).symm

theorem lift_projection_ratio (x : Compactification a 0) (hx : IsFiber a x) (t : DoubledTriple q 0) :
    (liftDR (projectUpper (projectDR x.val))).2 t = x.val.2.2 t := by
  rcases t with ⟨⟨u, v, w⟩, huv, huw⟩
  rcases u with (u | u) | u <;> rcases v with (v | v) | v <;> rcases w with (w | w) | w
  all_goals try exact Fin.elim0 u
  all_goals try exact Fin.elim0 v
  all_goals try exact Fin.elim0 w
  all_goals try solve | simp [liftDR, PlanarClusterDoubledData.ratio, projectUpper, projectDR, withinTriple, upperTriple]
  all_goals try solve |
    have h₁ : u ≠ v := fun h => huv (congrArg Sum.inr h)
    have h₂ : u ≠ w := fun h => huw (congrArg Sum.inr h)
    simpa [liftDR, PlanarClusterDoubledData.ratio, projectUpper, projectDR, withinTriple, upperTriple, lowerTriple] using
      (ratio_lower a x ⟨(u, v, w), h₁, h₂⟩).symm
  all_goals rw [ratio_of_base_ne a x hx _ (by
    intro h
    norm_num [base, Complex.ext_iff] at h)]
  all_goals apply Subtype.ext
  all_goals norm_num [liftDR, PlanarClusterDoubledData.ratio, base, normalizedNormRatio,
    norm_doubleI, norm_minusDoubleI, zeroRatio, oneRatio, halfRatio]

/-- No coordinates remain free beyond the upper full DR array on this fiber. -/
theorem lift_projection_eq (x : Compactification a 0) (hx : IsFiber a x) :
    liftCoordinates (projectUpper (projectDR x.val)) = x.val := by
  apply Prod.ext
  · funext j
    rcases j with j | j
    · exact (hx j).symm
    · exact Fin.elim0 j
  · exact Prod.ext (funext (lift_projection_direction a x hx)) (funext (lift_projection_ratio a x hx))

theorem embedding_projection (x : Compactification a 0) (hx : IsFiber a x) :
    PlanarClusterInteriorEmbedding.embedding a b (projection a b hab x) = x :=
  Subtype.ext (lift_projection_eq a x hx)

theorem embedding_fiber (x : PlanarClusterCompactification.Space a b) :
    IsFiber a (PlanarClusterInteriorEmbedding.embedding a b x) := fun _ => rfl

include hab in
theorem range_embedding : range (PlanarClusterInteriorEmbedding.embedding a b) = {x | IsFiber a x} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact embedding_fiber a b z
  · intro hx
    exact ⟨projection a b hab x, embedding_projection a b hab x hx⟩

/-- The actual compact planar model is precisely the genuine closed collision fiber. -/
def homeomorph : PlanarClusterCompactification.Space a b ≃ₜ Fiber a where
  toEquiv :=
    { toFun := fun z => ⟨PlanarClusterInteriorEmbedding.embedding a b z, embedding_fiber a b z⟩
      invFun := fun x => projection a b hab x.val
      left_inv := projection_embedding a b hab
      right_inv := fun x => Subtype.ext (embedding_projection a b hab x.val x.property) }
  continuous_toFun := (PlanarClusterInteriorEmbedding.continuous_embedding a b).subtype_mk _
  continuous_invFun := (continuous_projection a b hab).comp continuous_subtype_val

end EnvelopingIsomorphism.Deformation.Kontsevich.PlanarClusterFiber
