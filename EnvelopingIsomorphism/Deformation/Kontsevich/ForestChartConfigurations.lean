import EnvelopingIsomorphism.Deformation.Kontsevich.ForestPositiveScaleAdmissibility
import EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedRadiusOrthant

/-! The forward forest chart on arbitrary reflected radius and increment vectors.
Actual open unit/sign conditions produce genuine configurations at positive
internal radii. Perturbing only internal radii proves that the whole corner
encoder lands in the genuine configuration compactification.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestChartConfigurations

open AncestorScaleRatios ForestInsertionDifference ForestDirectionRatioCoordinates
open Configuration ComplexConjugate Set Filter
open scoped Classical Topology

variable {T : RootedTree} [Fintype T] {n m : ℕ} (D : ForestPositiveScale.ShapeData T n m)

/-- Literal forest positions, with arbitrary radius and increment vectors. -/
def positions (x : ForestDirectionRatioCoordinates.Parameters T) (v : DoubledLabel n m) : ℂ := position T x.1 x.2 (D.leaf v)

/-- Open geometric conditions on actual resolved units, without configuration predicates. -/
def OpenConditions (x : ForestDirectionRatioCoordinates.Parameters T) : Prop :=
  RegularUnits T D.leaf x ∧
    (∀ i : Fin n, 0 < (unitDifference T x.1 x.2
      (D.leaf (Sum.inl (Sum.inl i))) (D.leaf (Sum.inr i))).im) ∧
    ∀ j k : Fin m, j < k → 0 < (unitDifference T x.1 x.2
      (D.leaf (Sum.inl (Sum.inr k))) (D.leaf (Sum.inl (Sum.inr j)))).re

theorem isOpen_openConditions : IsOpen {x : ForestDirectionRatioCoordinates.Parameters T | OpenConditions D x} := by
  simp only [OpenConditions, setOf_and, setOf_forall]
  refine (isOpen_regularUnits T D.leaf).inter ?_
  refine (isOpen_iInter_of_finite fun i => ?_).inter ?_
  · exact isOpen_lt continuous_const (Complex.continuous_im.comp (contDiff_unitDifference T _ _).continuous)
  · apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro k
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_lt continuous_const (Complex.continuous_re.comp (contDiff_unitDifference T _ _).continuous)

/-- The original shape data satisfies the same actual open conditions at its full face. -/
theorem openConditions_fullFace :
    OpenConditions D (ForestPositiveScale.radii T 0, D.increment) :=
  ⟨D.regularUnits_zero, D.upper_unit_zero_pos, D.boundary_unit_zero_pos⟩

/-- Only actual internal-node radii enter the scale at a distinct pair's LCA. -/
theorem scale_lca_pos (r : T → ℝ) (hr : ∀ u, ¬ IsMax u → 0 < r u)
    (v w : DoubledLabel n m) (hvw : v ≠ w) : 0 < scale r (D.leaf v ⊓ D.leaf w) := by
  apply Finset.prod_pos
  intro u hu
  exact hr u (not_isMax_of_lt (lt_of_le_of_lt ((mem_ancestors u _).mp hu)
    (inf_lt_left_of_leaf T (D.leaf_max v) (D.leaf_injective.ne hvw))))

theorem positions_reflect (x : ForestDirectionRatioCoordinates.Parameters T)
    (hr : ∀ u, x.1 (D.reflection u) = x.1 u)
    (ha : ∀ u, x.2 (D.reflection u) = conj (x.2 u)) (v : DoubledLabel n m) :
    positions D x (doubledReflection v) = conj (positions D x v) := by
  unfold positions
  rw [← D.leaf_reflect]
  exact ReflectedForestInsertion.position_reflect T D.reflection x.1 hr x.2 ha (D.leaf v)

theorem boundary_eq_ofReal (x : ForestDirectionRatioCoordinates.Parameters T)
    (hr : ∀ u, x.1 (D.reflection u) = x.1 u)
    (ha : ∀ u, x.2 (D.reflection u) = conj (x.2 u)) (j : Fin m) :
    positions D x (Sum.inl (Sum.inr j)) = ((positions D x (Sum.inl (Sum.inr j))).re : ℂ) := by
  have him := Complex.conj_eq_iff_im.mp (positions_reflect D x hr ha (Sum.inl (Sum.inr j))).symm
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using him

theorem position_difference_positive (x : ForestDirectionRatioCoordinates.Parameters T)
    (hr : ∀ u, ¬ IsMax u → 0 < x.1 u) (v w : DoubledLabel n m) (hvw : v ≠ w)
    (f : ℂ →L[ℝ] ℝ)
    (hu : 0 < f (unitDifference T x.1 x.2 (D.leaf v) (D.leaf w))) :
    0 < f (positions D x v - positions D x w) := by
  unfold positions
  rw [position_sub_position, map_smul]
  exact mul_pos (scale_lca_pos D x.1 hr v w hvw) hu

theorem interior_pos (x : ForestDirectionRatioCoordinates.Parameters T) (hx : OpenConditions D x)
    (hpos : ∀ u, ¬ IsMax u → 0 < x.1 u)
    (hr : ∀ u, x.1 (D.reflection u) = x.1 u)
    (ha : ∀ u, x.2 (D.reflection u) = conj (x.2 u)) (i : Fin n) :
    0 < (positions D x (Sum.inl (Sum.inl i))).im := by
  have h := position_difference_positive D x hpos (Sum.inl (Sum.inl i)) (Sum.inr i)
    (by simp) Complex.imCLM (hx.2.1 i)
  change 0 < (positions D x (Sum.inl (Sum.inl i)) - positions D x (Sum.inr i)).im at h
  have href : positions D x (Sum.inr i) = conj (positions D x (Sum.inl (Sum.inl i))) :=
    positions_reflect D x hr ha (Sum.inl (Sum.inl i))
  rw [href, Complex.sub_im, Complex.conj_im] at h
  linarith

theorem boundary_strictMono (x : ForestDirectionRatioCoordinates.Parameters T) (hx : OpenConditions D x)
    (hpos : ∀ u, ¬ IsMax u → 0 < x.1 u) :
    StrictMono (fun j : Fin m => (positions D x (Sum.inl (Sum.inr j))).re) := by
  intro j k hjk
  have h := position_difference_positive D x hpos (Sum.inl (Sum.inr k)) (Sum.inl (Sum.inr j))
    (by simpa using ne_of_gt hjk) Complex.reCLM (hx.2.2 j k hjk)
  exact sub_pos.mp h

theorem positions_injective (x : ForestDirectionRatioCoordinates.Parameters T) (hx : OpenConditions D x)
    (hpos : ∀ u, ¬ IsMax u → 0 < x.1 u) : Function.Injective (positions D x) := by
  intro v w h
  by_contra hne
  have hu := hx.1 ⟨(w, v), Ne.symm hne⟩
  have hd : positions D x v - positions D x w ≠ 0 := by
    unfold positions
    rw [position_sub_position]
    exact smul_ne_zero (scale_lca_pos D x.1 hpos v w hne).ne' hu
  exact hd (sub_eq_zero.mpr h)

/-- A genuine configuration from arbitrary admissible radius/increment vectors.
The upper-half-plane, boundary order and injectivity fields are all derived. -/
def configuration (x : ForestDirectionRatioCoordinates.Parameters T) (hx : OpenConditions D x)
    (hpos : ∀ u, ¬ IsMax u → 0 < x.1 u)
    (hr : ∀ u, x.1 (D.reflection u) = x.1 u)
    (ha : ∀ u, x.2 (D.reflection u) = conj (x.2 u)) : Configuration n m where
  interior i := ⟨positions D x (Sum.inl (Sum.inl i)), interior_pos D x hx hpos hr ha i⟩
  boundary j := (positions D x (Sum.inl (Sum.inr j))).re
  interior_injective := by
    intro i j hij
    have h := positions_injective D x hx hpos (congrArg (fun z : UpperHalfPlane => (z : ℂ)) hij)
    simpa only [Sum.inl.injEq] using h
  boundary_strictMono := boundary_strictMono D x hx hpos

theorem configuration_doubledPoint (x : ForestDirectionRatioCoordinates.Parameters T) (hx : OpenConditions D x)
    (hpos : ∀ u, ¬ IsMax u → 0 < x.1 u)
    (hr : ∀ u, x.1 (D.reflection u) = x.1 u)
    (ha : ∀ u, x.2 (D.reflection u) = conj (x.2 u)) (v : DoubledLabel n m) :
    (configuration D x hx hpos hr ha).doubledPoint v = positions D x v := by
  rcases v with (i | j) | i
  · rfl
  · exact (boundary_eq_ofReal D x hr ha j).symm
  · exact (positions_reflect D x hr ha (Sum.inl (Sum.inl i))).symm

/-- Reflected radii with root and leaves fixed to one, and arbitrary reflected
increments satisfying the actual open unit/sign conditions. -/
def CornerConditions (x : ForestDirectionRatioCoordinates.Parameters T) : Prop :=
  ReflectedRadiusOrthant.Admissible T D.reflection x.1 ∧
    (∀ u, x.2 (D.reflection u) = conj (x.2 u)) ∧ OpenConditions D x

abbrev CornerDomain := {x : ForestDirectionRatioCoordinates.Parameters T // CornerConditions D x}

def resolvedParameters (x : CornerDomain D) : Domain T D.leaf :=
  ⟨x.val, x.property.1.2.2.2, x.property.2.2.1⟩

@[fun_prop] theorem continuous_resolvedParameters : Continuous (resolvedParameters D) :=
  continuous_subtype_val.subtype_mk _

/-- Every stored doubled pair direction and triple ratio, at all corners. -/
def fullDR (x : CornerDomain D) : DRData n m :=
  doubledCoordinates T D.leaf (resolvedParameters D x)

@[fun_prop] theorem continuous_fullDR : Continuous (fullDR D) :=
  (continuous_doubledCoordinates T D.leaf).comp (continuous_resolvedParameters D)

theorem fullDR_eq_configuration (x : CornerDomain D)
    (hpos : ∀ u, ¬ IsMax u → 0 < x.val.1 u) :
    fullDR D x = directionRatioCoordinates (configuration D x.val x.property.2.2 hpos
      x.property.1.2.2.1 x.property.2.1) := by
  have hp (u : T) : 0 < x.val.1 u := by
    by_cases hu : IsMax u
    · rw [x.property.1.2.1 u hu]
      exact zero_lt_one
    · exact hpos u hu
  apply doubledCoordinates_eq_configuration T D.leaf (resolvedParameters D x) hp _ 0
  intro v
  simpa only [zero_add, resolvedParameters, positions] using
    configuration_doubledPoint D x.val x.property.2.2 hpos x.property.1.2.2.1 x.property.2.1 v

/-- The actual open conditions persist when only the internal radii are perturbed. -/
theorem exists_perturbation_bound (x : CornerDomain D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      OpenConditions D (ReflectedRadiusOrthant.perturb T x.val.1 ε, x.val.2) := by
  have hc : Continuous (fun ε : ℝ => (ReflectedRadiusOrthant.perturb T x.val.1 ε, x.val.2)) :=
    (ReflectedRadiusOrthant.contDiff_perturb T x.val.1).continuous.prodMk continuous_const
  have he : ∀ᶠ ε : ℝ in 𝓝 0,
      OpenConditions D (ReflectedRadiusOrthant.perturb T x.val.1 ε, x.val.2) :=
    ((isOpen_openConditions D).preimage hc).mem_nhds (by simpa using x.property.2.2)
  obtain ⟨δ, hδ, hs⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (he.filter_mono nhdsWithin_le_nhds)
  exact ⟨δ, hδ, fun ε hε hεδ => hs ⟨hε, hεδ⟩⟩

def perturbationBound (x : CornerDomain D) : ℝ := (exists_perturbation_bound D x).choose

theorem perturbationBound_pos (x : CornerDomain D) : 0 < perturbationBound D x :=
  (exists_perturbation_bound D x).choose_spec.1

theorem perturbationBound_spec (x : CornerDomain D) (ε : ℝ) (hε : 0 < ε)
    (hεδ : ε < perturbationBound D x) :
    OpenConditions D (ReflectedRadiusOrthant.perturb T x.val.1 ε, x.val.2) :=
  (exists_perturbation_bound D x).choose_spec.2 ε hε hεδ

/-- A concrete sequence of internal-radius perturbations, with all other data fixed. -/
def approximationRadius (x : CornerDomain D) (k : ℕ) : ℝ :=
  (perturbationBound D x / 2) / ((k : ℝ) + 1)

theorem approximationRadius_pos (x : CornerDomain D) (k : ℕ) : 0 < approximationRadius D x k := by
  have hδ := perturbationBound_pos D x
  unfold approximationRadius
  positivity

theorem approximationRadius_lt (x : CornerDomain D) (k : ℕ) :
    approximationRadius D x k < perturbationBound D x := by
  have hδ := perturbationBound_pos D x
  exact (div_le_self (by positivity : 0 ≤ perturbationBound D x / 2)
    (by have h : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith : 1 ≤ (k : ℝ) + 1)).trans_lt (half_lt_self hδ)

theorem tendsto_approximationRadius (x : CornerDomain D) :
    Tendsto (approximationRadius D x) atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ => (perturbationBound D x / 2) / ((k : ℝ) + 1)) atTop (𝓝 0)
  simpa only [div_eq_mul_inv, one_mul, mul_zero] using
    (tendsto_const_nhds (x := perturbationBound D x / 2)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

def positiveApproximation (x : CornerDomain D) (k : ℕ) : CornerDomain D :=
  ⟨(ReflectedRadiusOrthant.perturb T x.val.1 (approximationRadius D x k), x.val.2),
    (ReflectedRadiusOrthant.perturb_positive T D.reflection x.val.1 x.property.1
      (approximationRadius_pos D x k)).1, x.property.2.1,
    perturbationBound_spec D x _ (approximationRadius_pos D x k) (approximationRadius_lt D x k)⟩

theorem positiveApproximation_pos (x : CornerDomain D) (k : ℕ) (u : T) :
    0 < (positiveApproximation D x k).val.1 u :=
  (ReflectedRadiusOrthant.perturb_positive T D.reflection x.val.1 x.property.1
    (approximationRadius_pos D x k)).2 u

theorem positiveApproximation_root (x : CornerDomain D) (k : ℕ) :
    (positiveApproximation D x k).val.1 ⊥ = 1 := (positiveApproximation D x k).property.1.1

theorem positiveApproximation_leaf (x : CornerDomain D) (k : ℕ) (u : T) (hu : IsMax u) :
    (positiveApproximation D x k).val.1 u = 1 := (positiveApproximation D x k).property.1.2.1 u hu

theorem positiveApproximation_increments (x : CornerDomain D) (k : ℕ) :
    (positiveApproximation D x k).val.2 = x.val.2 := rfl

theorem tendsto_positiveApproximation (x : CornerDomain D) :
    Tendsto (positiveApproximation D x) atTop (𝓝 x) := by
  apply tendsto_subtype_rng.mpr
  have hc := (ReflectedRadiusOrthant.contDiff_perturb T x.val.1).continuous.prodMk
    (continuous_const (y := x.val.2))
  convert! (hc.tendsto (0 : ℝ)).comp (tendsto_approximationRadius D x) using 1
  simp only [ReflectedRadiusOrthant.perturb_zero, Prod.mk.eta]

def approximatingConfiguration (x : CornerDomain D) (k : ℕ) : Configuration n m :=
  configuration D (positiveApproximation D x k).val (positiveApproximation D x k).property.2.2
    (fun u _ => positiveApproximation_pos D x k u)
    (positiveApproximation D x k).property.1.2.2.1 (positiveApproximation D x k).property.2.1

theorem fullDR_positiveApproximation (x : CornerDomain D) (k : ℕ) :
    fullDR D (positiveApproximation D x k) = directionRatioCoordinates (approximatingConfiguration D x k) :=
  fullDR_eq_configuration D (positiveApproximation D x k) (fun u _ => positiveApproximation_pos D x k u)

/-- Actual positive configurations converge in every retained direction/ratio coordinate. -/
theorem tendsto_approximatingConfiguration_DR (x : CornerDomain D) :
    Tendsto (fun k => directionRatioCoordinates (approximatingConfiguration D x k)) atTop
      (𝓝 (fullDR D x)) := by
  convert! (continuous_fullDR D).continuousAt.tendsto.comp (tendsto_positiveApproximation D x) using 1
  funext k
  exact (fullDR_positiveApproximation D x k).symm

/-- Whole-corner landing in the genuine closure, proved from actual configurations. -/
theorem fullDR_mem_directionRatioSet (x : CornerDomain D) : fullDR D x ∈ directionRatioSet n m := by
  change fullDR D x ∈ closure (range (directionRatioCoordinates : Configuration n m → DRData n m))
  apply mem_closure_of_tendsto (tendsto_approximatingConfiguration_DR D x)
  exact Filter.Eventually.of_forall (fun k => ⟨approximatingConfiguration D x k, rfl⟩)

def fullDRSpace (x : CornerDomain D) : DRSpace n m := ⟨fullDR D x, fullDR_mem_directionRatioSet D x⟩

@[fun_prop] theorem continuous_fullDRSpace : Continuous (fullDRSpace D) :=
  (continuous_fullDR D).subtype_mk _

/-- A continuous actual compactification insertion on the entire reflected corner domain. -/
def compactificationInsertion (i : Fin n) (x : CornerDomain D) : Compactification i m :=
  (toDRHomeomorph i).symm (fullDRSpace D x)

@[fun_prop] theorem continuous_compactificationInsertion (i : Fin n) :
    Continuous (compactificationInsertion D i) :=
  (toDRHomeomorph i).symm.continuous.comp (continuous_fullDRSpace D)

theorem compactificationInsertion_projectDR (i : Fin n) (x : CornerDomain D) :
    projectDR (compactificationInsertion D i x).val = fullDR D x :=
  congrArg Subtype.val ((toDRHomeomorph i).apply_symm_apply (fullDRSpace D x))

/-- On positive internal radii this is exactly the existing embedding of the
constructed configuration normalized at the chosen anchor. -/
theorem compactificationInsertion_eq_embedding (i : Fin n) (x : CornerDomain D)
    (hpos : ∀ u, ¬ IsMax u → 0 < x.val.1 u) :
    compactificationInsertion D i x = compactificationEmbedding i (Configuration.normalized i
      (configuration D x.val x.property.2.2 hpos x.property.1.2.2.1 x.property.2.1)) := by
  apply (toDRHomeomorph i).injective
  apply Subtype.ext
  change projectDR (compactificationInsertion D i x).val =
    normalizedDirectionRatios (Configuration.normalized i
      (configuration D x.val x.property.2.2 hpos x.property.1.2.2.1 x.property.2.1))
  rw [compactificationInsertion_projectDR, fullDR_eq_configuration D x hpos,
    normalizedDirectionRatios_normalized]

/-- The genuinely normalized positive configurations converge to the constructed
point of the actual compactification at every reflected corner. -/
theorem tendsto_normalized_approximatingConfiguration (i : Fin n) (x : CornerDomain D) :
    Tendsto (fun k => compactificationEmbedding i
      (Configuration.normalized i (approximatingConfiguration D x k))) atTop
      (𝓝 (compactificationInsertion D i x)) := by
  apply (toDRHomeomorph i).isEmbedding.tendsto_nhds_iff.mpr
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun k => normalizedDirectionRatios
    (Configuration.normalized i (approximatingConfiguration D x k))) atTop
      (𝓝 (projectDR (compactificationInsertion D i x).val))
  rw [compactificationInsertion_projectDR]
  simpa only [normalizedDirectionRatios_normalized] using tendsto_approximatingConfiguration_DR D x

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestChartConfigurations
