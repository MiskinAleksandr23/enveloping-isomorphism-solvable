import EnvelopingIsomorphism.Deformation.Kontsevich.ForestInsertionDifference
import EnvelopingIsomorphism.Deformation.Kontsevich.ConfigurationTopology
import EnvelopingIsomorphism.Deformation.Kontsevich.DoubledReflection
import EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedForestInsertion
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestDirectionRatioCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.AnchorCompactification
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Actual positive-scale configurations from finite forest shapes

The root scale is one and all nonroot radii are the same positive parameter.
The literal insertion differences factor by positive ancestor scales. Their
leading units are the first-diverging child-shape differences, so strict signs
and distinctness follow on one common positive-radius interval.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestPositiveScale

open AncestorScaleRatios ForestInsertionDifference Configuration ComplexConjugate Filter Set Topology
open scoped Topology Classical

variable (T : RootedTree)

/-- The coarse root remains at scale one; only genuine nonroot radii shrink. -/
def radii (r : ℝ) (u : T) : ℝ := if u = ⊥ then 1 else r

@[simp] theorem radii_root (r : ℝ) : radii T r ⊥ = 1 := by simp [radii]

@[simp] theorem radii_nonroot (r : ℝ) {u : T} (hu : u ≠ ⊥) : radii T r u = r := by
  simp [radii, hu]

theorem radii_pos {r : ℝ} (hr : 0 < r) (u : T) : 0 < radii T r u := by
  unfold radii
  split_ifs <;> positivity

theorem radii_nonneg {r : ℝ} (hr : 0 ≤ r) (u : T) : 0 ≤ radii T r u := by
  unfold radii
  split_ifs <;> positivity

@[fun_prop] theorem continuous_radii : Continuous (radii T) := by
  apply continuous_pi
  intro u
  unfold radii
  split_ifs <;> fun_prop

variable [Fintype T]

def positionAtRadius (A : T → ℂ) (v : T) (r : ℝ) : ℂ := position T (radii T r) A v

def unitAtRadius (A : T → ℂ) (v w : T) (r : ℝ) : ℂ := unitDifference T (radii T r) A v w

@[fun_prop] theorem continuous_positionAtRadius (A : T → ℂ) (v : T) :
    Continuous (positionAtRadius T A v) := by
  unfold positionAtRadius position
  apply continuous_finsetSum
  intro u hu
  exact ((contDiff_scale (Order.pred u)).continuous.comp (continuous_radii T)).smul continuous_const

@[fun_prop] theorem continuous_unitAtRadius (A : T → ℂ) (v w : T) :
    Continuous (unitAtRadius T A v w) := by
  have hb (c z : T) : Continuous (fun r => branchUnit T (radii T r) A c z) := by
    unfold branchUnit
    apply continuous_finsetSum
    intro u hu
    exact ((contDiff_residualScale c (Order.pred u)).continuous.comp (continuous_radii T)).smul continuous_const
  exact (hb (v ⊓ w) v).sub (hb (v ⊓ w) w)

theorem unitAtRadius_zero_eq_shapes (A : T → ℂ) {v w d e : T}
    (hd : (v ⊓ w) ⋖ d) (hdv : d ≤ v) (he : (v ⊓ w) ⋖ e) (hew : e ≤ w) :
    unitAtRadius T A v w 0 = A d - A e := by
  apply unitDifference_eq_shapes_at_face T _ A hd hdv he hew
  intro u hu
  exact radii_nonroot T 0 (ne_of_gt (lt_of_le_of_lt bot_le hu))

theorem leaf_unitAtRadius_zero_ne (A : T → ℂ) {v w : T}
    (hv : IsMax v) (hw : IsMax w) (hne : v ≠ w)
    (hshape : ∀ c d e : T, c ⋖ d → c ⋖ e → d ≠ e → A d ≠ A e) :
    unitAtRadius T A v w 0 ≠ 0 := by
  apply leaf_unitDifference_ne_zero_at_face T _ A hv hw hne
  · intro u hu
    exact radii_nonroot T 0 (ne_of_gt (lt_of_le_of_lt bot_le hu))
  · exact hshape (v ⊓ w)

theorem leaf_unitAtRadius_zero_positive (A : T → ℂ) {v w : T}
    (hv : IsMax v) (hw : IsMax w) (hne : v ≠ w) (f : ℂ →L[ℝ] ℝ)
    (hgap : ∀ d e : T, (v ⊓ w) ⋖ d → d ≤ v → (v ⊓ w) ⋖ e → e ≤ w →
      0 < f (A d - A e)) : 0 < f (unitAtRadius T A v w 0) := by
  obtain ⟨d, hd, hdv⟩ := exists_child_between T (inf_lt_left_of_leaf T hv hne)
  have hiw : v ⊓ w < w := by simpa only [inf_comm] using inf_lt_left_of_leaf T hw hne.symm
  obtain ⟨e, he, hew⟩ := exists_child_between T hiw
  rw [unitAtRadius_zero_eq_shapes T A hd hdv he hew]
  exact hgap d e hd hdv he hew

/-- Every strict leading-unit sign persists near the full descendant-zero face. -/
theorem eventually_unit_positive (A : T → ℂ) (v w : T) (f : ℂ →L[ℝ] ℝ)
    (hface : 0 < f (unitAtRadius T A v w 0)) :
    ∀ᶠ r : ℝ in 𝓝 0, 0 < f (unitAtRadius T A v w r) :=
  (isOpen_lt continuous_const (f.continuous.comp (continuous_unitAtRadius T A v w))).mem_nhds hface

theorem eventually_unit_positive_of_children (A : T → ℂ) {v w d e : T}
    (hd : (v ⊓ w) ⋖ d) (hdv : d ≤ v) (he : (v ⊓ w) ⋖ e) (hew : e ≤ w)
    (f : ℂ →L[ℝ] ℝ) (hgap : 0 < f (A d - A e)) :
    ∀ᶠ r : ℝ in 𝓝 0, 0 < f (unitAtRadius T A v w r) := by
  apply eventually_unit_positive T A v w f
  rwa [unitAtRadius_zero_eq_shapes T A hd hdv he hew]

theorem position_difference_positive (A : T → ℂ) (v w : T) (f : ℂ →L[ℝ] ℝ)
    {r : ℝ} (hr : 0 < r) (hu : 0 < f (unitAtRadius T A v w r)) :
    0 < f (positionAtRadius T A v r - positionAtRadius T A w r) := by
  change 0 < f (position T (radii T r) A v - position T (radii T r) A w)
  rw [position_sub_position, map_smul]
  exact mul_pos (scale_pos _ (radii_pos T hr) _) hu

theorem eventually_position_difference_positive (A : T → ℂ) (v w : T) (f : ℂ →L[ℝ] ℝ)
    (hface : 0 < f (unitAtRadius T A v w 0)) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < f (positionAtRadius T A v r - positionAtRadius T A w r) := by
  filter_upwards [(eventually_unit_positive T A v w f hface).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with r hu hr
  exact position_difference_positive T A v w f hr hu

/-- Finitely many strictly positive leading gaps yield one common positive
interval for the actual insertion inequalities. -/
theorem exists_radius_all_positive {J : Type*} [Finite J] (A : T → ℂ)
    (v w : J → T) (f : J → ℂ →L[ℝ] ℝ)
    (hface : ∀ j, 0 < f j (unitAtRadius T A (v j) (w j) 0)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      ∀ j, 0 < f j (positionAtRadius T A (v j) r - positionAtRadius T A (w j) r) := by
  have hevent : ∀ᶠ r : ℝ in 𝓝[>] 0,
      ∀ j, 0 < f j (positionAtRadius T A (v j) r - positionAtRadius T A (w j) r) :=
    eventually_all.mpr (fun j => eventually_position_difference_positive T A (v j) (w j) (f j) (hface j))
  obtain ⟨ε, hε, hmem⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  exact ⟨ε, hε, fun r hr hrε => hmem ⟨hr, hrε⟩⟩

/-- Distinct immediate-child centers force simultaneous nonzero pair units for
any finite family of distinct native leaves. -/
theorem eventually_leaf_units_ne_zero {I : Type*} [Finite I] (A : T → ℂ) (leaf : I → T)
    (hleaf : ∀ i, IsMax (leaf i)) (hinj : Function.Injective leaf)
    (hshape : ∀ c d e : T, c ⋖ d → c ⋖ e → d ≠ e → A d ≠ A e) :
    ∀ᶠ r : ℝ in 𝓝 0, ∀ i j, i ≠ j → unitAtRadius T A (leaf i) (leaf j) r ≠ 0 := by
  apply eventually_all.mpr
  intro i
  apply eventually_all.mpr
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall (by simp [hij])
  · have hzero := leaf_unitAtRadius_zero_ne T A (hleaf i) (hleaf j) (fun h => hij (hinj h)) hshape
    have h : ∀ᶠ r : ℝ in 𝓝 0, unitAtRadius T A (leaf i) (leaf j) r ≠ 0 :=
      ((isClosed_eq (continuous_unitAtRadius T A (leaf i) (leaf j)) continuous_const).isOpen_compl).mem_nhds hzero
    exact h.mono (fun r hr _ => hr)

theorem positionAtRadius_ne_of_unit_ne (A : T → ℂ) (v w : T) {r : ℝ} (hr : 0 < r)
    (hu : unitAtRadius T A v w r ≠ 0) : positionAtRadius T A v r ≠ positionAtRadius T A w r := by
  apply sub_ne_zero.mp
  change position T (radii T r) A v - position T (radii T r) A w ≠ 0
  rw [position_sub_position]
  exact smul_ne_zero (scale_pos _ (radii_pos T hr) _).ne' hu

/-- The literal inserted positions of all leaves are injective for every
sufficiently small positive radius, derived from the local shape separation. -/
theorem exists_radius_injective {I : Type*} [Finite I] (A : T → ℂ) (leaf : I → T)
    (hleaf : ∀ i, IsMax (leaf i)) (hinj : Function.Injective leaf)
    (hshape : ∀ c d e : T, c ⋖ d → c ⋖ e → d ≠ e → A d ≠ A e) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      Function.Injective (fun i => positionAtRadius T A (leaf i) r) := by
  have hevent : ∀ᶠ r : ℝ in 𝓝[>] 0,
      Function.Injective (fun i => positionAtRadius T A (leaf i) r) := by
    filter_upwards [(eventually_leaf_units_ne_zero T A leaf hleaf hinj hshape).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with r hu hr
    intro i j hij
    by_contra hne
    exact positionAtRadius_ne_of_unit_ne T A (leaf i) (leaf j) hr (hu i j hne) hij
  obtain ⟨ε, hε, hmem⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  exact ⟨ε, hε, fun r hr hrε => hmem ⟨hr, hrε⟩⟩

/-- Finite geometric inputs: genuine native leaves, conjugate-reflected child
increments, distinct sibling centers, and strict local first-branch signs.
No predicate asserting that the inserted positions form a configuration occurs. -/
structure ShapeData (T : RootedTree) (n m : ℕ) where
  leaf : DoubledLabel n m → T
  leaf_injective : Function.Injective leaf
  leaf_max : ∀ v, IsMax (leaf v)
  reflection : T ≃o T
  reflection_involutive : Function.Involutive reflection
  leaf_reflect : ∀ v, reflection (leaf v) = leaf (doubledReflection v)
  increment : T → ℂ
  increment_reflect : ∀ u, increment (reflection u) = conj (increment u)
  siblings_distinct : ∀ c d e : T, c ⋖ d → c ⋖ e → d ≠ e → increment d ≠ increment e
  upper_gap : ∀ (i : Fin n) (d e : T),
    (leaf (Sum.inl (Sum.inl i)) ⊓ leaf (Sum.inr i)) ⋖ d → d ≤ leaf (Sum.inl (Sum.inl i)) →
    (leaf (Sum.inl (Sum.inl i)) ⊓ leaf (Sum.inr i)) ⋖ e → e ≤ leaf (Sum.inr i) →
    0 < (increment d - increment e).im
  boundary_gap : ∀ (j k : Fin m), j < k → ∀ d e : T,
    (leaf (Sum.inl (Sum.inr k)) ⊓ leaf (Sum.inl (Sum.inr j))) ⋖ d → d ≤ leaf (Sum.inl (Sum.inr k)) →
    (leaf (Sum.inl (Sum.inr k)) ⊓ leaf (Sum.inl (Sum.inr j))) ⋖ e → e ≤ leaf (Sum.inl (Sum.inr j)) →
    0 < (increment d - increment e).re

namespace ShapeData

variable {T} {n m : ℕ} (D : ShapeData T n m)

def positions (r : ℝ) (v : DoubledLabel n m) : ℂ :=
  positionAtRadius T D.increment (D.leaf v) r

@[fun_prop] theorem continuous_positions (v : DoubledLabel n m) :
    Continuous (fun r => D.positions r v) := continuous_positionAtRadius T D.increment (D.leaf v)

theorem positions_reflect (r : ℝ) (v : DoubledLabel n m) :
    D.positions r (doubledReflection v) = conj (D.positions r v) := by
  unfold positions positionAtRadius
  rw [← D.leaf_reflect]
  apply ReflectedForestInsertion.position_reflect T D.reflection _ _ D.increment D.increment_reflect
  intro u
  by_cases hu : u = ⊥
  · subst u
    simp [radii]
  · have hσu : D.reflection u ≠ ⊥ := by
      intro h
      exact hu (D.reflection.injective (h.trans D.reflection.map_bot.symm))
    simp [radii, hu, hσu]

theorem boundary_im_eq_zero (r : ℝ) (j : Fin m) :
    (D.positions r (Sum.inl (Sum.inr j))).im = 0 := by
  have h := D.positions_reflect r (Sum.inl (Sum.inr j))
  exact Complex.conj_eq_iff_im.mp h.symm

theorem boundary_eq_ofReal (r : ℝ) (j : Fin m) :
    D.positions r (Sum.inl (Sum.inr j)) = ((D.positions r (Sum.inl (Sum.inr j))).re : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using D.boundary_im_eq_zero r j

theorem upper_unit_zero_pos (i : Fin n) :
    0 < (unitAtRadius T D.increment (D.leaf (Sum.inl (Sum.inl i))) (D.leaf (Sum.inr i)) 0).im := by
  have hne : D.leaf (Sum.inl (Sum.inl i)) ≠ D.leaf (Sum.inr i) := by
    intro h
    have hl := D.leaf_injective h
    cases hl
  exact leaf_unitAtRadius_zero_positive T D.increment
    (D.leaf_max _) (D.leaf_max _) hne Complex.imCLM (D.upper_gap i)

theorem boundary_unit_zero_pos (j k : Fin m) (hjk : j < k) :
    0 < (unitAtRadius T D.increment (D.leaf (Sum.inl (Sum.inr k)))
      (D.leaf (Sum.inl (Sum.inr j))) 0).re := by
  have hne : D.leaf (Sum.inl (Sum.inr k)) ≠ D.leaf (Sum.inl (Sum.inr j)) := by
    intro h
    have hkj : k = j := by
      simpa only [Sum.inl.injEq, Sum.inr.injEq] using D.leaf_injective h
    exact (ne_of_gt hjk) hkj
  exact leaf_unitAtRadius_zero_positive T D.increment
    (D.leaf_max _) (D.leaf_max _) hne Complex.reCLM (D.boundary_gap j k hjk)

theorem eventually_interior_pos :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ i : Fin n, 0 < (D.positions r (Sum.inl (Sum.inl i))).im := by
  apply eventually_all.mpr
  intro i
  have h := eventually_position_difference_positive T D.increment
    (D.leaf (Sum.inl (Sum.inl i))) (D.leaf (Sum.inr i)) Complex.imCLM (D.upper_unit_zero_pos i)
  filter_upwards [h] with r hr
  change 0 < (D.positions r (Sum.inl (Sum.inl i)) - D.positions r (Sum.inr i)).im at hr
  have href : D.positions r (Sum.inr i) = conj (D.positions r (Sum.inl (Sum.inl i))) :=
    D.positions_reflect r (Sum.inl (Sum.inl i))
  rw [href, Complex.sub_im, Complex.conj_im] at hr
  linarith

theorem eventually_boundary_strictMono :
    ∀ᶠ r : ℝ in 𝓝[>] 0, StrictMono (fun j : Fin m => (D.positions r (Sum.inl (Sum.inr j))).re) := by
  change ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ j k : Fin m, j < k →
    (D.positions r (Sum.inl (Sum.inr j))).re < (D.positions r (Sum.inl (Sum.inr k))).re
  apply eventually_all.mpr
  intro j
  apply eventually_all.mpr
  intro k
  by_cases hjk : j < k
  · have h := eventually_position_difference_positive T D.increment
      (D.leaf (Sum.inl (Sum.inr k))) (D.leaf (Sum.inl (Sum.inr j))) Complex.reCLM
      (D.boundary_unit_zero_pos j k hjk)
    filter_upwards [h] with r hr _
    exact sub_pos.mp hr
  · exact Filter.Eventually.of_forall (fun r h => (hjk h).elim)

theorem eventually_positions_injective :
    ∀ᶠ r : ℝ in 𝓝[>] 0, Function.Injective (D.positions r) := by
  obtain ⟨ε, hε, hs⟩ := exists_radius_injective T D.increment D.leaf
    D.leaf_max D.leaf_injective D.siblings_distinct
  filter_upwards [Ioo_mem_nhdsGT hε] with r hr
  exact hs r hr.1 hr.2

/-- Proved geometric properties of the actual positive-radius insertion. -/
structure AdmissibleRadius (r : ℝ) : Prop where
  interior_pos : ∀ i : Fin n, 0 < (D.positions r (Sum.inl (Sum.inl i))).im
  boundary_strictMono : StrictMono (fun j : Fin m => (D.positions r (Sum.inl (Sum.inr j))).re)
  positions_injective : Function.Injective (D.positions r)

/-- One interval works simultaneously for all actual interior signs, boundary
orders, and distinctness constraints. Every premise concerns only child shapes. -/
theorem exists_admissible_radius :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε → D.AdmissibleRadius r := by
  have hevent : ∀ᶠ r : ℝ in 𝓝[>] 0, D.AdmissibleRadius r := by
    filter_upwards [D.eventually_interior_pos, D.eventually_boundary_strictMono,
      D.eventually_positions_injective] with r hi hb hinj
    exact ⟨hi, hb, hinj⟩
  obtain ⟨ε, hε, hmem⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  exact ⟨ε, hε, fun r hr hrε => hmem ⟨hr, hrε⟩⟩

def radiusBound : ℝ := D.exists_admissible_radius.choose

theorem radiusBound_pos : 0 < D.radiusBound := D.exists_admissible_radius.choose_spec.1

theorem radiusBound_spec {r : ℝ} (hr : 0 < r) (hbound : r < D.radiusBound) : D.AdmissibleRadius r :=
  D.exists_admissible_radius.choose_spec.2 r hr hbound

/-- Actual native configuration produced from the finite local shape data and
a sufficiently small positive radius; no configuration premise is accepted. -/
def configuration (r : ℝ) (hr : 0 < r) (hbound : r < D.radiusBound) : Configuration n m where
  interior i := ⟨D.positions r (Sum.inl (Sum.inl i)), (D.radiusBound_spec hr hbound).interior_pos i⟩
  boundary j := (D.positions r (Sum.inl (Sum.inr j))).re
  interior_injective := by
    intro i j hij
    have h := (D.radiusBound_spec hr hbound).positions_injective
      (congrArg (fun z : UpperHalfPlane => (z : ℂ)) hij)
    simpa only [Sum.inl.injEq] using h
  boundary_strictMono := (D.radiusBound_spec hr hbound).boundary_strictMono

theorem configuration_doubledPoint (r : ℝ) (hr : 0 < r) (hbound : r < D.radiusBound)
    (v : DoubledLabel n m) : (D.configuration r hr hbound).doubledPoint v = D.positions r v := by
  rcases v with (i | j) | i
  · rfl
  · exact (D.boundary_eq_ofReal r j).symm
  · exact (D.positions_reflect r (Sum.inl (Sum.inl i))).symm

def normalized (i : Fin n) (r : ℝ) (hr : 0 < r) (hbound : r < D.radiusBound) :
    Configuration.Normalized i m := Configuration.normalized i (D.configuration r hr hbound)

theorem regularUnits_zero :
    ForestDirectionRatioCoordinates.RegularUnits T D.leaf (radii T 0, D.increment) :=
  ForestDirectionRatioCoordinates.regularUnits_at_full_face T D.leaf _ D.leaf_injective D.leaf_max
    (fun _ hu => radii_nonroot T 0 hu) D.siblings_distinct

theorem regularUnits_pos {r : ℝ} (hr : 0 < r) (hbound : r < D.radiusBound) :
    ForestDirectionRatioCoordinates.RegularUnits T D.leaf (radii T r, D.increment) := by
  intro p hp
  change unitDifference T (radii T r) D.increment (D.leaf p.val.2) (D.leaf p.val.1) = 0 at hp
  have heq : D.positions r p.val.2 = D.positions r p.val.1 := by
    apply sub_eq_zero.mp
    change position T (radii T r) D.increment (D.leaf p.val.2) -
      position T (radii T r) D.increment (D.leaf p.val.1) = 0
    rw [position_sub_position, hp, smul_zero]
  exact p.property ((D.radiusBound_spec hr hbound).positions_injective heq).symm

theorem regularUnits_nonneg {r : ℝ} (hr : 0 ≤ r) (hbound : r < D.radiusBound) :
    ForestDirectionRatioCoordinates.RegularUnits T D.leaf (radii T r, D.increment) := by
  by_cases hr0 : r = 0
  · subst r
    exact D.regularUnits_zero
  · exact D.regularUnits_pos (lt_of_le_of_ne hr (Ne.symm hr0)) hbound

abbrev RadiusDomain := Set.Ico (0 : ℝ) D.radiusBound

def zeroRadius : D.RadiusDomain := ⟨0, le_rfl, D.radiusBound_pos⟩

/-- Actual nonnegative forest parameters, with regular units proved for the
whole radius interval including its full descendant-zero endpoint. -/
def resolvedParameters (r : D.RadiusDomain) : ForestDirectionRatioCoordinates.Domain T D.leaf :=
  ⟨(radii T r.val, D.increment), radii_nonneg T r.property.1,
    D.regularUnits_nonneg r.property.1 r.property.2⟩

@[fun_prop] theorem continuous_resolvedParameters : Continuous D.resolvedParameters :=
  (((continuous_radii T).comp continuous_subtype_val).prodMk continuous_const).subtype_mk _

def resolvedDR (r : D.RadiusDomain) : DRData n m :=
  ForestDirectionRatioCoordinates.doubledCoordinates T D.leaf (D.resolvedParameters r)

@[fun_prop] theorem continuous_resolvedDR : Continuous D.resolvedDR :=
  (ForestDirectionRatioCoordinates.continuous_doubledCoordinates T D.leaf).comp D.continuous_resolvedParameters

theorem resolvedDR_eq_configuration (r : D.RadiusDomain) (hr : 0 < r.val) :
    D.resolvedDR r = directionRatioCoordinates (D.configuration r.val hr r.property.2) := by
  apply ForestDirectionRatioCoordinates.doubledCoordinates_eq_configuration
    T D.leaf (D.resolvedParameters r) (radii_pos T hr)
      (D.configuration r.val hr r.property.2) 0
  intro v
  simpa only [zero_add, positions, positionAtRadius, resolvedParameters] using
    D.configuration_doubledPoint r.val hr r.property.2 v

theorem resolvedDR_eq_normalized (i : Fin n) (r : D.RadiusDomain) (hr : 0 < r.val) :
    D.resolvedDR r = normalizedDirectionRatios (D.normalized i r.val hr r.property.2) := by
  rw [D.resolvedDR_eq_configuration r hr]
  exact (normalizedDirectionRatios_normalized i (D.configuration r.val hr r.property.2)).symm

/-- A specific sequence of positive radii strictly inside the proved common interval. -/
def radiusSequence (k : ℕ) : D.RadiusDomain :=
  ⟨(D.radiusBound / 2) / ((k : ℝ) + 1), by
    have hε := D.radiusBound_pos
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    constructor
    · positivity
    · exact (div_le_self (by positivity : 0 ≤ D.radiusBound / 2) (by linarith : 1 ≤ (k : ℝ) + 1)).trans_lt
        (half_lt_self hε)⟩

theorem radiusSequence_pos (k : ℕ) : 0 < (D.radiusSequence k).val := by
  have hε := D.radiusBound_pos
  change 0 < (D.radiusBound / 2) / ((k : ℝ) + 1)
  positivity

theorem tendsto_radiusSequence : Tendsto D.radiusSequence atTop (𝓝 D.zeroRadius) := by
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun k : ℕ => (D.radiusBound / 2) / ((k : ℝ) + 1)) atTop (𝓝 0)
  simpa only [div_eq_mul_inv, one_mul, mul_zero] using
    (tendsto_const_nhds (x := D.radiusBound / 2)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The actual resolved full direction/ratio face belongs to the genuine
configuration closure, proved using the constructed positive configurations. -/
theorem resolvedFace_mem_directionRatioSet : D.resolvedDR D.zeroRadius ∈ directionRatioSet n m := by
  have hlim := D.continuous_resolvedDR.continuousAt.tendsto.comp D.tendsto_radiusSequence
  change D.resolvedDR D.zeroRadius ∈ closure (Set.range (directionRatioCoordinates : Configuration n m → DRData n m))
  apply mem_closure_of_tendsto hlim
  exact Filter.Eventually.of_forall (fun k =>
    ⟨D.configuration (D.radiusSequence k).val (D.radiusSequence_pos k) (D.radiusSequence k).property.2,
      (D.resolvedDR_eq_configuration (D.radiusSequence k) (D.radiusSequence_pos k)).symm⟩)

def resolvedFace : DRSpace n m := ⟨D.resolvedDR D.zeroRadius, D.resolvedFace_mem_directionRatioSet⟩

/-- Every available interior anchor identifies the proved forest face with an
actual point of the existing compactification, including its infinity cases. -/
def compactFace (i : Fin n) : Compactification i m := (toDRHomeomorph i).symm D.resolvedFace

theorem compactFace_projectDR (i : Fin n) :
    projectDR (D.compactFace i).val = D.resolvedDR D.zeroRadius :=
  congrArg Subtype.val ((toDRHomeomorph i).apply_symm_apply D.resolvedFace)

def normalizedSequence (i : Fin n) : ℕ → Configuration.Normalized i m :=
  fun k => D.normalized i (D.radiusSequence k).val (D.radiusSequence_pos k) (D.radiusSequence k).property.2

/-- The explicit positive forest insertions, genuinely normalized at any chosen
interior anchor, converge in the actual compactification to this resolved face. -/
theorem tendsto_normalizedSequence (i : Fin n) :
    Tendsto (fun k => compactificationEmbedding i (D.normalizedSequence i k)) atTop
      (𝓝 (D.compactFace i)) := by
  apply (toDRHomeomorph i).isEmbedding.tendsto_nhds_iff.mpr
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun k => normalizedDirectionRatios (D.normalizedSequence i k)) atTop
    (𝓝 (projectDR (D.compactFace i).val))
  rw [D.compactFace_projectDR]
  have heq : (fun k => normalizedDirectionRatios (D.normalizedSequence i k)) =
      (fun k => D.resolvedDR (D.radiusSequence k)) :=
    funext (fun k => (D.resolvedDR_eq_normalized i (D.radiusSequence k) (D.radiusSequence_pos k)).symm)
  rw [heq]
  exact D.continuous_resolvedDR.continuousAt.tendsto.comp D.tendsto_radiusSequence

end ShapeData

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestPositiveScale
