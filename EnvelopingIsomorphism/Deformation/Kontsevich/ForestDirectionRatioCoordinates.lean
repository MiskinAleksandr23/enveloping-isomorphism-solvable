import EnvelopingIsomorphism.Deformation.Kontsevich.ForestInsertionDifference
import EnvelopingIsomorphism.Deformation.Kontsevich.DirectionRatioInvariant
import EnvelopingIsomorphism.Deformation.Kontsevich.LinearCollisionLimits
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Full direction/ratio coordinates of actual finite-tree insertion, resolved at zero radii. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestDirectionRatioCoordinates

open AncestorScaleRatios ForestInsertionDifference Configuration Topology Filter
open scoped Classical

abbrev Pair (Label : Type*) := {p : Label × Label // p.1 ≠ p.2}

/-- Both targets differ from the source; the targets are allowed to coincide. -/
abbrev Triple (Label : Type*) :=
  {q : Label × Label × Label // q.1 ≠ q.2.1 ∧ q.1 ≠ q.2.2}

abbrev Data (Label : Type*) := (Pair Label → Circle) × (Triple Label → Set.Icc (0 : ℝ) 1)

abbrev Parameters (t : RootedTree) := (t → ℝ) × (t → ℂ)

variable (t : RootedTree) [Fintype t] {Label : Type*} (lab : Label → t)

def firstPair (q : Triple Label) : Pair Label := ⟨(q.val.1, q.val.2.1), q.property.1⟩
def secondPair (q : Triple Label) : Pair Label := ⟨(q.val.1, q.val.2.2), q.property.2⟩

def pairNode (p : Pair Label) : t := lab p.val.1 ⊓ lab p.val.2

/-- The actual point difference is target minus source, matching `Configuration.pairDifference`. -/
def pairDifference (x : Parameters t) (p : Pair Label) : ℂ :=
  position t x.1 x.2 (lab p.val.2) - position t x.1 x.2 (lab p.val.1)

def pairUnit (x : Parameters t) (p : Pair Label) : ℂ :=
  unitDifference t x.1 x.2 (lab p.val.2) (lab p.val.1)

/-- Literal insertion produces this factorization; it is not an input to the encoder. -/
theorem pairDifference_factor (x : Parameters t) (p : Pair Label) :
    pairDifference t lab x p = scale x.1 (pairNode t lab p) • pairUnit t lab x p := by
  simpa only [pairDifference, pairNode, pairUnit, inf_comm] using
    position_sub_position t x.1 x.2 (lab p.val.2) (lab p.val.1)

@[fun_prop] theorem contDiff_pairUnit (p : Pair Label) :
    ContDiff ℝ ⊤ (fun x : Parameters t ↦ pairUnit t lab x p) :=
  contDiff_unitDifference t _ _

def RegularUnits (x : Parameters t) : Prop := ∀ p : Pair Label, pairUnit t lab x p ≠ 0

theorem isOpen_regularUnits [Fintype Label] : IsOpen {x : Parameters t | RegularUnits t lab x} := by
  simp only [RegularUnits, Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro p
  exact (isClosed_eq (contDiff_pairUnit t lab p).continuous continuous_const).isOpen_compl

def Admissible (x : Parameters t) : Prop := (∀ u, 0 ≤ x.1 u) ∧ RegularUnits t lab x

abbrev Domain := {x : Parameters t // Admissible t lab x}

omit [Fintype t] in
theorem tripleNodes_comparable (q : Triple Label) :
    pairNode t lab (firstPair q) ≤ pairNode t lab (secondPair q) ∨
      pairNode t lab (secondPair q) ≤ pairNode t lab (firstPair q) :=
  common_source_lca_comparable (lab q.val.1) (lab q.val.2.1) (lab q.val.2.2)

def direction (x : Parameters t) (p : Pair Label) : Circle := complexPhase (pairUnit t lab x p)

/-- The symmetric residual-product ratio for the two common-source LCA scales. -/
def ratioValue (x : Parameters t) (q : Triple Label) : ℝ :=
  resolvedRatio x.1 (pairNode t lab (firstPair q)) (pairNode t lab (secondPair q))
    ‖pairUnit t lab x (firstPair q)‖ ‖pairUnit t lab x (secondPair q)‖

theorem ratioValue_mem_Icc (x : Parameters t) (hx : Admissible t lab x) (q : Triple Label) :
    ratioValue t lab x q ∈ Set.Icc (0 : ℝ) 1 :=
  resolvedRatio_mem_Icc x.1 hx.1 (tripleNodes_comparable t lab q)
    (norm_pos_iff.mpr (hx.2 (firstPair q))) (norm_pos_iff.mpr (hx.2 (secondPair q)))

def ratio (x : Domain t lab) (q : Triple Label) : Set.Icc (0 : ℝ) 1 :=
  ⟨ratioValue t lab x.val q, ratioValue_mem_Icc t lab x.val x.property q⟩

/-- Every pair direction and every admissible triple ratio is retained. -/
def resolvedCoordinates (x : Domain t lab) : Data Label :=
  (direction t lab x.val, ratio t lab x)

/-- The ordinary full direction/ratio encoder of the actual insertion positions. -/
def rawCoordinates (x : Parameters t) : Data Label :=
  (fun p ↦ complexPhase (pairDifference t lab x p),
    fun q ↦ normalizedNormRatio (pairDifference t lab x (firstPair q))
      (pairDifference t lab x (secondPair q)))

theorem direction_eq_actual (x : Parameters t) (hρ : ∀ u, 0 < x.1 u) (p : Pair Label) :
    direction t lab x p = complexPhase (pairDifference t lab x p) := by
  rw [pairDifference_factor, complexPhase_pos_real_smul (scale_pos x.1 hρ _)]
  rfl

theorem norm_pairDifference (x : Parameters t) (hρ : ∀ u, 0 < x.1 u) (p : Pair Label) :
    ‖pairDifference t lab x p‖ = scale x.1 (pairNode t lab p) * ‖pairUnit t lab x p‖ := by
  rw [pairDifference_factor, norm_smul, Real.norm_eq_abs, abs_of_pos (scale_pos x.1 hρ _)]

theorem ratioValue_eq_actual (x : Parameters t) (hρ : ∀ u, 0 < x.1 u) (q : Triple Label) :
    ratioValue t lab x q =
      (normalizedNormRatio (pairDifference t lab x (firstPair q))
        (pairDifference t lab x (secondPair q)) : ℝ) := by
  change _ = ‖pairDifference t lab x (firstPair q)‖ /
    (‖pairDifference t lab x (firstPair q)‖ + ‖pairDifference t lab x (secondPair q)‖)
  rw [norm_pairDifference t lab x hρ, norm_pairDifference t lab x hρ]
  exact (ratio_eq_resolvedRatio x.1 hρ _ _ _ _).symm

/-- Exact full-coordinate agreement on positive radii follows from the actual insertion sum. -/
theorem resolvedCoordinates_eq_raw (x : Domain t lab) (hρ : ∀ u, 0 < x.val.1 u) :
    resolvedCoordinates t lab x = rawCoordinates t lab x.val := by
  apply Prod.ext
  · funext p
    exact direction_eq_actual t lab x.val hρ p
  · funext q
    exact Subtype.ext (ratioValue_eq_actual t lab x.val hρ q)

theorem continuousAt_direction (x : Parameters t) (p : Pair Label) (hp : pairUnit t lab x p ≠ 0) :
    ContinuousAt (fun y : Parameters t ↦ direction t lab y p) x :=
  (continuousAt_complexPhase hp).comp (f := fun y : Parameters t ↦ pairUnit t lab y p)
    (x := x) (contDiff_pairUnit t lab p).continuous.continuousAt

/-- The complex representatives of all circle directions are genuinely smooth at regular units. -/
theorem contDiffAt_direction_coe (x : Parameters t) (p : Pair Label) (hp : pairUnit t lab x p ≠ 0) :
    ContDiffAt ℝ ⊤ (fun y : Parameters t ↦ (direction t lab y p : ℂ)) x := by
  have hf := (contDiff_pairUnit t lab p).contDiffAt (x := x)
  have hn := hf.norm ℝ hp
  have hd : ContDiffAt ℝ ⊤ (fun y : Parameters t ↦ (‖pairUnit t lab y p‖ : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hn
  have hd0 : (‖pairUnit t lab x p‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hp)
  have hform : ContDiffAt ℝ ⊤
      (fun y : Parameters t ↦ pairUnit t lab y p / (‖pairUnit t lab y p‖ : ℂ)) x := by
    simpa only [div_eq_mul_inv, Pi.inv_apply] using hf.mul (hd.inv hd0)
  have hloc : ∀ᶠ y in 𝓝 x, pairUnit t lab y p ≠ 0 :=
    ((isClosed_eq (contDiff_pairUnit t lab p).continuous continuous_const).isOpen_compl).mem_nhds hp
  exact hform.congr_of_eventuallyEq (hloc.mono fun y hy ↦ complexPhase_coe hy)

theorem contDiffAt_ratioValue (x : Parameters t) (hx : Admissible t lab x) (q : Triple Label) :
    ContDiffAt ℝ ⊤ (fun y : Parameters t ↦ ratioValue t lab y q) x := by
  have hU := ((contDiff_pairUnit t lab (firstPair q)).contDiffAt (x := x)).norm ℝ (hx.2 (firstPair q))
  have hV := ((contDiff_pairUnit t lab (secondPair q)).contDiffAt (x := x)).norm ℝ (hx.2 (secondPair q))
  exact (AncestorScaleRatios.contDiffAt_resolvedRatio (tripleNodes_comparable t lab q)
    (x.1, ‖pairUnit t lab x (firstPair q)‖, ‖pairUnit t lab x (secondPair q)‖)
      ⟨hx.1, norm_pos_iff.mpr (hx.2 (firstPair q)), norm_pos_iff.mpr (hx.2 (secondPair q))⟩).comp x
        (contDiffAt_fst.prodMk (hU.prodMk hV))

/-- The resolved encoder is jointly continuous on the regular subset of the nonnegative-radius
half-space, including all corners. -/
@[fun_prop] theorem continuous_resolvedCoordinates : Continuous (resolvedCoordinates t lab) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro p
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (continuousAt_direction t lab x.val p (x.property.2 p)).comp continuous_subtype_val.continuousAt
  · apply continuous_pi
    intro q
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (contDiffAt_ratioValue t lab x.val x.property q).continuousAt.comp
      continuous_subtype_val.continuousAt

/-- Ambient complex/real representatives of the full direction/ratio array. -/
def representatives (x : Parameters t) : (Pair Label → ℂ) × (Triple Label → ℝ) :=
  (fun p ↦ (direction t lab x p : ℂ), ratioValue t lab x)

theorem contDiffAt_representatives [Fintype Label] (x : Parameters t) (hx : Admissible t lab x) :
    ContDiffAt ℝ ⊤ (representatives t lab) x := by
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro p
    exact contDiffAt_direction_coe t lab x p (hx.2 p)
  · apply contDiffAt_pi.mpr
    intro q
    exact contDiffAt_ratioValue t lab x hx q

theorem contDiffOn_representatives [Fintype Label] :
    ContDiffOn ℝ ⊤ (representatives t lab) {x | Admissible t lab x} :=
  fun x hx ↦ (contDiffAt_representatives t lab x hx).contDiffWithinAt

/-- The regularity restriction is open inside the actual nonnegative-radius half-space. -/
abbrev HalfSpace := {x : Parameters t // ∀ u, 0 ≤ x.1 u}

theorem isOpen_regularHalfSpace [Fintype Label] :
    IsOpen {x : HalfSpace t | RegularUnits t lab x.val} :=
  (isOpen_regularUnits t lab).preimage continuous_subtype_val

def domainHalfSpaceHomeomorph : Domain t lab ≃ₜ {x : HalfSpace t // RegularUnits t lab x.val} where
  toFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  invFun x := ⟨x.val.val, x.val.property, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem pairDifference_ne_zero (x : Parameters t) (hx : RegularUnits t lab x)
    (hρ : ∀ u, 0 < x.1 u) (p : Pair Label) : pairDifference t lab x p ≠ 0 := by
  rw [pairDifference_factor]
  exact smul_ne_zero (ne_of_gt (scale_pos x.1 hρ _)) (hx p)

/-- Positive radii and actual regular units yield distinct inserted labelled positions. -/
theorem position_lab_injective (x : Parameters t) (hx : RegularUnits t lab x)
    (hρ : ∀ u, 0 < x.1 u) : Function.Injective (fun j ↦ position t x.1 x.2 (lab j)) := by
  intro i j hij
  by_contra hne
  have h := pairDifference_ne_zero t lab x hx hρ ⟨(i, j), hne⟩
  apply h
  change position t x.1 x.2 (lab j) - position t x.1 x.2 (lab i) = 0
  exact sub_eq_zero.mpr hij.symm

/-- Pairwise distinct immediate-child shapes make every pair unit regular on the face
where all nonroot local radii vanish. The labels are actual distinct native leaves. -/
theorem regularUnits_at_full_face (x : Parameters t) (hlab : Function.Injective lab)
    (hleaf : ∀ j, IsMax (lab j)) (hzero : ∀ u : t, u ≠ ⊥ → x.1 u = 0)
    (hshape : ∀ c d e : t, c ⋖ d → c ⋖ e → d ≠ e → x.2 d ≠ x.2 e) :
    RegularUnits t lab x := by
  intro p
  apply leaf_unitDifference_ne_zero_at_face t x.1 x.2 (hleaf p.val.2) (hleaf p.val.1)
  · exact fun h ↦ p.property (hlab h).symm
  · intro u hu
    apply hzero u
    intro heq
    subst u
    exact hu.not_ge bot_le
  · exact hshape _

section Doubled

variable {n m : ℕ} (doubledLab : DoubledLabel n m → t)

/-- The exact existing doubled-pair/doubled-triple data type, with every coordinate retained. -/
def doubledCoordinates (x : Domain t doubledLab) : DRData n m :=
  resolvedCoordinates t doubledLab x

@[fun_prop] theorem continuous_doubledCoordinates : Continuous (doubledCoordinates t doubledLab) :=
  continuous_resolvedCoordinates t doubledLab

theorem doubledCoordinates_eq_raw (x : Domain t doubledLab) (hρ : ∀ u, 0 < x.val.1 u) :
    doubledCoordinates t doubledLab x = rawCoordinates t doubledLab x.val :=
  resolvedCoordinates_eq_raw t doubledLab x hρ

/-- Once a separately verified configuration has the actual inserted doubled positions,
the resolved full encoder agrees with its existing native direction/ratio encoder. -/
theorem doubledCoordinates_eq_configuration (x : Domain t doubledLab) (hρ : ∀ u, 0 < x.val.1 u)
    (c : Configuration n m) (z : ℂ)
    (hc : ∀ j, c.doubledPoint j = z + position t x.val.1 x.val.2 (doubledLab j)) :
    doubledCoordinates t doubledLab x = directionRatioCoordinates c := by
  rw [doubledCoordinates_eq_raw t doubledLab x hρ]
  have hp (p : DoubledPair n m) : c.pairDifference p = pairDifference t doubledLab x.val p := by
    simp only [Configuration.pairDifference, hc, pairDifference, add_sub_add_left_eq_sub]
  apply Prod.ext
  · funext p
    change complexPhase (pairDifference t doubledLab x.val p) = complexPhase (c.pairDifference p)
    rw [hp]
  · funext q
    apply Subtype.ext
    change ‖pairDifference t doubledLab x.val (firstPair q)‖ /
        (‖pairDifference t doubledLab x.val (firstPair q)‖ +
          ‖pairDifference t doubledLab x.val (secondPair q)‖) =
      ‖c.pairDifference (firstPair q)‖ /
        (‖c.pairDifference (firstPair q)‖ + ‖c.pairDifference (secondPair q)‖)
    rw [hp, hp]

end Doubled

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestDirectionRatioCoordinates
