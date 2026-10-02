import EnvelopingIsomorphism.Deformation.Kontsevich.SubtreeForestInsertion
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestChartOpenImage
import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarNormalizedCoordinates

/-! Actual planar positions extracted below an arbitrary native forest node.
The selected cluster radius is never divided out: its root is reset to one,
and all retained directions and ratios are proved to agree with the forest. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestDescendantPlanarCoordinates
open Configuration ExtractedForestParameters ExtractedForestFrames ExtractedForestChildShapes
open ForestInsertionDifference ForestDirectionRatioCoordinates InteriorFiberAngleSplit
open scoped Classical
variable {n m N : ℕ} (i : Fin n) (x : Compactification i m) (c : tree i x)
variable (labels : Point N → Fin n) (hinj : Function.Injective labels)
variable (hbelow : ∀ j, c ≤ canonicalLeaf i x (Sum.inl (Sum.inl (labels j))))

abbrev Tree := SubtreeForestInsertion.Tree (tree i x) c

def leaf (j : Point N) : Tree i x c :=
  ⟨canonicalLeaf i x (Sum.inl (Sum.inl (labels j))), hbelow j⟩

def pair (e : Pair (Point N)) : DoubledPair n m :=
  ⟨(Sum.inl (Sum.inl (labels e.val.1)), Sum.inl (Sum.inl (labels e.val.2))),
    fun h ↦ e.property (hinj (Sum.inl.inj (Sum.inl.inj h)))⟩

def triple (e : Triple (Point N)) : DoubledTriple n m :=
  ⟨(Sum.inl (Sum.inl (labels e.val.1)), Sum.inl (Sum.inl (labels e.val.2.1)),
    Sum.inl (Sum.inl (labels e.val.2.2))),
    fun h ↦ e.property.1 (hinj (Sum.inl.inj (Sum.inl.inj h))),
    fun h ↦ e.property.2 (hinj (Sum.inl.inj (Sum.inl.inj h)))⟩

def project (d : DRData n m) : Data (Point N) :=
  (fun e ↦ d.1 (pair labels hinj e), fun e ↦ d.2 (triple labels hinj e))

theorem continuous_project : Continuous (project (m := m) labels hinj) := by
  unfold project
  fun_prop

def parameters (p : ForestChartOpenImage.ParameterSpace i x) : Parameters (Tree i x c) :=
  SubtreeForestInsertion.parameters (tree i x) c p.val

def domain (p : ForestChartOpenImage.Source i x) : Domain (Tree i x c) (leaf i x c labels hbelow) :=
  ⟨parameters i x c p.val,
    SubtreeForestInsertion.radius_nonneg _ _ _ p.val.property.1.2.2.2,
    fun e ↦ (SubtreeForestInsertion.pairUnit_eq (tree i x) c (leaf i x c labels hbelow) p.val.val e).symm ▸
      p.property.1 (pair labels hinj e)⟩

theorem project_forward (p : ForestChartOpenImage.Source i x) :
    project labels hinj (projectDR (ForestChartOpenImage.forward i x p).val) =
      resolvedCoordinates (Tree i x c) (leaf i x c labels hbelow) (domain i x c labels hinj hbelow p) := by
  change project labels hinj (projectDR (ForestChartConfigurations.compactificationInsertion
    (shapeData i x) i (ForestChartOpenImage.toCorner i x p)).val) = _
  rw [ForestChartConfigurations.compactificationInsertion_projectDR]
  apply Prod.ext
  · funext e
    exact congrArg complexPhase
      (SubtreeForestInsertion.pairUnit_eq (tree i x) c (leaf i x c labels hbelow) p.val.val e)
  · funext e
    apply Subtype.ext
    exact SubtreeForestInsertion.ratioValue_eq (tree i x) c (leaf i x c labels hbelow) p.val.val e

/-- Exactly the positivity needed below the collapsed node; no condition on its radius. -/
def PositiveBelow (p : ForestChartOpenImage.ParameterSpace i x) : Prop :=
  ∀ v : Tree i x c, v ≠ ⊥ → ¬ IsMax v → 0 < p.val.1 v.val

theorem radius_pos (p : ForestChartOpenImage.ParameterSpace i x) (hp : PositiveBelow i x c p)
    (v : Tree i x c) : 0 < (parameters i x c p).1 v := by
  by_cases hv : v = ⊥
  · subst v
    change 0 < SubtreeForestInsertion.radius (tree i x) c p.val.1 ⊥
    rw [SubtreeForestInsertion.radius_root]
    exact zero_lt_one
  · change 0 < SubtreeForestInsertion.radius (tree i x) c p.val.1 v
    rw [SubtreeForestInsertion.radius_nonroot _ _ _ _ hv]
    by_cases hn : IsMax v
    · have hn' : IsMax v.val := by
        intro w hvw
        exact hn (b := (⟨w, v.property.trans hvw⟩ : Tree i x c)) hvw
      rw [p.property.1.2.1 v.val hn']
      exact zero_lt_one
    · exact hp v hv hn

/-- These are literal residual branch insertion polynomials. -/
def positions (p : Parameters (tree i x)) (j : Point N) : ℂ :=
  branchUnit (tree i x) p.1 p.2 c (canonicalLeaf i x (Sum.inl (Sum.inl (labels j))))

theorem positions_eq_subtree (p : ForestChartOpenImage.ParameterSpace i x) (j : Point N) :
    positions i x c labels p.val j =
      position (Tree i x c) (parameters i x c p).1 (parameters i x c p).2 (leaf i x c labels hbelow j) :=
  (SubtreeForestInsertion.position_eq_branchUnit (tree i x) c p.val.1 p.val.2
    (leaf i x c labels hbelow j)).symm

theorem contDiff_positions (j : Point N) : ContDiff ℝ ⊤ (fun p ↦ positions i x c labels p j) :=
  contDiff_branchUnit _ _ _

include hinj hbelow

theorem positions_injective (p : ForestChartOpenImage.Source i x) (hp : PositiveBelow i x c p.val) :
    Function.Injective (positions i x c labels p.val.val) := by
  intro j k he
  by_contra hjk
  rw [positions_eq_subtree i x c labels hbelow p.val j,
    positions_eq_subtree i x c labels hbelow p.val k] at he
  exact ForestDRInverse.inserted_reference_ne (Tree i x c) (leaf i x c labels hbelow)
    (domain i x c labels hinj hbelow p) (radius_pos i x c p.val hp) j k hjk he

theorem project_forward_eq_ofPositions (p : ForestChartOpenImage.Source i x)
    (hp : PositiveBelow i x c p.val) :
    project labels hinj (projectDR (ForestChartOpenImage.forward i x p).val) =
      MarkedDRIdentification.ofPositions (positions i x c labels p.val.val) := by
  rw [project_forward i x c labels hinj hbelow p,
    resolvedCoordinates_eq_raw _ _ _ (radius_pos i x c p.val hp)]
  have he : (fun j ↦ position (Tree i x c) (parameters i x c p.val).1
      (parameters i x c p.val).2 (leaf i x c labels hbelow j)) =
      positions i x c labels p.val.val := by
    funext j
    exact (positions_eq_subtree i x c labels hbelow p.val j).symm
  exact congrArg MarkedDRIdentification.ofPositions he

def referenceRadius (p : Parameters (tree i x)) : ℝ :=
  ‖positions i x c labels p 1 - positions i x c labels p 0‖

theorem referenceRadius_pos (p : ForestChartOpenImage.Source i x) (hp : PositiveBelow i x c p.val) :
    0 < referenceRadius i x c labels p.val.val :=
  norm_pos_iff.mpr (sub_ne_zero.mpr
    ((positions_injective i x c labels hinj hbelow p hp).ne Fin.zero_ne_one.symm))

def normalized (p : ForestChartOpenImage.Source i x) (hp : PositiveBelow i x c p.val) :
    PlanarNormalizedCoordinates.Normalized N :=
  ⟨fun j ↦ (positions i x c labels p.val.val j - positions i x c labels p.val.val 0) /
    (referenceRadius i x c labels p.val.val : ℂ), by
    intro j k he
    apply positions_injective i x c labels hinj hbelow p hp
    exact sub_left_inj.mp ((div_left_inj'
      (Complex.ofReal_ne_zero.mpr (referenceRadius_pos i x c labels hinj hbelow p hp).ne')).mp he),
    by simp,
    by rw [norm_div, Complex.norm_real,
      Real.norm_of_nonneg (referenceRadius_pos i x c labels hinj hbelow p hp).le]
       exact div_self (referenceRadius_pos i x c labels hinj hbelow p hp).ne'⟩

/-- Native residual positions become a genuine original planar point, carrying
an actual unit phase and Cartesian normalized shape. -/
def coordinates (p : ForestChartOpenImage.Source i x) (hp : PositiveBelow i x c p.val) :
    Circle × PlanarNormalizedCoordinates.Configuration N :=
  PlanarNormalizedCoordinates.toCoordinates (normalized i x c labels hinj hbelow p hp)

theorem positions_reconstruct (p : ForestChartOpenImage.Source i x) (hp : PositiveBelow i x c p.val)
    (j : Point N) :
    positions i x c labels p.val.val j = positions i x c labels p.val.val 0 +
      (referenceRadius i x c labels p.val.val : ℂ) *
        ((coordinates i x c labels hinj hbelow p hp).1 : ℂ) *
        normalizedPoint (coordinates i x c labels hinj hbelow p hp).2.val j := by
  have h := congrArg (fun q : PlanarNormalizedCoordinates.Normalized N ↦ q.val j)
    (PlanarNormalizedCoordinates.ofCoordinates_toCoordinates (normalized i x c labels hinj hbelow p hp))
  change ((coordinates i x c labels hinj hbelow p hp).1 : ℂ) *
    normalizedPoint (coordinates i x c labels hinj hbelow p hp).2.val j =
    (positions i x c labels p.val.val j - positions i x c labels p.val.val 0) /
      (referenceRadius i x c labels p.val.val : ℂ) at h
  rw [mul_assoc, h, mul_div_cancel₀ _
    (Complex.ofReal_ne_zero.mpr (referenceRadius_pos i x c labels hinj hbelow p hp).ne')]
  abel


theorem normalized_encode (p : ForestChartOpenImage.Source i x) (hp : PositiveBelow i x c p.val) :
    PlanarClusterCompactification.encode 0 1 (normalized i x c labels hinj hbelow p hp) =
      MarkedDRIdentification.ofPositions (positions i x c labels p.val.val) := by
  have hd (j k : Point N) :
      (normalized i x c labels hinj hbelow p hp).val k -
        (normalized i x c labels hinj hbelow p hp).val j =
      (referenceRadius i x c labels p.val.val)⁻¹ •
        (positions i x c labels p.val.val k - positions i x c labels p.val.val j) := by
    change (_ / _) - (_ / _) = _
    rw [← sub_div]
    have he : (positions i x c labels p.val.val k - positions i x c labels p.val.val 0) -
        (positions i x c labels p.val.val j - positions i x c labels p.val.val 0) =
        positions i x c labels p.val.val k - positions i x c labels p.val.val j := by abel
    rw [he]
    simp only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]
  have hr := inv_pos.mpr (referenceRadius_pos i x c labels hinj hbelow p hp)
  apply Prod.ext
  · funext e
    change complexPhase ((normalized i x c labels hinj hbelow p hp).val e.val.2 -
      (normalized i x c labels hinj hbelow p hp).val e.val.1) = _
    rw [hd, complexPhase_pos_real_smul hr]
    rfl
  · funext e
    apply Subtype.ext
    change ‖(normalized i x c labels hinj hbelow p hp).val e.val.2.1 -
      (normalized i x c labels hinj hbelow p hp).val e.val.1‖ /
      (‖(normalized i x c labels hinj hbelow p hp).val e.val.2.1 -
        (normalized i x c labels hinj hbelow p hp).val e.val.1‖ +
       ‖(normalized i x c labels hinj hbelow p hp).val e.val.2.2 -
        (normalized i x c labels hinj hbelow p hp).val e.val.1‖) = _
    simp only [hd, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    rw [← mul_add, mul_div_mul_left _ _ hr.ne']
    rfl

/-- Cartesian shape extraction is a quotient of actual residual polynomials. -/
def ambientShape (p : Parameters (tree i x)) : Shape N := fun j ↦
  (positions i x c labels p j.succ.succ - positions i x c labels p 0) /
    (positions i x c labels p 1 - positions i x c labels p 0)

theorem coordinates_shape (p : ForestChartOpenImage.Source i x) (hp : PositiveBelow i x c p.val) :
    (coordinates i x c labels hinj hbelow p hp).2.val = ambientShape i x c labels p.val.val := by
  funext j
  change (_ / _) / (_ / _) = _
  exact div_div_div_cancel_right₀
    (Complex.ofReal_ne_zero.mpr (referenceRadius_pos i x c labels hinj hbelow p hp).ne') _ _

theorem contDiffAt_ambientShape (p : ForestChartOpenImage.Source i x)
    (hp : PositiveBelow i x c p.val) : ContDiffAt ℝ ⊤ (ambientShape i x c labels) p.val.val := by
  apply contDiffAt_pi.mpr
  intro j
  change ContDiffAt ℝ ⊤ (fun q : Parameters (tree i x) ↦
    (positions i x c labels q j.succ.succ - positions i x c labels q 0) /
      (positions i x c labels q 1 - positions i x c labels q 0)) p.val.val
  have hnum : ContDiffAt ℝ ⊤ (fun q : Parameters (tree i x) ↦
      positions i x c labels q j.succ.succ - positions i x c labels q 0) p.val.val :=
    ((contDiff_positions i x c labels j.succ.succ).sub (contDiff_positions i x c labels 0)).contDiffAt
  have hden : ContDiffAt ℝ ⊤ (fun q : Parameters (tree i x) ↦
      positions i x c labels q 1 - positions i x c labels q 0) p.val.val :=
    ((contDiff_positions i x c labels 1).sub (contDiff_positions i x c labels 0)).contDiffAt
  simpa only [div_eq_mul_inv, Pi.inv_apply] using hnum.mul (hden.inv
    (sub_ne_zero.mpr ((positions_injective i x c labels hinj hbelow p hp).ne Fin.zero_ne_one.symm)))


/-- Ambient real normalization of every descendant position. -/
def ambientNormalized (q : Parameters (tree i x)) : Point N → ℂ := fun j ↦
  (positions i x c labels q j - positions i x c labels q 0) /
    (referenceRadius i x c labels q : ℂ)

@[simp] theorem normalized_val (p : ForestChartOpenImage.Source i x)
    (hp : PositiveBelow i x c p.val) :
    (normalized i x c labels hinj hbelow p hp).val = ambientNormalized i x c labels p.val.val := rfl

/-- The whole phase-carrying normalization has a genuine smooth ambient extension
near each positive-descendant point, including when the cluster radius is zero. -/
theorem contDiffAt_ambientNormalized (p : ForestChartOpenImage.Source i x)
    (hp : PositiveBelow i x c p.val) :
    ContDiffAt ℝ ⊤ (ambientNormalized i x c labels) p.val.val := by
  have hdiff : ContDiffAt ℝ ⊤ (fun q : Parameters (tree i x) ↦
      positions i x c labels q 1 - positions i x c labels q 0) p.val.val :=
    ((contDiff_positions i x c labels 1).sub (contDiff_positions i x c labels 0)).contDiffAt
  have hne := sub_ne_zero.mpr
    ((positions_injective i x c labels hinj hbelow p hp).ne Fin.zero_ne_one.symm)
  have hr : ContDiffAt ℝ ⊤ (fun q ↦ (referenceRadius i x c labels q : ℂ)) p.val.val :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hdiff.norm ℝ hne)
  apply contDiffAt_pi.mpr
  intro j
  have hn : ContDiffAt ℝ ⊤ (fun q : Parameters (tree i x) ↦
      positions i x c labels q j - positions i x c labels q 0) p.val.val :=
    ((contDiff_positions i x c labels j).sub (contDiff_positions i x c labels 0)).contDiffAt
  simpa only [ambientNormalized, div_eq_mul_inv, Pi.inv_apply] using hn.mul
    (hr.inv (Complex.ofReal_ne_zero.mpr (referenceRadius_pos i x c labels hinj hbelow p hp).ne'))

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestDescendantPlanarCoordinates
