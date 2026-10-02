import EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestShapeCoordinates
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! Standard local angle charts for the actual free forest model. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestOrthantCharts

open Configuration Set Topology
open scoped Classical NNReal ContDiff

def exponentialChart : OpenPartialHomeomorph ℝ Circle where
  toFun := Circle.exp
  invFun := fun z => Complex.arg z
  source := Ioo (-Real.pi) Real.pi
  target := {z | (z : ℂ) ∈ Complex.slitPlane}
  map_source' := by
    intro t ht
    apply Complex.mem_slitPlane_iff_arg.mpr
    exact ⟨(Circle.arg_exp ht.1 ht.2.le).trans_ne ht.2.ne, (Circle.exp t).coe_ne_zero⟩
  map_target' := by
    intro z hz
    exact ⟨Complex.neg_pi_lt_arg _, lt_of_le_of_ne (Complex.arg_le_pi _) (Complex.mem_slitPlane_iff_arg.mp hz).1⟩
  left_inv' := fun _ ht => Circle.arg_exp ht.1 ht.2.le
  right_inv' := fun z _ => Circle.exp_arg z
  continuousOn_toFun := Circle.exp.continuous.continuousOn
  continuousOn_invFun := by
    intro z hz
    exact ((Complex.continuousAt_arg hz).comp continuous_subtype_val.continuousAt).continuousWithinAt
  open_source := isOpen_Ioo
  open_target := Complex.isOpen_slitPlane.preimage continuous_subtype_val

def rotation (u : Circle) : Circle ≃ₜ Circle where
  toEquiv :=
    { toFun := fun z => u * z
      invFun := fun z => u⁻¹ * z
      left_inv := by intro z; simp
      right_inv := by intro z; simp }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def angleChart (u : Circle) : OpenPartialHomeomorph ℝ Circle :=
  exponentialChart.trans (rotation u).toOpenPartialHomeomorph

theorem angleChart_apply (u : Circle) (t : ℝ) : angleChart u t = u * Circle.exp t := rfl

theorem angleChart_source (u : Circle) : (angleChart u).source = Ioo (-Real.pi) Real.pi := by
  simp only [angleChart, OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
    Set.preimage_univ, Set.inter_univ]
  rfl

theorem center_mem_angleChart_target (u : Circle) : u ∈ (angleChart u).target := by
  have hzero : 0 ∈ (angleChart u).source := by
    rw [angleChart_source]
    exact ⟨neg_neg_of_pos Real.pi_pos, Real.pi_pos⟩
  simpa only [angleChart_apply, Circle.exp_zero, mul_one] using (angleChart u).map_source hzero

theorem contDiff_angleChart_coe (u : Circle) {ν : ℕ∞ω} :
    ContDiff ℝ ν (fun t : ℝ => (angleChart u t : ℂ)) := by
  simp only [angleChart_apply, Circle.coe_mul, Circle.coe_exp]
  apply ContDiff.mul contDiff_const
  exact Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)

variable {n m : ℕ} (i : Fin n) (x : Compactification i m)

abbrev R := ExtractedForestShapeCoordinates.radialCount i x
abbrev C := ExtractedForestShapeCoordinates.circleCount i x
abbrev Q := ExtractedForestShapeCoordinates.realCount i x

def centerModel : ExtractedForestShapeCoordinates.Model i x :=
  (ExtractedForestShapeCoordinates.chart i x).symm x

abbrev SplitModel := (Fin (R i x) → ℝ≥0) × ((Fin (C i x) → ℝ) × (Fin (Q i x) → ℝ))

def angles : OpenPartialHomeomorph (SplitModel i x) (ExtractedForestShapeCoordinates.Model i x) :=
  (OpenPartialHomeomorph.refl _).prod
    ((OpenPartialHomeomorph.pi fun j : Fin (C i x) => angleChart ((centerModel i x).2.1 j)).prod
      (OpenPartialHomeomorph.refl _))

theorem centerModel_mem_angles_target : centerModel i x ∈ (angles i x).target := by
  refine ⟨Set.mem_univ _, ?_, Set.mem_univ _⟩
  intro j _
  exact center_mem_angleChart_target _

def splitChart : OpenPartialHomeomorph (SplitModel i x) (Compactification i m) :=
  (angles i x).trans (ExtractedForestShapeCoordinates.chart i x)

theorem mem_splitChart_target : x ∈ (splitChart i x).target :=
  ⟨ExtractedForestShapeCoordinates.mem_chart_target i x, centerModel_mem_angles_target i x⟩

abbrev Model := (Fin (R i x) → ℝ≥0) × (Fin (C i x + Q i x) → ℝ)

def combineReal : ((Fin (C i x) → ℝ) × (Fin (Q i x) → ℝ)) ≃ₜ (Fin (C i x + Q i x) → ℝ) :=
  Homeomorph.sumArrowHomeomorphProdArrow.symm.trans
    (Homeomorph.piCongrLeft (Y := fun _ : Fin (C i x + Q i x) => ℝ) (finSumFinEquiv))

def splitHomeomorph : Model i x ≃ₜ SplitModel i x := (Homeomorph.refl _).prodCongr (combineReal i x).symm

/-- Actual compactification chart on a standard nonnegative orthant times a
real vector space, with circle angles in (-π,π). -/
def chart : OpenPartialHomeomorph (Model i x) (Compactification i m) :=
  (splitHomeomorph i x).toOpenPartialHomeomorph.trans (splitChart i x)

theorem mem_chart_target : x ∈ (chart i x).target := by
  change x ∈ (splitChart i x).target ∩ _
  exact ⟨mem_splitChart_target i x, Set.mem_univ _⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestOrthantCharts
