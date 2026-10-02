import Mathlib.Analysis.BoxIntegral.DivergenceTheorem
import Mathlib.Analysis.BoxIntegral.Integrability
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# Stokes' theorem on coordinate boxes

Differential forms and their exterior derivative are Mathlib's continuous
alternating-map forms. The proof uses the existing box divergence theorem.
The dimension is `n + 1`, so `n = 0` includes the fundamental-theorem case.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoxStokes

open Set ContinuousAlternatingMap BoxIntegral
open scoped Topology

abbrev Coord (n : ℕ) := Fin n → ℝ
abbrev Form (n : ℕ) := Coord (n + 1) → Coord (n + 1) [⋀^Fin n]→L[ℝ] ℝ

def standardBasis (n : ℕ) (i : Fin n) : Coord n := Pi.single i 1

def faceCoefficient {n : ℕ} (ω : Form n) (i : Fin (n + 1)) (x : Coord (n + 1)) : ℝ :=
  ω x (i.removeNth (standardBasis (n + 1)))

def flux {n : ℕ} (ω : Form n) (x : Coord (n + 1)) : Coord (n + 1) :=
  fun i => (-1 : ℝ) ^ i.val • faceCoefficient ω i x

def fluxDeriv {n : ℕ} (ω : Form n) (x : Coord (n + 1)) :
    Coord (n + 1) →L[ℝ] Coord (n + 1) :=
  ContinuousLinearMap.pi fun i => (-1 : ℝ) ^ i.val •
    (ContinuousAlternatingMap.apply ℝ _ ℝ (i.removeNth (standardBasis (n + 1)))).comp
      (fderiv ℝ ω x)

theorem hasFDerivAt_flux {n : ℕ} {ω : Form n} {x : Coord (n + 1)}
    (hω : DifferentiableAt ℝ ω x) : HasFDerivAt (flux ω) (fluxDeriv ω x) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact ((ContinuousAlternatingMap.apply ℝ _ ℝ
    (i.removeNth (standardBasis (n + 1)))).hasFDerivAt.comp x hω.hasFDerivAt).const_smul
      ((-1 : ℝ) ^ i.val)

/-- Evaluation of the exterior derivative on the standard basis is the
divergence of the signed coordinate coefficients of the form. -/
theorem extDeriv_eq_divergence {n : ℕ} (ω : Form n) (x : Coord (n + 1)) :
    extDeriv ω x (standardBasis (n + 1)) =
      ∑ i, fluxDeriv ω x (standardBasis (n + 1) i) i := by
  simp [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    fluxDeriv, smul_eq_mul]

/-- The tangent map of the coordinate face obtained by inserting a constant in
position `i`. -/
def faceTangent {n : ℕ} (i : Fin (n + 1)) : Coord n →L[ℝ] Coord (n + 1) where
  toFun := fun x => i.insertNth (α := fun _ => ℝ) 0 x
  map_add' x y := by
    funext j
    induction j using i.succAboveCases <;> simp
  map_smul' c x := by
    funext j
    induction j using i.succAboveCases <;> simp
  cont := continuous_const.finInsertNth i continuous_id

def faceEmbedding {n : ℕ} (i : Fin (n + 1)) (c : ℝ) : Coord n → Coord (n + 1) :=
  fun x => i.insertNth (α := fun _ => ℝ) c x

theorem hasFDerivAt_faceEmbedding {n : ℕ} (i : Fin (n + 1)) (c : ℝ) (x : Coord n) :
    HasFDerivAt (faceEmbedding i c) (faceTangent i) x := by
  have heq : faceEmbedding i c =
      fun y => i.insertNth (α := fun _ => ℝ) c 0 + faceTangent i y := by
    funext y j
    induction j using i.succAboveCases <;> simp [faceEmbedding, faceTangent]
  rw [heq]
  exact (faceTangent i).hasFDerivAt.const_add _

theorem fderiv_faceEmbedding {n : ℕ} (i : Fin (n + 1)) (c : ℝ) (x : Coord n) :
    fderiv ℝ (faceEmbedding i c) x = faceTangent i :=
  (hasFDerivAt_faceEmbedding i c x).fderiv

theorem faceTangent_standardBasis {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    faceTangent i (standardBasis n j) = standardBasis (n + 1) (i.succAbove j) := by
  funext l
  induction l using i.succAboveCases with
  | x => simp [faceTangent, standardBasis]
  | p l => simp [faceTangent, standardBasis, Pi.single_apply]

/-- Actual pullback by the affine face inclusion, using its Fréchet derivative. -/
def facePullback {n : ℕ} (ω : Form n) (i : Fin (n + 1)) (c : ℝ) :
    Coord n → Coord n [⋀^Fin n]→L[ℝ] ℝ :=
  fun x => (ω (faceEmbedding i c x)).compContinuousLinearMap
    (fderiv ℝ (faceEmbedding i c) x)

theorem facePullback_standardBasis {n : ℕ} (ω : Form n) (i : Fin (n + 1))
    (c : ℝ) (x : Coord n) :
    facePullback ω i c x (standardBasis n) = faceCoefficient ω i (i.insertNth c x) := by
  simp only [facePullback, fderiv_faceEmbedding, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    faceCoefficient, faceEmbedding]
  congr 1
  funext j
  exact faceTangent_standardBasis i j

def boundaryBoxIntegral {n : ℕ} (I : Box (Fin (n + 1))) (ω : Form n) : ℝ :=
  ∑ i : Fin (n + 1), (-1 : ℝ) ^ i.val •
    (BoxIntegral.integral (I.face i) IntegrationParams.GP
        (fun x => facePullback ω i (I.upper i) x (standardBasis n)) BoxAdditiveMap.volume -
      BoxIntegral.integral (I.face i) IntegrationParams.GP
        (fun x => facePullback ω i (I.lower i) x (standardBasis n)) BoxAdditiveMap.volume)

/-- Stokes for the generalized Perron box integral. Pointwise differentiability
on the closed box suffices for this version. -/
theorem hasBoxIntegral_extDeriv {n : ℕ} (I : Box (Fin (n + 1))) (ω : Form n)
    (hω : ∀ x ∈ Box.Icc I, DifferentiableAt ℝ ω x) :
    HasIntegral I IntegrationParams.GP (fun x => extDeriv ω x (standardBasis (n + 1)))
      BoxAdditiveMap.volume (boundaryBoxIntegral I ω) := by
  have hd := BoxIntegral.hasIntegral_GP_divergence_of_forall_hasDerivWithinAt I
    (flux ω) (fluxDeriv ω) ∅ Set.countable_empty (by simp)
    (by
      intro x hx
      exact (hasFDerivAt_flux (hω x hx.1)).hasFDerivWithinAt)
  simpa only [boundaryBoxIntegral, extDeriv_eq_divergence, standardBasis, flux,
    BoxIntegral.integral_smul, facePullback_standardBasis, smul_sub] using hd

theorem boxIntegral_extDeriv {n : ℕ} (I : Box (Fin (n + 1))) (ω : Form n)
    (hω : ∀ x ∈ Box.Icc I, DifferentiableAt ℝ ω x) :
    BoxIntegral.integral I IntegrationParams.GP
      (fun x => extDeriv ω x (standardBasis (n + 1))) BoxAdditiveMap.volume =
        boundaryBoxIntegral I ω :=
  (hasBoxIntegral_extDeriv I ω hω).integral_eq

theorem continuousOn_extDeriv_density {n : ℕ} (I : Box (Fin (n + 1))) (ω : Form n)
    (hω : ∀ x ∈ Box.Icc I, ContDiffAt ℝ 1 ω x) :
    ContinuousOn (fun x => extDeriv ω x (standardBasis (n + 1))) (Box.Icc I) := by
  have hD : ContinuousOn (fderiv ℝ ω) (Box.Icc I) :=
    fun x hx => ((hω x hx).continuousAt_fderiv (by decide)).continuousWithinAt
  exact (ContinuousAlternatingMap.apply ℝ _ ℝ (standardBasis (n + 1))).continuous.comp_continuousOn
    ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ _ ℝ).continuous.comp_continuousOn hD)

theorem continuousOn_face_density {n : ℕ} (I : Box (Fin (n + 1))) (ω : Form n)
    (hω : ContinuousOn ω (Box.Icc I)) (i : Fin (n + 1)) {c : ℝ}
    (hc : c ∈ Set.Icc (I.lower i) (I.upper i)) :
    ContinuousOn (fun x => facePullback ω i c x (standardBasis n)) (Box.Icc (I.face i)) := by
  have hcoef : ContinuousOn (faceCoefficient ω i) (Box.Icc I) :=
    (ContinuousAlternatingMap.apply ℝ _ ℝ
      (i.removeNth (standardBasis (n + 1)))).continuous.comp_continuousOn hω
  simpa only [facePullback_standardBasis, Function.comp_def] using Box.continuousOn_face_Icc hcoef hc

/-- Stokes' theorem on a rectangular box with the Lebesgue integral. The upper
face has sign `(-1)^i` and the lower face has its negative; face forms are actual
pullbacks along the affine coordinate inclusions. -/
theorem integral_extDeriv_eq_faces {n : ℕ} (I : Box (Fin (n + 1))) (ω : Form n)
    (hω : ∀ x ∈ Box.Icc I, ContDiffAt ℝ 1 ω x) :
    (∫ x in (I : Set (Coord (n + 1))), extDeriv ω x (standardBasis (n + 1))) =
      ∑ i : Fin (n + 1), (-1 : ℝ) ^ i.val •
        ((∫ x in (I.face i : Set (Coord n)), facePullback ω i (I.upper i) x (standardBasis n)) -
          ∫ x in (I.face i : Set (Coord n)), facePullback ω i (I.lower i) x (standardBasis n)) := by
  have hdiff : ∀ x ∈ Box.Icc I, DifferentiableAt ℝ ω x :=
    fun x hx => (hω x hx).differentiableAt (by decide)
  have hcont : ContinuousOn ω (Box.Icc I) := fun x hx => (hω x hx).continuousAt.continuousWithinAt
  have hbody := (MeasureTheory.ContinuousOn.hasBoxIntegral MeasureTheory.volume
    (continuousOn_extDeriv_density I ω hω) IntegrationParams.GP).integral_eq
  rw [← hbody, ← BoxAdditiveMap.volume, boxIntegral_extDeriv I ω hdiff]
  unfold boundaryBoxIntegral
  apply Finset.sum_congr rfl
  intro i hi
  have hu := (MeasureTheory.ContinuousOn.hasBoxIntegral MeasureTheory.volume
    (continuousOn_face_density I ω hcont i ⟨I.lower_le_upper i, le_rfl⟩)
    IntegrationParams.GP).integral_eq
  have hl := (MeasureTheory.ContinuousOn.hasBoxIntegral MeasureTheory.volume
    (continuousOn_face_density I ω hcont i ⟨le_rfl, I.lower_le_upper i⟩)
    IntegrationParams.GP).integral_eq
  simp only [BoxAdditiveMap.volume]
  rw [hu, hl]

/-- Closed-box version of Stokes. The change from half-open box integrals to
closed rectangles uses equality almost everywhere, including zero-dimensional
faces when `n = 0`. -/
theorem integral_Icc_extDeriv_eq_faces {n : ℕ} (I : Box (Fin (n + 1))) (ω : Form n)
    (hω : ∀ x ∈ Box.Icc I, ContDiffAt ℝ 1 ω x) :
    (∫ x in Box.Icc I, extDeriv ω x (standardBasis (n + 1))) =
      ∑ i : Fin (n + 1), (-1 : ℝ) ^ i.val •
        ((∫ x in Box.Icc (I.face i), facePullback ω i (I.upper i) x (standardBasis n)) -
          ∫ x in Box.Icc (I.face i), facePullback ω i (I.lower i) x (standardBasis n)) := by
  simp only [← MeasureTheory.setIntegral_congr_set (Box.coe_ae_eq_Icc _)]
  exact integral_extDeriv_eq_faces I ω hω

theorem integrableOn_extDeriv_density {n : ℕ} (I : Box (Fin (n + 1))) (ω : Form n)
    (hω : ∀ x ∈ Box.Icc I, ContDiffAt ℝ 1 ω x) :
    MeasureTheory.IntegrableOn (fun x => extDeriv ω x (standardBasis (n + 1))) (Box.Icc I) :=
  (continuousOn_extDeriv_density I ω hω).integrableOn_compact I.isCompact_Icc

theorem integrableOn_face_density {n : ℕ} (I : Box (Fin (n + 1))) (ω : Form n)
    (hω : ContinuousOn ω (Box.Icc I)) (i : Fin (n + 1)) {c : ℝ}
    (hc : c ∈ Set.Icc (I.lower i) (I.upper i)) :
    MeasureTheory.IntegrableOn (fun x => facePullback ω i c x (standardBasis n)) (Box.Icc (I.face i)) :=
  (continuousOn_face_density I ω hω i hc).integrableOn_compact (I.face i).isCompact_Icc

/-- The oriented boundary integral of a closed form vanishes on a box. -/
theorem boundary_integral_eq_zero_of_closed {n : ℕ} (I : Box (Fin (n + 1))) (ω : Form n)
    (hω : ∀ x ∈ Box.Icc I, ContDiffAt ℝ 1 ω x)
    (hclosed : ∀ x ∈ Box.Icc I, extDeriv ω x = 0) :
    (∑ i : Fin (n + 1), (-1 : ℝ) ^ i.val •
      ((∫ x in Box.Icc (I.face i), facePullback ω i (I.upper i) x (standardBasis n)) -
        ∫ x in Box.Icc (I.face i), facePullback ω i (I.lower i) x (standardBasis n))) = 0 := by
  rw [← integral_Icc_extDeriv_eq_faces I ω hω]
  apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
  intro x hx
  simp [hclosed x hx]

end EnvelopingIsomorphism.Deformation.Kontsevich.BoxStokes
