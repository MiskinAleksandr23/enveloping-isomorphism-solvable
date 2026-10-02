import EnvelopingIsomorphism.Deformation.Kontsevich.SignedFormChangeVariables
import EnvelopingIsomorphism.Deformation.Kontsevich.UnorientedFormIntegrability
import EnvelopingIsomorphism.Deformation.Kontsevich.OrthantInteriorIntegration

/-! Finite oriented Stokes assembly from genuine compact local forms. All
signed integral identities and native integrability are proved here from
local derivative matching, support bounds, and actual coordinate changes. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.OrientedOrthantAssembly

open Set MeasureTheory BoxStokes CompactOrthantStokes OrthantInteriorIntegration
open OrientedFormChangeVariables
open scoped Topology Classical

variable {r : ℕ}

def lowerFaces (θ : Form r) (S : Finset (Fin (r + 1))) : ℝ :=
  ∑ j ∈ S, -((-1 : ℝ) ^ j.val) •
    ∫ z in orthant (faceIndices S j), facePullback θ j 0 z (standardBasis r)

theorem isOpen_strictOrthant (S : Finset (Fin (r + 1))) : IsOpen (strictOrthant S) := by
  change IsOpen {z : Coord (r + 1) | ∀ j ∈ S, 0 < z j}
  simp only [setOf_forall]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro _
  exact isOpen_lt continuous_const (continuous_apply j)

/-- Compact derivative densities localize to the actual positive chart
region. Coordinate hyperplanes contribute no measure. -/
theorem integral_extDeriv_eq_region (θ : Form r) (S : Finset (Fin (r + 1)))
    (U : Set (Coord (r + 1))) (hUS : U ⊆ strictOrthant S)
    (hsupp : tsupport θ ∩ strictOrthant S ⊆ U) :
    (∫ z in orthant S, density (extDeriv θ) z) = ∫ z in U, density (extDeriv θ) z := by
  rw [integral_orthant_eq_strictOrthant]
  exact CompactSupportBoxes.setIntegral_extDeriv_density_eq_of_subset θ
    (strictOrthant S) U (isOpen_strictOrthant S).measurableSet hUS hsupp

/-- Both native L1 and the signed lower-face identity are consequences of
the actual compact source form; neither integral identity is a premise. -/
theorem exists_signed_local_identity
    (e : OpenPartialHomeomorph (Coord (r + 1)) (Coord (r + 1)))
    (he : ContDiffOn ℝ 1 e e.source) (hinv : ContDiffOn ℝ 1 e.symm e.target)
    (U V : Set (Coord (r + 1))) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hUe : U ⊆ e.source) (hconn : IsPreconnected U) (himage : e '' U ⊆ V)
    (S : Finset (Fin (r + 1))) (hUS : U ⊆ strictOrthant S)
    (θ ψ : Form r) (hθ : ContDiff ℝ 1 θ) (hcθ : HasCompactSupport θ)
    (hsupp : tsupport θ ∩ strictOrthant S ⊆ U)
    (hmatch : EqOn (extDeriv θ) (pullback e (extDeriv ψ)) U)
    (hzero : ∀ y ∈ V \ (e '' U), density (extDeriv ψ) y = 0) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      (∀ z ∈ U, ε * jacobian e z = |jacobian e z|) ∧
      IntegrableOn (density (extDeriv ψ)) V ∧
      ε * lowerFaces θ S = ∫ y in V, density (extDeriv ψ) y := by
  obtain ⟨ε, hε, hsign⟩ := SignedFormChangeVariables.exists_sign e he hinv U hUe hconn
  have hsource : IntegrableOn (density (pullback e (extDeriv ψ))) U := by
    apply (integrableOn_congr_fun (fun z hz => congrArg (fun A => A (standardBasis (r + 1)))
      (hmatch hz).symm) hU).mpr
    exact (CompactSupportBoxes.integrable_extDeriv_density θ hθ hcθ).integrableOn
  have hnative : IntegrableOn (density (extDeriv ψ)) V :=
    (UnorientedFormIntegrability.integrableOn_domain_iff_pullback e U V hU hV
      (fun z hz => he.contDiffAt (e.open_source.mem_nhds (hUe hz))) (e.injOn.mono hUe)
      himage (extDeriv ψ) hzero).mpr hsource
  refine ⟨ε, hε, hsign, hnative, ?_⟩
  have hstokes := CompactOrthantStokes.integral_extDeriv_eq_lower_faces θ S hθ hcθ
  change (∫ z in orthant S, density (extDeriv θ) z) = lowerFaces θ S at hstokes
  rw [← hstokes, integral_extDeriv_eq_region θ S U hUS hsupp]
  calc
    ε * (∫ z in U, density (extDeriv θ) z) =
        ε * (∫ z in U, density (pullback e (extDeriv ψ)) z) := by
      congr 1
      exact setIntegral_congr_fun hU (fun z hz => congrArg (fun A => A (standardBasis (r + 1))) (hmatch hz))
    _ = ∫ y in e '' U, density (extDeriv ψ) y :=
      SignedFormChangeVariables.sign_mul_integral_pullback_eq_image e he U hU hUe ε hsign (extDeriv ψ)
    _ = ∫ y in V, density (extDeriv ψ) y :=
      (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hV himage hzero).symm

/-- A finite family of actual source charts gives zero total oriented lower
faces whenever the original exterior derivatives cancel pointwise. -/
theorem exists_finite_signed_boundary_cancellation {J : Type*} [Fintype J]
    (e : J → OpenPartialHomeomorph (Coord (r + 1)) (Coord (r + 1)))
    (he : ∀ j, ContDiffOn ℝ 1 (e j) (e j).source)
    (hinv : ∀ j, ContDiffOn ℝ 1 (e j).symm (e j).target)
    (U : J → Set (Coord (r + 1))) (V : Set (Coord (r + 1)))
    (hU : ∀ j, MeasurableSet (U j)) (hV : MeasurableSet V)
    (hUe : ∀ j, U j ⊆ (e j).source) (hconn : ∀ j, IsPreconnected (U j))
    (himage : ∀ j, e j '' U j ⊆ V)
    (S : J → Finset (Fin (r + 1))) (hUS : ∀ j, U j ⊆ strictOrthant (S j))
    (θ ψ : J → Form r) (hθ : ∀ j, ContDiff ℝ 1 (θ j))
    (hcθ : ∀ j, HasCompactSupport (θ j))
    (hsupp : ∀ j, tsupport (θ j) ∩ strictOrthant (S j) ⊆ U j)
    (hmatch : ∀ j, EqOn (extDeriv (θ j)) (pullback (e j) (extDeriv (ψ j))) (U j))
    (hzero : ∀ j, ∀ y ∈ V \ (e j '' U j), density (extDeriv (ψ j)) y = 0)
    (hcancel : ∀ y ∈ V, ∑ j, extDeriv (ψ j) y = 0) :
    ∃ ε : J → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧
      (∀ j, ∀ z ∈ U j, ε j * jacobian (e j) z = |jacobian (e j) z|) ∧
      (∀ j, IntegrableOn (density (extDeriv (ψ j))) V) ∧
      ∑ j, ε j * lowerFaces (θ j) (S j) = 0 := by
  choose ε hε hsign hL1 hint using fun j => exists_signed_local_identity
    (e j) (he j) (hinv j) (U j) V (hU j) hV (hUe j) (hconn j) (himage j)
    (S j) (hUS j) (θ j) (ψ j) (hθ j) (hcθ j) (hsupp j) (hmatch j) (hzero j)
  refine ⟨ε, hε, hsign, hL1, ?_⟩
  simp_rw [hint]
  rw [← integral_finsetSum Finset.univ (fun j _ => hL1 j)]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  have h := congrArg (fun A => A (standardBasis (r + 1))) (hcancel y hy)
  change (∑ j, extDeriv (ψ j) y) (standardBasis (r + 1)) = 0 at h
  simpa only [density, ContinuousAlternatingMap.sum_apply] using h

end EnvelopingIsomorphism.Deformation.Kontsevich.OrientedOrthantAssembly
