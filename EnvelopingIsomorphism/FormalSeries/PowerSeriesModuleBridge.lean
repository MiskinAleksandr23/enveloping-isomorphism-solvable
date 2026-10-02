import EnvelopingIsomorphism.FormalSeries.PowerSeriesModule
import EnvelopingIsomorphism.Deformation.FormalConjugation

/-! The vector-series model agrees with standard power series when its coefficient
module is an algebra. Formal exponentials preserve arbitrary formal bilinear
operations whenever their generator is an actual derivation of that operation. -/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.PowerSeriesModuleBridge

open EnvelopingIsomorphism.Deformation
open EnvelopingIsomorphism.Deformation.NilpotentConjugation
open EnvelopingIsomorphism.Deformation.FormalConjugation
open PowerSeriesModule

section Bridge

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- The additive bridge from vector-valued Hahn series to standard power series. -/
def addEquiv : PowerSeriesModule k A ≃+ PowerSeries A where
  toEquiv := (HahnModule.of k).symm.trans HahnSeries.toPowerSeries.toEquiv
  map_add' p q := by
    change HahnSeries.toPowerSeries ((HahnModule.of k).symm (p + q)) = _
    rw [HahnModule.of_symm_add, map_add]
    rfl

@[simp] theorem coeff_addEquiv (p : PowerSeriesModule k A) (n : ℕ) :
    PowerSeries.coeff n (addEquiv p) = coeffV n p :=
  HahnSeries.coeff_toPowerSeries

/-- The bridge is linear over the full scalar power-series ring. -/
def moduleEquiv : PowerSeriesModule k A ≃ₗ[PowerSeries k] PowerSeries A where
  toAddEquiv := addEquiv
  map_smul' a p := by
    ext n
    change PowerSeries.coeff n (addEquiv (a • p)) = PowerSeries.coeff n (a • addEquiv p)
    rw [coeff_addEquiv, coeffV_series_smul]
    simp only [Algebra.smul_def, PowerSeries.algebraMap_apply'', PowerSeries.coeff_mul,
      PowerSeries.coeff_map, coeff_addEquiv]

@[simp] theorem coeff_moduleEquiv (p : PowerSeriesModule k A) (n : ℕ) :
    PowerSeries.coeff n (moduleEquiv p) = coeffV n p := coeff_addEquiv p n

@[simp] theorem coeff_moduleEquiv_symm (p : PowerSeries A) (n : ℕ) :
    coeffV n ((moduleEquiv (k := k)).symm p) = PowerSeries.coeff n p := rfl

theorem moduleEquiv_actV (F : PowerSeries (Module.End k A)) (p : PowerSeriesModule k A) :
    moduleEquiv (actV F p) = EndomorphismSeries.act F (moduleEquiv p) := by
  ext n
  simp only [coeff_moduleEquiv, coeffV_actV, EndomorphismSeries.coeff_act]

theorem moduleEquiv_symm_act (F : PowerSeries (Module.End k A)) (p : PowerSeries A) :
    (moduleEquiv (k := k)).symm (EndomorphismSeries.act F p) =
      actV F ((moduleEquiv (k := k)).symm p) := by
  apply (moduleEquiv (k := k)).injective
  rw [LinearEquiv.apply_symm_apply, moduleEquiv_actV, LinearEquiv.apply_symm_apply]

/-- Transport the actual completed binary convolution to the standard series model. -/
def binaryBridge (B : PowerSeriesModule k (Binary k A)) :
    Binary (PowerSeries k) (PowerSeries A) :=
  (((extendBinary B).comp moduleEquiv.symm.toLinearMap).compl₂
    moduleEquiv.symm.toLinearMap).compr₂ moduleEquiv.toLinearMap

@[simp] theorem binaryBridge_apply (B : PowerSeriesModule k (Binary k A)) (p q : PowerSeries A) :
    binaryBridge B p q = moduleEquiv (extendBinary B (moduleEquiv.symm p) (moduleEquiv.symm q)) := rfl

theorem moduleEquiv_extendBinary (B : PowerSeriesModule k (Binary k A)) (p q : PowerSeriesModule k A) :
    moduleEquiv (extendBinary B p q) = binaryBridge B (moduleEquiv p) (moduleEquiv q) := by
  simp

end Bridge

section FiniteExponential

variable {k V : Type*} [CommRing k] [Algebra ℚ k] [AddCommGroup V] [Module k V] [Module ℚ V]

/-- The finite nilpotent exponential preserves any bilinear operation for which
its generator satisfies Leibniz. No ring structure on the vector space is assumed. -/
theorem nilpotent_exp_preserves_binary (D : Module.End k V) (hD : IsNilpotent D)
    (μ : Binary k V) (hder : ∀ x y, D (μ x y) = μ (D x) y + μ x (D y)) (x y : V) :
    IsNilpotent.exp D (μ x y) = μ (IsNilpotent.exp D x) (IsNilpotent.exp D y) := by
  letI : Module (Module.End k (Binary k V)) (Binary k V) := Module.End.applyModule
  have hzero : unaryActionEnd D μ = 0 := by
    ext a b
    simp only [unaryActionEnd, LinearMap.sub_apply, output_apply, inputLeft_apply,
      inputRight_apply, LinearMap.zero_apply, hder]
    abel
  have hkill : (unaryActionEnd D ^ 1) • μ = 0 := by
    change (unaryActionEnd D ^ 1) μ = 0
    simpa only [pow_one] using hzero
  have hfix : IsNilpotent.exp (unaryActionEnd D) μ = μ := by
    simpa using IsNilpotent.exp_smul_eq_sum
      (A := Module.End k (Binary k V)) (M := Binary k V)
      hkill (isNilpotent_unaryActionEnd hD)
  have hc : conjugate (expEquiv D hD) μ = μ :=
    (conjugate_expEquiv hD μ).trans hfix
  exact (conjugate_eq_iff (expEquiv D hD) μ μ).mp hc x y

end FiniteExponential

section CompleteExponential

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
variable [Algebra ℚ k] [Algebra ℚ A]

/-- A complete positive derivation of an arbitrary jet-compatible binary operation
exponentiates to a genuine intertwiner of that operation. -/
theorem exp_act_preserves_binary (F : PowerSeries (Module.End k A))
    (hF : PowerSeries.constantCoeff F = 0) (μ : Binary k (PowerSeries A))
    (hμ : RespectsJets μ)
    (hder : ∀ p q, EndomorphismSeries.act F (μ p q) =
      μ (EndomorphismSeries.act F p) q + μ p (EndomorphismSeries.act F q))
    (p q : PowerSeries A) :
    EndomorphismSeries.act (FormalSeries.exp F) (μ p q) =
      μ (EndomorphismSeries.act (FormalSeries.exp F) p)
        (EndomorphismSeries.act (FormalSeries.exp F) q) := by
  apply FormalSeries.ext_of_toJet_eq
  intro N
  have hjet : ∀ x y : Jet A N,
      EndomorphismSeries.actionJetHom N F (jetBinary μ hμ N x y) =
        jetBinary μ hμ N (EndomorphismSeries.actionJetHom N F x) y +
          jetBinary μ hμ N x (EndomorphismSeries.actionJetHom N F y) := by
    intro x y
    induction x using Quotient.inductionOn with | h x
    induction y using Quotient.inductionOn with | h y
    change toJet N (EndomorphismSeries.act F (μ x y)) =
      toJet N (μ (EndomorphismSeries.act F x) y) + toJet N (μ x (EndomorphismSeries.act F y))
    rw [hder, map_add]
  have h := nilpotent_exp_preserves_binary (EndomorphismSeries.actionJetHom N F)
    (EndomorphismSeries.isNilpotent_actionJetHom hF N) (jetBinary μ hμ N) hjet
    (toJet N p) (toJet N q)
  rw [← EndomorphismSeries.actionJetHom_exp hF N] at h
  simpa only [jetBinary_toJet, EndomorphismSeries.actionJetHom_toJet] using h

/-- The actual full vector-series exponential stabilizes the actual binary convolution.
The coefficient algebra is commutative; the supplied binary operation is arbitrary. -/
theorem exp_actV_extendBinary (F : PowerSeries (Module.End k A))
    (hF : PowerSeries.constantCoeff F = 0) (B : PowerSeriesModule k (Binary k A))
    (hder : ∀ p q : PowerSeriesModule k A, actV F (extendBinary B p q) =
      extendBinary B (actV F p) q + extendBinary B p (actV F q))
    (p q : PowerSeriesModule k A) :
    actV (FormalSeries.exp F) (extendBinary B p q) =
      extendBinary B (actV (FormalSeries.exp F) p) (actV (FormalSeries.exp F) q) := by
  let μ : Binary k (PowerSeries A) := (binaryBridge B).restrictScalars₁₂ k k
  have hμ : RespectsJets μ := respectsJets_of_powerSeriesBilinear (binaryBridge B)
  have hd : ∀ x y, EndomorphismSeries.act F (μ x y) =
      μ (EndomorphismSeries.act F x) y + μ x (EndomorphismSeries.act F y) := by
    intro x y
    change EndomorphismSeries.act F (binaryBridge B x y) =
      binaryBridge B (EndomorphismSeries.act F x) y + binaryBridge B x (EndomorphismSeries.act F y)
    have h := congrArg moduleEquiv (hder (moduleEquiv.symm x) (moduleEquiv.symm y))
    simpa only [binaryBridge_apply, moduleEquiv_actV,
      moduleEquiv_symm_act, map_add] using h
  apply moduleEquiv.injective
  simp only [moduleEquiv_actV, moduleEquiv_extendBinary]
  exact exp_act_preserves_binary F hF μ hμ hd (moduleEquiv p) (moduleEquiv q)

end CompleteExponential

end EnvelopingIsomorphism.FormalSeries.PowerSeriesModuleBridge
