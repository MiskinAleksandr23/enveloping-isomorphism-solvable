import EnvelopingIsomorphism.Deformation.NilpotentConjugation
import EnvelopingIsomorphism.FormalSeries.PowerSeriesJetAction

/-! Complete formal gauge conjugation. The adjoint exponential is defined
coefficientwise by actual finite nilpotent exponentials on jets, not by choosing
unrelated gauge transformations at each finite order. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.FormalConjugation

open PowerSeries EnvelopingIsomorphism.FormalSeries
open EnvelopingIsomorphism.FormalSeries.EndomorphismSeries
open NilpotentConjugation

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]

/-- A complete bilinear cochain respects every finite formal quotient. -/
def RespectsJets (μ : Binary k (PowerSeries A)) : Prop :=
  ∀ N p p' q q', toJet N p = toJet N p' → toJet N q = toJet N q' →
    toJet N (μ p q) = toJet N (μ p' q')

private def jetBinaryFn (μ : Binary k (PowerSeries A)) (hμ : RespectsJets μ) (N : ℕ)
    (p q : Jet A N) : Jet A N :=
  Quotient.liftOn₂ p q (fun p q ↦ toJet N (μ p q)) (by
    intro p p' q q' hp hq
    exact hμ N p q p' q' (toJet_eq_iff.mpr hp) (toJet_eq_iff.mpr hq))

/-- The bilinear product induced on one finite jet. -/
def jetBinary (μ : Binary k (PowerSeries A)) (hμ : RespectsJets μ) (N : ℕ) :
    Binary k (Jet A N) :=
  LinearMap.mk₂ k (jetBinaryFn μ hμ N)
    (fun p p' q ↦ Quotient.inductionOn₃ p p' q fun a a' b ↦ by
      change toJet N (μ (a + a') b) = toJet N (μ a b) + toJet N (μ a' b)
      simp [map_add])
    (fun c p q ↦ Quotient.inductionOn₂ p q fun a b ↦ by
      change toJet N (μ (c • a) b) = c • toJet N (μ a b)
      simp only [map_smul, LinearMap.smul_apply]
      rfl)
    (fun p q q' ↦ Quotient.inductionOn₃ p q q' fun a b b' ↦ by
      change toJet N (μ a (b + b')) = toJet N (μ a b) + toJet N (μ a b')
      simp [map_add])
    (fun c p q ↦ Quotient.inductionOn₂ p q fun a b ↦ by
      change toJet N (μ a (c • b)) = c • toJet N (μ a b)
      rw [map_smul]
      rfl)

@[simp] theorem jetBinary_toJet (μ : Binary k (PowerSeries A)) (hμ : RespectsJets μ)
    (N : ℕ) (p q : PowerSeries A) :
    jetBinary μ hμ N (toJet N p) (toJet N q) = toJet N (μ p q) := rfl

/-- Extract degree n from a jet known through degree n. -/
def jetCoeff (n : ℕ) : Jet A (n + 1) →ₗ[k] A where
  toFun z := Quotient.liftOn z (coeff n) (fun p q hpq ↦ hpq n (Nat.lt_succ_self n))
  map_add' z w := Quotient.inductionOn₂ z w fun p q ↦ by
    change coeff n (p + q) = coeff n p + coeff n q
    rw [map_add]
  map_smul' c z := Quotient.inductionOn z fun p ↦ by
    change coeff n (c • p) = c • coeff n p
    rw [PowerSeries.coeff_smul]

@[simp] theorem jetCoeff_toJet (n : ℕ) (p : PowerSeries A) :
    jetCoeff (k := k) n (toJet (n + 1) p) = coeff n p := rfl

theorem toJet_eq_iff_X_pow_dvd_sub {N : ℕ} {p q : PowerSeries A} :
    toJet N p = toJet N q ↔ (X : PowerSeries A) ^ N ∣ p - q := by
  rw [toJet_eq_iff, PowerSeries.X_pow_dvd_iff]
  simp only [map_sub, sub_eq_zero]

section ScalarLinear

variable {B : Type*} [CommRing B] [Algebra k B]

instance powerSeriesScalarTower : IsScalarTower k (PowerSeries k) (PowerSeries B) :=
  IsScalarTower.of_algebraMap_eq fun c ↦ by
    rw [PowerSeries.algebraMap_apply, PowerSeries.algebraMap_apply'',
      PowerSeries.algebraMap_apply, PowerSeries.map_C]
    simp

/-- Linearity over all formal scalars automatically preserves every finite jet. -/
theorem linear_respectsJets (f : PowerSeries B →ₗ[PowerSeries k] PowerSeries B)
    {N : ℕ} {p q : PowerSeries B} (hpq : toJet N p = toJet N q) :
    toJet N (f p) = toJet N (f q) := by
  rw [toJet_eq_iff_X_pow_dvd_sub] at hpq ⊢
  obtain ⟨s, hs⟩ := hpq
  refine ⟨f s, ?_⟩
  have hscalar (z : PowerSeries B) :
      (X : PowerSeries k) ^ N • z = (X : PowerSeries B) ^ N * z := by
    rw [Algebra.smul_def, map_pow, PowerSeries.algebraMap_apply'', PowerSeries.map_X]
  rw [← map_sub, hs, ← hscalar, map_smul, hscalar]

/-- Every bilinear cochain over `k[[t]]` satisfies the finite-jet condition used
in the complete conjugation theorem. -/
theorem respectsJets_of_powerSeriesBilinear
    (μ : Binary (PowerSeries k) (PowerSeries B)) :
    RespectsJets (μ.restrictScalars₁₂ k k) := by
  intro N p p' q q' hp hq
  change toJet N (μ p q) = toJet N (μ p' q')
  exact (linear_respectsJets (μ.flip q) hp).trans (linear_respectsJets (μ p') hq)

end ScalarLinear

section Rational

variable [Algebra ℚ k] [Algebra ℚ A]

/-- The finite-jet coordinate change induced by one fixed complete formal
exponential. -/
def expJetEquiv (F : PowerSeries (Module.End k A)) (hF : constantCoeff F = 0) (N : ℕ) :
    Jet A N ≃ₗ[k] Jet A N :=
  expEquiv (actionJetHom N F) (isNilpotent_actionJetHom hF N)

theorem expJetEquiv_toJet (F : PowerSeries (Module.End k A)) (hF : constantCoeff F = 0)
    (N : ℕ) (p : PowerSeries A) :
    expJetEquiv F hF N (toJet N p) = toJet N (expLinearEquiv F hF p) := by
  change IsNilpotent.exp (actionJetHom N F) (toJet N p) = toJet N (act (exp F) p)
  rw [← actionJetHom_exp hF N, actionJetHom_toJet]

theorem expJetEquiv_symm_toJet (F : PowerSeries (Module.End k A)) (hF : constantCoeff F = 0)
    (N : ℕ) (p : PowerSeries A) :
    (expJetEquiv F hF N).symm (toJet N p) = toJet N ((expLinearEquiv F hF).symm p) := by
  apply (expJetEquiv F hF N).injective
  rw [LinearEquiv.apply_symm_apply, expJetEquiv_toJet, LinearEquiv.apply_symm_apply]

/-- The complete conjugation induces actual conjugation of every finite jet. -/
theorem conjugate_toJet (F : PowerSeries (Module.End k A)) (hF : constantCoeff F = 0)
    (μ : Binary k (PowerSeries A)) (hμ : RespectsJets μ) (N : ℕ) (p q : PowerSeries A) :
    toJet N (conjugate (expLinearEquiv F hF) μ p q) =
      conjugate (expJetEquiv F hF N) (jetBinary μ hμ N) (toJet N p) (toJet N q) := by
  rw [conjugate_apply, conjugate_apply, expJetEquiv_symm_toJet, expJetEquiv_symm_toJet,
    jetBinary_toJet, expJetEquiv_toJet]

/-- A precise finite coefficient formula for the adjoint exponential of a
complete cochain. Every exponential on the right is a finite nilpotent one. -/
def adjointExpApply (F : PowerSeries (Module.End k A)) (hF : constantCoeff F = 0)
    (μ : Binary k (PowerSeries A)) (hμ : RespectsJets μ) (p q : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk fun n ↦ jetCoeff (k := k) n
    (adjointExponential (actionJetHom (n + 1) F)
      (jetBinary μ hμ (n + 1)) (toJet (n + 1) p) (toJet (n + 1) q))

/-- Full formal conjugation equals the full adjoint exponential. This is an
equality of complete series, obtained from one fixed formal coordinate change. -/
theorem conjugate_eq_adjointExpApply (F : PowerSeries (Module.End k A))
    (hF : constantCoeff F = 0) (μ : Binary k (PowerSeries A)) (hμ : RespectsJets μ)
    (p q : PowerSeries A) :
    conjugate (expLinearEquiv F hF) μ p q = adjointExpApply F hF μ hμ p q := by
  ext n
  rw [adjointExpApply, coeff_mk]
  have h := conjugate_toJet F hF μ hμ (n + 1) p q
  rw [expJetEquiv, conjugate_expEquiv] at h
  have hc := congrArg (jetCoeff (k := k) n) h
  simpa only [jetCoeff_toJet, adjointExponential] using hc

/-- The complete adjoint exponential as a bilinear cochain. Its definition
uses coefficientwise finite nilpotent exponentials. -/
def adjointExp (F : PowerSeries (Module.End k A)) (hF : constantCoeff F = 0)
    (μ : Binary k (PowerSeries A)) (hμ : RespectsJets μ) : Binary k (PowerSeries A) :=
  LinearMap.mk₂ k (adjointExpApply F hF μ hμ)
    (by intros; simp only [← conjugate_eq_adjointExpApply, map_add, LinearMap.add_apply])
    (by intros; simp only [← conjugate_eq_adjointExpApply, map_smul, LinearMap.smul_apply])
    (by intros; simp only [← conjugate_eq_adjointExpApply, map_add])
    (by intros; simp only [← conjugate_eq_adjointExpApply, map_smul])

/-- Genuine complete gauge transport equals `exp([X,-])`. -/
theorem conjugate_eq_adjointExp (F : PowerSeries (Module.End k A))
    (hF : constantCoeff F = 0) (μ : Binary k (PowerSeries A)) (hμ : RespectsJets μ) :
    conjugate (expLinearEquiv F hF) μ = adjointExp F hF μ hμ := by
  apply LinearMap.ext
  intro p
  apply LinearMap.ext
  intro q
  exact conjugate_eq_adjointExpApply F hF μ hμ p q

end Rational

end EnvelopingIsomorphism.Deformation.FormalConjugation
