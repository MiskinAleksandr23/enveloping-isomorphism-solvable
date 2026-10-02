import EnvelopingIsomorphism.Deformation.HochschildDGLA

/-! Maurer-Cartan curvature and its exact associative-algebra interpretation. -/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable {K : Type u} [Field K]

namespace SignedDGLA

variable (D : SignedDGLA.{u, v} K)

def curvature (α : D.Obj 1) : D.Obj 2 :=
  gradedModuleCongr K D.complex.X (by decide : (1 : ℤ) + 1 = 2)
    (D.d 1 α + (2 : K)⁻¹ • D.bracket 1 1 α α)

def IsMaurerCartan (α : D.Obj 1) : Prop := D.curvature α = 0

theorem isMaurerCartan_zero : D.IsMaurerCartan 0 := by
  unfold IsMaurerCartan curvature
  simp only [map_zero, smul_zero, add_zero]

/-- Infinitesimal gauge motion, in the convention e^X α = [X,α]−dX to first order. -/
def infinitesimalGauge (X : D.Obj 0) (α : D.Obj 1) : D.Obj 1 :=
  D.zeroAction 1 X α - gradedModuleCongr K D.complex.X (by decide : (0 : ℤ) + 1 = 1) (D.d 0 X)

@[simp] theorem infinitesimalGauge_zero (X : D.Obj 0) :
    D.infinitesimalGauge X 0 =
      -gradedModuleCongr K D.complex.X (by decide : (0 : ℤ) + 1 = 1) (D.d 0 X) := by
  rw [infinitesimalGauge, map_zero, zero_sub]

end SignedDGLA

variable [CharZero K] {A : Type v} [AddCommGroup A] [Module K A]

theorem hochschild_curvature (μ : Binary K A)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c)) (η : Binary K A) :
    (hochschildDGLA μ hμ).curvature η = differentialTwo μ η + insertBinary η η := by
  have hd : fullDifferential μ 1 η = differentialTwo μ η := by
    change curriedDifferential μ 1 η = differentialTwo μ η
    rw [curriedDifferential_eq_bracket, curriedBracket_binary_binary]
    rfl
  have hD : (hochschildDGLA μ hμ).d 1 η = differentialTwo μ η := by
    change ((fullComplex μ hμ).d 1 (1 + 1)).hom η = _
    rw [fullComplex_d]
    exact hd
  let delta : Ternary K A := (hochschildDGLA μ hμ).d 1 η
  have hdelta : delta = differentialTwo μ η := hD
  let beta : Ternary K A := (hochschildDGLA μ hμ).bracket 1 1 η η
  have hbeta : beta = insertBinary η η + insertBinary η η := by
    change curriedBracket 1 1 η η = _
    rw [curriedBracket_binary_binary]
    rfl
  change delta + (2 : K)⁻¹ • beta = _
  rw [hdelta, hbeta]
  rw [← two_smul K (insertBinary η η), smul_smul,
    inv_mul_cancel₀ (show (2 : K) ≠ 0 from two_ne_zero), one_smul]

/-- Actual Hochschild Maurer-Cartan elements are exactly associative perturbations. -/
theorem hochschild_isMaurerCartan_iff (μ : Binary K A)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c)) (η : Binary K A) :
    (hochschildDGLA μ hμ).IsMaurerCartan η ↔
      ∀ a b c, (μ + η) ((μ + η) a b) c = (μ + η) a ((μ + η) b c) := by
  change (hochschildDGLA μ hμ).curvature η = 0 ↔ _
  rw [hochschild_curvature]
  change differentialTwo μ η + insertBinary η η = 0 ↔ _
  exact maurerCartan_iff_associative μ η hμ

end EnvelopingIsomorphism.Deformation
