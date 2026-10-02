import EnvelopingIsomorphism.Deformation.Gauge.ReflectionLimit
import EnvelopingIsomorphism.FormalSeries.BinaryAssociator
import EnvelopingIsomorphism.FormalSeries.PowerSeriesModuleBridge

/-! A reflected invertible operator preserving the ordinary product gives a
genuine algebra equivalence on the native complete power-series algebra. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

theorem extendBinary_single_zero (μ : Binary k A) (p q : PowerSeriesModule k A) :
    extendBinary (single 0 μ) p q = extendBilinear μ p q := by
  rw [extendBinary_apply]
  change linearApply (applyBilinear (LinearMap.id : Binary k A →ₗ[k] A →ₗ[k] (A →ₗ[k] A))
    (single 0 μ) p) q = _
  rw [applyBilinear_single_zero_left]
  ext n
  rfl

/-- The ordinary coefficient product gives the native product on actual series. -/
theorem moduleEquiv_ordinary_mul (p q : PowerSeriesModule k A) :
    PowerSeriesModuleBridge.moduleEquiv
      (extendBinary (single 0 (LinearMap.mul k A)) p q) =
        PowerSeriesModuleBridge.moduleEquiv p * PowerSeriesModuleBridge.moduleEquiv q := by
  ext n
  rw [PowerSeriesModuleBridge.coeff_moduleEquiv, extendBinary_single_zero,
    extendBilinear_apply, coeffV_applyBilinear, PowerSeries.coeff_mul]
  simp only [PowerSeriesModuleBridge.coeff_moduleEquiv]
  rfl

/-- Transport a vector-series equivalence through the canonical native-series bridge. -/
def nativeLinearEquiv (g : PowerSeriesModule k A ≃ₗ[PowerSeries k] PowerSeriesModule k A) :
    PowerSeries A ≃ₗ[PowerSeries k] PowerSeries A :=
  PowerSeriesModuleBridge.moduleEquiv.symm.trans (g.trans PowerSeriesModuleBridge.moduleEquiv)

@[simp] theorem nativeLinearEquiv_apply
    (g : PowerSeriesModule k A ≃ₗ[PowerSeries k] PowerSeriesModule k A) (p : PowerSeries A) :
    nativeLinearEquiv g p = PowerSeriesModuleBridge.moduleEquiv
      (g (PowerSeriesModuleBridge.moduleEquiv.symm p)) := rfl

theorem nativeLinearEquiv_mul
    (g : PowerSeriesModule k A ≃ₗ[PowerSeries k] PowerSeriesModule k A)
    (hg : ∀ p q, g (extendBinary (single 0 (LinearMap.mul k A)) p q) =
      extendBinary (single 0 (LinearMap.mul k A)) (g p) (g q)) (p q : PowerSeries A) :
    nativeLinearEquiv g (p * q) = nativeLinearEquiv g p * nativeLinearEquiv g q := by
  let e := PowerSeriesModuleBridge.moduleEquiv (k := k) (A := A)
  have h : e.symm (p * q) = extendBinary (single 0 (LinearMap.mul k A)) (e.symm p) (e.symm q) := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, moduleEquiv_ordinary_mul,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  change e (g (e.symm (p * q))) = e (g (e.symm p)) * e (g (e.symm q))
  rw [h, hg, moduleEquiv_ordinary_mul]

/-- Unitality follows from multiplicativity and surjectivity of the actual operator. -/
theorem nativeLinearEquiv_one
    (g : PowerSeriesModule k A ≃ₗ[PowerSeries k] PowerSeriesModule k A)
    (hg : ∀ p q, g (extendBinary (single 0 (LinearMap.mul k A)) p q) =
      extendBinary (single 0 (LinearMap.mul k A)) (g p) (g q)) :
    nativeLinearEquiv g 1 = 1 := by
  have h := nativeLinearEquiv_mul g hg 1 ((nativeLinearEquiv g).symm 1)
  simpa only [one_mul, LinearEquiv.apply_symm_apply, mul_one] using h.symm

/-- The reflected operator is a native algebra equivalence over all scalar series. -/
def nativeAlgEquiv
    (g : PowerSeriesModule k A ≃ₗ[PowerSeries k] PowerSeriesModule k A)
    (hg : ∀ p q, g (extendBinary (single 0 (LinearMap.mul k A)) p q) =
      extendBinary (single 0 (LinearMap.mul k A)) (g p) (g q)) :
    PowerSeries A ≃ₐ[PowerSeries k] PowerSeries A :=
  AlgEquiv.ofLinearEquiv (nativeLinearEquiv g) (nativeLinearEquiv_one g hg) (nativeLinearEquiv_mul g hg)

@[simp] theorem nativeAlgEquiv_apply
    (g : PowerSeriesModule k A ≃ₗ[PowerSeries k] PowerSeriesModule k A)
    (hg : ∀ p q, g (extendBinary (single 0 (LinearMap.mul k A)) p q) =
      extendBinary (single 0 (LinearMap.mul k A)) (g p) (g q)) (p : PowerSeries A) :
    nativeAlgEquiv g hg p = nativeLinearEquiv g p := rfl

/-- Every transported formal bracket remains transported in native series coordinates. -/
theorem nativeAlgEquiv_intertwines
    (g : PowerSeriesModule k A ≃ₗ[PowerSeries k] PowerSeriesModule k A)
    (hg : ∀ p q, g (extendBinary (single 0 (LinearMap.mul k A)) p q) =
      extendBinary (single 0 (LinearMap.mul k A)) (g p) (g q))
    (B C : PowerSeriesModule k (Binary k A))
    (hBC : ∀ p q, g (extendBinary B p q) = extendBinary C (g p) (g q))
    (p q : PowerSeries A) :
    nativeAlgEquiv g hg (PowerSeriesModuleBridge.binaryBridge B p q) =
      PowerSeriesModuleBridge.binaryBridge C (nativeAlgEquiv g hg p) (nativeAlgEquiv g hg q) := by
  simp only [nativeAlgEquiv_apply, nativeLinearEquiv_apply, PowerSeriesModuleBridge.binaryBridge_apply,
    LinearEquiv.symm_apply_apply]
  rw [hBC]

/-- A marked vector-series operator has the same marking in native coordinates. -/
theorem nativeAlgEquiv_constantCoeff
    (g : PowerSeriesModule k A ≃ₗ[PowerSeries k] PowerSeriesModule k A)
    (hg : ∀ p q, g (extendBinary (single 0 (LinearMap.mul k A)) p q) =
      extendBinary (single 0 (LinearMap.mul k A)) (g p) (g q))
    (hzero : ∀ p, coeffV 0 (g p) = coeffV 0 p) (p : PowerSeries A) :
    PowerSeries.constantCoeff (nativeAlgEquiv g hg p) = PowerSeries.constantCoeff p := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, nativeAlgEquiv_apply, nativeLinearEquiv_apply,
    PowerSeriesModuleBridge.coeff_moduleEquiv, hzero, PowerSeriesModuleBridge.coeff_moduleEquiv_symm,
    PowerSeries.coeff_zero_eq_constantCoeff]

/-- The compatible limit retains identity modulo the outer formal parameter. -/
theorem compatibleGaugeEquiv_constantCoeff
    (F : ℕ → PowerSeries (Module.End k A)) (hF : PowerSeries.constantCoeff (F 1) = 1)
    (p : PowerSeriesModule k A) :
    coeffV 0 (compatibleGaugeEquiv F hF p) = coeffV 0 p := by
  rw [compatibleGaugeEquiv, operatorUnitEquiv_apply, operator_apply, coe_compatibleUnit]
  simp [coeffV_actV, coeff_compatibleLimit, PowerSeries.coeff_zero_eq_constantCoeff, hF]

namespace ElementaryComparison

open CategoryTheory

universe u v w
variable {k : Type u} [CommRing k]
variable {C D : CochainComplex (ModuleCat.{v} k) ℤ} {φ : LowTangent C D} [φ.IsMiddleExact]
variable {BC : C.X 1 →ₗ[k] C.X 1 →ₗ[k] C.X 2}
variable {BD : D.X 1 →ₗ[k] D.X 1 →ₗ[k] D.X 2}
variable {S : Type w} [Group S]
variable {RS RT : Type*} [Ring RS] [Ring RT]
variable [MulAction S (MCSeries (C.d 1 2).hom BC)]
variable [MulAction (GaugeUnit RT) (MCSeries (D.d 1 2).hom BD)]
variable (F : ElementaryComparison φ BC BD S RS RT)
variable (b c : MCSeries (C.d 1 2).hom BC)
variable {A : Type*} [CommRing A] [Algebra k A]
variable (ρ : RS →+* Module.End k A)

theorem reflectedLinearEquiv_constantCoeff (G : GaugeUnit RT)
    (hG : G • F.quantize b = F.quantize c) (p : PowerSeriesModule k A) :
    coeffV 0 (F.reflectedLinearEquiv b c ρ G hG p) = coeffV 0 p :=
  compatibleGaugeEquiv_constantCoeff _ (F.representedStages_constantCoeff b c ρ G hG) p

variable (hsource : ∀ s : S, ∀ p q : PowerSeriesModule k A,
  operator (PowerSeries.map ρ (F.sourceOperators s).series)
      (extendBinary (single 0 (LinearMap.mul k A)) p q) =
    extendBinary (single 0 (LinearMap.mul k A))
      (operator (PowerSeries.map ρ (F.sourceOperators s).series) p)
      (operator (PowerSeries.map ρ (F.sourceOperators s).series) q))

/-- The reflected source product gives one native algebra equivalence on the completion. -/
def reflectedAlgEquiv (G : GaugeUnit RT) (hG : G • F.quantize b = F.quantize c) :
    PowerSeries A ≃ₐ[PowerSeries k] PowerSeries A :=
  nativeAlgEquiv (F.reflectedLinearEquiv b c ρ G hG)
    (F.reflectedLinearEquiv_preserves b c ρ _ hsource G hG)

theorem reflectedAlgEquiv_constantCoeff (G : GaugeUnit RT)
    (hG : G • F.quantize b = F.quantize c) (p : PowerSeries A) :
    PowerSeries.constantCoeff (F.reflectedAlgEquiv b c ρ hsource G hG p) =
      PowerSeries.constantCoeff p :=
  nativeAlgEquiv_constantCoeff _ _ (F.reflectedLinearEquiv_constantCoeff b c ρ G hG) p

theorem reflectedAlgEquiv_intertwines
    (base : PowerSeriesModule k (Binary k A))
    (inclusion : C.X 1 →ₗ[k] Binary k A)
    (hPoisson : ∀ s : S, ∀ p q : PowerSeriesModule k A,
      operator (PowerSeries.map ρ (F.sourceOperators s).series)
          (extendBinary (base + map inclusion b.val) p q) =
        extendBinary (base + map inclusion (s • b).val)
          (operator (PowerSeries.map ρ (F.sourceOperators s).series) p)
          (operator (PowerSeries.map ρ (F.sourceOperators s).series) q))
    (G : GaugeUnit RT) (hG : G • F.quantize b = F.quantize c) (p q : PowerSeries A) :
    F.reflectedAlgEquiv b c ρ hsource G hG
        (PowerSeriesModuleBridge.binaryBridge (base + map inclusion b.val) p q) =
      PowerSeriesModuleBridge.binaryBridge (base + map inclusion c.val)
        (F.reflectedAlgEquiv b c ρ hsource G hG p)
        (F.reflectedAlgEquiv b c ρ hsource G hG q) :=
  nativeAlgEquiv_intertwines _ _ _ _
    (F.reflectedLinearEquiv_intertwines b c ρ base inclusion hPoisson G hG) p q

end ElementaryComparison

end EnvelopingIsomorphism.Deformation.Gauge
