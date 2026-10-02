import EnvelopingIsomorphism.Deformation.Gauge.Tangent
import EnvelopingIsomorphism.Deformation.Gauge.TaylorNaturality

/-! Genuine polynomial-path tangent evaluation. Its first nonzero formal
coefficient is the linear tangent map, even with unbounded path degree across
the outer formal coefficients. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule

variable {k V₀ V₁ W₀ : Type*} [CommRing k]
variable [AddCommGroup V₀] [Module k V₀] [AddCommGroup V₁] [Module k V₁]
variable [AddCommGroup W₀] [Module k W₀]

def polynomialTangentApply
    (T : TangentFamily (k := k) (V₀ := V₀) (V₁ := V₁) (W₀ := W₀))
    (b : ModulePath k V₁) (v : ModulePath k V₀) : ModulePath k W₀ :=
  pathMap T.linear v + pathBilinear (LinearMap.id : (V₀ →ₗ[k] W₀) →ₗ[k] V₀ →ₗ[k] W₀)
    (polynomialTaylorApply T.higher b) v

theorem polynomialTangentApply_eval
    (T : TangentFamily (k := k) (V₀ := V₀) (V₁ := V₁) (W₀ := W₀))
    (b : ModulePath k V₁) (v : ModulePath k V₀) (s : k) :
    PolynomialModuleCalculus.seriesEval s (polynomialTangentApply T b v) =
      tangentApply T (PolynomialModuleCalculus.seriesEval s b)
        (PolynomialModuleCalculus.seriesEval s v) := by
  rw [polynomialTangentApply, map_add, pathBilinear_eval, polynomialTaylor_eval]
  congr 1
  apply PowerSeriesModule.ext
  intro n
  simp only [pathMap, coeffV_map, PolynomialModuleCalculus.coeff_seriesEval]
  exact PolynomialModule.eval_map k T.linear (coeffV n v) s

theorem polynomialTangentApply_leading
    (T : TangentFamily (k := k) (V₀ := V₀) (V₁ := V₁) (W₀ := W₀))
    (b : ModulePath k V₁) (v : ModulePath k V₀) (N : ℕ)
    (hv : ∀ i < N, coeffV i v = 0) :
    coeffV N (polynomialTangentApply T b v) = PolynomialModule.map k T.linear (coeffV N v) := by
  rw [polynomialTangentApply, coeffV_add]
  change PolynomialModule.map k T.linear (coeffV N v) +
    coeffV N (applyBilinear (PolynomialModuleCalculus.extendBilinear
      (LinearMap.id : (V₀ →ₗ[k] W₀) →ₗ[k] V₀ →ₗ[k] W₀))
        (polynomialTaylorApply T.higher b) v) = _
  rw [coeffV_applyBilinear, add_eq_left]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  have hij' := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  by_cases hi : i = 0
  · subst i
    change PolynomialModuleCalculus.extendBilinear _
      (coeffV 0 (taylorApply (polynomialTaylorFamily T.higher) b)) (coeffV j v) = 0
    rw [taylorApply_constantCoeff, map_zero, LinearMap.zero_apply]
  · rw [hv j (by omega), map_zero]

theorem polynomialTangentApply_preserves_order
    (T : TangentFamily (k := k) (V₀ := V₀) (V₁ := V₁) (W₀ := W₀))
    (b : ModulePath k V₁) (v : ModulePath k V₀) (N : ℕ)
    (hv : ∀ i < N, coeffV i v = 0) :
    ∀ i < N, coeffV i (polynomialTangentApply T b v) = 0 := by
  intro i hi
  rw [polynomialTangentApply_leading T b v i (fun j hj ↦ hv j (hj.trans hi)), hv i hi, map_zero]

theorem polynomialTangentApply_leading_constant
    (T : TangentFamily (k := k) (V₀ := V₀) (V₁ := V₁) (W₀ := W₀))
    (b : ModulePath k V₁) (v : ModulePath k V₀) (N : ℕ)
    (hv : ∀ i < N, coeffV i v = 0) (x : V₀)
    (hx : coeffV N v = PolynomialModule.single k 0 x) :
    coeffV N (polynomialTangentApply T b v) = PolynomialModule.single k 0 (T.linear x) := by
  rw [polynomialTangentApply_leading T b v N hv, hx]
  simp

end EnvelopingIsomorphism.Deformation.Gauge
