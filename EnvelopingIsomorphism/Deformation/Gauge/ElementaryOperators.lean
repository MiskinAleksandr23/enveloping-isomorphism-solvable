import EnvelopingIsomorphism.Deformation.Gauge.UnitGroup
import EnvelopingIsomorphism.Deformation.Gauge.OperatorLimit
import EnvelopingIsomorphism.Deformation.Conjugation
import EnvelopingIsomorphism.FormalSeries.Endomorphism

/-! Actual elementary formal exponentials and leading terms of their operator
actions. The coefficient rings are allowed to be noncommutative. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open PowerSeries EnvelopingIsomorphism.FormalSeries

section Exponential

variable {R : Type*} [Ring R] [Algebra ℚ R]

theorem toJet_eq_zero_of_coeff_zero {N : ℕ} {F : PowerSeries R}
    (hF : ∀ i < N, coeff i F = 0) : toJet N F = 0 := by
  rw [← map_zero (toJet N), toJet_eq_iff]
  intro i hi
  rw [hF i hi, map_zero]

/-- A series vanishing below positive order N has square zero modulo t^(N+1). -/
theorem toJet_square_zero {N : ℕ} (hN : 0 < N) {F : PowerSeries R}
    (hF : ∀ i < N, coeff i F = 0) : toJet (N + 1) F ^ 2 = 0 := by
  rw [← map_pow, ← map_zero (toJet (N + 1)), toJet_eq_iff]
  intro i hi
  rw [pow_two, coeff_mul, map_zero]
  apply Finset.sum_eq_zero
  rintro ⟨a, b⟩ hab
  have hab' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  by_cases ha : a < N
  · rw [hF a ha, zero_mul]
  · rw [hF b (by omega), mul_zero]

/-- The genuine noncommutative exponential has its expected first-order jet. -/
theorem exp_firstJet {N : ℕ} (hN : 0 < N) {F : PowerSeries R}
    (hF : ∀ i < N, coeff i F = 0) :
    toJet (N + 1) (exp F) = toJet (N + 1) (1 + F) := by
  have hF₀ : constantCoeff F = 0 := by
    simpa only [coeff_zero_eq_constantCoeff] using hF 0 hN
  rw [toJet_exp hF₀, IsNilpotent.exp_eq_sum (toJet_square_zero hN hF)]
  simp [Finset.sum_range_succ, map_add]

theorem nearIdentity_exp {N : ℕ} (hN : 0 < N) {F : PowerSeries R}
    (hF : ∀ i < N, coeff i F = 0) : NearIdentity N (exp F) := by
  have hF₀ : constantCoeff F = 0 := by
    simpa only [coeff_zero_eq_constantCoeff] using hF 0 hN
  change toJet N (exp F) = 1
  rw [toJet_exp hF₀, toJet_eq_zero_of_coeff_zero hF, IsNilpotent.exp_zero]

theorem coeff_exp_leading {N : ℕ} (hN : 0 < N) {F : PowerSeries R}
    (hF : ∀ i < N, coeff i F = 0) : coeff N (exp F) = coeff N F := by
  have h := (toJet_eq_iff.mp (exp_firstJet hN hF)) N (Nat.lt_succ_self N)
  simpa only [map_add, coeff_one, if_neg (Nat.ne_of_gt hN), zero_add] using h

/-- A positive formal exponential, with its actual exponential inverse. -/
def formalExpUnit (F : PowerSeries R) (hF : constantCoeff F = 0) : (PowerSeries R)ˣ where
  val := exp F
  inv := exp (-F)
  val_inv := exp_mul_exp_neg hF
  inv_val := exp_neg_mul_exp hF

@[simp] theorem coe_formalExpUnit (F : PowerSeries R) (hF : constantCoeff F = 0) :
    (formalExpUnit F hF : PowerSeries R) = exp F := rfl

@[simp] theorem coe_formalExpUnit_inv (F : PowerSeries R) (hF : constantCoeff F = 0) :
    (↑((formalExpUnit F hF)⁻¹) : PowerSeries R) = exp (-F) := rfl

/-- A positive correction with arbitrary higher-order operator coefficients. -/
def correctionGauge (N : ℕ) (hN : 0 < N) (F : PowerSeries R)
    (hF : ∀ i < N, coeff i F = 0) : GaugeUnit R :=
  ⟨formalExpUnit F (by simpa only [coeff_zero_eq_constantCoeff] using hF 0 hN),
    (nearIdentity_exp hN hF).mono hN⟩

@[simp] theorem correctionGauge_series (N : ℕ) (hN : 0 < N) (F : PowerSeries R)
    (hF : ∀ i < N, coeff i F = 0) : (correctionGauge N hN F hF).series = exp F := rfl

theorem correctionGauge_near (N : ℕ) (hN : 0 < N) (F : PowerSeries R)
    (hF : ∀ i < N, coeff i F = 0) : NearIdentity N (correctionGauge N hN F hF).series :=
  nearIdentity_exp hN hF

theorem correctionGauge_leading (N : ℕ) (hN : 0 < N) (F : PowerSeries R)
    (hF : ∀ i < N, coeff i F = 0) : coeff N (correctionGauge N hN F hF).series = coeff N F :=
  coeff_exp_leading hN hF

theorem monomial_coeff_below (N : ℕ) (x : R) (i : ℕ) (hi : i < N) :
    coeff i (monomial N x) = 0 := by
  simp [PowerSeries.coeff_monomial, Nat.ne_of_lt hi]

theorem monomial_constantCoeff_zero {N : ℕ} (hN : 0 < N) (x : R) :
    constantCoeff (monomial N x) = 0 := by
  simpa only [coeff_zero_eq_constantCoeff] using monomial_coeff_below N x 0 hN

/-- The elementary gauge exp(t^N x), as a genuine element of the near-identity group. -/
def elementaryGauge (N : ℕ) (hN : 0 < N) (x : R) : GaugeUnit R :=
  ⟨formalExpUnit (monomial N x) (monomial_constantCoeff_zero hN x),
    (nearIdentity_exp hN (monomial_coeff_below N x)).mono hN⟩

@[simp] theorem elementaryGauge_series (N : ℕ) (hN : 0 < N) (x : R) :
    (elementaryGauge N hN x).series = exp (monomial N x) := rfl

theorem elementaryGauge_near (N : ℕ) (hN : 0 < N) (x : R) :
    NearIdentity N (elementaryGauge N hN x).series :=
  nearIdentity_exp hN (monomial_coeff_below N x)

@[simp] theorem elementaryGauge_leading (N : ℕ) (hN : 0 < N) (x : R) :
    coeff N (elementaryGauge N hN x).series = x := by
  rw [elementaryGauge_series, coeff_exp_leading hN (monomial_coeff_below N x)]
  exact PowerSeries.coeff_monomial_same N x

end Exponential

section BilinearLeading

open PowerSeriesModule

variable {k V W Z : Type*} [CommRing k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup Z] [Module k Z]

theorem coeffV_applyBilinear_single_right (β : V →ₗ[k] W →ₗ[k] Z)
    (p : PowerSeriesModule k V) (w : W) (n : ℕ) :
    coeffV n (applyBilinear β p (single 0 w)) = β (coeffV n p) w := by
  rw [coeffV_applyBilinear, Finset.sum_eq_single_of_mem (n, 0) (by simp)]
  · simp
  · rintro ⟨i, j⟩ hij hne
    have hij' := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hj : j ≠ 0 := by
      intro hj
      subst j
      have hi : i = n := by omega
      subst i
      exact hne rfl
    simp [coeffV_single, hj]

/-- Only the constant coefficient of the first input can contribute when the
second input first appears in degree N. -/
theorem coeffV_applyBilinear_right_vanishing (β : V →ₗ[k] W →ₗ[k] Z)
    (p : PowerSeriesModule k V) (q : PowerSeriesModule k W) (N : ℕ)
    (hq : ∀ i < N, coeffV i q = 0) :
    coeffV N (applyBilinear β p q) = β (coeffV 0 p) (coeffV N q) := by
  rw [coeffV_applyBilinear, Finset.sum_eq_single_of_mem (0, N) (by simp)]
  rintro ⟨i, j⟩ hij hne
  have hij' := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  have hj : j < N := by
    by_contra hj
    have hj' : j = N := by omega
    subst j
    have hi : i = 0 := by omega
    subst i
    exact hne rfl
  rw [hq j hj, map_zero]

theorem coeffV_applyBilinear_right_constant (β : V →ₗ[k] W →ₗ[k] Z)
    (p : PowerSeriesModule k V) (q : PowerSeriesModule k W) (w : W)
    {N : ℕ} (hN : 0 < N) (hq : ∀ i < N, coeffV i q = if i = 0 then w else 0) :
    coeffV N (applyBilinear β p q) = β (coeffV N p) w + β (coeffV 0 p) (coeffV N q) := by
  let δ := q - single 0 w
  have hδ : ∀ i < N, coeffV i δ = 0 := by
    intro i hi
    simp only [δ, coeffV_sub, hq i hi, coeffV_single, sub_self]
  have he : q = single 0 w + δ := by dsimp [δ]; abel
  change coeffV N (extendBilinear β p q) = _
  conv_lhs => rw [he, map_add]
  rw [coeffV_add, extendBilinear_apply, extendBilinear_apply,
    coeffV_applyBilinear_single_right, coeffV_applyBilinear_right_vanishing β p δ N hδ]
  simp [δ, coeffV_single, Nat.ne_of_gt hN]

theorem coeffV_applyBilinear_right_agree (β : V →ₗ[k] W →ₗ[k] Z)
    (p : PowerSeriesModule k V) (q : PowerSeriesModule k W) (w : W)
    {N : ℕ} (hq : ∀ i < N, coeffV i q = if i = 0 then w else 0)
    (n : ℕ) (hn : n < N) : coeffV n (applyBilinear β p q) = β (coeffV n p) w := by
  let δ := q - single 0 w
  have hδ : ∀ i < N, coeffV i δ = 0 := by
    intro i hi
    simp only [δ, coeffV_sub, hq i hi, coeffV_single, sub_self]
  have he : q = single 0 w + δ := by dsimp [δ]; abel
  change coeffV n (extendBilinear β p q) = _
  conv_lhs => rw [he, map_add]
  rw [coeffV_add, extendBilinear_apply, extendBilinear_apply,
    coeffV_applyBilinear_single_right,
    coeffV_applyBilinear_right_vanishing β p δ n (fun i hi ↦ hδ i (hi.trans hn)),
    hδ n hn, map_zero, add_zero]

theorem coeffV_applyBilinear_left_constant (β : V →ₗ[k] W →ₗ[k] Z)
    (p : PowerSeriesModule k V) (q : PowerSeriesModule k W) (v : V)
    {N : ℕ} (hN : 0 < N) (hp : ∀ i < N, coeffV i p = if i = 0 then v else 0) :
    coeffV N (applyBilinear β p q) = β v (coeffV N q) + β (coeffV N p) (coeffV 0 q) := by
  rw [applyBilinear_flip]
  exact coeffV_applyBilinear_right_constant β.flip q p v hN hp

theorem coeffV_applyBilinear_left_agree (β : V →ₗ[k] W →ₗ[k] Z)
    (p : PowerSeriesModule k V) (q : PowerSeriesModule k W) (v : V)
    {N : ℕ} (hp : ∀ i < N, coeffV i p = if i = 0 then v else 0)
    (n : ℕ) (hn : n < N) : coeffV n (applyBilinear β p q) = β v (coeffV n q) := by
  rw [applyBilinear_flip]
  exact coeffV_applyBilinear_right_agree β.flip q p v hp n hn

end BilinearLeading

section Constants

open PowerSeriesModule

variable {k V W : Type*} [CommRing k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

theorem coeffV_linearApply_single_zero (F : PowerSeriesModule k (V →ₗ[k] W))
    (v : V) (n : ℕ) : coeffV n (linearApply F (single 0 v)) = coeffV n F v :=
  coeffV_applyBilinear_single_right (LinearMap.id : (V →ₗ[k] W) →ₗ[k] V →ₗ[k] W) F v n

theorem coeffV_extendBinary_constants (B : PowerSeriesModule k (Binary k V))
    (a b : V) (n : ℕ) :
    coeffV n (extendBinary B (single 0 a) (single 0 b)) = coeffV n B a b := by
  rw [extendBinary_apply, coeffV_linearApply_single_zero, coeffV_linearApply_single_zero]

/-- Coefficients of a formal binary family are recovered on constant inputs. -/
theorem extendBinary_injective : Function.Injective
    (extendBinary (k := k) (V := V) (W := V) (X := V)) := by
  intro B C h
  apply PowerSeriesModule.ext
  intro n
  ext a b
  have hc := congrArg (fun μ : Binary (PowerSeries k) (PowerSeriesModule k V) ↦
    coeffV n (μ (single 0 a) (single 0 b))) h
  simpa only [coeffV_extendBinary_constants] using hc

end Constants

section ConjugationLeading

open PowerSeriesModule

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]

/-- Regard ring-valued operator coefficients as a vector-valued series. -/
def operatorSeries (F : PowerSeries (Module.End k V)) : PowerSeriesModule k (Module.End k V) :=
  PowerSeriesModule.mk fun n ↦ coeff n F

@[simp] theorem coeffV_operatorSeries (F : PowerSeries (Module.End k V)) (n : ℕ) :
    coeffV n (operatorSeries F) = coeff n F := rfl

theorem operatorSeries_near {N : ℕ} {F : PowerSeries (Module.End k V)} (hF : NearIdentity N F) :
    ∀ i < N, coeffV i (operatorSeries F) = if i = 0 then 1 else 0 := by
  intro i hi
  simpa only [coeffV_operatorSeries, PowerSeries.coeff_one] using hF.coeff i hi

theorem precompose_left_leading (B : PowerSeriesModule k (Binary k V))
    {F : PowerSeries (Module.End k V)} {N : ℕ} (hN : 0 < N) (hF : NearIdentity N F) :
    coeffV N (linearCompose B (operatorSeries F)) =
      coeffV N B + (coeffV 0 B).comp (coeff N F) := by
  have h := coeffV_applyBilinear_right_constant (LinearMap.llcomp k V V (V →ₗ[k] V))
    B (operatorSeries F) 1 hN (operatorSeries_near hF)
  ext a b
  have hab := congrArg (fun μ : Binary k V ↦ μ a b) h
  simpa [linearCompose, extendBilinear_apply, LinearMap.llcomp_apply] using hab

theorem precompose_left_agree (B : PowerSeriesModule k (Binary k V))
    {F : PowerSeries (Module.End k V)} {N : ℕ} (hF : NearIdentity N F) :
    AgreeBelow N (linearCompose B (operatorSeries F)) B := by
  intro n hn
  have h := coeffV_applyBilinear_right_agree (LinearMap.llcomp k V V (V →ₗ[k] V))
    B (operatorSeries F) 1 (operatorSeries_near hF) n hn
  ext a b
  have hab := congrArg (fun μ : Binary k V ↦ μ a b) h
  simpa [linearCompose, extendBilinear_apply, LinearMap.llcomp_apply] using hab

theorem precompose_right_leading (B : PowerSeriesModule k (Binary k V))
    {F : PowerSeries (Module.End k V)} {N : ℕ} (hN : 0 < N) (hF : NearIdentity N F) :
    coeffV N (precomposeBinaryRight B (operatorSeries F)) =
      coeffV N B + (coeffV 0 B).compl₂ (coeff N F) := by
  rw [precomposeBinaryRight, coeffV_flipBinarySeries, precompose_left_leading _ hN hF]
  ext a b
  simp

theorem precompose_right_agree (B : PowerSeriesModule k (Binary k V))
    {F : PowerSeries (Module.End k V)} {N : ℕ} (hF : NearIdentity N F) :
    AgreeBelow N (precomposeBinaryRight B (operatorSeries F)) B := by
  intro n hn
  rw [precomposeBinaryRight, coeffV_flipBinarySeries, precompose_left_agree _ hF n hn]
  simp

private theorem post_operatorSeries_near {F : PowerSeries (Module.End k V)} {N : ℕ}
    (hF : NearIdentity N F) :
    ∀ i < N, coeffV i (PowerSeriesModule.map (LinearMap.llcomp k V V V) (operatorSeries F)) =
      if i = 0 then (LinearMap.llcomp k V V V (1 : Module.End k V) :
        Module.End k (Module.End k V)) else 0 := by
  intro i hi
  rw [coeffV_map, coeffV_operatorSeries, hF.coeff i hi, PowerSeries.coeff_one]
  split_ifs <;> simp

theorem postcompose_leading (B : PowerSeriesModule k (Binary k V))
    {F : PowerSeries (Module.End k V)} {N : ℕ} (hN : 0 < N) (hF : NearIdentity N F) :
    coeffV N (postcomposeBinary (operatorSeries F) B) =
      coeffV N B + (coeffV 0 B).compr₂ (coeff N F) := by
  have h := coeffV_applyBilinear_left_constant (LinearMap.llcomp k V (V →ₗ[k] V) (V →ₗ[k] V))
    (PowerSeriesModule.map (LinearMap.llcomp k V V V) (operatorSeries F)) B
    (LinearMap.llcomp k V V V (1 : Module.End k V)) hN (post_operatorSeries_near hF)
  ext a b
  have hab := congrArg (fun μ : Binary k V ↦ μ a b) h
  simpa [postcomposeBinary, linearCompose, extendBilinear_apply] using hab

theorem postcompose_agree (B : PowerSeriesModule k (Binary k V))
    {F : PowerSeries (Module.End k V)} {N : ℕ} (hF : NearIdentity N F) :
    AgreeBelow N (postcomposeBinary (operatorSeries F) B) B := by
  intro n hn
  have h := coeffV_applyBilinear_left_agree (LinearMap.llcomp k V (V →ₗ[k] V) (V →ₗ[k] V))
    (PowerSeriesModule.map (LinearMap.llcomp k V V V) (operatorSeries F)) B
    (LinearMap.llcomp k V V V (1 : Module.End k V)) (post_operatorSeries_near hF) n hn
  ext a b
  have hab := congrArg (fun μ : Binary k V ↦ μ a b) h
  simpa [postcomposeBinary, linearCompose, extendBilinear_apply] using hab

/-- Transport a formal bilinear family by one actual formal operator unit. -/
def conjugateBinarySeries (G : (PowerSeries (Module.End k V))ˣ)
    (B : PowerSeriesModule k (Binary k V)) : PowerSeriesModule k (Binary k V) :=
  postcomposeBinary (operatorSeries (G : PowerSeries (Module.End k V)))
    (precomposeBinaryRight
      (linearCompose B (operatorSeries (↑(G⁻¹) : PowerSeries (Module.End k V))))
      (operatorSeries (↑(G⁻¹) : PowerSeries (Module.End k V))))

/-- This coefficient construction is the genuine complete conjugation action. -/
theorem extendBinary_conjugateBinarySeries (G : (PowerSeries (Module.End k V))ˣ)
    (B : PowerSeriesModule k (Binary k V)) (x y : PowerSeriesModule k V) :
    extendBinary (conjugateBinarySeries G B) x y =
      conjugate (operatorUnitEquiv G) (extendBinary B) x y := by
  rw [conjugateBinarySeries, extendBinary_postcomp, extendBinary_precomp_right,
    extendBinary_precomp_left, conjugate_apply]
  rfl

theorem conjugateBinarySeries_agree (G : (PowerSeries (Module.End k V))ˣ)
    (B : PowerSeriesModule k (Binary k V)) {N : ℕ}
    (hG : NearIdentity N (G : PowerSeries (Module.End k V))) :
    AgreeBelow N (conjugateBinarySeries G B) B := by
  intro n hn
  rw [conjugateBinarySeries, postcompose_agree _ hG n hn,
    precompose_right_agree _ hG.inv n hn, precompose_left_agree _ hG.inv n hn]

/-- The first nontrivial coefficient of actual gauge transport is precisely the
unary Hochschild action, with output-minus-inputs signs. -/
theorem conjugateBinarySeries_leading (G : (PowerSeries (Module.End k V))ˣ)
    (B : PowerSeriesModule k (Binary k V)) {N : ℕ} (hN : 0 < N)
    (hG : NearIdentity N (G : PowerSeries (Module.End k V))) :
    coeffV N (conjugateBinarySeries G B) = coeffV N B +
      unaryAction (coeff N (G : PowerSeries (Module.End k V))) (coeffV 0 B) := by
  rw [conjugateBinarySeries, postcompose_leading _ hN hG,
    precompose_right_leading _ hN hG.inv, precompose_left_leading _ hN hG.inv,
    precompose_right_agree _ hG.inv 0 hN, precompose_left_agree _ hG.inv 0 hN,
    coeff_inv_nearIdentity hN hG]
  ext a b
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.compl₂_apply,
    LinearMap.compr₂_apply, unaryAction_apply, LinearMap.neg_apply, map_neg]
  abel

theorem conjugateBinarySeries_leading_sub (G : (PowerSeries (Module.End k V))ˣ)
    (B : PowerSeriesModule k (Binary k V)) {N : ℕ} (hN : 0 < N)
    (hG : NearIdentity N (G : PowerSeries (Module.End k V))) :
    coeffV N (conjugateBinarySeries G B) - coeffV N B =
      -differentialOne (coeffV 0 B) (coeff N (G : PowerSeries (Module.End k V))) := by
  rw [conjugateBinarySeries_leading G B hN hG, differentialOne_eq_neg_unaryAction, neg_neg]
  abel

end ConjugationLeading

end EnvelopingIsomorphism.Deformation.Gauge
