import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.LinearAlgebra.Multilinear.DFinsupp
import Mathlib.Algebra.Algebra.Rat
import EnvelopingIsomorphism.FormalSeries.PowerSeriesModule

/-! Algebraic differentiation and integration of vector-valued polynomials.
Coefficient vectors need no ring structure. -/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.PolynomialModuleCalculus

open PolynomialModule

variable {k V W : Type*} [CommRing k]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Linear extension from vector-valued monomials. -/
def liftCoefficients (f : ℕ → V →ₗ[k] W) : PolynomialModule k V →ₗ[k] W :=
  (Finsupp.lsum k f).comp (PolynomialModule.coeffLinearEquiv k k).toLinearMap

@[simp] theorem liftCoefficients_single (f : ℕ → V →ₗ[k] W) (n : ℕ) (v : V) :
    liftCoefficients f (single k n v) = f n v := by
  change Finsupp.lsum k f (Finsupp.single n v) = f n v
  simp

@[simp] theorem liftCoefficients_lsingle (f : ℕ → V →ₗ[k] W) (n : ℕ) (v : V) :
    liftCoefficients f (PolynomialModule.lsingle k n v) = f n v :=
  liftCoefficients_single f n v

@[simp] theorem coeff_smul (a : k) (p : PolynomialModule k V) (n : ℕ) :
    (a • p).coeff n = a • p.coeff n := rfl

/-- Formal derivative, linear over the coefficient ring. -/
def derivative : PolynomialModule k V →ₗ[k] PolynomialModule k V :=
  liftCoefficients fun n ↦ (n : k) • PolynomialModule.lsingle k (n - 1)

@[simp] theorem derivative_single (n : ℕ) (v : V) :
    derivative (single k n v) = (n : k) • single k (n - 1) v := by
  rw [derivative, liftCoefficients_single]
  rfl

@[simp] theorem derivative_single_zero (v : V) : derivative (single k 0 v) = 0 := by simp

theorem coeff_derivative (p : PolynomialModule k V) (n : ℕ) :
    (derivative p).coeff n = (n + 1 : k) • p.coeff (n + 1) := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq, smul_add]
  | single m v =>
    cases m with
    | zero => simp
    | succ m =>
      by_cases h : m = n
      · subst m; simp
      · simp [Ne.symm h]

@[simp] theorem eval_zero (p : PolynomialModule k V) : PolynomialModule.eval 0 p = p.coeff 0 := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single n v => cases n <;> simp

theorem derivative_map (f : V →ₗ[k] W) (p : PolynomialModule k V) :
    derivative (PolynomialModule.map k f p) = PolynomialModule.map k f (derivative p) := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single n v => simp

section Integration

variable [Algebra ℚ k]

/-- The inverse of a positive integer, mapped into the coefficient ring. -/
def inverseSucc (n : ℕ) : k := algebraMap ℚ k ((n + 1 : ℚ)⁻¹)

theorem inverseSucc_mul (n : ℕ) : inverseSucc (k := k) n * (n + 1 : k) = 1 := by
  have h : (n + 1 : ℚ)⁻¹ * (n + 1 : ℚ) = 1 := inv_mul_cancel₀ (by positivity)
  simpa only [inverseSucc, map_mul, map_add, map_natCast, map_one] using
    congrArg (algebraMap ℚ k) h

theorem mul_inverseSucc (n : ℕ) : (n + 1 : k) * inverseSucc (k := k) n = 1 := by
  rw [mul_comm, inverseSucc_mul]

/-- The formal antiderivative with zero constant coefficient. -/
def integral : PolynomialModule k V →ₗ[k] PolynomialModule k V :=
  liftCoefficients fun n ↦ inverseSucc (k := k) n • PolynomialModule.lsingle k (n + 1)

@[simp] theorem integral_single (n : ℕ) (v : V) :
    integral (single k n v) = inverseSucc (k := k) n • single k (n + 1) v := by
  rw [integral, liftCoefficients_single]
  rfl

@[simp] theorem derivative_integral (p : PolynomialModule k V) : derivative (integral p) = p := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single n v => simp [smul_smul, inverseSucc_mul]

@[simp] theorem coeff_zero_integral (p : PolynomialModule k V) : (integral p).coeff 0 = 0 := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single n v => simp

@[simp] theorem eval_zero_integral (p : PolynomialModule k V) : PolynomialModule.eval 0 (integral p) = 0 := by
  rw [eval_zero, coeff_zero_integral]

theorem integral_derivative (p : PolynomialModule k V) :
    integral (derivative p) = p - single k 0 (PolynomialModule.eval 0 p) := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq, single_add]; abel
  | single n v =>
    cases n with
    | zero => simp
    | succ n => simp [smul_smul, mul_inverseSucc]

/-- A vector polynomial is determined by its derivative and its value at zero. -/
theorem ext_of_derivative_eval_zero {p q : PolynomialModule k V}
    (hd : derivative p = derivative q)
    (h0 : PolynomialModule.eval 0 p = PolynomialModule.eval 0 q) : p = q := by
  have h := congrArg integral hd
  rw [integral_derivative, integral_derivative, h0] at h
  exact sub_left_inj.mp h

theorem integral_unique {p q : PolynomialModule k V}
    (hd : derivative q = p) (h0 : PolynomialModule.eval 0 q = 0) : q = integral p :=
  ext_of_derivative_eval_zero (hd.trans (derivative_integral p).symm)
    (h0.trans (eval_zero_integral p).symm)

theorem integral_map (f : V →ₗ[k] W) (p : PolynomialModule k V) :
    integral (PolynomialModule.map k f p) = PolynomialModule.map k f (integral p) := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single n v => simp

end Integration

section Multilinear

open scoped BigOperators Classical

variable {ι N P : Type*} [Fintype ι]
variable {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]
variable [AddCommGroup N] [Module k N] [AddCommGroup P] [Module k P]

/-- Polynomial coefficient vectors in the native dependent finite-support API. -/
def coefficientEquiv : PolynomialModule k V ≃ₗ[k] (Π₀ _ : ℕ, V) :=
  (PolynomialModule.coeffLinearEquiv k k).trans (finsuppLequivDFinsupp k)

@[simp] theorem coefficientEquiv_single (n : ℕ) (v : V) :
    coefficientEquiv (single k n v) = DFinsupp.single n v := by
  change (Finsupp.single n v).toDFinsupp = _
  exact Finsupp.toDFinsupp_single n v

@[simp] theorem coefficientEquiv_symm_single (n : ℕ) (v : V) :
    (coefficientEquiv (k := k)).symm (DFinsupp.single n v) = single k n v := by
  rw [← coefficientEquiv_single (k := k), LinearEquiv.symm_apply_apply]

/-- Multilinear extension on finite polynomial coefficient families. -/
def extendMultilinear (f : MultilinearMap k M N) :
    MultilinearMap k (fun i ↦ PolynomialModule k (M i)) (PolynomialModule k N) :=
  (MultilinearMap.fromDFinsuppEquiv (fun _ : ι ↦ ℕ) k
    (fun a ↦ (PolynomialModule.lsingle k (∑ i, a i)).compMultilinearMap f)).compLinearMap
      (fun _ ↦ coefficientEquiv.toLinearMap)

@[simp] theorem extendMultilinear_single (f : MultilinearMap k M N)
    (a : ι → ℕ) (v : ∀ i, M i) :
    extendMultilinear f (fun i ↦ single k (a i) (v i)) = single k (∑ i, a i) (f v) := by
  simp [extendMultilinear]
  rfl

/-- Multilinear maps on polynomial modules are determined by vector monomials. -/
theorem multilinear_ext {f g : MultilinearMap k (fun i ↦ PolynomialModule k (M i)) N}
    (h : ∀ (a : ι → ℕ) (v : ∀ i, M i),
      f (fun i ↦ single k (a i) (v i)) = g (fun i ↦ single k (a i) (v i))) : f = g := by
  apply MultilinearMap.compLinearMap_injective
    (fun _ ↦ (coefficientEquiv (k := k)).symm.toLinearMap)
    (fun _ ↦ (coefficientEquiv (k := k)).symm.surjective)
  apply MultilinearMap.dfinsupp_ext
  intro a
  apply MultilinearMap.ext
  intro v
  simpa using h a v

/-- Evaluation commutes with arbitrary fixed finite-arity multilinear operations. -/
theorem eval_extendMultilinear (f : MultilinearMap k M N)
    (p : ∀ i, PolynomialModule k (M i)) (r : k) :
    PolynomialModule.eval r (extendMultilinear f p) = f (fun i ↦ PolynomialModule.eval r (p i)) := by
  have h : (PolynomialModule.eval r).compMultilinearMap (extendMultilinear f) =
      f.compLinearMap (fun _ ↦ PolynomialModule.eval r) := by
    apply multilinear_ext
    intro a v
    simp [MultilinearMap.map_smul_univ, Finset.prod_pow_eq_pow_sum]
  exact MultilinearMap.congr_fun h p

theorem map_extendMultilinear (f : MultilinearMap k M N) (g : N →ₗ[k] P)
    (p : ∀ i, PolynomialModule k (M i)) :
    PolynomialModule.map k g (extendMultilinear f p) =
      extendMultilinear (g.compMultilinearMap f) p := by
  have h : (PolynomialModule.map k g).compMultilinearMap (extendMultilinear f) =
      extendMultilinear (g.compMultilinearMap f) := by
    apply multilinear_ext
    intro a v
    simp
  exact MultilinearMap.congr_fun h p

/-- Differentiate one input and leave the other input modules unchanged. -/
def derivativeIn (i : ι) : ∀ j, PolynomialModule k (M j) →ₗ[k] PolynomialModule k (M j) :=
  Function.update (fun _ ↦ LinearMap.id) i derivative

omit [Fintype ι] in
theorem derivativeIn_apply (i : ι) (p : ∀ j, PolynomialModule k (M j)) :
    (fun j ↦ derivativeIn i j (p j)) = Function.update p i (derivative (p i)) := by
  funext j
  by_cases h : j = i
  · subst j; simp [derivativeIn]
  · simp [derivativeIn, h]

omit [Fintype ι] in
private theorem derivativeIn_single (i : ι) (a : ι → ℕ) (v : ∀ j, M j) :
    (fun j ↦ derivativeIn i j (single k (a j) (v j))) =
      (fun j ↦ single k (Function.update a i (a i - 1) j)
        (Function.update v i ((a i : k) • v i) j)) := by
  funext j
  by_cases h : j = i
  · subst j; simp [derivativeIn, single_smul]
  · simp [derivativeIn, h]

private theorem extendMultilinear_derivativeIn_single (f : MultilinearMap k M N)
    (i : ι) (a : ι → ℕ) (v : ∀ j, M j) :
    ((extendMultilinear f).compLinearMap (derivativeIn i))
      (fun j ↦ single k (a j) (v j)) =
      (a i : k) • single k ((∑ j, a j) - 1) (f v) := by
  rw [MultilinearMap.compLinearMap_apply, derivativeIn_single, extendMultilinear_single,
    f.map_update_smul, Function.update_eq_self, single_smul]
  by_cases h : a i = 0
  · simp [h]
  · have hs : (∑ j, Function.update a i (a i - 1) j) = (∑ j, a j) - 1 := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
      have ha := Finset.sum_erase_add Finset.univ a (Finset.mem_univ i)
      omega
    rw [hs]

/-- The finite-arity Leibniz rule for polynomial paths in arbitrary vector modules. -/
theorem derivative_extendMultilinear (f : MultilinearMap k M N)
    (p : ∀ i, PolynomialModule k (M i)) :
    derivative (extendMultilinear f p) =
      ∑ i, extendMultilinear f (Function.update p i (derivative (p i))) := by
  have h : derivative.compMultilinearMap (extendMultilinear f) =
      ∑ i, (extendMultilinear f).compLinearMap (derivativeIn i) := by
    apply multilinear_ext
    intro a v
    simp only [LinearMap.compMultilinearMap_apply, extendMultilinear_single,
      derivative_single, sum_apply, extendMultilinear_derivativeIn_single,
      Nat.cast_sum, Finset.sum_smul]
  have hp := MultilinearMap.congr_fun h p
  simpa only [LinearMap.compMultilinearMap_apply, sum_apply,
    MultilinearMap.compLinearMap_apply, derivativeIn_apply] using hp

end Multilinear

section Bilinear

variable {N : Type*} [AddCommGroup N] [Module k N]

private def bilinearCoefficient (f : V →ₗ[k] W →ₗ[k] N) (n : ℕ) :
    V →ₗ[k] PolynomialModule k W →ₗ[k] PolynomialModule k N where
  toFun v := liftCoefficients fun m ↦ (PolynomialModule.lsingle k (n + m)).comp (f v)
  map_add' v w := by
    apply PolynomialModule.hom_ext
    intro m
    apply LinearMap.ext
    intro x
    simp
  map_smul' r v := by
    apply PolynomialModule.hom_ext
    intro m
    apply LinearMap.ext
    intro x
    simp

/-- The usual bilinear operation on vector-polynomial paths, in curried form. -/
def extendBilinear (f : V →ₗ[k] W →ₗ[k] N) :
    PolynomialModule k V →ₗ[k] PolynomialModule k W →ₗ[k] PolynomialModule k N :=
  liftCoefficients (bilinearCoefficient f)

@[simp] theorem extendBilinear_single_single (f : V →ₗ[k] W →ₗ[k] N)
    (n m : ℕ) (v : V) (w : W) :
    extendBilinear f (single k n v) (single k m w) = single k (n + m) (f v w) := by
  simp [extendBilinear, bilinearCoefficient]
  rfl

/-- Evaluation commutes with the extended bilinear operation. -/
theorem eval_extendBilinear (f : V →ₗ[k] W →ₗ[k] N)
    (p : PolynomialModule k V) (q : PolynomialModule k W) (r : k) :
    PolynomialModule.eval r (extendBilinear f p q) =
      f (PolynomialModule.eval r p) (PolynomialModule.eval r q) := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add p p' hp hp' => simp [hp, hp']
  | single n v =>
    induction q using PolynomialModule.induction_linear with
    | zero => simp
    | add q q' hq hq' => simp [hq, hq']
    | single m w => simp [pow_add, smul_smul, mul_comm]

/-- Bilinear Leibniz rule without any multiplication on the vector modules. -/
theorem derivative_extendBilinear (f : V →ₗ[k] W →ₗ[k] N)
    (p : PolynomialModule k V) (q : PolynomialModule k W) :
    derivative (extendBilinear f p q) =
      extendBilinear f (derivative p) q + extendBilinear f p (derivative q) := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add p p' hp hp' => simp only [map_add, LinearMap.add_apply, hp, hp']; abel
  | single n v =>
    induction q using PolynomialModule.induction_linear with
    | zero => simp
    | add q q' hq hq' => simp only [map_add, hq, hq']; abel
    | single m w =>
      cases n <;> cases m <;>
        simp [Nat.add_comm, Nat.add_left_comm, Nat.cast_add, add_smul]
      module

end Bilinear

section OuterSeries

open scoped BigOperators Classical

/-- Differentiate the polynomial path parameter at each outer-series coefficient. -/
def seriesDerivative : PowerSeriesModule k (PolynomialModule k V) →ₗ[PowerSeries k]
    PowerSeriesModule k (PolynomialModule k V) :=
  PowerSeriesModule.map derivative

/-- Evaluate the polynomial parameter while retaining the full outer formal series. -/
def seriesEval (r : k) : PowerSeriesModule k (PolynomialModule k V) →ₗ[PowerSeries k]
    PowerSeriesModule k V :=
  PowerSeriesModule.map (PolynomialModule.eval r)

@[simp] theorem coeff_seriesDerivative (p : PowerSeriesModule k (PolynomialModule k V)) (n : ℕ) :
    PowerSeriesModule.coeffV n (seriesDerivative p) = derivative (PowerSeriesModule.coeffV n p) := rfl

@[simp] theorem coeff_seriesEval (p : PowerSeriesModule k (PolynomialModule k V)) (n : ℕ) (r : k) :
    PowerSeriesModule.coeffV n (seriesEval r p) = PolynomialModule.eval r (PowerSeriesModule.coeffV n p) := rfl

variable {ι N : Type*} [Fintype ι]
variable {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]
variable [AddCommGroup N] [Module k N]

/-- The complete multilinear chain rule, with no uniform degree bound in the path variable. -/
theorem seriesDerivative_extendMultilinear (f : MultilinearMap k M N)
    (p : ∀ i, PowerSeriesModule k (PolynomialModule k (M i))) :
    seriesDerivative (PowerSeriesModule.extendMultilinear (extendMultilinear f) p) =
      ∑ i, PowerSeriesModule.extendMultilinear (extendMultilinear f)
        (Function.update p i (seriesDerivative (p i))) := by
  apply PowerSeriesModule.ext
  intro n
  simp only [coeff_seriesDerivative, PowerSeriesModule.extendMultilinear_apply,
    PowerSeriesModule.coeffV_applyMultilinear, PowerSeriesModule.coeffV_sum,
    map_sum, derivative_extendMultilinear]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  funext j
  by_cases hj : j = i
  · subst j; simp
  · simp [hj]

theorem seriesEval_extendMultilinear (f : MultilinearMap k M N)
    (p : ∀ i, PowerSeriesModule k (PolynomialModule k (M i))) (r : k) :
    seriesEval r (PowerSeriesModule.extendMultilinear (extendMultilinear f) p) =
      PowerSeriesModule.extendMultilinear f (fun i ↦ seriesEval r (p i)) := by
  ext n
  simp only [coeff_seriesEval, PowerSeriesModule.extendMultilinear_apply,
    PowerSeriesModule.coeffV_applyMultilinear, map_sum, eval_extendMultilinear]

section Integration

variable [Algebra ℚ k]

/-- Integrate every polynomial coefficient separately; its degree may depend on the outer order. -/
def seriesIntegral : PowerSeriesModule k (PolynomialModule k V) →ₗ[PowerSeries k]
    PowerSeriesModule k (PolynomialModule k V) :=
  PowerSeriesModule.map integral

@[simp] theorem coeff_seriesIntegral (p : PowerSeriesModule k (PolynomialModule k V)) (n : ℕ) :
    PowerSeriesModule.coeffV n (seriesIntegral p) = integral (PowerSeriesModule.coeffV n p) := rfl

@[simp] theorem seriesDerivative_integral (p : PowerSeriesModule k (PolynomialModule k V)) :
    seriesDerivative (seriesIntegral p) = p := by
  ext n
  simp

@[simp] theorem seriesEval_zero_integral (p : PowerSeriesModule k (PolynomialModule k V)) :
    seriesEval 0 (seriesIntegral p) = 0 := by
  ext n
  simp

theorem series_ext_of_derivative_eval_zero {p q : PowerSeriesModule k (PolynomialModule k V)}
    (hd : seriesDerivative p = seriesDerivative q) (h0 : seriesEval 0 p = seriesEval 0 q) : p = q := by
  apply PowerSeriesModule.ext
  intro n
  apply ext_of_derivative_eval_zero
  · exact congrArg (PowerSeriesModule.coeffV n) hd
  · exact congrArg (PowerSeriesModule.coeffV n) h0

end Integration

end OuterSeries

end EnvelopingIsomorphism.FormalSeries.PolynomialModuleCalculus
