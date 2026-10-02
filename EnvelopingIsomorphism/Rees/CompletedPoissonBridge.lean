import EnvelopingIsomorphism.Rees.ReflectionSource
import EnvelopingIsomorphism.Deformation.Gauge.LaurentSourceAlgebra
import EnvelopingIsomorphism.Poisson.ComparisonMatrix

/-! The actual Laurent Schouten Rees operation is the native completed linear Poisson bracket. -/

noncomputable section

namespace EnvelopingIsomorphism.Rees.CompletedPoissonBridge

open EnvelopingIsomorphism.Deformation EnvelopingIsomorphism.FormalSeries
open scoped BigOperators LaurentAlgebra

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

namespace LMHelpers

variable {k A : Type*} [CommRing k] [AddCommGroup A] [Module k A]

def singleLinear (e : ℤ) : A →ₗ[k] LaurentModule k A where
  toFun := LaurentModule.single e
  map_add' := LaurentModule.single_add e
  map_smul' := LaurentModule.single_smul e

theorem single_sum {ι : Type*} (s : Finset ι) (e : ℤ) (f : ι → A) :
    LaurentModule.single (k := k) e (∑ i ∈ s, f i) = ∑ i ∈ s, LaurentModule.single e (f i) :=
  map_sum (singleLinear (k := k) e) f s

theorem boundedBelow_sum {ι : Type*} (s : Finset ι) (f : ι → LaurentModule k A) (b : ℤ)
    (h : ∀ i ∈ s, LaurentModule.BoundedBelow b (f i)) :
    LaurentModule.BoundedBelow b (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro j hj; simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact LaurentModule.boundedBelow_add (h i (by simp))
        (ih (fun a ha ↦ h a (by simp [ha])))

end LMHelpers

section Laurent

variable {k : Type*} [Field k] {d : ℕ}

local notation "Poly" => MvPolynomial (Fin d) k
local notation "LM" => LaurentModule k Poly

/-- The actual Laurent-module differential expression for one linear Poisson tensor. -/
def modulePoisson (c : Fin d → Fin d → Fin d → k) :
    Binary (LaurentSeries k) LM :=
  ∑ i : Fin d, ∑ j : Fin d, ∑ r : Fin d,
    ((LaurentDerivationSeries.moduleMul (k := k) (A := Poly)).compl₁₂
      (LaurentModule.map (MvPolynomial.pderiv i).toLinearMap)
      (LaurentModule.map (MvPolynomial.pderiv j).toLinearMap)).compr₂
      (LaurentDerivationSeries.moduleMul (LaurentModule.single 0
        (MvPolynomial.C (c i j r) * MvPolynomial.X r)))

theorem modulePoisson_apply (c : Fin d → Fin d → Fin d → k) (x y : LM) :
    modulePoisson c x y = ∑ i : Fin d, ∑ j : Fin d, ∑ r : Fin d,
      LaurentDerivationSeries.moduleMul
        (LaurentModule.single 0 (MvPolynomial.C (c i j r) * MvPolynomial.X r))
        (LaurentDerivationSeries.moduleMul
          (LaurentModule.map (MvPolynomial.pderiv i).toLinearMap x)
          (LaurentModule.map (MvPolynomial.pderiv j).toLinearMap y)) := by
  simp only [modulePoisson, LinearMap.sum_apply, LinearMap.compr₂_apply,
    LinearMap.compl₁₂_apply]

theorem boundedBelow_modulePoisson (c : Fin d → Fin d → Fin d → k) (x y : LM)
    {a b : ℤ} (hx : LaurentModule.BoundedBelow a x) (hy : LaurentModule.BoundedBelow b y) :
    LaurentModule.BoundedBelow (a + b) (modulePoisson c x y) := by
  rw [modulePoisson_apply]
  apply LMHelpers.boundedBelow_sum
  intro i hi
  apply LMHelpers.boundedBelow_sum
  intro j hj
  apply LMHelpers.boundedBelow_sum
  intro r hr
  simpa only [zero_add] using LaurentDerivationSeries.boundedBelow_moduleMul _ _
    (LaurentModule.boundedBelow_single 0 _)
    (LaurentDerivationSeries.boundedBelow_moduleMul _ _
      (LaurentModule.boundedBelow_map _ hx) (LaurentModule.boundedBelow_map _ hy))

theorem modulePoisson_single (c : Fin d → Fin d → Fin d → k)
    (a b : ℤ) (x y : Poly) :
    modulePoisson c (LaurentModule.single a x) (LaurentModule.single b y) =
      LaurentModule.single (a + b) (Kontsevich.linearPoissonBinary c x y) := by
  simp only [modulePoisson_apply, LaurentModule.map_single,
    LaurentDerivationSeries.moduleMul_single, zero_add,
    Kontsevich.linearPoissonBinary_apply, Poisson.linearBracket,
    LMHelpers.single_sum, mul_assoc]
  rfl

/-- The genuine Laurent extension agrees on all inputs, by its proved uniform bound. -/
theorem extendBilinear_linearPoisson (c : Fin d → Fin d → Fin d → k) :
    LaurentModule.extendBilinear (Kontsevich.linearPoissonBinary c) = modulePoisson c := by
  have he := LaurentModule.bilinear_ext_of_bounded
    (LaurentModule.restrictBilinear (LaurentModule.extendBilinear (Kontsevich.linearPoissonBinary c)))
    (LaurentModule.restrictBilinear (modulePoisson c)) 0
    (fun x y a b hx hy ↦ by
      change LaurentModule.BoundedBelow ((a + b) + 0)
        (LaurentModule.extendBilinear (Kontsevich.linearPoissonBinary c) x y)
      simpa only [add_zero] using LaurentModule.boundedBelow_extendBilinear _ x y hx hy)
    (fun x y a b hx hy ↦ by
      change LaurentModule.BoundedBelow ((a + b) + 0) (modulePoisson c x y)
      simpa only [add_zero] using boundedBelow_modulePoisson c x y hx hy)
    (fun a b x y ↦ (LaurentModule.extendBilinear_single _ a b x y).trans
      (modulePoisson_single c a b x y).symm)
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact DFunLike.congr_fun (DFunLike.congr_fun he x) y

theorem binaryEvaluation_single (B : Binary k Poly) (e : ℤ) (x y : LM) :
    LaurentModule.binaryEvaluation (LaurentModule.single e B) x y =
      (HahnSeries.single e (1 : k) : LaurentSeries k) • LaurentModule.extendBilinear B x y := by
  rw [LaurentModule.single_as_series_smul e B, map_smul, LinearMap.smul_apply,
    LinearMap.smul_apply]
  congr 1
  rw [LaurentModule.binaryEvaluation_apply, LaurentModule.extendBinary_apply,
    LaurentModule.linearApply_single_zero]
  exact LaurentModule.extendBilinear_precomp_left LinearMap.id B x y

def laurentPoisson (c : Fin d → Fin d → Fin d → k)
    (p q : LaurentSeries Poly) : LaurentSeries Poly :=
  ∑ i : Fin d, ∑ j : Fin d, ∑ r : Fin d,
    HahnSeries.C (MvPolynomial.C (c i j r)) *
      (HahnSeries.C (MvPolynomial.X r) *
        (LaurentAlgebra.derivation (MvPolynomial.pderiv i) p *
          LaurentAlgebra.derivation (MvPolynomial.pderiv j) q))

theorem moduleEquiv_modulePoisson (c : Fin d → Fin d → Fin d → k) (x y : LM) :
    LaurentAlgebra.moduleEquiv (modulePoisson c x y) =
      laurentPoisson c (LaurentAlgebra.moduleEquiv x) (LaurentAlgebra.moduleEquiv y) := by
  have hd (i : Fin d) (z : LM) :
      LaurentAlgebra.moduleEquiv (LaurentModule.map (MvPolynomial.pderiv i).toLinearMap z) =
        LaurentAlgebra.derivation (MvPolynomial.pderiv i) (LaurentAlgebra.moduleEquiv z) := by
    apply HahnSeries.ext
    funext n
    rfl
  simp only [modulePoisson_apply, map_sum, LaurentDerivationSeries.moduleEquiv_mul, hd]
  change (∑ i : Fin d, ∑ j : Fin d, ∑ r : Fin d,
    HahnSeries.C (MvPolynomial.C (c i j r) * MvPolynomial.X r) *
      (LaurentAlgebra.derivation (MvPolynomial.pderiv i) (LaurentAlgebra.moduleEquiv x) *
        LaurentAlgebra.derivation (MvPolynomial.pderiv j) (LaurentAlgebra.moduleEquiv y))) = _
  simp only [laurentPoisson, map_mul, mul_assoc]

/-- Evaluating a single Laurent coefficient gives the actual inner differential expression. -/
theorem nativeBivector_single_linear
    (π : Multiderivation k (PolynomialFunctions k d) 2) (c : Fin d → Fin d → Fin d → k)
    (hπ : rawBivector π = Kontsevich.linearPoissonBinary c)
    (e : ℤ) (p q : LaurentSeries Poly) :
    Gauge.LaurentSourceAlgebra.nativeBivector (LaurentModule.single e π) p q =
      (HahnSeries.single e (1 : k) : LaurentSeries k) • laurentPoisson c p q := by
  rw [Gauge.LaurentSourceAlgebra.nativeBivector_apply]
  change LaurentAlgebra.moduleEquiv
    (LaurentModule.binaryEvaluation
      (LaurentModule.map rawBivectorLinearMap (LaurentModule.single e π))
      (LaurentAlgebra.moduleEquiv.symm p) (LaurentAlgebra.moduleEquiv.symm q)) = _
  rw [LaurentModule.map_single]
  change LaurentAlgebra.moduleEquiv
    (LaurentModule.binaryEvaluation (LaurentModule.single e (rawBivector π))
      (LaurentAlgebra.moduleEquiv.symm p) (LaurentAlgebra.moduleEquiv.symm q)) = _
  rw [hπ, binaryEvaluation_single, map_smul, extendBilinear_linearPoisson,
    moduleEquiv_modulePoisson, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end Laurent

section Outer

variable {k : Type*} [Field k] {d : ℕ}

local notation "Poly" => MvPolynomial (Fin d) k
local notation "Native" => LaurentSeries Poly

/-- A scalar series table whose inner coefficients are constant Laurent series. -/
def tableSeries (c : ℕ → Fin d → Fin d → Fin d → k)
    (i j r : Fin d) : Poisson.Completed.Scalars k :=
  PowerSeries.mk (fun n ↦ HahnSeries.C (c n i j r))

@[simp] theorem coeff_tableSeries (c : ℕ → Fin d → Fin d → Fin d → k)
    (i j r : Fin d) (n : ℕ) :
    PowerSeries.coeff n (tableSeries c i j r) = HahnSeries.C (c n i j r) :=
  PowerSeries.coeff_mk _ _

theorem laurent_algebraMap_C (a : k) :
    algebraMap (LaurentSeries k) Native (HahnSeries.C a) = HahnSeries.C (MvPolynomial.C a) := by
  apply HahnSeries.ext
  funext j
  by_cases hj : j = 0 <;>
    simp [LaurentAlgebra.coeff_algebraMap, HahnSeries.C_apply, hj]

theorem coeff_completed_term (a : Poisson.Completed.Scalars k) (i j r : Fin d)
    (p q : Poisson.Completed.Functions (Fin d) k) (n : ℕ) :
    PowerSeries.coeff n
      (algebraMap (Poisson.Completed.Scalars k) (Poisson.Completed.Functions (Fin d) k) a *
        (Poisson.Completed.coordinate r *
          (Poisson.Completed.partialDerivation i p * Poisson.Completed.partialDerivation j q))) =
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n,
        algebraMap (LaurentSeries k) Native (PowerSeries.coeff ab.1 a) *
          (HahnSeries.C (MvPolynomial.X r) *
            (∑ bc ∈ Finset.HasAntidiagonal.antidiagonal ab.2,
              LaurentAlgebra.derivation (MvPolynomial.pderiv i) (PowerSeries.coeff bc.1 p) *
                LaurentAlgebra.derivation (MvPolynomial.pderiv j) (PowerSeries.coeff bc.2 q))) := by
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ab hab
  rw [PowerSeries.algebraMap_apply'', PowerSeries.coeff_map, Poisson.Completed.coordinate,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_mul]
  simp only [Poisson.Completed.partialDerivation, PowerSeriesAlgebra.coeff_derivation]

/-- Native completed differentiation and multiplication have the same finite outer convolution. -/
theorem coeff_completed_bracket (c : ℕ → Fin d → Fin d → Fin d → k)
    (p q : Poisson.Completed.Functions (Fin d) k) (n : ℕ) :
    PowerSeries.coeff n (Poisson.Completed.bracket (tableSeries c) p q) =
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n,
        ∑ bc ∈ Finset.HasAntidiagonal.antidiagonal ab.2,
          laurentPoisson (c ab.1) (PowerSeries.coeff bc.1 p) (PowerSeries.coeff bc.2 q) := by
  simp only [Poisson.Completed.bracket, Poisson.differentialLinearBracket, map_sum,
    coeff_completed_term, coeff_tableSeries, laurent_algebraMap_C, Finset.mul_sum,
    laurentPoisson]
  have hs (f : Fin d → (ℕ × ℕ) → (ℕ × ℕ) → Native) :
      (∑ i : Fin d, ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n,
        ∑ bc ∈ Finset.HasAntidiagonal.antidiagonal ab.2, f i ab bc) =
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n,
        ∑ bc ∈ Finset.HasAntidiagonal.antidiagonal ab.2, ∑ i : Fin d, f i ab bc := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ab hab
    exact Finset.sum_comm
  simp_rw [hs]

/-- The inner parameter viewed as a constant outer scalar series. -/
def hbar (k : Type*) [Field k] : Poisson.Completed.Scalars k :=
  PowerSeries.C (HahnSeries.single 1 (1 : k) : LaurentSeries k)

theorem coeff_hbar_smul (p : Poisson.Completed.Functions (Fin d) k) (n : ℕ) :
    PowerSeries.coeff n (hbar k • p) =
      (HahnSeries.single 1 (1 : k) : LaurentSeries k) • PowerSeries.coeff n p := by
  simp only [hbar, Algebra.smul_def, PowerSeries.algebraMap_apply'',
    PowerSeries.map_C, PowerSeries.coeff_C_mul]

/-- A coefficientwise identified family gives equality on every pair of native completed inputs. -/
theorem binaryBridge_eq_hbar_bracket
    (B : PowerSeriesModule (LaurentSeries k) (Binary (LaurentSeries k) Native))
    (c : ℕ → Fin d → Fin d → Fin d → k)
    (hB : ∀ n p q, PowerSeriesModule.coeffV n B p q =
      (HahnSeries.single 1 (1 : k) : LaurentSeries k) • laurentPoisson (c n) p q)
    (p q : Poisson.Completed.Functions (Fin d) k) :
    PowerSeriesModuleBridge.binaryBridge B p q = hbar k • Poisson.Completed.bracket (tableSeries c) p q := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeriesModuleBridge.binaryBridge_apply, PowerSeriesModuleBridge.coeff_moduleEquiv,
    PowerSeriesModule.coeffV_extendBinary, coeff_hbar_smul, coeff_completed_bracket]
  simp only [PowerSeriesModuleBridge.coeff_moduleEquiv_symm, hB, Finset.smul_sum]
  exact PowerSeriesModule.sum_antidiagonal_assoc
    (fun i j l ↦ (HahnSeries.single 1 (1 : k) : LaurentSeries k) •
      laurentPoisson (c i) (PowerSeries.coeff j p) (PowerSeries.coeff l q)) n

end Outer

section Rees

variable {k L : Type*} [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
  {d : ℕ} {b : Module.Basis (Fin d) k L} (W : WeightData b)

-- The polynomial parameter remains the outer power-series parameter.
local instance completedScalarPolynomialModule :
    Module (Polynomial k) (Poisson.Completed.Scalars k) := Algebra.toModule

/-- The actual scalar-extended Rees structure constants. -/
def coefficients : Fin d → Fin d → Fin d → Poisson.Completed.Scalars k :=
  Poisson.structureCoeff ((Family.basis W).baseChange (Poisson.Completed.Scalars k))

omit [CharZero k] in
theorem tableSeries_eq_algebraMap (i j r : Fin d) :
    tableSeries (PoissonMCFamily.coeffTable W) i j r =
      algebraMap (Polynomial k) (Poisson.Completed.Scalars k) (W.coeff i j r) := by
  apply PowerSeries.ext
  intro n
  rw [coeff_tableSeries, PowerSeries.algebraMap_apply', PowerSeries.coeff_map,
    Polynomial.coeff_coe]
  simp [PoissonMCFamily.coeffTable, HahnSeries.algebraMap_apply']

omit [CharZero k] in
theorem tableSeries_eq_coefficients : tableSeries (PoissonMCFamily.coeffTable W) = coefficients W := by
  funext i j r
  rw [coefficients, Poisson.structureCoeff, Family.baseChange_structureCoeff]
  exact tableSeries_eq_algebraMap W i j r

/-- The full evaluated Rees family on all native completed functions is exactly `hπ(t)`. -/
theorem total_binary_eq (p q : Poisson.Completed.Functions (Fin d) k) :
    PowerSeriesModuleBridge.binaryBridge
        (PowerSeriesModule.map Gauge.LaurentSourceAlgebra.nativeBivector
          (PoissonMCFamily.totalLaurentSeries W)) p q =
      hbar k • Poisson.Completed.bracket (coefficients W) p q := by
  rw [← tableSeries_eq_coefficients W]
  apply binaryBridge_eq_hbar_bracket
  intro n x y
  rw [PowerSeriesModule.coeffV_map, PoissonMCFamily.totalLaurentSeries_coeff]
  exact nativeBivector_single_linear (PoissonMCFamily.bivectorCoefficient W n)
    (PoissonMCFamily.coeffTable W n) (PoissonMCFamily.raw_bivectorCoefficient W n) 1 x y

end Rees

section Recovered

variable {k L M : Type*} [Field k] [CharZero k]
  [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]
  (D : Identification.RecoveredData k L M)

theorem source_native_family_eq :
    PowerSeriesModule.single 0
        (Gauge.LaurentSourceAlgebra.nativeBivector (ReflectionSource.base D)) +
      PowerSeriesModule.map Gauge.LaurentSourceAlgebra.nativeBivector (ReflectionSource.source D).val =
    PowerSeriesModule.map Gauge.LaurentSourceAlgebra.nativeBivector
      (PoissonMCFamily.totalLaurentSeries D.sourceWeightData) := by
  rw [ReflectionSource.source_val, PoissonMCFamily.perturbationSeries, map_sub,
    PowerSeriesModule.map_single]
  abel

theorem target_native_family_eq :
    PowerSeriesModule.single 0
        (Gauge.LaurentSourceAlgebra.nativeBivector (ReflectionSource.base D)) +
      PowerSeriesModule.map Gauge.LaurentSourceAlgebra.nativeBivector (ReflectionSource.target D).val =
    PowerSeriesModule.map Gauge.LaurentSourceAlgebra.nativeBivector
      (PoissonMCFamily.totalLaurentSeries D.targetWeightData) := by
  rw [ReflectionSource.target_val_common_base, map_sub, PowerSeriesModule.map_single]
  abel

theorem sourceBinary_bridge
    (p q : PowerSeriesModule (LaurentSeries k) (Gauge.LaurentSchouten.Functions k D.size)) :
    Gauge.LaurentSchouten.functionSeriesBridge
        (Gauge.LaurentSchouten.sourceBinary (ReflectionSource.base D)
          (ReflectionSource.base_isMaurerCartan D) (ReflectionSource.source D) p q) =
      hbar k • Poisson.Completed.bracket (coefficients D.sourceWeightData)
        (Gauge.LaurentSchouten.functionSeriesBridge p)
        (Gauge.LaurentSchouten.functionSeriesBridge q) := by
  rw [Gauge.LaurentSourceAlgebra.functionSeriesBridge_sourceBinary, source_native_family_eq]
  exact total_binary_eq D.sourceWeightData _ _

theorem targetBinary_bridge
    (p q : PowerSeriesModule (LaurentSeries k) (Gauge.LaurentSchouten.Functions k D.size)) :
    Gauge.LaurentSchouten.functionSeriesBridge
        (Gauge.LaurentSchouten.sourceBinary (ReflectionSource.base D)
          (ReflectionSource.base_isMaurerCartan D) (ReflectionSource.target D) p q) =
      hbar k • Poisson.Completed.bracket (coefficients D.targetWeightData)
        (Gauge.LaurentSchouten.functionSeriesBridge p)
        (Gauge.LaurentSchouten.functionSeriesBridge q) := by
  rw [Gauge.LaurentSourceAlgebra.functionSeriesBridge_sourceBinary, target_native_family_eq]
  exact total_binary_eq D.targetWeightData _ _

end Recovered

section Complex

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [LieRing M] [LieAlgebra ℂ M]
  (D : Identification.RecoveredData ℂ L M)

local instance comparisonScalarPolynomialModule :
    Module (Polynomial ℂ) (Poisson.Completed.Scalars ℂ) := Algebra.toModule

/-- Exact source operation consumed by the native completed Poisson comparison endpoint. -/
theorem source_binary_eq (p q : Poisson.Completed.Functions (Fin D.size) ℂ) :
    PowerSeriesModuleBridge.binaryBridge
      (PowerSeriesModule.single 0
          (Gauge.LaurentSourceAlgebra.nativeBivector (ReflectionSource.base D)) +
        PowerSeriesModule.map Gauge.LaurentSourceAlgebra.nativeBivector (ReflectionSource.source D).val) p q =
      Poisson.ComparisonMatrix.hbar •
        Poisson.Completed.bracket (Poisson.ComparisonMatrix.sourceCoefficients D) p q := by
  rw [source_native_family_eq]
  exact total_binary_eq D.sourceWeightData p q

/-- The target uses the same reflected base and the actual target Rees bracket. -/
theorem target_binary_eq (p q : Poisson.Completed.Functions (Fin D.size) ℂ) :
    PowerSeriesModuleBridge.binaryBridge
      (PowerSeriesModule.single 0
          (Gauge.LaurentSourceAlgebra.nativeBivector (ReflectionSource.base D)) +
        PowerSeriesModule.map Gauge.LaurentSourceAlgebra.nativeBivector (ReflectionSource.target D).val) p q =
      Poisson.ComparisonMatrix.hbar •
        Poisson.Completed.bracket (Poisson.ComparisonMatrix.targetCoefficients D) p q := by
  rw [target_native_family_eq]
  exact total_binary_eq D.targetWeightData p q

end Complex

end EnvelopingIsomorphism.Rees.CompletedPoissonBridge
