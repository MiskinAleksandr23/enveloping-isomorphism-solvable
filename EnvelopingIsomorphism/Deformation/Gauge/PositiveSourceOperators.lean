import EnvelopingIsomorphism.Deformation.Gauge.LaurentSourceComplex
import EnvelopingIsomorphism.Deformation.MiddleExactPerturbation

/-! Positive formal operator representatives of the genuine twisted source differential. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge.PositiveSourceOperators

open EnvelopingIsomorphism.FormalSeries

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

section MonomialAction

universe u v
variable {k : Type u} [Field k]
  {U V W : Type v} [AddCommGroup U] [Module k U]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Acting by a monomial coefficient operator is exactly insertion of a monomial
in the first slot of the original bilinear operation. -/
theorem act_single_left (B : U →ₗ[k] V →ₗ[k] W) (u : U) (n : ℕ) :
    MiddleExactPerturbation.act (PowerSeriesModule.single (k := k) n (B u)) =
      LaurentModule.extendBilinear B (LaurentModule.single (k := k) (n : ℤ) u) := by
  rw [MiddleExactPerturbation.act, MiddleExactPerturbation.toLaurent_single]
  have h : (LaurentModule.linearApply (LaurentModule.single (k := k) (n : ℤ) (B u))).restrictScalars k =
      (LaurentModule.extendBilinear B (LaurentModule.single (k := k) (n : ℤ) u)).restrictScalars k := by
    apply LaurentModule.linear_ext_of_bounded _ _ (n : ℤ)
    · intro b x hx
      change LaurentModule.BoundedBelow (b + n)
        (LaurentModule.linearApply (LaurentModule.single (k := k) (n : ℤ) (B u)) x)
      simpa only [add_comm b (n : ℤ)] using LaurentModule.boundedBelow_linearApply
        (LaurentModule.single (k := k) (n : ℤ) (B u)) x
        (LaurentModule.boundedBelow_single _ _) hx
    · intro b x hx
      change LaurentModule.BoundedBelow (b + n)
        (LaurentModule.extendBilinear B (LaurentModule.single (k := k) (n : ℤ) u) x)
      simpa only [add_comm b (n : ℤ)] using LaurentModule.boundedBelow_extendBilinear B
        (LaurentModule.single (k := k) (n : ℤ) u) x (LaurentModule.boundedBelow_single _ _) hx
    · intro e v
      change LaurentModule.linearApply (LaurentModule.single (k := k) (n : ℤ) (B u))
          (LaurentModule.single (k := k) e v) =
        LaurentModule.extendBilinear B (LaurentModule.single (k := k) (n : ℤ) u)
          (LaurentModule.single (k := k) e v)
      rw [LaurentModule.linearApply_single, LaurentModule.extendBilinear_single]
  exact LinearMap.ext (fun x => DFunLike.congr_fun h x)

theorem act_injective : Function.Injective (MiddleExactPerturbation.act (k := k) (U := U) (V := V)) :=
  LaurentModule.linearApply_injective.comp MiddleExactPerturbation.toLaurent_injective

end MonomialAction

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

local instance : CharZero (LaurentSchouten.Scalars K) := LaurentSchouten.scalarCharZero

def coefficientZero : SchoutenBivector K d →ₗ[K] SchoutenVector K d →ₗ[K] SchoutenBivector K d :=
  schoutenBracket K d 1 0

def C0 (π₀ : SchoutenBivector K d) :
    MiddleExactPerturbation.OperatorSeries (k := K) (SchoutenVector K d) (SchoutenBivector K d) :=
  PowerSeriesModule.single 1 (coefficientZero π₀)

def C1 (π₀ : SchoutenBivector K d) :
    MiddleExactPerturbation.OperatorSeries (k := K) (SchoutenBivector K d) (SchoutenTrivector K d) :=
  PowerSeriesModule.single 1 (schoutenBivectorBracket π₀)

@[simp] theorem coeff_C0 (π₀ : SchoutenBivector K d) (n : ℕ) :
    PowerSeriesModule.coeffV n (C0 π₀) = if n = 1 then coefficientZero π₀ else 0 := by
  simp only [C0, PowerSeriesModule.coeffV_single]

@[simp] theorem coeff_C1 (π₀ : SchoutenBivector K d) (n : ℕ) :
    PowerSeriesModule.coeffV n (C1 π₀) = if n = 1 then schoutenBivectorBracket π₀ else 0 := by
  simp only [C1, PowerSeriesModule.coeffV_single]

@[simp] theorem coeff_zero_C0 (π₀ : SchoutenBivector K d) : PowerSeriesModule.coeffV 0 (C0 π₀) = 0 := by
  simp only [coeff_C0, Nat.zero_ne_one, if_false]

@[simp] theorem coeff_zero_C1 (π₀ : SchoutenBivector K d) : PowerSeriesModule.coeffV 0 (C1 π₀) = 0 := by
  simp only [coeff_C1, Nat.zero_ne_one, if_false]

variable (π₀ : SchoutenBivector K d)
variable (hπ : (polynomialSchoutenDGLA K d).laurent.IsMaurerCartan (LaurentModule.single (k := K) 1 π₀))

/-- The positive unary-to-binary operator represents the exact native source differential. -/
theorem act_C0 : MiddleExactPerturbation.act (C0 π₀) =
    ((LaurentSchouten.sourceComplex (LaurentModule.single (k := K) 1 π₀) hπ).d 0 1).hom := by
  rw [C0, act_single_left]
  change LaurentModule.extendBilinear coefficientZero
      (LaurentModule.single (k := K) 1 π₀) =
    ((polynomialSchoutenDGLA K d).laurent.twist (LaurentModule.single (k := K) 1 π₀) hπ).d 0
  rw [SignedDGLA.twist_d]
  simp only [SignedDGLA.twistedD, LaurentSchouten.laurent_d_zero, zero_add]
  rfl

/-- The positive binary-to-ternary operator represents the exact native source differential. -/
theorem act_C1 : MiddleExactPerturbation.act (C1 π₀) =
    ((LaurentSchouten.sourceComplex (LaurentModule.single (k := K) 1 π₀) hπ).d 1 2).hom := by
  rw [C1, act_single_left, LaurentSchouten.sourceComplex_d_one]
  rfl

include hπ in
/-- The actual positive operator coefficients obey the differential's square-zero identity. -/
theorem compose_eq_zero : PowerSeriesModule.linearCompose (C1 π₀) (C0 π₀) = 0 := by
  apply act_injective (k := K) (U := SchoutenVector K d) (V := SchoutenTrivector K d)
  rw [← MiddleExactPerturbation.act_comp, act_C0 π₀ hπ, act_C1 π₀ hπ]
  have hz : MiddleExactPerturbation.act
      (0 : MiddleExactPerturbation.OperatorSeries (k := K) (SchoutenVector K d) (SchoutenTrivector K d)) = 0 := by
    simp only [MiddleExactPerturbation.act, MiddleExactPerturbation.toLaurent_zero, map_zero]
  rw [hz]
  apply LinearMap.ext
  intro X
  exact ContractibleComplex.differential_squared
    (LaurentSchouten.sourceComplex (LaurentModule.single (k := K) 1 π₀) hπ) 0 1 2 X

end EnvelopingIsomorphism.Deformation.Gauge.PositiveSourceOperators
