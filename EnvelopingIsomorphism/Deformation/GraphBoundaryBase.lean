import EnvelopingIsomorphism.Deformation.GraphBoundaryProfiles
import EnvelopingIsomorphism.Deformation.Gauge.CanonicalTangentExactness

/-! The scalar graph boundary relation produces actual Laurent base-star
associativity. This extension concerns the fixed positive-h base cochain;
it does not assert the Taylor MC identity on arbitrary Laurent directions. -/

noncomputable section
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.GraphBoundaryBase
open EnvelopingIsomorphism.FormalSeries
open MiddleExactPerturbation

universe u v
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

/-- Positive-to-Laurent embedding commutes with the actual insertion convolution. -/
theorem toLaurent_insertion
    (B C : PowerSeriesModule k (Binary k V)) :
    toLaurent (PowerSeriesModule.applyBilinear PowerSeriesModule.insertBinaryLinear B C) =
      LaurentModule.insertBinarySeries (toLaurent B) (toLaurent C) := by
  rw [PowerSeriesModule.applyBilinear_insertBinary]
  rw [show toLaurent
      (PowerSeriesModule.applyBilinear PowerSeriesModule.insertLeftLinear B C -
        PowerSeriesModule.applyBilinear PowerSeriesModule.insertRightLinear B C) =
      toLaurent (PowerSeriesModule.applyBilinear PowerSeriesModule.insertLeftLinear B C) -
        toLaurent (PowerSeriesModule.applyBilinear PowerSeriesModule.insertRightLinear B C) from
    map_sub (PositiveLaurent.toLaurentLinear (k := k)) _ _]
  rw [toLaurent_applyBilinear, toLaurent_applyBilinear]
  rfl

/-- A proved positive coefficient insertion identity controls all bounded-below
Laurent arguments, through the existing genuine Laurent cochain evaluation. -/
theorem laurent_associative_of_insertion_zero
    (B : PowerSeriesModule k (Binary k V))
    (h : PowerSeriesModule.applyBilinear PowerSeriesModule.insertBinaryLinear B B = 0) :
    ∀ x y z, Gauge.LaurentConjugation.evaluateCoefficient (toLaurent B)
      (Gauge.LaurentConjugation.evaluateCoefficient (toLaurent B) x y) z =
      Gauge.LaurentConjugation.evaluateCoefficient (toLaurent B) x
        (Gauge.LaurentConjugation.evaluateCoefficient (toLaurent B) y z) := by
  apply (insertBinary_self_eq_zero_iff _).mp
  change insertBinary (LaurentModule.binaryEvaluation (toLaurent B))
    (LaurentModule.binaryEvaluation (toLaurent B)) = 0
  rw [← LaurentModule.ternaryEvaluation_insertBinary, ← toLaurent_insertion, h,
    toLaurent_zero, map_zero]

variable [CharZero k] [Algebra ℝ k] {d : ℕ}
local instance : CharZero (LaurentSeries k) := Gauge.LaurentSchouten.scalarCharZero

omit [Algebra ℝ k] in
/-- The native Laurent source-base MC hypothesis implies the polynomial
Poisson equation by extracting the h² coefficient of its actual bracket. -/
theorem poisson_of_baseMC
    (π : GraphWeightedInsertion.Bivector (k := k) (d := d))
    (hπ : (polynomialSchoutenDGLA k d).laurent.IsMaurerCartan
      (Gauge.CanonicalTangentExactness.baseBivector k d π)) :
    (show Multiderivation k (MvPolynomial (Fin d) k) 3 from
      schoutenBracket k d 1 1 π π) = 0 := by
  have hcurv : (2 : LaurentSeries k)⁻¹ •
      (polynomialSchoutenDGLA k d).laurent.bracket 1 1
        (LaurentModule.single (k := k) 1 π) (LaurentModule.single (k := k) 1 π) = 0 := by
    change (polynomialSchoutenDGLA k d).laurent.curvature _ = 0 at hπ
    unfold SignedDGLA.curvature at hπ
    rw [Gauge.LaurentSchouten.laurent_d_zero] at hπ
    simp only [LinearMap.zero_apply, zero_add] at hπ
    exact hπ
  have hb := (smul_eq_zero.mp hcurv).resolve_left (inv_ne_zero (two_ne_zero))
  rw [SignedDGLA.laurent_bracket, SignedDGLA.laurentBracket_single] at hb
  have hc := congrArg (fun F ↦ LaurentModule.coeff F (2 : ℤ)) hb
  simp only [LaurentModule.coeff_single, LaurentModule.coeff_zero,
    show (2 : ℤ) = 1 + 1 from rfl, if_true] at hc
  exact hc

/-- The exact first graph-identity field follows from normalized scalar boundary
relations and the native polynomial Poisson equation. -/
theorem canonical_starAssociative
    (h : GraphBoundaryProfiles.CanonicalScalarBoundaryRelation (k := k))
    (π : GraphWeightedInsertion.Bivector (k := k) (d := d))
    (hπ : (show Multiderivation k (MvPolynomial (Fin d) k) 3 from
      schoutenBracket k d 1 1 π π) = 0) :
    Gauge.CanonicalTangentExactness.StarAssociative k d π :=
  laurent_associative_of_insertion_zero _ (GraphBoundaryProfiles.canonical_insertion_zero h π hπ)

/-- The first field of the terminal graph contract, with exactly its existing
native source-base MC premise, is produced by a pure scalar boundary relation. -/
theorem canonical_starAssociative_of_baseMC
    (h : GraphBoundaryProfiles.CanonicalScalarBoundaryRelation (k := k))
    (π : GraphWeightedInsertion.Bivector (k := k) (d := d))
    (hπ : (polynomialSchoutenDGLA k d).laurent.IsMaurerCartan
      (Gauge.CanonicalTangentExactness.baseBivector k d π)) :
    Gauge.CanonicalTangentExactness.StarAssociative k d π :=
  canonical_starAssociative h π (poisson_of_baseMC π hπ)

end EnvelopingIsomorphism.Deformation.GraphBoundaryBase
