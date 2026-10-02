import EnvelopingIsomorphism.Rees.PoissonMCFamily
import EnvelopingIsomorphism.Identification.RecoveredData

/-! The two actual source MC series associated to recovered enveloping data,
living in one common Laurent-twisted Schouten complex. -/

namespace EnvelopingIsomorphism.Rees.RecoveredPoissonMC

open Module
open EnvelopingIsomorphism.Deformation EnvelopingIsomorphism.FormalSeries

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {k L M : Type*} [Field k] [CharZero k]
variable [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]
variable (D : Identification.RecoveredData k L M)

omit [CharZero k] in
/-- The prescribed native zero-fiber Lie map gives equality of the two complete zero tables. -/
theorem zero_coeff_eq (i j r : Fin D.size) :
    Polynomial.eval 0 (D.sourceWeightData.coeff i j r) =
      Polynomial.eval 0 (D.targetWeightData.coeff i j r) := by
  rw [← Family.fiber_structureCoeff, ← Family.fiber_structureCoeff]
  have h := D.zeroLieEquiv.map_lie
    (Family.fiberBasis D.sourceWeightData 0 i) (Family.fiberBasis D.sourceWeightData 0 j)
  rw [D.zeroLieEquiv_basis, D.zeroLieEquiv_basis] at h
  have hr := congrArg (fun x => (Family.fiberBasis D.targetWeightData 0).repr x r) h
  change (Family.fiberBasis D.targetWeightData 0).repr
    (D.zeroLieEquiv.toLinearEquiv ⁅Family.fiberBasis D.sourceWeightData 0 i,
      Family.fiberBasis D.sourceWeightData 0 j⁆) r = _ at hr
  rw [D.zeroLieEquiv_toLinearEquiv] at hr
  simpa [Basis.equiv] using hr

omit [CharZero k] in
theorem constantBivector_eq : PoissonMCFamily.constantBivector D.sourceWeightData =
    PoissonMCFamily.constantBivector D.targetWeightData :=
  PoissonMCFamily.constantBivector_eq_of_zero D.sourceWeightData D.targetWeightData (zero_coeff_eq D)

theorem baseLaurentBivector_eq : PoissonMCFamily.baseLaurentBivector D.sourceWeightData =
    PoissonMCFamily.baseLaurentBivector D.targetWeightData :=
  PoissonMCFamily.baseLaurentBivector_eq_of_zero D.sourceWeightData D.targetWeightData (zero_coeff_eq D)

/-- One common complex, twisted at the actual common `h * π₀`. -/
abbrev sourceComplex := (PoissonMCFamily.twistedSource D.sourceWeightData).complex

def sourceMCSeries : Gauge.MCSeries ((sourceComplex D).d 1 2).hom
    (PoissonMCFamily.sourceQuadratic (k := k) (d := D.size)) :=
  PoissonMCFamily.sourceMCSeries D.sourceWeightData

theorem source_target_d_one : ((sourceComplex D).d 1 2).hom =
    ((PoissonMCFamily.twistedSource D.targetWeightData).complex.d 1 2).hom := by
  calc
    ((sourceComplex D).d 1 2).hom =
        PoissonMCFamily.laurentBivectorBracket (PoissonMCFamily.baseLaurentBivector D.sourceWeightData) :=
      PoissonMCFamily.twistedSource_d_one D.sourceWeightData
    _ = PoissonMCFamily.laurentBivectorBracket
        (PoissonMCFamily.baseLaurentBivector D.targetWeightData) :=
      congrArg PoissonMCFamily.laurentBivectorBracket (baseLaurentBivector_eq D)
    _ = ((PoissonMCFamily.twistedSource D.targetWeightData).complex.d 1 2).hom :=
      (PoissonMCFamily.twistedSource_d_one D.targetWeightData).symm

/-- The target perturbation is MC in the very same source complex, with no common-base hypothesis. -/
def targetMCSeries : Gauge.MCSeries ((sourceComplex D).d 1 2).hom
    (PoissonMCFamily.sourceQuadratic (k := k) (d := D.size)) :=
  ⟨PoissonMCFamily.perturbationSeries D.targetWeightData,
    PoissonMCFamily.perturbationSeries_positive D.targetWeightData, by
      rw [source_target_d_one]
      exact PoissonMCFamily.perturbationSeries_curvature D.targetWeightData⟩

@[simp] theorem sourceMCSeries_val : (sourceMCSeries D).val =
    PoissonMCFamily.perturbationSeries D.sourceWeightData := rfl

@[simp] theorem targetMCSeries_val : (targetMCSeries D).val =
    PoissonMCFamily.perturbationSeries D.targetWeightData := rfl

theorem targetMCSeries_val_common_base : (targetMCSeries D).val =
    PoissonMCFamily.totalLaurentSeries D.targetWeightData -
      PowerSeriesModule.single (k := LaurentSeries k) 0
        (PoissonMCFamily.baseLaurentBivector D.sourceWeightData) := by
  change PoissonMCFamily.totalLaurentSeries D.targetWeightData -
    PowerSeriesModule.single (k := LaurentSeries k) 0
      (PoissonMCFamily.baseLaurentBivector D.targetWeightData) = _
  rw [baseLaurentBivector_eq]

end

end EnvelopingIsomorphism.Rees.RecoveredPoissonMC
