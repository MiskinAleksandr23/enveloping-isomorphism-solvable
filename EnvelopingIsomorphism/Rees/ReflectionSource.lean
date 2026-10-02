import EnvelopingIsomorphism.Rees.RecoveredPoissonMC
import EnvelopingIsomorphism.Deformation.Gauge.LaurentSourceComplex

/-! The two recovered Rees perturbations on the precise native source carrier
of gauge reflection. Their common base and Maurer-Cartan equations are already
proved; this file only aligns the explicit equivalent quadratic formulas. -/

noncomputable section

namespace EnvelopingIsomorphism.Rees.ReflectionSource

open EnvelopingIsomorphism.Deformation EnvelopingIsomorphism.FormalSeries

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

variable {k L M : Type*} [Field k] [CharZero k]
variable [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]
variable (D : Identification.RecoveredData k L M)

abbrev base := PoissonMCFamily.baseLaurentBivector D.sourceWeightData

abbrev base_isMaurerCartan := PoissonMCFamily.baseLaurentBivector_isMaurerCartan D.sourceWeightData

abbrev Complex := Gauge.LaurentSchouten.sourceComplex (base D) (base_isMaurerCartan D)

abbrev Quadratic := Gauge.LaurentSchouten.sourceQuadratic (base D) (base_isMaurerCartan D)

abbrev MC := Gauge.LaurentSchouten.SourceMC (base D) (base_isMaurerCartan D)

theorem quadratic_eq : Quadratic D = PoissonMCFamily.sourceQuadratic (k := k) (d := D.size) := by
  rw [PoissonMCFamily.sourceQuadratic_eq]
  rfl

/-- This conversion changes only proof fields and preserves every coefficient. -/
def ofRecoveredMC
    (b : Gauge.MCSeries ((RecoveredPoissonMC.sourceComplex D).d 1 2).hom
      (PoissonMCFamily.sourceQuadratic (k := k) (d := D.size))) : MC D :=
  ⟨b.val, b.property.1, by
    let v : Gauge.LaurentSchouten.Families k D.size := b.val
    have h : Gauge.quadraticCurvature ((Complex D).d 1 2).hom
        (PoissonMCFamily.sourceQuadratic (k := k) (d := D.size)) v = 0 := b.property.2
    have he := congrArg (fun I => Gauge.quadraticCurvature ((Complex D).d 1 2).hom I v) (quadratic_eq D)
    exact he.trans h⟩

@[simp] theorem ofRecoveredMC_val
    (b : Gauge.MCSeries ((RecoveredPoissonMC.sourceComplex D).d 1 2).hom
      (PoissonMCFamily.sourceQuadratic (k := k) (d := D.size))) :
    (ofRecoveredMC D b).val = b.val := rfl

/-- The actual source Rees perturbation in the shared reflection carrier. -/
def source : MC D := ofRecoveredMC D (RecoveredPoissonMC.sourceMCSeries D)

/-- The actual target Rees perturbation in the same shared reflection carrier. -/
def target : MC D := ofRecoveredMC D (RecoveredPoissonMC.targetMCSeries D)

@[simp] theorem source_val : (source D).val = PoissonMCFamily.perturbationSeries D.sourceWeightData := rfl

@[simp] theorem target_val : (target D).val = PoissonMCFamily.perturbationSeries D.targetWeightData := rfl

theorem target_val_common_base : (target D).val =
    PoissonMCFamily.totalLaurentSeries D.targetWeightData -
      PowerSeriesModule.single (k := LaurentSeries k) 0 (base D) :=
  RecoveredPoissonMC.targetMCSeries_val_common_base D

end EnvelopingIsomorphism.Rees.ReflectionSource
