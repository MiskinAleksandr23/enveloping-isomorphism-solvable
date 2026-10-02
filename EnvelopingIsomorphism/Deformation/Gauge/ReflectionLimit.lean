import EnvelopingIsomorphism.Deformation.Gauge.ReflectionInduction

/-!
The compatible source product acts by one actual linear equivalence on the
completed function module.  Its transport of the represented Poisson structure
follows coefficientwise from the finite source actions.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open CategoryTheory
open EnvelopingIsomorphism.FormalSeries
open PowerSeriesModule

theorem Compatible.map {R R' : Type*} [Ring R] [Ring R'] (ρ : R →+* R')
    {F : ℕ → PowerSeries R} (hF : Compatible F) :
    Compatible (fun n => PowerSeries.map ρ (F n)) := by
  intro N i hi
  simpa only [PowerSeries.coeff_map] using congrArg ρ (hF N i hi)

theorem compatibleLimit_map {R R' : Type*} [Ring R] [Ring R']
    (ρ : R →+* R') (F : ℕ → PowerSeries R) :
    PowerSeries.map ρ (compatibleLimit F) = compatibleLimit (fun n => PowerSeries.map ρ (F n)) := by
  ext n
  simp only [PowerSeries.coeff_map, coeff_compatibleLimit]

variable {k V W : Type*} [CommRing k]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

theorem AgreeBelow.map {N : ℕ} {x y : PowerSeriesModule k V} (hxy : AgreeBelow N x y)
    (L : V →ₗ[k] W) : AgreeBelow N (map L x) (map L y) := by
  intro i hi
  rw [coeffV_map, coeffV_map, hxy i hi]

theorem AgreeBelow.add_left {N : ℕ} {x y : PowerSeriesModule k V} (hxy : AgreeBelow N x y)
    (b : PowerSeriesModule k V) : AgreeBelow N (b + x) (b + y) := by
  intro i hi
  rw [coeffV_add, coeffV_add, hxy i hi]

theorem extendBinary_congr_operation {N : ℕ}
    {B C : PowerSeriesModule k (V →ₗ[k] V →ₗ[k] V)} (hBC : AgreeBelow N B C)
    (x y : PowerSeriesModule k V) :
    AgreeBelow N (extendBinary B x y) (extendBinary C x y) := by
  intro n hn
  rw [coeffV_extendBinary, coeffV_extendBinary]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hij
  have hij' := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  apply Finset.sum_congr rfl
  rintro ⟨a, b⟩ hab
  have hab' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  rw [hBC a (by omega)]

namespace ElementaryComparison

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
variable {V : Type*} [AddCommGroup V] [Module k V]
variable (ρ : RS →+* Module.End k V)

def representedStages (G : GaugeUnit RT) (hG : G • F.quantize b = F.quantize c) (n : ℕ) :
    PowerSeries (Module.End k V) := PowerSeries.map ρ (F.operatorStages b c G hG n)

theorem representedStages_compatible (G : GaugeUnit RT) (hG : G • F.quantize b = F.quantize c) :
    Compatible (F.representedStages b c ρ G hG) :=
  (F.operatorStages_compatible b c G hG).map ρ

theorem representedStages_constantCoeff (G : GaugeUnit RT)
    (hG : G • F.quantize b = F.quantize c) :
    PowerSeries.constantCoeff (F.representedStages b c ρ G hG 1) = 1 := by
  rw [representedStages, ← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff, F.operatorStages_constantCoeff, map_one]

/-- A genuine equivalence over the completed scalar ring, obtained from the reflected corrections. -/
def reflectedLinearEquiv (G : GaugeUnit RT) (hG : G • F.quantize b = F.quantize c) :
    PowerSeriesModule k V ≃ₗ[PowerSeries k] PowerSeriesModule k V :=
  compatibleGaugeEquiv (F.representedStages b c ρ G hG) (F.representedStages_constantCoeff b c ρ G hG)

/-- Exact structure transport at the limit, for an affine linear representation of MC states. -/
theorem reflectedLinearEquiv_intertwines
    (base : PowerSeriesModule k (V →ₗ[k] V →ₗ[k] V))
    (inclusion : C.X 1 →ₗ[k] V →ₗ[k] V →ₗ[k] V)
    (hsource : ∀ s : S, ∀ x y : PowerSeriesModule k V,
      operator (PowerSeries.map ρ (F.sourceOperators s).series)
        (extendBinary (base + map inclusion b.val) x y) =
      extendBinary (base + map inclusion (s • b).val)
        (operator (PowerSeries.map ρ (F.sourceOperators s).series) x)
        (operator (PowerSeries.map ρ (F.sourceOperators s).series) y))
    (G : GaugeUnit RT) (hG : G • F.quantize b = F.quantize c) (x y : PowerSeriesModule k V) :
    F.reflectedLinearEquiv b c ρ G hG (extendBinary (base + map inclusion b.val) x y) =
      extendBinary (base + map inclusion c.val)
        (F.reflectedLinearEquiv b c ρ G hG x) (F.reflectedLinearEquiv b c ρ G hG y) := by
  apply compatibleGaugeEquiv_intertwines (F.representedStages_compatible b c ρ G hG)
  intro N x y
  change AgreeBelow N
    (operator (PowerSeries.map ρ (F.sourceOperators (F.sources b c G hG N)).series)
      (extendBinary (base + map inclusion b.val) x y)) _
  rw [hsource]
  apply extendBinary_congr_operation
  intro i hi
  exact (((F.sources_agree b c G hG N).map inclusion).add_left base) i (by omega)

/-- Any fixed bilinear product preserved by all source gauges is also preserved by the limit. -/
theorem reflectedLinearEquiv_preserves
    (B : PowerSeriesModule k (V →ₗ[k] V →ₗ[k] V))
    (hsource : ∀ s : S, ∀ x y : PowerSeriesModule k V,
      operator (PowerSeries.map ρ (F.sourceOperators s).series) (extendBinary B x y) =
        extendBinary B (operator (PowerSeries.map ρ (F.sourceOperators s).series) x)
          (operator (PowerSeries.map ρ (F.sourceOperators s).series) y))
    (G : GaugeUnit RT) (hG : G • F.quantize b = F.quantize c) (x y : PowerSeriesModule k V) :
    F.reflectedLinearEquiv b c ρ G hG (extendBinary B x y) =
      extendBinary B (F.reflectedLinearEquiv b c ρ G hG x) (F.reflectedLinearEquiv b c ρ G hG y) := by
  apply compatibleGaugeEquiv_intertwines (F.representedStages_compatible b c ρ G hG)
  intro N x y i hi
  change coeffV i (operator (PowerSeries.map ρ (F.sourceOperators (F.sources b c G hG N)).series)
    (extendBinary B x y)) = _
  rw [hsource]
  rfl

end ElementaryComparison

end EnvelopingIsomorphism.Deformation.Gauge
