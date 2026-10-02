import EnvelopingIsomorphism.Deformation.Gauge.ElementaryComparison

/-!
The complete gauge-reflection induction.  Elementary source corrections are
chosen coherently, multiplied in order, and give a genuine formal unit limit.
Forward path lifting is an input producer obligation; reflection itself is
proved from the cohomological obstruction step.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge.ElementaryComparison

open CategoryTheory
open EnvelopingIsomorphism.FormalSeries
open PowerSeriesModule

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

structure Approximation (N : ℕ) where
  source : S
  target : GaugeUnit RT
  target_near : NearIdentity N target.series
  source_agrees : AgreeBelow N (source • b).val c.val
  target_transports : target • F.quantize (source • b) = F.quantize c

def initial (G : GaugeUnit RT) (hG : G • F.quantize b = F.quantize c) :
    F.Approximation b c 1 where
  source := 1
  target := G
  target_near := G.near_one
  source_agrees := by
    intro i hi
    have he : i = 0 := by omega
    subst i
    simp only [one_smul, b.property.1, c.property.1]
  target_transports := by simpa only [one_smul] using hG

structure Step (N : ℕ) (hN : 0 < N) (A : F.Approximation b c N) where
  correction : C.X 0
  result : F.Approximation b c (N + 1)
  source_eq : result.source = F.sourceElementary N hN correction * A.source

theorem step_nonempty (N : ℕ) (hN : 0 < N) (A : F.Approximation b c N) :
    Nonempty (F.Step b c N hN A) := by
  obtain ⟨y, G', hnear, hagree, hmap⟩ := F.improve N hN (A.source • b) c A.target
    A.target_near A.source_agrees A.target_transports
  exact ⟨{
    correction := y
    result := {
      source := F.sourceElementary N hN y * A.source
      target := G'
      target_near := hnear
      source_agrees := by simpa only [mul_smul] using hagree
      target_transports := by simpa only [mul_smul] using hmap }
    source_eq := rfl }⟩

def step (N : ℕ) (hN : 0 < N) (A : F.Approximation b c N) : F.Step b c N hN A :=
  Classical.choice (F.step_nonempty b c N hN A)

/-- The nth approximation has already settled all coefficients below n+1. -/
def approximations (G : GaugeUnit RT) (hG : G • F.quantize b = F.quantize c) :
    (n : ℕ) → F.Approximation b c (n + 1)
  | 0 => F.initial b c G hG
  | n + 1 => (F.step b c (n + 1) (Nat.succ_pos n) (approximations G hG n)).result

def sources (G : GaugeUnit RT) (hG : G • F.quantize b = F.quantize c) (n : ℕ) : S :=
  (F.approximations b c G hG n).source

def corrections (G : GaugeUnit RT) (hG : G • F.quantize b = F.quantize c) (n : ℕ) : C.X 0 :=
  (F.step b c (n + 1) (Nat.succ_pos n) (F.approximations b c G hG n)).correction

@[simp] theorem sources_zero (G : GaugeUnit RT) (hG : G • F.quantize b = F.quantize c) :
    F.sources b c G hG 0 = 1 := rfl

theorem sources_succ (G : GaugeUnit RT) (hG : G • F.quantize b = F.quantize c) (n : ℕ) :
    F.sources b c G hG (n + 1) =
      F.sourceElementary (n + 1) (Nat.succ_pos n) (F.corrections b c G hG n) * F.sources b c G hG n :=
  (F.step b c (n + 1) (Nat.succ_pos n) (F.approximations b c G hG n)).source_eq

theorem sources_agree (G : GaugeUnit RT) (hG : G • F.quantize b = F.quantize c) (n : ℕ) :
    AgreeBelow (n + 1) (F.sources b c G hG n • b).val c.val :=
  (F.approximations b c G hG n).source_agrees

def operatorStages (G : GaugeUnit RT) (hG : G • F.quantize b = F.quantize c) (n : ℕ) :
    PowerSeries RS := (F.sourceOperators (F.sources b c G hG n)).series

theorem operatorStages_step (G : GaugeUnit RT) (hG : G • F.quantize b = F.quantize c) (n : ℕ) :
    toJet (n + 1) (F.operatorStages b c G hG (n + 1)) =
      toJet (n + 1) (F.operatorStages b c G hG n) := by
  unfold operatorStages
  rw [F.sources_succ, map_mul, GaugeUnit.series_mul, map_mul,
    F.source_near (n + 1) (Nat.succ_pos n), one_mul]

theorem operatorStages_compatible (G : GaugeUnit RT) (hG : G • F.quantize b = F.quantize c) :
    Compatible (F.operatorStages b c G hG) := by
  intro n i hi
  exact ((toJet_eq_iff.mp (F.operatorStages_step b c G hG n)) i (by omega)).symm

theorem operatorStages_constantCoeff (G : GaugeUnit RT) (hG : G • F.quantize b = F.quantize c) :
    PowerSeries.constantCoeff (F.operatorStages b c G hG 1) = 1 :=
  GaugeUnit.constantCoeff_series (F.sourceOperators (F.sources b c G hG 1))

/-- The coherent source product gives one actual invertible formal operator. -/
def limitUnit (G : GaugeUnit RT) (hG : G • F.quantize b = F.quantize c) : (PowerSeries RS)ˣ :=
  compatibleUnit (F.operatorStages b c G hG) (F.operatorStages_constantCoeff b c G hG)

theorem limitUnit_toJet (G : GaugeUnit RT) (hG : G • F.quantize b = F.quantize c) (N : ℕ) :
    toJet N (F.limitUnit b c G hG : PowerSeries RS) = toJet N (F.operatorStages b c G hG N) :=
  compatibleLimit_toJet (F.operatorStages_compatible b c G hG) N

/-- Gauge reflection produces a compatible infinite product of elementary source gauges.
The limit is an actual unit; no unrelated choices of finite quotient equivalences are used. -/
theorem exists_reflection_product (G : GaugeUnit RT) (hG : G • F.quantize b = F.quantize c) :
    ∃ s : ℕ → S, ∃ y : ℕ → C.X 0, ∃ U : (PowerSeries RS)ˣ,
      s 0 = 1 ∧
      (∀ n, s (n + 1) = F.sourceElementary (n + 1) (Nat.succ_pos n) (y n) * s n) ∧
      (∀ n, AgreeBelow (n + 1) (s n • b).val c.val) ∧
      (∀ N, toJet N (U : PowerSeries RS) = toJet N (F.sourceOperators (s N)).series) := by
  exact ⟨F.sources b c G hG, F.corrections b c G hG, F.limitUnit b c G hG,
    F.sources_zero b c G hG, F.sources_succ b c G hG,
    F.sources_agree b c G hG, F.limitUnit_toJet b c G hG⟩

end EnvelopingIsomorphism.Deformation.Gauge.ElementaryComparison
