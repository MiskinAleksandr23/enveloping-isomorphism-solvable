import EnvelopingIsomorphism.Deformation.ContractibleComplex
import EnvelopingIsomorphism.FormalSeries.Endomorphism
import EnvelopingIsomorphism.FormalSeries.PowerSeriesModule
import EnvelopingIsomorphism.FormalSeries.LaurentBinaryComposition

/-!
# Formal perturbation of exactness at the middle of a short sequence

Only `range A₀ = ker B₀` and the actual convolution identity `BA = 0` are
required. No injectivity or surjectivity at the endpoints is assumed. The
proof constructs two formal inverses in the endomorphism ring of the middle
space, then acts on the actual Laurent modules of vectors.
-/

namespace EnvelopingIsomorphism.Deformation.MiddleExactPerturbation

noncomputable section

open EnvelopingIsomorphism.FormalSeries

universe u v
variable {k : Type u} [Field k]
variable {U V W : Type v} [AddCommGroup U] [Module k U]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

section Splitting

/-- A reflexive generalized inverse; unlike an arbitrary extension, it satisfies `TBT=T`. -/
def rightSplitting (B : V →ₗ[k] W) : W →ₗ[k] V :=
  (ContractibleComplex.generalizedInverse B).comp
    (B.comp (ContractibleComplex.generalizedInverse B))

theorem rightSplitting_outer (B : V →ₗ[k] W) (v : V) :
    B (rightSplitting B (B v)) = B v := by
  simp only [rightSplitting, LinearMap.comp_apply]
  rw [ContractibleComplex.generalizedInverse_apply,
    ContractibleComplex.generalizedInverse_apply]

theorem rightSplitting_inner (B : V →ₗ[k] W) (w : W) :
    rightSplitting B (B (rightSplitting B w)) = rightSplitting B w := by
  simp only [rightSplitting, LinearMap.comp_apply]
  rw [ContractibleComplex.generalizedInverse_apply,
    ContractibleComplex.generalizedInverse_apply]

/-- Projection onto the kernel of the outgoing constant map. -/
def middleProjection (B : V →ₗ[k] W) : Module.End k V :=
  LinearMap.id - (rightSplitting B).comp B

theorem middleProjection_mem_ker (B : V →ₗ[k] W) (v : V) :
    middleProjection B v ∈ LinearMap.ker B := by
  change B (v - rightSplitting B (B v)) = 0
  rw [map_sub, rightSplitting_outer, sub_self]

/-- A preimage operator for the kernel, extended linearly to the whole middle space. -/
def leftSplitting (A : U →ₗ[k] V) (B : V →ₗ[k] W) : V →ₗ[k] U :=
  (ContractibleComplex.generalizedInverse A).comp (middleProjection B)

theorem middle_splitting (A : U →ₗ[k] V) (B : V →ₗ[k] W)
    (h : LinearMap.range A = LinearMap.ker B) :
    A.comp (leftSplitting A B) + (rightSplitting B).comp B = LinearMap.id := by
  ext v
  have hp : middleProjection B v ∈ LinearMap.range A := by
    rw [h]
    exact middleProjection_mem_ker B v
  change A (ContractibleComplex.generalizedInverse A (middleProjection B v)) +
    rightSplitting B (B v) = v
  rw [ContractibleComplex.generalizedInverse_apply_of_mem_range A hp]
  exact sub_add_cancel _ _

end Splitting

section FormalAlgebra

variable {R : Type*} [Ring R]

/-- The two-inverse identity proving exactness only in the middle. -/
theorem two_inverse_identity (F G P : PowerSeries R)
    (hF : G * F = 0) (hP : P * G = G)
    (hK : PowerSeries.constantCoeff (F + G) = 1)
    (hL : PowerSeries.constantCoeff (1 - P + G) = 1) :
    F * inverseOne (F + G) + inverseOne (1 - P + G) * G = 1 := by
  let K := F + G
  let L := 1 - P + G
  have hLG : L * G = G * K := by
    dsimp [L, K]
    rw [add_mul, sub_mul, one_mul, hP, sub_self, zero_add, mul_add, hF, zero_add]
  have hmove : G * inverseOne K = inverseOne L * G := by
    calc
      G * inverseOne K = (inverseOne L * L) * (G * inverseOne K) := by
        rw [inverseOne_mul hL, one_mul]
      _ = inverseOne L * ((L * G) * inverseOne K) := by simp only [mul_assoc]
      _ = inverseOne L * ((G * K) * inverseOne K) := by rw [hLG]
      _ = inverseOne L * G := by rw [mul_assoc G, mul_inverseOne hK, mul_one]
  rw [← hmove, ← add_mul]
  exact mul_inverseOne hK

end FormalAlgebra

section Series

/-- The nonnegative vector-series model for heterogeneous formal operators. -/
abbrev OperatorSeries (U V : Type v) [AddCommGroup U] [Module k U]
    [AddCommGroup V] [Module k V] := PowerSeriesModule k (U →ₗ[k] V)

/-- Embed a vector-valued power series into the actual Laurent module. -/
def toLaurent {X : Type v} [AddCommGroup X] [Module k X]
    (x : PowerSeriesModule k X) : LaurentModule k X :=
  HahnModule.of k (HahnSeries.embDomain (Nat.castOrderEmbedding (α := ℤ))
    ((HahnModule.of k).symm x))

@[simp] theorem coeff_toLaurent_nat {X : Type v} [AddCommGroup X] [Module k X]
    (x : PowerSeriesModule k X) (n : ℕ) :
    LaurentModule.coeff (toLaurent x) (n : ℤ) = PowerSeriesModule.coeffV n x := by
  exact HahnSeries.embDomain_coeff

theorem coeff_toLaurent_neg {X : Type v} [AddCommGroup X] [Module k X]
    (x : PowerSeriesModule k X) (d : ℤ) (hd : d < 0) : LaurentModule.coeff (toLaurent x) d = 0 := by
  apply HahnSeries.embDomain_notin_range
  rintro ⟨n, hn⟩
  change (n : ℤ) = d at hn
  omega

theorem toLaurent_boundedBelow {X : Type v} [AddCommGroup X] [Module k X]
    (x : PowerSeriesModule k X) : LaurentModule.BoundedBelow 0 (toLaurent x) :=
  fun d hd => coeff_toLaurent_neg x d hd

@[simp] theorem toLaurent_zero {X : Type v} [AddCommGroup X] [Module k X] :
    toLaurent (0 : PowerSeriesModule k X) = 0 := by
  apply LaurentModule.ext
  intro d
  by_cases hd : 0 ≤ d
  · lift d to ℕ using hd
    simp
  · rw [coeff_toLaurent_neg _ _ (lt_of_not_ge hd), LaurentModule.coeff_zero]

theorem toLaurent_map {X Y : Type v} [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] (f : X →ₗ[k] Y) (x : PowerSeriesModule k X) :
    toLaurent (PowerSeriesModule.map f x) = LaurentModule.map f (toLaurent x) := by
  apply LaurentModule.ext
  intro d
  by_cases hd : 0 ≤ d
  · lift d to ℕ using hd
    simp
  · simp only [coeff_toLaurent_neg _ _ (lt_of_not_ge hd), LaurentModule.coeff_map, map_zero]

theorem toLaurent_injective {X : Type v} [AddCommGroup X] [Module k X] :
    Function.Injective (toLaurent (k := k) (X := X)) := by
  intro x y h
  apply PowerSeriesModule.ext
  intro n
  have hc := congrArg (fun z => LaurentModule.coeff z (n : ℤ)) h
  simpa only [coeff_toLaurent_nat] using hc

theorem toLaurent_single {X : Type v} [AddCommGroup X] [Module k X]
    (n : ℕ) (x : X) :
    toLaurent (PowerSeriesModule.single (k := k) n x) = LaurentModule.single (k := k) (n : ℤ) x := by
  apply LaurentModule.ext
  intro d
  by_cases hd : 0 ≤ d
  · lift d to ℕ using hd
    simp [PowerSeriesModule.coeffV_single]
  · have hne : d ≠ (n : ℤ) := by omega
    simp [coeff_toLaurent_neg _ _ (lt_of_not_ge hd), hne]

private def natPair (ij : ℕ × ℕ) : Fin 2 → ℤ :=
  Fin.cons (ij.1 : ℤ) (fun _ => (ij.2 : ℤ))

private def natPairEmbedding : (ℕ × ℕ) ↪ (Fin 2 → ℤ) where
  toFun := natPair
  inj' a b h := by
    apply Prod.ext
    · have h0 := congrFun h 0
      exact Int.ofNat_inj.mp h0
    · have h1 := congrFun h 1
      exact Int.ofNat_inj.mp h1

/-- Zero extension preserves the actual bilinear convolution, with finite
antidiagonals on the power-series side and the full Laurent convolution on the other. -/
theorem toLaurent_applyBilinear {X Y Z : Type v} [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] [AddCommGroup Z] [Module k Z]
    (f : X →ₗ[k] Y →ₗ[k] Z) (x : PowerSeriesModule k X) (y : PowerSeriesModule k Y) :
    toLaurent (PowerSeriesModule.applyBilinear f x y) =
      LaurentModule.extendBilinear f (toLaurent x) (toLaurent y) := by
  classical
  apply LaurentModule.ext
  intro d
  by_cases hd : 0 ≤ d
  · lift d to ℕ using hd
    rw [coeff_toLaurent_nat, PowerSeriesModule.coeffV_applyBilinear,
      LaurentModule.coeff_extendBilinear]
    let g : (Fin 2 → ℤ) → Z := fun a =>
      if ∑ i, a i = (d : ℤ) then
        f (LaurentModule.coeff (toLaurent x) (a 0))
          (LaurentModule.coeff (toLaurent y) (a 1)) else 0
    have hs : Function.support g ⊆
        ↑((Finset.HasAntidiagonal.antidiagonal d).map natPairEmbedding) := by
      intro a ha
      change g a ≠ 0 at ha
      have heq : ∑ i, a i = (d : ℤ) := by
        by_contra h
        exact ha (if_neg h)
      change (if ∑ i, a i = (d : ℤ) then _ else 0) ≠ 0 at ha
      rw [if_pos heq] at ha
      have h0 : 0 ≤ a 0 := by
        by_contra h
        exact ha (by rw [coeff_toLaurent_neg x _ (lt_of_not_ge h), map_zero,
          LinearMap.zero_apply])
      have h1 : 0 ≤ a 1 := by
        by_contra h
        exact ha (by rw [coeff_toLaurent_neg y _ (lt_of_not_ge h), map_zero])
      have hc0 : ((a 0).toNat : ℤ) = a 0 := Int.toNat_of_nonneg h0
      have hc1 : ((a 1).toNat : ℤ) = a 1 := Int.toNat_of_nonneg h1
      refine Finset.mem_map.mpr ⟨((a 0).toNat, (a 1).toNat), ?_, ?_⟩
      · rw [Finset.HasAntidiagonal.mem_antidiagonal]
        have heq' : a 0 + a 1 = (d : ℤ) := by simpa [Fin.sum_univ_two] using heq
        omega
      · funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hc0
        · have hj : j = 0 := Subsingleton.elim _ _
          subst j
          exact hc1
    change (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal d,
      f (PowerSeriesModule.coeffV ij.1 x) (PowerSeriesModule.coeffV ij.2 y)) = ∑ᶠ a, g a
    rw [finsum_eq_sum_of_support_subset g hs, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro ij hij
    have hsum : (ij.1 : ℤ) + (ij.2 : ℤ) = d := by
      exact_mod_cast (Finset.HasAntidiagonal.mem_antidiagonal.mp hij)
    simp [g, natPairEmbedding, natPair, Fin.sum_univ_two, hsum]
  · have hd' : d < 0 := lt_of_not_ge hd
    rw [coeff_toLaurent_neg _ _ hd']
    exact (LaurentModule.boundedBelow_extendBilinear f (toLaurent x) (toLaurent y)
      (toLaurent_boundedBelow x) (toLaurent_boundedBelow y) d (by simpa using hd')).symm

theorem toLaurent_linearCompose (B : OperatorSeries (k := k) V W)
    (A : OperatorSeries (k := k) U V) :
    toLaurent (PowerSeriesModule.linearCompose B A) =
      LaurentModule.linearCompose (toLaurent B) (toLaurent A) :=
  toLaurent_applyBilinear (LinearMap.llcomp k U V W) B A

theorem series_compose_assoc {X : Type v} [AddCommGroup X] [Module k X]
    (C : OperatorSeries (k := k) W X) (B : OperatorSeries (k := k) V W)
    (A : OperatorSeries (k := k) U V) :
    PowerSeriesModule.linearCompose (PowerSeriesModule.linearCompose C B) A =
      PowerSeriesModule.linearCompose C (PowerSeriesModule.linearCompose B A) := by
  apply toLaurent_injective
  simp only [toLaurent_linearCompose]
  apply LaurentModule.linearApply_injective
  apply LinearMap.ext
  intro x
  simp only [LaurentModule.linearApply_comp]

theorem series_compose_single (B : V →ₗ[k] W) (A : U →ₗ[k] V) :
    PowerSeriesModule.linearCompose (PowerSeriesModule.single 0 B) (PowerSeriesModule.single 0 A) =
      PowerSeriesModule.single 0 (B.comp A) := by
  apply toLaurent_injective
  rw [toLaurent_linearCompose, toLaurent_single, toLaurent_single,
    LaurentModule.linearCompose_single, toLaurent_single]
  rfl

@[simp] theorem coeff0_series_compose (B : OperatorSeries (k := k) V W)
    (A : OperatorSeries (k := k) U V) :
    PowerSeriesModule.coeffV 0 (PowerSeriesModule.linearCompose B A) =
      (PowerSeriesModule.coeffV 0 B).comp (PowerSeriesModule.coeffV 0 A) := by
  simp [PowerSeriesModule.linearCompose, PowerSeriesModule.extendBilinear_apply]
  rfl

/-- The actual Laurent-linear convolution action of a nonnegative formal operator. -/
def act (A : OperatorSeries (k := k) U V) :
    LaurentModule k U →ₗ[LaurentSeries k] LaurentModule k V :=
  LaurentModule.linearApply (toLaurent A)

theorem act_boundedBelow (A : OperatorSeries (k := k) U V) {b : ℤ} {x : LaurentModule k U}
    (hx : LaurentModule.BoundedBelow b x) : LaurentModule.BoundedBelow b (act A x) := by
  simpa only [zero_add, act] using LaurentModule.boundedBelow_linearApply (toLaurent A) x
    (toLaurent_boundedBelow A) hx

theorem act_comp (B : OperatorSeries (k := k) V W) (A : OperatorSeries (k := k) U V) :
    (act B).comp (act A) = act (PowerSeriesModule.linearCompose B A) := by
  apply LinearMap.ext
  intro x
  exact (LaurentModule.linearApply_comp (toLaurent B) (toLaurent A) x).symm.trans
    (congrArg (fun F => LaurentModule.linearApply F x) (toLaurent_linearCompose B A).symm)

/-- View an endomorphism-valued vector series in the usual noncommutative power-series ring. -/
def endSeries (F : OperatorSeries (k := k) V V) : PowerSeries (Module.End k V) :=
  PowerSeries.mk fun n => PowerSeriesModule.coeffV n F

/-- The inverse additive conversion, preserving every coefficient. -/
def ofEndSeries (F : PowerSeries (Module.End k V)) : OperatorSeries (k := k) V V :=
  PowerSeriesModule.mk fun n => PowerSeries.coeff n F

@[simp] theorem coeff_endSeries (F : OperatorSeries (k := k) V V) (n : ℕ) :
    PowerSeries.coeff n (endSeries F) = PowerSeriesModule.coeffV n F := by simp [endSeries]

@[simp] theorem coeff_ofEndSeries (F : PowerSeries (Module.End k V)) (n : ℕ) :
    PowerSeriesModule.coeffV n (ofEndSeries F) = PowerSeries.coeff n F := rfl

@[simp] theorem ofEndSeries_endSeries (F : OperatorSeries (k := k) V V) :
    ofEndSeries (endSeries F) = F := by ext n; simp

@[simp] theorem endSeries_ofEndSeries (F : PowerSeries (Module.End k V)) :
    endSeries (ofEndSeries F) = F := by ext n; simp

@[simp] theorem endSeries_zero : endSeries (0 : OperatorSeries (k := k) V V) = 0 := by
  ext n
  simp

@[simp] theorem endSeries_single (f : Module.End k V) :
    endSeries (PowerSeriesModule.single 0 f) = PowerSeries.C f := by
  ext n
  simp [PowerSeriesModule.coeffV_single, PowerSeries.coeff_C]

@[simp] theorem constantCoeff_endSeries (F : OperatorSeries (k := k) V V) :
    PowerSeries.constantCoeff (endSeries F) = PowerSeriesModule.coeffV 0 F := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_endSeries]

theorem endSeries_compose (G F : OperatorSeries (k := k) V V) :
    endSeries (PowerSeriesModule.linearCompose G F) = endSeries G * endSeries F := by
  ext n
  simp only [coeff_endSeries, PowerSeries.coeff_mul,
    PowerSeriesModule.linearCompose, PowerSeriesModule.extendBilinear_apply,
    PowerSeriesModule.coeffV_applyBilinear]
  rfl

theorem toLaurent_ofEndSeries (F : PowerSeries (Module.End k V)) :
    toLaurent (ofEndSeries F) = HahnModule.of k (HahnSeries.ofPowerSeries ℤ (Module.End k V) F) := by
  have h : (HahnModule.of k).symm (ofEndSeries F) = HahnSeries.toPowerSeries.symm F := by
    ext n
    rfl
  rw [toLaurent, h, HahnSeries.ofPowerSeries_apply]

/-- The actual Laurent action of the noncommutative formal endomorphism ring. -/
def formalActionHom : PowerSeries (Module.End k V) →+*
    Module.End (LaurentSeries k) (LaurentModule k V) :=
  LaurentOperator.actionHom.comp (HahnSeries.ofPowerSeries ℤ (Module.End k V))

theorem formalAction_boundedBelow (F : PowerSeries (Module.End k V))
    {b : ℤ} {x : LaurentModule k V} (hx : LaurentModule.BoundedBelow b x) :
    LaurentModule.BoundedBelow b (formalActionHom F x) := by
  have hF : ∀ d < 0, (HahnSeries.ofPowerSeries ℤ (Module.End k V) F).coeff d = 0 := by
    intro d hd
    have h := coeff_toLaurent_neg (ofEndSeries F) d hd
    rw [toLaurent_ofEndSeries] at h
    exact h
  change LaurentModule.BoundedBelow b
    (LaurentOperator.act (HahnSeries.ofPowerSeries ℤ (Module.End k V) F) x)
  simpa only [zero_add] using LaurentOperator.boundedBelow_act _ x hF hx

/-- The two middle endomorphism series `AS` and `TB`. -/
def firstPart (A : OperatorSeries (k := k) U V) (S : V →ₗ[k] U) :
    PowerSeries (Module.End k V) :=
  endSeries (PowerSeriesModule.linearCompose A (PowerSeriesModule.single 0 S))

def secondPart (B : OperatorSeries (k := k) V W) (T : W →ₗ[k] V) :
    PowerSeries (Module.End k V) :=
  endSeries (PowerSeriesModule.linearCompose (PowerSeriesModule.single 0 T) B)

theorem secondPart_mul_firstPart (A : OperatorSeries (k := k) U V)
    (B : OperatorSeries (k := k) V W) (S : V →ₗ[k] U) (T : W →ₗ[k] V)
    (hBA : PowerSeriesModule.linearCompose B A = 0) :
    secondPart B T * firstPart A S = 0 := by
  rw [secondPart, firstPart, ← endSeries_compose, series_compose_assoc,
    ← series_compose_assoc B A, hBA]
  simp

theorem constant_projection_secondPart (B : OperatorSeries (k := k) V W) :
    PowerSeries.C ((rightSplitting (PowerSeriesModule.coeffV 0 B)).comp
      (PowerSeriesModule.coeffV 0 B)) *
        secondPart B (rightSplitting (PowerSeriesModule.coeffV 0 B)) =
      secondPart B (rightSplitting (PowerSeriesModule.coeffV 0 B)) := by
  let T := rightSplitting (PowerSeriesModule.coeffV 0 B)
  have hT : (T.comp (PowerSeriesModule.coeffV 0 B)).comp T = T := by
    ext w
    exact rightSplitting_inner (PowerSeriesModule.coeffV 0 B) w
  change PowerSeries.C (T.comp (PowerSeriesModule.coeffV 0 B)) * secondPart B T = secondPart B T
  rw [secondPart, ← endSeries_single, ← endSeries_compose, ← series_compose_assoc,
    series_compose_single, hT]

/-- Formal middle exactness has an actual two-inverse operator witness. -/
theorem formal_middle_identity (A : OperatorSeries (k := k) U V)
    (B : OperatorSeries (k := k) V W)
    (hBA : PowerSeriesModule.linearCompose B A = 0)
    (h0 : LinearMap.range (PowerSeriesModule.coeffV 0 A) =
      LinearMap.ker (PowerSeriesModule.coeffV 0 B)) :
    let S := leftSplitting (PowerSeriesModule.coeffV 0 A) (PowerSeriesModule.coeffV 0 B)
    let T := rightSplitting (PowerSeriesModule.coeffV 0 B)
    let F := firstPart A S
    let G := secondPart B T
    let P := PowerSeries.C (T.comp (PowerSeriesModule.coeffV 0 B))
    F * inverseOne (F + G) + inverseOne (1 - P + G) * G = 1 := by
  dsimp only
  apply two_inverse_identity
  · exact secondPart_mul_firstPart A B _ _ hBA
  · exact constant_projection_secondPart B
  · rw [map_add]
    simp only [firstPart, secondPart, constantCoeff_endSeries, coeff0_series_compose,
      PowerSeriesModule.coeffV_single, ite_true]
    exact middle_splitting (PowerSeriesModule.coeffV 0 A) (PowerSeriesModule.coeffV 0 B) h0
  · simp [secondPart, PowerSeriesModule.coeffV_single]

/-- The explicit lifting operator. Its values are actual Laurent series, with
no finite-dimensionality condition on any of the coefficient spaces. -/
def lift (A : OperatorSeries (k := k) U V) (B : OperatorSeries (k := k) V W) :
    LaurentModule k V →ₗ[LaurentSeries k] LaurentModule k U :=
  let S := leftSplitting (PowerSeriesModule.coeffV 0 A) (PowerSeriesModule.coeffV 0 B)
  let T := rightSplitting (PowerSeriesModule.coeffV 0 B)
  (LaurentModule.map S).comp (formalActionHom (inverseOne (firstPart A S + secondPart B T)))

theorem lift_boundedBelow (A : OperatorSeries (k := k) U V) (B : OperatorSeries (k := k) V W)
    {b : ℤ} {z : LaurentModule k V} (hz : LaurentModule.BoundedBelow b z) :
    LaurentModule.BoundedBelow b (lift A B z) :=
  LaurentModule.boundedBelow_map _ (formalAction_boundedBelow _ hz)

theorem act_single (f : U →ₗ[k] V) :
    act (PowerSeriesModule.single 0 f) = LaurentModule.map f := by
  rw [act, toLaurent_single]
  exact LaurentModule.linearApply_single_zero f

theorem act_ofEndSeries (F : PowerSeries (Module.End k V)) :
    act (ofEndSeries F) = formalActionHom F := by
  rw [act, toLaurent_ofEndSeries, LaurentModule.linearApply_eq_actionHom]
  rfl

theorem formalAction_endSeries (F : OperatorSeries (k := k) V V) :
    formalActionHom (endSeries F) = act F := by
  rw [← act_ofEndSeries, ofEndSeries_endSeries]

theorem formalAction_firstPart (A : OperatorSeries (k := k) U V) (S : V →ₗ[k] U) :
    formalActionHom (firstPart A S) = (act A).comp (LaurentModule.map S) := by
  rw [firstPart, formalAction_endSeries, ← act_comp, act_single]

theorem formalAction_secondPart (B : OperatorSeries (k := k) V W) (T : W →ₗ[k] V) :
    formalActionHom (secondPart B T) = (LaurentModule.map T).comp (act B) := by
  rw [secondPart, formalAction_endSeries, ← act_comp, act_single]

/-- Every actual Laurent cycle has the explicit Laurent preimage constructed above. -/
theorem lift_spec (A : OperatorSeries (k := k) U V) (B : OperatorSeries (k := k) V W)
    (hBA : PowerSeriesModule.linearCompose B A = 0)
    (h0 : LinearMap.range (PowerSeriesModule.coeffV 0 A) =
      LinearMap.ker (PowerSeriesModule.coeffV 0 B))
    (z : LaurentModule k V) (hz : act B z = 0) : act A (lift A B z) = z := by
  let S := leftSplitting (PowerSeriesModule.coeffV 0 A) (PowerSeriesModule.coeffV 0 B)
  let T := rightSplitting (PowerSeriesModule.coeffV 0 B)
  let J := inverseOne (firstPart A S + secondPart B T)
  let Q := inverseOne (1 - PowerSeries.C (T.comp (PowerSeriesModule.coeffV 0 B)) + secondPart B T)
  have hid : formalActionHom (firstPart A S) * formalActionHom J +
      formalActionHom Q * formalActionHom (secondPart B T) = 1 := by
    have h := congrArg (formalActionHom (k := k) (V := V)) (formal_middle_identity A B hBA h0)
    simpa only [map_add, map_mul, map_one] using h
  have h := LinearMap.congr_fun hid z
  rw [formalAction_firstPart, formalAction_secondPart] at h
  change act A (LaurentModule.map S (formalActionHom J z)) +
    formalActionHom Q (LaurentModule.map T (act B z)) = z at h
  rw [hz, map_zero, map_zero, add_zero] at h
  exact h

/-- Middle exactness persists under positive formal perturbation on actual Laurent modules. -/
theorem laurent_middle_exact (A : OperatorSeries (k := k) U V) (B : OperatorSeries (k := k) V W)
    (hBA : PowerSeriesModule.linearCompose B A = 0)
    (h0 : LinearMap.range (PowerSeriesModule.coeffV 0 A) =
      LinearMap.ker (PowerSeriesModule.coeffV 0 B)) :
    LinearMap.range (act A) = LinearMap.ker (act B) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    have hc : (act B).comp (act A) = 0 := by
      rw [act_comp, hBA]
      simp [act]
    exact LinearMap.congr_fun hc x
  · intro z hz
    exact ⟨lift A B z, lift_spec A B hBA h0 z hz⟩

theorem exists_preimage (A : OperatorSeries (k := k) U V) (B : OperatorSeries (k := k) V W)
    (hBA : PowerSeriesModule.linearCompose B A = 0)
    (h0 : LinearMap.range (PowerSeriesModule.coeffV 0 A) =
      LinearMap.ker (PowerSeriesModule.coeffV 0 B))
    (z : LaurentModule k V) (hz : act B z = 0) :
    ∃ w : LaurentModule k U, act A w = z :=
  ⟨lift A B z, lift_spec A B hBA h0 z hz⟩

/-- The middle-exactness witness retains any lower bound of the individual input.
No global bound for all Laurent vectors or finite-dimensionality is needed. -/
theorem exists_preimage_bounded (A : OperatorSeries (k := k) U V)
    (B : OperatorSeries (k := k) V W)
    (hBA : PowerSeriesModule.linearCompose B A = 0)
    (h0 : LinearMap.range (PowerSeriesModule.coeffV 0 A) =
      LinearMap.ker (PowerSeriesModule.coeffV 0 B))
    (z : LaurentModule k V) (hz : act B z = 0) (b : ℤ) (hb : LaurentModule.BoundedBelow b z) :
    ∃ w : LaurentModule k U, LaurentModule.BoundedBelow b w ∧ act A w = z :=
  ⟨lift A B z, lift_boundedBelow A B hb, lift_spec A B hBA h0 z hz⟩

end Series

end

end EnvelopingIsomorphism.Deformation.MiddleExactPerturbation
