import EnvelopingIsomorphism.Deformation.Gauge.LaurentSchoutenEmbedding

/-! Actual elementary MC equivalences for the Laurent-completed polynomial Schouten source. -/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries

theorem map_exp {R S : Type*} [Ring R] [Algebra ℚ R] [Ring S] [Algebra ℚ S]
    (ρ : R →+* S) (F : PowerSeries R) :
    PowerSeries.map ρ (exp F) = exp (PowerSeries.map ρ F) := by
  apply PowerSeries.ext
  intro n
  simp only [exp, PowerSeries.coeff_map, coeff_sumPowers, map_sum, map_rat_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← map_pow, PowerSeries.coeff_map]

end EnvelopingIsomorphism.FormalSeries

namespace EnvelopingIsomorphism.Deformation.Gauge.LaurentSchouten

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule PowerSeries

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

local instance : CharZero (Scalars K) := scalarCharZero

local instance bivectorRationalModule : Module ℚ (Bivector K d) :=
  Module.compHom (Bivector K d) (algebraMap ℚ (Scalars K))

local instance bivectorRationalTower : IsScalarTower ℚ (Scalars K) (Bivector K d) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

local instance bivectorRationalComm : SMulCommClass (Scalars K) ℚ (Bivector K d) where
  smul_comm s r F := smul_comm s (algebraMap ℚ (Scalars K) r) F

local instance functionRationalModule : Module ℚ (Functions K d) :=
  Module.compHom (Functions K d) (algebraMap ℚ (Scalars K))

local instance functionRationalTower : IsScalarTower ℚ (Scalars K) (Functions K d) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

local instance functionRationalComm : SMulCommClass (Scalars K) ℚ (Functions K d) where
  smul_comm s r F := smul_comm s (algebraMap ℚ (Scalars K) r) F

local instance sourceEndRing : Ring (Module.End (Scalars K) (Bivector K d)) :=
  @Module.End.instRing (Scalars K) (Bivector K d) inferInstance inferInstance inferInstance

local instance ambientEndRing : Ring (Module.End (Scalars K) (Binary (Scalars K) (Functions K d))) :=
  @Module.End.instRing (Scalars K) (Binary (Scalars K) (Functions K d)) inferInstance inferInstance inferInstance

local instance functionEndRing : Ring (Module.End (Scalars K) (Functions K d)) :=
  @Module.End.instRing (Scalars K) (Functions K d) inferInstance inferInstance inferInstance

local instance sourceSeriesAddGroup : AddCommGroup (PowerSeriesModule (Scalars K) (Bivector K d)) :=
  @HahnModule.instAddCommGroup ℕ (Scalars K) (Bivector K d) inferInstance inferInstance inferInstance

abbrev Families (K : Type*) [Field K] (d : ℕ) := PowerSeriesModule (Scalars K) (Bivector K d)

def sourceGauge (N : ℕ) (hN : 0 < N) (X : Vector K d) :
    GaugeUnit (Module.End (Scalars K) (Bivector K d)) := elementaryGauge N hN (action X)

def sourceEquiv (N : ℕ) (hN : 0 < N) (X : Vector K d) :
    Families K d ≃ₗ[PowerSeries (Scalars K)] Families K d :=
  operatorUnitEquiv (k := Scalars K) (V := Bivector K d) (sourceGauge N hN X).val

theorem sourceEquiv_apply (N : ℕ) (hN : 0 < N) (X : Vector K d) (B : Families K d) :
    sourceEquiv N hN X B = actV (k := Scalars K) (V := Bivector K d)
      (exp (monomial N (action X))) B := operator_apply _ _

def ambientCoordinateGauge (N : ℕ) (hN : 0 < N) (X : Vector K d) :
    GaugeUnit (Module.End (Scalars K) (Functions K d)) := elementaryGauge N hN (coordinateEnd X)

/-- The coordinate unit belongs to the original Laurent operator ring. -/
def coordinateGauge (N : ℕ) (hN : 0 < N) (X : Vector K d) :
    GaugeUnit (LaurentSeries (Module.End K (PolynomialFunctions K d))) :=
  elementaryGauge N hN (vectorOperator X)

def rawSeries : Families K d →ₗ[PowerSeries (Scalars K)]
    PowerSeriesModule (Scalars K) (Binary (Scalars K) (Functions K d)) :=
  PowerSeriesModule.map evaluateBivector

theorem sourceEquiv_raw (N : ℕ) (hN : 0 < N) (X : Vector K d) (B : Families K d) :
    rawSeries (sourceEquiv N hN X B) =
      actV (k := Scalars K) (V := Binary (Scalars K) (Functions K d))
        (exp (monomial N (NilpotentConjugation.unaryActionEnd (coordinateEnd X)))) (rawSeries B) := by
  rw [sourceEquiv_apply]
  exact map_actV_exp_monomial evaluateBivector (action X)
    (NilpotentConjugation.unaryActionEnd (coordinateEnd X)) (evaluate_action X) N B

theorem sourceEquiv_raw_conjugate (N : ℕ) (hN : 0 < N) (X : Vector K d) (B : Families K d) :
    rawSeries (sourceEquiv N hN X B) =
      conjugateBinarySeries (ambientCoordinateGauge N hN X).val (rawSeries B) := by
  rw [sourceEquiv_raw]
  exact AdjointMonomialExp.adjoint_monomial_exp_eq_conjugate (coordinateEnd X) N hN (rawSeries B)

theorem ambient_coordinateGauge (N : ℕ) (hN : 0 < N) (X : Vector K d) :
    LaurentConjugation.ambientGauge (coordinateGauge N hN X) = ambientCoordinateGauge N hN X := by
  apply Subtype.ext
  apply Units.ext
  change PowerSeries.map LaurentOperator.actionHom (exp (monomial N (vectorOperator X))) =
    exp (monomial N (coordinateEnd X))
  rw [FormalSeries.map_exp]
  apply congrArg (FormalSeries.exp (R := Module.End (Scalars K) (Functions K d)))
  apply PowerSeries.ext
  intro j
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_monomial, coordinateEnd_eq_actionHom]
  split_ifs <;> simp

theorem sourceEquiv_neg (N : ℕ) (hN : 0 < N) (X : Vector K d) :
    sourceEquiv N hN (-X) = (sourceEquiv N hN X).symm := by
  apply LinearEquiv.ext
  intro B
  rw [sourceEquiv_apply]
  change actV (exp (monomial N (action (-X)))) B =
    operator (exp (-monomial N (action X))) B
  rw [map_neg, map_neg, operator_apply]

/-- Affine source motion relative to the fixed Laurent Poisson base. -/
def motion (π : Bivector K d) (N : ℕ) (hN : 0 < N) (X : Vector K d) (b : Families K d) : Families K d :=
  sourceEquiv N hN X (single 0 π + b) - single 0 π

theorem motion_full (π : Bivector K d) (N : ℕ) (hN : 0 < N) (X : Vector K d) (b : Families K d) :
    single 0 π + motion π N hN X b = sourceEquiv N hN X (single 0 π + b) := by
  unfold motion
  abel

theorem motion_agree (π : Bivector K d) (N : ℕ) (hN : 0 < N) (X : Vector K d) (b : Families K d) :
    AgreeBelow N (motion π N hN X b) b := by
  intro j hj
  have hG : toJet N (sourceGauge N hN X).series =
      toJet N (1 : PowerSeries (Module.End (Scalars K) (Bivector K d))) :=
    (elementaryGauge_near N hN (action X)).trans (map_one (toJet N)).symm
  have h := operator_congr (k := Scalars K) (V := Bivector K d) hG (single 0 π + b) j hj
  change coeffV j (sourceEquiv N hN X (single 0 π + b)) =
    coeffV j (operator (1 : PowerSeries (Module.End (Scalars K) (Bivector K d))) (single 0 π + b)) at h
  rw [operator_one, LinearMap.id_apply] at h
  change coeffV j (sourceEquiv N hN X (single 0 π + b) - single 0 π) = _
  rw [coeffV_sub, h, coeffV_add]
  abel

theorem motion_leading (π : Bivector K d) (N : ℕ) (hN : 0 < N) (X : Vector K d)
    (b : Families K d) (hb : coeffV 0 b = 0) :
    coeffV N (motion π N hN X b) - coeffV N b = action X π := by
  have h := coeffV_applyBilinear_left_constant
    (LinearMap.id : Module.End (Scalars K) (Bivector K d) →ₗ[Scalars K] Bivector K d →ₗ[Scalars K] Bivector K d)
    (operatorSeries (sourceGauge N hN X).series) (single 0 π + b) 1 hN
    (operatorSeries_near (elementaryGauge_near N hN (action X)))
  change coeffV N (sourceEquiv N hN X (single 0 π + b)) =
    coeffV N (single 0 π + b) + (coeff N (sourceGauge N hN X).series) (coeffV 0 (single 0 π + b)) at h
  change coeffV N (sourceEquiv N hN X (single 0 π + b) - single 0 π) - coeffV N b = _
  rw [coeffV_sub, h, show coeff N (sourceGauge N hN X).series = action X from elementaryGauge_leading N hN _]
  simp only [coeffV_add, coeffV_single, hb, add_zero]
  abel

theorem twisted_d_one (π : Bivector K d)
    (hπ : (polynomialSchoutenDGLA K d).laurent.IsMaurerCartan π) :
    ((polynomialSchoutenDGLA K d).laurent.twist π hπ).d 1 = bivectorBracket π := by
  rw [SignedDGLA.twist_d, SignedDGLA.twistedD, laurent_d_zero, zero_add]
  rfl

theorem motion_leading_twist (π : Bivector K d)
    (hπ : (polynomialSchoutenDGLA K d).laurent.IsMaurerCartan π)
    (N : ℕ) (hN : 0 < N) (X : Vector K d) (b : Families K d) (hb : coeffV 0 b = 0) :
    coeffV N (motion π N hN X b) - coeffV N b =
      -((polynomialSchoutenDGLA K d).laurent.twist π hπ).d 0 X := by
  rw [motion_leading π N hN X b hb, SignedDGLA.twist_d]
  simp only [SignedDGLA.twistedD, laurent_d_zero, zero_add]
  change (polynomialSchoutenDGLA K d).laurent.bracket 0 1 X π =
    -(polynomialSchoutenDGLA K d).laurent.bracket 1 0 π X
  have h := eq_of_heq ((polynomialSchoutenDGLA K d).laurent.skew 0 1 X π)
  simpa only [Int.zero_mul, Int.negOnePow_zero, Units.val_one, Int.cast_one, neg_one_smul] using h

omit [CharZero K] in
theorem rawSeries_full (π : Bivector K d) (b : Families K d) :
    rawSeries (single 0 π + b) = single 0 (evaluateBivector π) + rawSeries b := by
  simp only [rawSeries, map_add, map_single]

theorem motion_preserves_MC (π : Bivector K d)
    (hπ : (polynomialSchoutenDGLA K d).laurent.IsMaurerCartan π)
    (N : ℕ) (hN : 0 < N) (X : Vector K d) (b : Families K d)
    (hb : quadraticCurvature (bivectorBracket π) ((2 : Scalars K)⁻¹ • bivectorBracket) b = 0) :
    quadraticCurvature (bivectorBracket π) ((2 : Scalars K)⁻¹ • bivectorBracket) (motion π N hN X b) = 0 := by
  apply (curvature_iff_Jacobi π hπ _).mpr
  have hJ := (curvature_iff_Jacobi π hπ b).mp hb
  have hfull : single (k := Scalars K) 0 (evaluateBivector π) +
      PowerSeriesModule.map evaluateBivector (motion π N hN X b) =
      conjugateBinarySeries (ambientCoordinateGauge N hN X).val
        (single 0 (evaluateBivector π) + PowerSeriesModule.map evaluateBivector b) := by
    change single 0 (evaluateBivector π) + rawSeries (motion π N hN X b) =
      conjugateBinarySeries (ambientCoordinateGauge N hN X).val
        (single 0 (evaluateBivector π) + rawSeries b)
    rw [← rawSeries_full, motion_full, sourceEquiv_raw_conjugate, rawSeries_full]
  rw [hfull, extendBinary_conjugateBinarySeries_eq]
  apply conjugate_jacobi
  exact hJ

theorem motion_inverse (π : Bivector K d) (N : ℕ) (hN : 0 < N) (X : Vector K d) (b : Families K d) :
    motion π N hN (-X) (motion π N hN X b) = b := by
  unfold motion
  rw [sourceEquiv_neg]
  have h : single 0 π + (sourceEquiv N hN X (single 0 π + b) - single 0 π) =
      sourceEquiv N hN X (single 0 π + b) := by abel
  rw [h, LinearEquiv.symm_apply_apply]
  abel

theorem motion_inverse_right (π : Bivector K d) (N : ℕ) (hN : 0 < N) (X : Vector K d) (b : Families K d) :
    motion π N hN X (motion π N hN (-X) b) = b := by
  simpa only [neg_neg] using motion_inverse π N hN (-X) b

/-- Every actual Laurent vector direction induces a genuine elementary equivalence of MC solutions. -/
def mcElementary (π : Bivector K d)
    (hπ : (polynomialSchoutenDGLA K d).laurent.IsMaurerCartan π)
    (N : ℕ) (hN : 0 < N) (X : Vector K d) : Equiv.Perm (MC π) where
  toFun b := ⟨motion π N hN X b.val,
    (motion_agree π N hN X b.val 0 hN).trans b.property.1,
    motion_preserves_MC π hπ N hN X b.val b.property.2⟩
  invFun b := ⟨motion π N hN (-X) b.val,
    (motion_agree π N hN (-X) b.val 0 hN).trans b.property.1,
    motion_preserves_MC π hπ N hN (-X) b.val b.property.2⟩
  left_inv b := Subtype.ext (motion_inverse π N hN X b.val)
  right_inv b := Subtype.ext (motion_inverse_right π N hN X b.val)

@[simp] theorem mcElementary_val (π : Bivector K d)
    (hπ : (polynomialSchoutenDGLA K d).laurent.IsMaurerCartan π)
    (N : ℕ) (hN : 0 < N) (X : Vector K d) (b : MC π) :
    (mcElementary π hπ N hN X b).val = motion π N hN X b.val := rfl

theorem mcElementary_agree (π : Bivector K d)
    (hπ : (polynomialSchoutenDGLA K d).laurent.IsMaurerCartan π)
    (N : ℕ) (hN : 0 < N) (X : Vector K d) (b : MC π) :
    AgreeBelow N (mcElementary π hπ N hN X b).val b.val := motion_agree π N hN X b.val

theorem mcElementary_leading (π : Bivector K d)
    (hπ : (polynomialSchoutenDGLA K d).laurent.IsMaurerCartan π)
    (N : ℕ) (hN : 0 < N) (X : Vector K d) (b : MC π) :
    coeffV N (mcElementary π hπ N hN X b).val - coeffV N b.val =
      -((polynomialSchoutenDGLA K d).laurent.twist π hπ).d 0 X :=
  motion_leading_twist π hπ N hN X b.val b.property.1

/-- Compatibility with the differential of the actual twisted complex. -/
def twistedMCEquiv (π : Bivector K d)
    (hπ : (polynomialSchoutenDGLA K d).laurent.IsMaurerCartan π) :
    MC π ≃ MCSeries (((polynomialSchoutenDGLA K d).laurent.twist π hπ).d 1)
      ((2 : Scalars K)⁻¹ • bivectorBracket) :=
  Equiv.cast (by rw [twisted_d_one])

def mcMove (π : Bivector K d)
    (hπ : (polynomialSchoutenDGLA K d).laurent.IsMaurerCartan π)
    (γ : ElementaryLabel (Vector K d)) : Equiv.Perm (MC π) :=
  mcElementary π hπ γ.order γ.positive γ.direction

def mcCoordinateUnit (γ : ElementaryLabel (Vector K d)) :
    GaugeUnit (LaurentSeries (Module.End K (PolynomialFunctions K d))) :=
  coordinateGauge γ.order γ.positive γ.direction

def mcBinary (π : Bivector K d) (b : MC π) :
    Binary (PowerSeries (Scalars K)) (PowerSeriesModule (Scalars K) (Functions K d)) :=
  extendBinary (rawSeries (single 0 π + b.val))

/-- The original Laurent operator ring intertwines every genuine elementary MC move. -/
theorem mcMove_intertwines (π : Bivector K d)
    (hπ : (polynomialSchoutenDGLA K d).laurent.IsMaurerCartan π)
    (γ : ElementaryLabel (Vector K d)) (b : MC π)
    (p q : PowerSeriesModule (Scalars K) (Functions K d)) :
    operator (PowerSeries.map LaurentOperator.actionHom (mcCoordinateUnit γ).series) (mcBinary π b p q) =
      mcBinary π (mcMove π hπ γ b)
        (operator (PowerSeries.map LaurentOperator.actionHom (mcCoordinateUnit γ).series) p)
        (operator (PowerSeries.map LaurentOperator.actionHom (mcCoordinateUnit γ).series) q) := by
  have hu : PowerSeries.map LaurentOperator.actionHom (mcCoordinateUnit γ).series =
      (ambientCoordinateGauge γ.order γ.positive γ.direction).series :=
    congrArg GaugeUnit.series (ambient_coordinateGauge γ.order γ.positive γ.direction)
  rw [hu]
  let G := operatorUnitEquiv (k := Scalars K) (V := Functions K d)
    (ambientCoordinateGauge γ.order γ.positive γ.direction).val
  have hf : single (k := Scalars K) 0 π + (mcMove π hπ γ b).val =
      sourceEquiv γ.order γ.positive γ.direction (single 0 π + b.val) :=
    motion_full π γ.order γ.positive γ.direction b.val
  change G (extendBinary (rawSeries (single 0 π + b.val)) p q) =
    extendBinary (rawSeries (single 0 π + (mcMove π hπ γ b).val)) (G p) (G q)
  rw [hf, sourceEquiv_raw_conjugate, extendBinary_conjugateBinarySeries, conjugate_apply]
  change G (extendBinary (rawSeries (single 0 π + b.val)) p q) =
    G (extendBinary (rawSeries (single 0 π + b.val)) (G.symm (G p)) (G.symm (G q)))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

@[reducible] def mcGeneratedAction (π : Bivector K d)
    (hπ : (polynomialSchoutenDGLA K d).laurent.IsMaurerCartan π) :
    MulAction (FreeGroup (ElementaryLabel (Vector K d))) (MC π) := generatedMulAction (mcMove π hπ)

/-- All finite generated source motions retain the actual Laurent-ring intertwiner. -/
theorem mcGenerated_intertwines (π : Bivector K d)
    (hπ : (polynomialSchoutenDGLA K d).laurent.IsMaurerCartan π)
    (s : FreeGroup (ElementaryLabel (Vector K d))) (b : MC π)
    (p q : PowerSeriesModule (Scalars K) (Functions K d)) :
    operator (k := Scalars K) (V := Functions K d) (PowerSeries.map (LaurentOperator.actionHom (k := K) (X := PolynomialFunctions K d))
      (FreeGroup.lift (mcCoordinateUnit (K := K) (d := d)) s).series)
      (mcBinary π b p q) =
      mcBinary π (FreeGroup.lift (mcMove π hπ) s b)
        (operator (k := Scalars K) (V := Functions K d) (PowerSeries.map (LaurentOperator.actionHom (k := K) (X := PolynomialFunctions K d))
      (FreeGroup.lift (mcCoordinateUnit (K := K) (d := d)) s).series) p)
        (operator (k := Scalars K) (V := Functions K d) (PowerSeries.map (LaurentOperator.actionHom (k := K) (X := PolynomialFunctions K d))
      (FreeGroup.lift (mcCoordinateUnit (K := K) (d := d)) s).series) q) :=
  generatedGauge_intertwines (k := Scalars K) (V := Functions K d)
    (R := LaurentSeries (Module.End K (PolynomialFunctions K d)))
    (LaurentOperator.actionHom (k := K) (X := PolynomialFunctions K d)) (mcCoordinateUnit (K := K) (d := d)) (mcMove π hπ)
    (mcBinary π) (mcMove_intertwines π hπ) s b p q

end EnvelopingIsomorphism.Deformation.Gauge.LaurentSchouten
