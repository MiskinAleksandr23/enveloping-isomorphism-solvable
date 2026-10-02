import EnvelopingIsomorphism.Deformation.Gauge.JacobiEmbedding
import EnvelopingIsomorphism.Deformation.Gauge.SchoutenElementary
import EnvelopingIsomorphism.Deformation.Gauge.GeneratedAction

/-!
# Genuine complete Schouten MC families and elementary equivalences

The coefficient MC equation is detected by the actual full-series Jacobi
identity. The elementary exponential is restricted to its MC solution set
using the proved raw conjugation formula and actual preservation of Jacobi.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule

set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

abbrev SchoutenTrivector (K : Type*) [Field K] (d : ℕ) :=
  Multiderivation K (PolynomialFunctions K d) 3

local instance bivectorSeriesAddGroup : AddCommGroup (PowerSeriesModule K (SchoutenBivector K d)) :=
  @HahnModule.instAddCommGroup ℕ K (SchoutenBivector K d) inferInstance inferInstance inferInstance

local instance trivectorSeriesAddGroup : AddCommGroup (PowerSeriesModule K (SchoutenTrivector K d)) :=
  @HahnModule.instAddCommGroup ℕ K (SchoutenTrivector K d) inferInstance inferInstance inferInstance

/-- The actual degree-(1,1) Schouten bracket on coefficient bivectors. -/
def schoutenBivectorBracket : SchoutenBivector K d →ₗ[K] SchoutenBivector K d →ₗ[K] SchoutenTrivector K d :=
  schoutenBracket K d 1 1

/-- The ordinary MC coefficient space relative to a fixed bivector. -/
abbrev SchoutenMCSeries (π : SchoutenBivector K d) : Type _ :=
  MCSeries (k := K) (V := SchoutenBivector K d) (W := SchoutenTrivector K d)
    (schoutenBivectorBracket π) ((2 : K)⁻¹ • schoutenBivectorBracket)

omit [CharZero K] in
theorem rawBivectorSeries_full (π : SchoutenBivector K d)
    (b : PowerSeriesModule K (SchoutenBivector K d)) :
    rawBivectorSeries (single (k := K) 0 π + b) =
      single (k := K) 0 (rawBivector π) +
        map (k := K) (V := SchoutenBivector K d) (W := Binary K (PolynomialFunctions K d)) rawBivectorLinearMap b := by
  change map (k := K) rawBivectorLinearMap (single (k := K) 0 π + b) = _
  rw [map_add, map_single]
  rfl

/-- The genuine complete Schouten MC equation is exactly Jacobi on all formal polynomial inputs. -/
theorem schoutenMCSeries_curvature_iff_Jacobi (π : SchoutenBivector K d)
    (hπ : (polynomialSchoutenDGLA K d).IsMaurerCartan π)
    (b : PowerSeriesModule K (SchoutenBivector K d)) :
    quadraticCurvature (k := K) (V := SchoutenBivector K d) (W := SchoutenTrivector K d)
      (schoutenBivectorBracket π) ((2 : K)⁻¹ • schoutenBivectorBracket) b = 0 ↔
      ∀ p q r : PowerSeriesModule K (PolynomialFunctions K d),
        jacobiInsert (extendBinary (rawBivectorSeries (single (k := K) 0 π + b)))
          (extendBinary (rawBivectorSeries (single (k := K) 0 π + b))) p q r = 0 := by
  rw [rawBivectorSeries_full]
  apply quadratic_MC_iff_Jacobi_of_embedding
    (k := K) (C := SchoutenBivector K d) (T := SchoutenTrivector K d) (A := PolynomialFunctions K d)
    (schoutenBivectorBracket π) ((2 : K)⁻¹ • schoutenBivectorBracket)
    rawBivectorLinearMap rawTrivectorLinearMap rawTrivector_injective (rawBivector π)
    ((polynomialSchouten_MC_iff_Jacobi π).mp hπ)
  · intro F
    exact rawTrivector_schoutenBracket π F
  · intro F G
    change rawTrivectorLinearMap ((2 : K)⁻¹ •
      (show SchoutenTrivector K d from schoutenBracket K d 1 1 F G)) = _
    rw [map_smul]
    exact congrArg (fun T : Ternary K (PolynomialFunctions K d) => (2 : K)⁻¹ • T)
      (rawTrivector_schoutenBracket F G)

/-- Actual elementary conjugation preserves the complete Schouten curvature equation. -/
theorem schoutenElementaryMotion_preserves_MC (π : SchoutenBivector K d)
    (hπ : (polynomialSchoutenDGLA K d).IsMaurerCartan π)
    (N : ℕ) (hN : 0 < N) (X : SchoutenVector K d)
    (b : PowerSeriesModule K (SchoutenBivector K d))
    (hb : quadraticCurvature (k := K) (V := SchoutenBivector K d) (W := SchoutenTrivector K d)
      (schoutenBivectorBracket π) ((2 : K)⁻¹ • schoutenBivectorBracket) b = 0) :
    quadraticCurvature (k := K) (V := SchoutenBivector K d) (W := SchoutenTrivector K d)
      (schoutenBivectorBracket π) ((2 : K)⁻¹ • schoutenBivectorBracket)
        (schoutenElementaryMotion π N hN X b) = 0 := by
  apply (schoutenMCSeries_curvature_iff_Jacobi π hπ _).mpr
  have hJ := (schoutenMCSeries_curvature_iff_Jacobi π hπ b).mp hb
  have hfull : single (k := K) 0 π + schoutenElementaryMotion π N hN X b =
      schoutenElementaryEquiv N hN X (single (k := K) 0 π + b) := by
    unfold schoutenElementaryMotion
    abel
  rw [hfull, schoutenElementaryEquiv_raw_conjugate, extendBinary_conjugateBinarySeries_eq]
  exact conjugate_jacobi
    (operatorUnitEquiv (k := K) (V := PolynomialFunctions K d) (schoutenCoordinateGauge N hN X).val)
    (extendBinary (rawBivectorSeries (single (k := K) 0 π + b))) hJ

/-- The elementary exponential is an actual equivalence of MC solutions, with inverse direction `-X`. -/
def schoutenMCElementary (π : SchoutenBivector K d)
    (hπ : (polynomialSchoutenDGLA K d).IsMaurerCartan π)
    (N : ℕ) (hN : 0 < N) (X : SchoutenVector K d) : Equiv.Perm (SchoutenMCSeries π) where
  toFun b := ⟨schoutenElementaryMotion π N hN X b.val,
    schoutenElementaryMotion_positive π N hN X b.val b.property.1,
    schoutenElementaryMotion_preserves_MC π hπ N hN X b.val b.property.2⟩
  invFun b := ⟨schoutenElementaryMotion π N hN (-X) b.val,
    schoutenElementaryMotion_positive π N hN (-X) b.val b.property.1,
    schoutenElementaryMotion_preserves_MC π hπ N hN (-X) b.val b.property.2⟩
  left_inv b := Subtype.ext (schoutenElementaryMotion_inverse π N hN X b.val)
  right_inv b := Subtype.ext (schoutenElementaryMotion_inverse_right π N hN X b.val)

@[simp] theorem schoutenMCElementary_val (π : SchoutenBivector K d)
    (hπ : (polynomialSchoutenDGLA K d).IsMaurerCartan π)
    (N : ℕ) (hN : 0 < N) (X : SchoutenVector K d) (b : SchoutenMCSeries π) :
    (schoutenMCElementary π hπ N hN X b).val = schoutenElementaryMotion π N hN X b.val := rfl

theorem schoutenMCElementary_agree (π : SchoutenBivector K d)
    (hπ : (polynomialSchoutenDGLA K d).IsMaurerCartan π)
    (N : ℕ) (hN : 0 < N) (X : SchoutenVector K d) (b : SchoutenMCSeries π) :
    AgreeBelow (k := K) (V := SchoutenBivector K d) N (schoutenMCElementary π hπ N hN X b).val b.val :=
  schoutenElementaryMotion_agree π N hN X b.val

theorem schoutenMCElementary_leading (π : SchoutenBivector K d)
    (hπ : (polynomialSchoutenDGLA K d).IsMaurerCartan π)
    (N : ℕ) (hN : 0 < N) (X : SchoutenVector K d) (b : SchoutenMCSeries π) :
    coeffV (k := K) N (schoutenMCElementary π hπ N hN X b).val - coeffV (k := K) N b.val =
      -schoutenBracket K d 1 0 π X :=
  schoutenElementaryMotion_leading_twist π N hN X b.val b.property.1

/-- Per-generator MC equivalences for the already constructed free-group action machinery. -/
def schoutenMCMove (π : SchoutenBivector K d)
    (hπ : (polynomialSchoutenDGLA K d).IsMaurerCartan π)
    (γ : ElementaryLabel (SchoutenVector K d)) : Equiv.Perm (SchoutenMCSeries π) :=
  schoutenMCElementary π hπ γ.order γ.positive γ.direction

def schoutenMCCoordinateUnit (γ : ElementaryLabel (SchoutenVector K d)) :
    GaugeUnit (Module.End K (PolynomialFunctions K d)) :=
  schoutenCoordinateGauge γ.order γ.positive γ.direction

/-- The actual complete bracket attached to a source MC element. -/
def schoutenMCBinary (π : SchoutenBivector K d) (b : SchoutenMCSeries π) :
    Binary (PowerSeries K) (PowerSeriesModule K (PolynomialFunctions K d)) :=
  extendBinary (rawBivectorSeries (single (k := K) 0 π + b.val))

/-- Every elementary MC move is intertwined by its actual coordinate operator. -/
theorem schoutenMCMove_intertwines (π : SchoutenBivector K d)
    (hπ : (polynomialSchoutenDGLA K d).IsMaurerCartan π)
    (γ : ElementaryLabel (SchoutenVector K d)) (b : SchoutenMCSeries π)
    (p q : PowerSeriesModule K (PolynomialFunctions K d)) :
    operator (schoutenMCCoordinateUnit γ).series (schoutenMCBinary π b p q) =
      schoutenMCBinary π (schoutenMCMove π hπ γ b)
        (operator (schoutenMCCoordinateUnit γ).series p) (operator (schoutenMCCoordinateUnit γ).series q) := by
  let G := operatorUnitEquiv (k := K) (V := PolynomialFunctions K d) (schoutenMCCoordinateUnit γ).val
  have hfull : single (k := K) 0 π + (schoutenMCMove π hπ γ b).val =
      schoutenElementaryEquiv γ.order γ.positive γ.direction (single (k := K) 0 π + b.val) := by
    change single (k := K) 0 π +
      (schoutenElementaryEquiv γ.order γ.positive γ.direction (single (k := K) 0 π + b.val) -
        single (k := K) 0 π) = _
    abel
  change G (extendBinary (rawBivectorSeries (single (k := K) 0 π + b.val)) p q) =
    extendBinary (rawBivectorSeries (single (k := K) 0 π + (schoutenMCMove π hπ γ b).val)) (G p) (G q)
  rw [hfull, schoutenElementaryEquiv_raw_conjugate, extendBinary_conjugateBinarySeries, conjugate_apply]
  change G (extendBinary (rawBivectorSeries (single (k := K) 0 π + b.val)) p q) =
    G (extendBinary (rawBivectorSeries (single (k := K) 0 π + b.val)) (G.symm (G p)) (G.symm (G q)))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

/-- Genuine source MC solutions carry the action generated by elementary corrections. -/
@[reducible] def schoutenMCGeneratedAction (π : SchoutenBivector K d)
    (hπ : (polynomialSchoutenDGLA K d).IsMaurerCartan π) :
    MulAction (FreeGroup (ElementaryLabel (SchoutenVector K d))) (SchoutenMCSeries π) :=
  generatedMulAction (schoutenMCMove π hπ)

/-- The actual complete coordinate equivalence for an elementary label. -/
def schoutenMCCoordinateEquiv (γ : ElementaryLabel (SchoutenVector K d)) :
    PowerSeriesModule K (PolynomialFunctions K d) ≃ₗ[PowerSeries K]
      PowerSeriesModule K (PolynomialFunctions K d) :=
  operatorUnitEquiv (k := K) (V := PolynomialFunctions K d) (schoutenMCCoordinateUnit γ).val

/-- Intertwining holds for every finite word, including inverse elementary moves. -/
theorem schoutenMCGenerated_intertwines (π : SchoutenBivector K d)
    (hπ : (polynomialSchoutenDGLA K d).IsMaurerCartan π)
    (s : FreeGroup (ElementaryLabel (SchoutenVector K d))) (b : SchoutenMCSeries π)
    (p q : PowerSeriesModule K (PolynomialFunctions K d)) :
    FreeGroup.lift schoutenMCCoordinateEquiv s (schoutenMCBinary π b p q) =
      schoutenMCBinary π (FreeGroup.lift (schoutenMCMove π hπ) s b)
        (FreeGroup.lift schoutenMCCoordinateEquiv s p)
        (FreeGroup.lift schoutenMCCoordinateEquiv s q) :=
  generated_intertwines (schoutenMCMove π hπ) schoutenMCCoordinateEquiv
    (schoutenMCBinary π) (schoutenMCMove_intertwines π hπ) s b p q

end EnvelopingIsomorphism.Deformation.Gauge
