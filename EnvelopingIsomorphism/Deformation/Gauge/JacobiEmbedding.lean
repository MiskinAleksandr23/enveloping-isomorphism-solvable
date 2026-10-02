import EnvelopingIsomorphism.Deformation.SchoutenJacobi
import EnvelopingIsomorphism.Deformation.Gauge.AssociativeEmbedding

/-!
# Faithful coefficient embeddings detect full-series Jacobi equations

The ternary operation is the genuine cyclic insertion and its extension is
the actual nested bracket on complete vector series. Coefficient spaces may
be arbitrary modules, including the bounded Laurent cochain spaces.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

section JacobiLinear

variable {k A : Type*} [CommRing k] [AddCommGroup A] [Module k A]

/-- The actual cyclic insertion as a bilinear map on coefficient brackets. -/
def jacobiInsertLinear : Binary k A →ₗ[k] Binary k A →ₗ[k] Ternary k A :=
  insertLeftLinear + insertLeftLinear.compr₂ rotateTernary +
    insertLeftLinear.compr₂ (rotateTernary.comp rotateTernary)

@[simp] theorem jacobiInsertLinear_apply (μ ν : Binary k A) : jacobiInsertLinear μ ν = jacobiInsert μ ν := rfl

def jacobiDifferential (μ : Binary k A) : Binary k A →ₗ[k] Ternary k A :=
  jacobiInsertLinear μ + jacobiInsertLinear.flip μ

@[simp] theorem jacobiDifferential_apply (μ ν : Binary k A) :
    jacobiDifferential μ ν = jacobiInsert μ ν + jacobiInsert ν μ := rfl

def jacobiInsertionSeries (B C : PowerSeriesModule k (Binary k A)) :
    PowerSeriesModule k (Ternary k A) :=
  applyBilinear (k := k) (V := Binary k A) (W := Binary k A) (X := Ternary k A)
    (jacobiInsertLinear (k := k) (A := A)) B C

theorem jacobiInsertionSeries_eq_rotations (B C : PowerSeriesModule k (Binary k A)) :
    jacobiInsertionSeries B C = postcomposeBinary B C +
      map rotateTernary (postcomposeBinary B C) +
      map rotateTernary (map rotateTernary (postcomposeBinary B C)) := by
  simp only [← applyBilinear_insertLeft]
  apply PowerSeriesModule.ext
  intro n
  simp only [jacobiInsertionSeries,
    coeffV_applyBilinear (k := k) (V := Binary k A) (W := Binary k A) (X := Ternary k A),
    coeffV_add, coeffV_map, map_sum, jacobiInsertLinear_apply, jacobiInsert, Finset.sum_add_distrib]
  rfl

theorem extendTernary_add (F G : PowerSeriesModule k (Ternary k A))
    (p q r : PowerSeriesModule k A) :
    extendTernary (F + G) p q r = extendTernary F p q r + extendTernary G p q r := by
  simp [extendTernary, extendBinary_apply]

/-- The coefficient convolution evaluates to the full nested Jacobi insertion. -/
theorem extendTernary_jacobiInsertion (B C : PowerSeriesModule k (Binary k A))
    (p q r : PowerSeriesModule k A) :
    extendTernary (jacobiInsertionSeries B C) p q r =
      jacobiInsert (extendBinary B) (extendBinary C) p q r := by
  rw [jacobiInsertionSeries_eq_rotations]
  simp only [extendTernary_add, extendTernary_rotate, ← applyBilinear_insertLeft,
    extendTernary_insertLeft, jacobiInsert_apply]

theorem jacobiInsertionSeries_self_zero_iff (B : PowerSeriesModule k (Binary k A)) :
    jacobiInsertionSeries B B = 0 ↔
      ∀ p q r, jacobiInsert (extendBinary B) (extendBinary B) p q r = 0 := by
  rw [← extendTernary_eq_zero_iff]
  simp only [extendTernary_jacobiInsertion]

theorem jacobiInsertionSeries_constant_zero (μ : Binary k A)
    (hμ : ∀ a b c, jacobiInsert μ μ a b c = 0) :
    jacobiInsertionSeries (single 0 μ) (single 0 μ) = 0 := by
  have hz : jacobiInsertLinear (k := k) (A := A) μ μ = 0 := by ext a b c; exact hμ a b c
  rw [jacobiInsertionSeries, applyBilinear_single_zero_left, map_single, hz]
  apply PowerSeriesModule.ext
  intro n
  simp

theorem jacobiInsertionSeries_eq_curvature (μ : Binary k A)
    (hμ : ∀ a b c, jacobiInsert μ μ a b c = 0) (b : PowerSeriesModule k (Binary k A)) :
    jacobiInsertionSeries (single 0 μ + b) (single 0 μ + b) =
      Gauge.quadraticCurvature (k := k) (V := Binary k A) (W := Ternary k A)
        (jacobiDifferential μ) (jacobiInsertLinear (k := k) (A := A)) b := by
  change extendBilinear (k := k) (V := Binary k A) (W := Binary k A) (X := Ternary k A)
    (jacobiInsertLinear (k := k) (A := A)) (single 0 μ + b) (single 0 μ + b) = _
  simp only [map_add, LinearMap.add_apply, extendBilinear_apply]
  rw [show applyBilinear (k := k) (V := Binary k A) (W := Binary k A) (X := Ternary k A)
      (jacobiInsertLinear (k := k) (A := A)) (single 0 μ) (single 0 μ) = 0 from
    jacobiInsertionSeries_constant_zero μ hμ, zero_add,
    applyBilinear_single_zero_left, applyBilinear_single_zero_right]
  apply PowerSeriesModule.ext
  intro n
  simp only [Gauge.quadraticCurvature, coeffV_add, coeffV_map, jacobiDifferential, LinearMap.add_apply]
  abel

theorem quadratic_MC_iff_Jacobi (μ : Binary k A)
    (hμ : ∀ a b c, jacobiInsert μ μ a b c = 0) (b : PowerSeriesModule k (Binary k A)) :
    Gauge.quadraticCurvature (k := k) (V := Binary k A) (W := Ternary k A)
      (jacobiDifferential μ) (jacobiInsertLinear (k := k) (A := A)) b = 0 ↔
      ∀ p q r, jacobiInsert (extendBinary (single 0 μ + b)) (extendBinary (single 0 μ + b)) p q r = 0 := by
  rw [← jacobiInsertionSeries_eq_curvature μ hμ b, jacobiInsertionSeries_self_zero_iff]

end JacobiLinear

namespace Gauge

variable {k C T A : Type*} [Field k] [CharZero k]
  [AddCommGroup C] [Module k C] [AddCommGroup T] [Module k T]
  [AddCommGroup A] [Module k A]

/-- The source mixed bracket carries the half-normalized symmetric Jacobi insertion. -/
theorem jacobi_curvature_embedding
    (d : C →ₗ[k] T) (I : C →ₗ[k] C →ₗ[k] T)
    (ι : C →ₗ[k] Binary k A) (κ : T →ₗ[k] Ternary k A) (μ : Binary k A)
    (hd : ∀ c, κ (d c) = jacobiInsert μ (ι c) + jacobiInsert (ι c) μ)
    (hI : ∀ c e, κ (I c e) = (2 : k)⁻¹ •
      (jacobiInsert (ι c) (ι e) + jacobiInsert (ι e) (ι c)))
    (b : PowerSeriesModule k C) :
    map κ (quadraticCurvature d I b) =
      quadraticCurvature (k := k) (V := Binary k A) (W := Ternary k A)
        (jacobiDifferential μ) (jacobiInsertLinear (k := k) (A := A)) (map ι b) := by
  apply PowerSeriesModule.ext
  intro n
  simp only [quadraticCurvature, coeffV_map, coeffV_add, map_add, coeffV_applyBilinear,
    coeffV_applyBilinear (k := k) (V := Binary k A) (W := Binary k A) (X := Ternary k A),
    map_sum, hd, jacobiDifferential_apply, jacobiInsertLinear_apply]
  congr 1
  simp only [hI]
  rw [← Finset.smul_sum, Finset.sum_add_distrib]
  have hs : (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      jacobiInsert (ι (coeffV ij.2 b)) (ι (coeffV ij.1 b))) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        jacobiInsert (ι (coeffV ij.1 b)) (ι (coeffV ij.2 b)) :=
    Finset.Nat.sum_antidiagonal_swap (n := n)
      (f := fun ij => jacobiInsert (ι (coeffV ij.1 b)) (ι (coeffV ij.2 b)))
  rw [hs, ← two_smul k, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

/-- Faithful ternary evaluation detects the genuine full-series source MC equation. -/
theorem quadratic_MC_iff_Jacobi_of_embedding
    (d : C →ₗ[k] T) (I : C →ₗ[k] C →ₗ[k] T)
    (ι : C →ₗ[k] Binary k A) (κ : T →ₗ[k] Ternary k A) (hκ : Function.Injective κ)
    (μ : Binary k A) (hμ : ∀ a b c, jacobiInsert μ μ a b c = 0)
    (hd : ∀ c, κ (d c) = jacobiInsert μ (ι c) + jacobiInsert (ι c) μ)
    (hI : ∀ c e, κ (I c e) = (2 : k)⁻¹ •
      (jacobiInsert (ι c) (ι e) + jacobiInsert (ι e) (ι c)))
    (b : PowerSeriesModule k C) :
    quadraticCurvature d I b = 0 ↔
      ∀ p q r, jacobiInsert (extendBinary (single 0 μ + map ι b))
        (extendBinary (single 0 μ + map ι b)) p q r = 0 := by
  rw [← quadratic_MC_iff_Jacobi μ hμ, ← jacobi_curvature_embedding d I ι κ μ hd hI]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    apply seriesMap_injective (k := k) (V := T) (W := Ternary k A) κ hκ
    simpa only [map_zero] using h

end Gauge

end EnvelopingIsomorphism.Deformation
