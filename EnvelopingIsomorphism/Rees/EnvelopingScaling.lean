import EnvelopingIsomorphism.Rees.Family
import EnvelopingIsomorphism.PBW.Weighted
import EnvelopingIsomorphism.Enveloping.BaseChange
import Mathlib.RingTheory.TensorProduct.Maps

/-! The actual injective enveloping-algebra comparison used in D3. -/

noncomputable section

namespace EnvelopingIsomorphism.Rees

open Module UniversalEnvelopingAlgebra
open scoped TensorProduct BigOperators

variable {k ι L : Type*} [Field k] [Fintype ι] [LinearOrder ι]
    [LieRing L] [LieAlgebra k L] {b : Basis ι k L} (d : WeightData b)

attribute [local instance] EnvelopingIsomorphism.Rees.laurentBaseModule
local instance envelopingLaurentSMul : SMul k (LaurentSeries k) :=
  (inferInstance : Algebra k (LaurentSeries k)).toSMul

namespace EnvelopingFamily

abbrev U := UniversalEnvelopingAlgebra (Polynomial k) (Family d)
abbrev Ambient := LaurentSeries k ⊗[k] UniversalEnvelopingAlgebra k L

scoped instance ambientPolynomialAlgebra : Algebra (Polynomial k) (Ambient (k := k) (L := L)) :=
  Algebra.restrictScalars (Polynomial k) (LaurentSeries k) _
scoped instance ambientPolynomialSMul : SMul (Polynomial k) (Ambient (k := k) (L := L)) :=
  ambientPolynomialAlgebra.toSMul
scoped instance ambientPolynomialModule : Module (Polynomial k) (Ambient (k := k) (L := L)) :=
  Algebra.toModule
local instance ambientPolynomialTower :
    IsScalarTower (Polynomial k) (LaurentSeries k) (Ambient (k := k) (L := L)) :=
  IsScalarTower.of_compHom (Polynomial k) (LaurentSeries k) _

/-- Scalar extension of the Rees enveloping algebra is the original scalar-extended envelope. -/
def ambientScaleEquiv : LaurentSeries k ⊗[Polynomial k] U d ≃ₐ[LaurentSeries k]
    Ambient (k := k) (L := L) :=
  (EnvelopingIsomorphism.Enveloping.baseChangeEquiv (Polynomial k) (LaurentSeries k) (Family d)).symm.trans
    ((EnvelopingIsomorphism.Enveloping.congr (Family.scaleLieEquiv d)).trans
      (EnvelopingIsomorphism.Enveloping.baseChangeEquiv k (LaurentSeries k) L))

/-- Embed the actual polynomial enveloping algebra by diagonal Laurent scaling. -/
def scaling : U d →ₐ[Polynomial k] Ambient (k := k) (L := L) :=
  { toRingHom := (ambientScaleEquiv d).toRingHom.comp
      (Algebra.TensorProduct.includeRight : U d →ₐ[Polynomial k]
        LaurentSeries k ⊗[Polynomial k] U d).toRingHom
    commutes' p := by
      change ambientScaleEquiv d ((1 : LaurentSeries k) ⊗ₜ[Polynomial k]
        algebraMap (Polynomial k) (U d) p) =
          algebraMap (LaurentSeries k) (Ambient (k := k) (L := L))
            (algebraMap (Polynomial k) (LaurentSeries k) p)
      rw [← Algebra.TensorProduct.algebraMap_apply']
      exact (ambientScaleEquiv d).commutes _ }

omit [LinearOrder ι] in
@[simp] theorem scaling_ι_basis (i : ι) :
    scaling d (UniversalEnvelopingAlgebra.ι (Polynomial k) (Family.basis d i)) =
      d.scale i ⊗ₜ[k] UniversalEnvelopingAlgebra.ι k (b i) := by
  change ambientScaleEquiv d ((1 : LaurentSeries k) ⊗ₜ[Polynomial k]
    UniversalEnvelopingAlgebra.ι (Polynomial k) (Family.basis d i)) = _
  simp only [ambientScaleEquiv, AlgEquiv.trans_apply,
    EnvelopingIsomorphism.Enveloping.baseChangeEquiv_symm_tmul_ι,
    EnvelopingIsomorphism.Enveloping.congr_ι, Family.scaleLieEquiv_basis,
    EnvelopingIsomorphism.Enveloping.baseChangeEquiv_ι_tmul]

/-- PBW freeness makes extension to the Laurent field injective, before any relations are tested. -/
theorem scaling_injective : Function.Injective (scaling d) := by
  intro x y h
  have ht : (1 : LaurentSeries k) ⊗ₜ[Polynomial k] x = 1 ⊗ₜ[Polynomial k] y :=
    (ambientScaleEquiv d).injective h
  apply (PBW.pbwBasis (Family.basis d)).ext_elem
  intro m
  have he := congrArg
    (fun z ↦ ((PBW.pbwBasis (Family.basis d)).baseChange (LaurentSeries k)).repr z m) ht
  apply Polynomial.algebraMap_hahnSeries_injective (R := k) ℤ
  simpa [Algebra.smul_def] using he

/-- Scaling an arbitrary word gives one Laurent monomial times the original word. -/
theorem scaling_word (w : List ι) :
    scaling d ((w.map (UniversalEnvelopingAlgebra.ι (Polynomial k) ∘ Family.basis d)).prod) =
      HahnSeries.single (-(PBW.wordWeight d.weight w : ℤ)) (1 : k) ⊗ₜ[k]
        ((w.map (UniversalEnvelopingAlgebra.ι k ∘ b)).prod) := by
  induction w with
  | nil => simp [Algebra.TensorProduct.one_def, PBW.wordWeight]
  | cons i w ih =>
      simp only [List.map_cons, List.prod_cons, Function.comp_apply, map_mul,
        scaling_ι_basis, ih, Algebra.TensorProduct.tmul_mul_tmul]
      simp [WeightData.scale, PBW.wordWeight_cons, HahnSeries.single_mul_single, add_comm]

@[simp] theorem scaling_pbwBasis (m : ι →₀ ℕ) :
    scaling d (PBW.pbwBasis (Family.basis d) m) =
      HahnSeries.single (-(Finsupp.weight d.weight m : ℤ)) (1 : k) ⊗ₜ[k] PBW.pbwBasis b m := by
  simpa only [PBW.pbwBasis_apply, PBW.wordWeight, PBW.wordIndex_orderedWord] using
    scaling_word d (PBW.orderedWord m)

/-- Scalar multiplication through the polynomial-to-Laurent embedding. -/
theorem polynomial_smul_tmul (p : Polynomial k) (a : LaurentSeries k)
    (x : UniversalEnvelopingAlgebra k L) :
    p • (a ⊗ₜ[k] x : Ambient (k := k) (L := L)) =
      (algebraMap (Polynomial k) (LaurentSeries k) p * a) ⊗ₜ[k] x := by
  rw [Algebra.smul_def]
  change ((algebraMap (Polynomial k) (LaurentSeries k) p) ⊗ₜ[k] (1 : UniversalEnvelopingAlgebra k L)) *
    (a ⊗ₜ[k] x) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- The elementary exponent identity behind polynomial Rees reweighting. -/
theorem reweighted_scalar (n w : ℕ) (hw : n ≤ w) (c : k) :
    algebraMap (Polynomial k) (LaurentSeries k) (Polynomial.C c * Polynomial.X ^ (w - n)) *
      HahnSeries.single (-(w : ℤ)) 1 = HahnSeries.single (-(n : ℤ)) c := by
  have he : ((w - n : ℕ) : ℤ) + -(w : ℤ) = -(n : ℤ) := by omega
  simp [Polynomial.algebraMap_hahnSeries_apply, HahnSeries.C_apply,
    HahnSeries.single_mul_single, he]

omit [Fintype ι] in
include b in
theorem single_coeff_tmul (n : ℤ) (c : k) (x : UniversalEnvelopingAlgebra k L) :
    HahnSeries.single n c ⊗ₜ[k] x = HahnSeries.single n (1 : k) ⊗ₜ[k] (c • x) := by
  apply ((PBW.pbwBasis b).baseChange (LaurentSeries k)).ext_elem
  intro m
  simp only [Basis.baseChange_repr_tmul, map_smul, Finsupp.smul_apply]
  simp [Algebra.smul_def, HahnSeries.algebraMap_apply', HahnSeries.C_apply,
    HahnSeries.single_mul_single, mul_comm]

/-- The explicit PBW polynomial lift of a fixed lower-weight element. -/
def homogenize (n : ℕ) (a : UniversalEnvelopingAlgebra k L) : U d :=
  ((PBW.pbwBasis b).repr a).sum (fun m c ↦
    (Polynomial.C c * Polynomial.X ^ (Finsupp.weight d.weight m - n)) •
      PBW.pbwBasis (Family.basis d) m)

@[simp] theorem homogenize_zero (n : ℕ) : homogenize d n 0 = 0 := by simp [homogenize]

theorem homogenize_add (n : ℕ) (a a' : UniversalEnvelopingAlgebra k L) :
    homogenize d n (a + a') = homogenize d n a + homogenize d n a' := by
  simp [homogenize, Finsupp.sum_add_index, add_mul, add_smul]

theorem homogenize_neg (n : ℕ) (a : UniversalEnvelopingAlgebra k L) :
    homogenize d n (-a) = -homogenize d n a := by
  apply add_left_cancel (a := homogenize d n a)
  rw [← homogenize_add, add_neg_cancel, homogenize_zero, add_neg_cancel]

@[simp] theorem homogenize_pbwBasis (n : ℕ) (m : ι →₀ ℕ) :
    homogenize d n (PBW.pbwBasis b m) =
      (Polynomial.X : Polynomial k) ^ (Finsupp.weight d.weight m - n) •
        PBW.pbwBasis (Family.basis d) m := by
  rw [homogenize, (PBW.pbwBasis b).repr_self]
  simp

/-- The polynomial lift has exactly the desired Laurent-scaled value when its support permits it. -/
theorem scaling_homogenize (n : ℕ) (a : UniversalEnvelopingAlgebra k L)
    (ha : a ∈ PBW.weightedLower b d.weight n) :
    scaling d (homogenize d n a) = HahnSeries.single (-(n : ℤ)) (1 : k) ⊗ₜ[k] a := by
  conv_rhs =>
    rw [← (PBW.pbwBasis b).linearCombination_repr a,
      Finsupp.linearCombination_apply, Finsupp.sum, TensorProduct.tmul_sum]
  simp only [homogenize, Finsupp.sum, map_sum, map_smul, scaling_pbwBasis]
  apply Finset.sum_congr rfl
  intro m hm
  rw [polynomial_smul_tmul, reweighted_scalar n _
    ((PBW.mem_weightedLower_iff b d.weight n a).mp ha m hm)]
  exact single_coeff_tmul (b := b) _ _ _

section Specialization

variable {B : Type*} [Ring B] [Algebra (Polynomial k) B]

/-- Strictly higher weight gives a positive parameter power, hence vanishes in every zero fiber. -/
theorem homogenize_high_specializes_zero (n : ℕ) (a : UniversalEnvelopingAlgebra k L)
    (ha : a ∈ PBW.weightedLower b d.weight (n + 1)) (χ : U d →ₐ[Polynomial k] B)
    (hX : algebraMap (Polynomial k) B Polynomial.X = 0) : χ (homogenize d n a) = 0 := by
  simp only [homogenize, Finsupp.sum, map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro m hm
  have hw := (PBW.mem_weightedLower_iff b d.weight (n + 1) a).mp ha m hm
  have hd : Finsupp.weight d.weight m - n ≠ 0 := by omega
  simp [Algebra.smul_def, hX, hd]

/-- A leading generator congruence becomes the exact generator identity in the zero fiber. -/
theorem homogenize_leading_specializes (a : UniversalEnvelopingAlgebra k L) (i : ι)
    (ha : a - UniversalEnvelopingAlgebra.ι k (b i) ∈
      PBW.weightedLower b d.weight (d.weight i + 1))
    (χ : U d →ₐ[Polynomial k] B) (hX : algebraMap (Polynomial k) B Polynomial.X = 0) :
    χ (homogenize d (d.weight i) a) =
      χ (UniversalEnvelopingAlgebra.ι (Polynomial k) (Family.basis d i)) := by
  have hz := homogenize_high_specializes_zero d (d.weight i) _ ha χ hX
  have hs : homogenize d (d.weight i) (UniversalEnvelopingAlgebra.ι k (b i)) =
      UniversalEnvelopingAlgebra.ι (Polynomial k) (Family.basis d i) := by
    rw [← PBW.pbwBasis_single b i, homogenize_pbwBasis]
    simp [Finsupp.weight_single]
  have he : homogenize d (d.weight i) a =
      homogenize d (d.weight i) (a - UniversalEnvelopingAlgebra.ι k (b i)) +
        homogenize d (d.weight i) (UniversalEnvelopingAlgebra.ι k (b i)) := by
    rw [← homogenize_add, sub_add_cancel]
  rw [he, map_add, hz, zero_add, hs]

end Specialization

end EnvelopingFamily

end EnvelopingIsomorphism.Rees
