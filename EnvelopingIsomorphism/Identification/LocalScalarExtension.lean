import EnvelopingIsomorphism.Identification.LocallyFinite
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Descent

/-!
Local nilpotence and local finiteness under field extensions.  The underlying
vector space is arbitrary and is not assumed finite dimensional.
-/

namespace EnvelopingIsomorphism.Identification

open scoped TensorProduct

universe u v w
variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {V : Type w} [AddCommGroup V] [Module k V]

/-- The submodule spanned by the orbit of a single vector. -/
abbrev orbitSpan (D : Module.End k V) (x : V) : Submodule k V :=
  Submodule.span k (Set.range (fun n : ℕ => (D ^ n) x))

@[simp] theorem baseChange_pow_tmul (D : Module.End k V) (n : ℕ) (a : K) (x : V) :
    (D.baseChange K ^ n) (a ⊗ₜ[k] x) = a ⊗ₜ[k] (D ^ n) x := by
  rw [← LinearMap.baseChange_pow, LinearMap.baseChange_tmul]

/-- Local nilpotence extends to arbitrary finite sums of pure tensors. -/
theorem IsLocallyNilpotent.baseChange {D : Module.End k V}
    (hD : IsLocallyNilpotent D) : IsLocallyNilpotent (D.baseChange K) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, rfl⟩
  | tmul a x =>
      obtain ⟨n, hn⟩ := hD x
      refine ⟨n, ?_⟩
      simp only [baseChange_pow_tmul, hn, TensorProduct.tmul_zero]
  | add x y hx hy =>
      obtain ⟨n, hn⟩ := hx
      obtain ⟨m, hm⟩ := hy
      refine ⟨max n m, ?_⟩
      rw [map_add, pow_apply_eq_zero_of_le _ hn (Nat.le_max_left _ _),
        pow_apply_eq_zero_of_le _ hm (Nat.le_max_right _ _), add_zero]

/-- Local nilpotence is detected after any field extension. -/
theorem isLocallyNilpotent_baseChange_iff (D : Module.End k V) :
    IsLocallyNilpotent (D.baseChange K) ↔ IsLocallyNilpotent D := by
  constructor
  · intro hD x
    obtain ⟨n, hn⟩ := hD ((1 : K) ⊗ₜ[k] x)
    refine ⟨n, ?_⟩
    rw [baseChange_pow_tmul] at hn
    exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff k V (A := K) _).mp hn
  · exact IsLocallyNilpotent.baseChange

/-- The orbit of `1 ⊗ x` is the scalar extension of the orbit of `x`. -/
theorem orbitSpan_one_tmul (D : Module.End k V) (x : V) :
    orbitSpan (D.baseChange K) ((1 : K) ⊗ₜ[k] x) = (orbitSpan D x).baseChange K := by
  rw [orbitSpan, Submodule.baseChange_span, ← Set.range_comp]
  congr 2
  funext n
  exact baseChange_pow_tmul D n 1 x

/-- Finite generation of submodules is preserved by extending scalars. -/
theorem fg_baseChange (P : Submodule k V) (hP : P.FG) : (P.baseChange K).FG := by
  rw [Submodule.baseChange_eq_span]
  exact (hP.map (TensorProduct.mk k K V 1)).span

/-- Finite generation of a submodule is detected after any field extension. -/
theorem fg_baseChange_iff (P : Submodule k V) : (P.baseChange K).FG ↔ P.FG := by
  constructor
  · intro hP
    letI : Module.Finite K (P.baseChange K) := Module.Finite.iff_fg.mpr hP
    letI : Module.Finite K (K ⊗[k] P) :=
      Module.Finite.equiv (Submodule.toBaseChange.toLinearEquiv K P).symm
    exact Module.Finite.iff_fg.mp (Module.Finite.of_finite_tensorProduct_of_faithfullyFlat K)
  · exact fg_baseChange P

/-- The orbit of a sum lies in the sum of the two orbit spaces. -/
theorem orbitSpan_add_le (D : Module.End k V) (x y : V) :
    orbitSpan D (x + y) ≤ orbitSpan D x ⊔ orbitSpan D y := by
  apply Submodule.span_le.mpr
  rintro z ⟨n, rfl⟩
  dsimp only
  rw [map_add]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (Submodule.subset_span ⟨n, rfl⟩))
    (Submodule.mem_sup_right (Submodule.subset_span ⟨n, rfl⟩))

/-- Finite generation of an individual orbit is closed under addition. -/
theorem orbitSpan_add_fg (D : Module.End k V) {x y : V}
    (hx : (orbitSpan D x).FG) (hy : (orbitSpan D y).FG) : (orbitSpan D (x + y)).FG :=
  (hx.sup hy).of_le (orbitSpan_add_le D x y)

/-- Local finiteness extends to arbitrary finite sums of pure tensors. -/
theorem IsLocallyFinite.baseChange {D : Module.End k V}
    (hD : IsLocallyFinite D) : IsLocallyFinite (D.baseChange K) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simpa [orbitSpan, map_zero] using (Submodule.fg_bot :
      (⊥ : Submodule K (K ⊗[k] V)).FG)
  | tmul a x =>
      apply (fg_baseChange (K := K) (orbitSpan D x) (hD x)).of_le
      apply Submodule.span_le.mpr
      rintro z ⟨n, rfl⟩
      dsimp only
      rw [baseChange_pow_tmul]
      exact Submodule.tmul_mem_baseChange_of_mem a (Submodule.subset_span ⟨n, rfl⟩)
  | add x y hx hy => exact orbitSpan_add_fg _ hx hy

/-- Local finiteness is detected after arbitrary field extension, without any
finite-dimensionality assumption on the original vector space. -/
theorem isLocallyFinite_baseChange_iff (D : Module.End k V) :
    IsLocallyFinite (D.baseChange K) ↔ IsLocallyFinite D := by
  constructor
  · intro hD x
    apply (fg_baseChange_iff (K := K) (orbitSpan D x)).mp
    rw [← orbitSpan_one_tmul]
    exact hD ((1 : K) ⊗ₜ[k] x)
  · exact IsLocallyFinite.baseChange

section Associative

variable {A : Type w} [Ring A] [Algebra k A]
attribute [local instance 100] LieRing.ofAssociativeRing

/-- Scalar extension commutes with the inner derivation of a fixed element. -/
theorem baseChange_ad (a : A) :
    (LieAlgebra.ad k A a).baseChange K =
      LieAlgebra.ad K (K ⊗[k] A) ((1 : K) ⊗ₜ[k] a) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro b x
  simp only [LinearMap.baseChange_tmul, LieAlgebra.ad_apply, Ring.lie_def,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, TensorProduct.tmul_sub]

/-- Whether a fixed element has locally nilpotent inner derivation can be
checked after any field extension, including transcendental extensions. -/
theorem mem_LN_one_tmul_iff (a : A) :
    (1 : K) ⊗ₜ[k] a ∈ LN K (K ⊗[k] A) ↔ a ∈ LN k A := by
  change IsLocallyNilpotent (LieAlgebra.ad K _ _) ↔ IsLocallyNilpotent _
  rw [← baseChange_ad]
  exact isLocallyNilpotent_baseChange_iff _

/-- Whether a fixed element has locally finite inner derivation can be checked
after arbitrary algebraic or transcendental field extension. -/
theorem mem_LF_one_tmul_iff (a : A) :
    (1 : K) ⊗ₜ[k] a ∈ LF K (K ⊗[k] A) ↔ a ∈ LF k A := by
  change IsLocallyFinite (LieAlgebra.ad K _ _) ↔ IsLocallyFinite _
  rw [← baseChange_ad]
  exact isLocallyFinite_baseChange_iff _

end Associative

end EnvelopingIsomorphism.Identification
