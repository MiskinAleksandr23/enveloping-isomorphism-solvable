import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.RingTheory.Finiteness.Basic

/-! Local finiteness and local nilpotence of linear endomorphisms, including
their intrinsic interpretation for inner derivations of associative algebras. -/

namespace EnvelopingIsomorphism.Identification

universe u v w
variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable {W : Type w} [AddCommGroup W] [Module R W]

/-- Each individual vector is killed by some power of the endomorphism. -/
def IsLocallyNilpotent (D : Module.End R V) : Prop :=
  ∀ x, ∃ n : ℕ, (D ^ n) x = 0

/-- Each orbit spans a finitely generated submodule. Over a field this is
precisely finite dimensionality of every orbit space. -/
def IsLocallyFinite (D : Module.End R V) : Prop :=
  ∀ x, (Submodule.span R (Set.range (fun n : ℕ => (D ^ n) x))).FG

theorem pow_apply_eq_zero_of_le (D : Module.End R V)
    {x : V} {n m : ℕ} (hx : (D ^ n) x = 0) (hnm : n ≤ m) : (D ^ m) x = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [add_comm n r, pow_add, Module.End.mul_apply, hx, map_zero]

/-- A locally nilpotent operator has finitely generated orbit spaces. -/
theorem IsLocallyNilpotent.isLocallyFinite {D : Module.End R V}
    (hD : IsLocallyNilpotent D) : IsLocallyFinite D := by
  intro x
  obtain ⟨n, hn⟩ := hD x
  have hrange : Set.range (fun j : ℕ => (D ^ j) x) =
      Set.range (fun j : Fin (n + 1) => (D ^ (j : ℕ)) x) := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      by_cases hj : j < n + 1
      · exact ⟨⟨j, hj⟩, rfl⟩
      · refine ⟨⟨n, Nat.lt_succ_self n⟩, ?_⟩
        change (D ^ n) x = (D ^ j) x
        rw [hn, pow_apply_eq_zero_of_le D hn (by omega)]
    · rintro ⟨j, rfl⟩
      exact ⟨j, rfl⟩
  rw [hrange]
  exact Submodule.fg_span (Set.finite_range _)

theorem intertwine_pow_apply (D : Module.End R V) (E : Module.End R W)
    (f : V →ₗ[R] W) (hf : ∀ x, f (D x) = E (f x)) (n : ℕ) (x : V) :
    f ((D ^ n) x) = (E ^ n) (f x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ', Module.End.mul_apply, hf, ih]

theorem locallyNilpotent_of_surjective_intertwiner
    (D : Module.End R V) (E : Module.End R W) (f : V →ₗ[R] W)
    (hf : ∀ x, f (D x) = E (f x)) (hsurj : Function.Surjective f)
    (hD : IsLocallyNilpotent D) : IsLocallyNilpotent E := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  obtain ⟨n, hn⟩ := hD x
  refine ⟨n, ?_⟩
  rw [← intertwine_pow_apply D E f hf, hn, map_zero]

theorem locallyNilpotent_of_injective_intertwiner
    (D : Module.End R V) (E : Module.End R W) (f : V →ₗ[R] W)
    (hf : ∀ x, f (D x) = E (f x)) (hinj : Function.Injective f)
    (hE : IsLocallyNilpotent E) : IsLocallyNilpotent D := by
  intro x
  obtain ⟨n, hn⟩ := hE (f x)
  refine ⟨n, hinj ?_⟩
  rw [intertwine_pow_apply D E f hf, hn, map_zero]

theorem orbitSpan_map (D : Module.End R V) (E : Module.End R W)
    (f : V →ₗ[R] W) (hf : ∀ x, f (D x) = E (f x)) (x : V) :
    (Submodule.span R (Set.range (fun n : ℕ => (D ^ n) x))).map f =
      Submodule.span R (Set.range (fun n : ℕ => (E ^ n) (f x))) := by
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext n
  exact intertwine_pow_apply D E f hf n x

theorem locallyFinite_of_surjective_intertwiner
    (D : Module.End R V) (E : Module.End R W) (f : V →ₗ[R] W)
    (hf : ∀ x, f (D x) = E (f x)) (hsurj : Function.Surjective f)
    (hD : IsLocallyFinite D) : IsLocallyFinite E := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  rw [← orbitSpan_map D E f hf]
  exact (hD x).map f

theorem locallyFinite_of_injective_intertwiner
    (D : Module.End R V) (E : Module.End R W) (f : V →ₗ[R] W)
    (hf : ∀ x, f (D x) = E (f x)) (hinj : Function.Injective f)
    (hE : IsLocallyFinite E) : IsLocallyFinite D := by
  intro x
  apply Submodule.fg_of_fg_map_injective f hinj
  rw [orbitSpan_map D E f hf]
  exact hE (f x)

section Associative

variable {A : Type v} [Ring A] [Algebra R A]
variable {B : Type w} [Ring B] [Algebra R B]
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The intrinsic set of elements with locally nilpotent inner derivation. -/
def LN (R : Type u) [CommRing R] (A : Type v) [Ring A] [Algebra R A] : Set A :=
  {a | IsLocallyNilpotent (LieAlgebra.ad R A a)}

/-- The intrinsic set of elements with locally finite inner derivation. -/
def LF (R : Type u) [CommRing R] (A : Type v) [Ring A] [Algebra R A] : Set A :=
  {a | IsLocallyFinite (LieAlgebra.ad R A a)}

theorem LN_subset_LF : LN R A ⊆ LF R A :=
  fun _ ha => ha.isLocallyFinite

/-- Local nilpotence of an inner derivation descends through an associative
algebra quotient. -/
theorem mem_LN_map_of_surjective (f : A →ₐ[R] B) (hf : Function.Surjective f)
    {a : A} (ha : a ∈ LN R A) : f a ∈ LN R B := by
  apply locallyNilpotent_of_surjective_intertwiner _ _ f.toLinearMap _ hf ha
  intro x
  simp only [AlgHom.toLinearMap_apply, LieAlgebra.ad_apply, Ring.lie_def, map_sub, map_mul]

/-- Local finiteness of an inner derivation descends through an associative
algebra quotient. -/
theorem mem_LF_map_of_surjective (f : A →ₐ[R] B) (hf : Function.Surjective f)
    {a : A} (ha : a ∈ LF R A) : f a ∈ LF R B := by
  apply locallyFinite_of_surjective_intertwiner _ _ f.toLinearMap _ hf ha
  intro x
  simp only [AlgHom.toLinearMap_apply, LieAlgebra.ad_apply, Ring.lie_def, map_sub, map_mul]

theorem mem_LN_map_iff (e : A ≃ₐ[R] B) (a : A) : e a ∈ LN R B ↔ a ∈ LN R A := by
  have h (x : A) : e (LieAlgebra.ad R A a x) = LieAlgebra.ad R B (e a) (e x) := by
    simp only [LieAlgebra.ad_apply, Ring.lie_def, map_sub, map_mul]
  exact ⟨locallyNilpotent_of_injective_intertwiner _ _ e.toLinearMap h e.injective,
    locallyNilpotent_of_surjective_intertwiner _ _ e.toLinearMap h e.surjective⟩

theorem mem_LF_map_iff (e : A ≃ₐ[R] B) (a : A) : e a ∈ LF R B ↔ a ∈ LF R A := by
  have h (x : A) : e (LieAlgebra.ad R A a x) = LieAlgebra.ad R B (e a) (e x) := by
    simp only [LieAlgebra.ad_apply, Ring.lie_def, map_sub, map_mul]
  exact ⟨locallyFinite_of_injective_intertwiner _ _ e.toLinearMap h e.injective,
    locallyFinite_of_surjective_intertwiner _ _ e.toLinearMap h e.surjective⟩

theorem image_LN (e : A ≃ₐ[R] B) : e '' LN R A = LN R B := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (mem_LN_map_iff e a).mpr ha
  · intro hb
    exact ⟨e.symm b, (mem_LN_map_iff e (e.symm b)).mp (by simpa using hb),
      e.apply_symm_apply b⟩

theorem image_LF (e : A ≃ₐ[R] B) : e '' LF R A = LF R B := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (mem_LF_map_iff e a).mpr ha
  · intro hb
    exact ⟨e.symm b, (mem_LF_map_iff e (e.symm b)).mp (by simpa using hb),
      e.apply_symm_apply b⟩

end Associative
end EnvelopingIsomorphism.Identification
