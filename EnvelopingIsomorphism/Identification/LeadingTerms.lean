import EnvelopingIsomorphism.Identification.IdealFiltration

/-!
# Linear leading terms of an actual enveloping-algebra isomorphism

Approximations in degrees zero and one propagate along the lower central
series. They supply filtered linear lifts and eventually matched adapted bases.
-/

noncomputable section

namespace EnvelopingIsomorphism.Identification

open UniversalEnvelopingAlgebra
open EnvelopingIsomorphism Enveloping Lie PBW

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing M] [LieAlgebra R M]

/-- Elements admitting a linear approximation in a specified lower-central degree. -/
def leadingApproximation
    (φ : UniversalEnvelopingAlgebra R L →ₐ[R] UniversalEnvelopingAlgebra R M)
    (N' : LieIdeal R M) (d : ℕ) : Submodule R L where
  carrier := {x | ∃ y ∈ lowerCentralFiltration N' d,
    φ (ι R x) - ι R y ∈ adicPower R _ (envelopingIdeal N') (d + 1)}
  zero_mem' := ⟨0, Submodule.zero_mem _, by simp⟩
  add_mem' := by
    rintro x z ⟨y, hy, he⟩ ⟨w, hw, hf⟩
    refine ⟨y + w, Submodule.add_mem _ hy hw, ?_⟩
    convert Submodule.add_mem _ he hf using 1
    simp only [map_add]
    abel
  smul_mem' := by
    rintro a x ⟨y, hy, he⟩
    refine ⟨a • y, Submodule.smul_mem _ a hy, ?_⟩
    simpa only [map_smul, smul_sub] using Submodule.smul_mem _ a he

/-- Lie elements in a filtration layer belong to the corresponding actual ideal power. -/
theorem ι_mem_adicPower_of_mem_filtration (N : LieIdeal R L) (d : ℕ)
    {x : L} (hx : x ∈ lowerCentralFiltration N d) :
    ι R x ∈ adicPower R _ (envelopingIdeal N) d := by
  cases d with
  | zero => rw [adicPower_zero]; exact Submodule.mem_top
  | succ d => exact lowerCentralSeries_le_comap_adicPower N d hx

/-- An element with a degree-d approximation already maps into the dth ideal power. -/
theorem map_mem_adicPower_of_leadingApproximation
    (φ : UniversalEnvelopingAlgebra R L →ₐ[R] UniversalEnvelopingAlgebra R M)
    (N' : LieIdeal R M) (d : ℕ) {x : L} (hx : x ∈ leadingApproximation φ N' d) :
    φ (ι R x) ∈ adicPower R _ (envelopingIdeal N') d := by
  obtain ⟨y, hy, he⟩ := hx
  have he' := adicPower_antitone (envelopingIdeal N') (Nat.le_succ d) he
  have h := Submodule.add_mem _ he' (ι_mem_adicPower_of_mem_filtration N' d hy)
  simpa only [sub_add_cancel] using h

/-- Brackets add leading-approximation degrees. -/
theorem lie_mem_leadingApproximation
    (φ : UniversalEnvelopingAlgebra R L →ₐ[R] UniversalEnvelopingAlgebra R M)
    (N' : LieIdeal R M) {d e : ℕ} {x z : L}
    (hx : x ∈ leadingApproximation φ N' d) (hz : z ∈ leadingApproximation φ N' e) :
    ⁅x, z⁆ ∈ leadingApproximation φ N' (d + e) := by
  have hz' := map_mem_adicPower_of_leadingApproximation φ N' e hz
  obtain ⟨y, hy, he⟩ := hx
  obtain ⟨w, hw, hf⟩ := hz
  refine ⟨⁅y, w⁆, lowerCentralFiltration_lie_le N' d e (LieSubmodule.lie_mem_lie hy hw), ?_⟩
  have h₁ := lie_mem_adicPower (envelopingIdeal N') he hz'
  have h₂ := lie_mem_adicPower (envelopingIdeal N')
    (ι_mem_adicPower_of_mem_filtration N' d hy) hf
  have h := Submodule.add_mem (adicPower R _ (envelopingIdeal N') (d + e + 1))
    (by simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h₁)
    (by simpa only [Nat.add_assoc] using h₂)
  convert h using 1
  simp only [LieHom.map_lie, Ring.lie_def, map_mul, map_sub]
  noncomm_ring

/-- Degree-one linear approximations propagate through every lower-central term. -/
theorem lowerCentral_le_leadingApproximation
    (φ : UniversalEnvelopingAlgebra R L →ₐ[R] UniversalEnvelopingAlgebra R M)
    (N : LieIdeal R L) (N' : LieIdeal R M)
    (h₁ : N.toSubmodule ≤ leadingApproximation φ N' 1) (n : ℕ) :
    (lowerCentralSeriesOfIdeal N n).toSubmodule ≤ leadingApproximation φ N' (n + 1) := by
  induction n with
  | zero => exact h₁
  | succ n ih =>
    rw [lowerCentralSeriesOfIdeal_succ, LieSubmodule.lieIdeal_oper_eq_linear_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, y, rfl⟩
    change ⁅(x : L), (y : L)⁆ ∈ leadingApproximation φ N' (n + 1 + 1)
    have h := lie_mem_leadingApproximation φ N' (h₁ x.property) (ih y.property)
    simpa only [Nat.add_comm 1 (n + 1)] using h

/-- The two starting approximation bounds determine all lower-central degrees. -/
theorem filtration_le_leadingApproximation
    (φ : UniversalEnvelopingAlgebra R L →ₐ[R] UniversalEnvelopingAlgebra R M)
    (N : LieIdeal R L) (N' : LieIdeal R M)
    (h₀ : (⊤ : Submodule R L) ≤ leadingApproximation φ N' 0)
    (h₁ : N.toSubmodule ≤ leadingApproximation φ N' 1) (d : ℕ) :
    (lowerCentralFiltration N d).toSubmodule ≤ leadingApproximation φ N' d := by
  cases d with
  | zero => exact h₀
  | succ d => exact lowerCentral_le_leadingApproximation φ N N' h₁ d

/-- A degree-one approximation sends the actual generated ideal into the target ideal. -/
theorem envelopingIdeal_le_comap_of_leadingApproximation
    (φ : UniversalEnvelopingAlgebra R L →ₐ[R] UniversalEnvelopingAlgebra R M)
    (N : LieIdeal R L) (N' : LieIdeal R M)
    (h₁ : N.toSubmodule ≤ leadingApproximation φ N' 1) :
    envelopingIdeal N ≤ TwoSidedIdeal.comap φ (envelopingIdeal N') := by
  apply TwoSidedIdeal.span_le.mpr
  rintro _ ⟨x, hx, rfl⟩
  have h := map_mem_adicPower_of_leadingApproximation φ N' 1 (h₁ hx)
  change φ (ι R x) ∈ (envelopingIdeal N').asIdeal ^ 1 at h
  simpa only [Submodule.pow_one, TwoSidedIdeal.mem_asIdeal, SetLike.mem_coe,
    TwoSidedIdeal.mem_comap] using h

section Associative

variable {A B : Type*} [Ring A] [Algebra R A] [Ring B] [Algebra R B]

/-- An algebra map carrying one two-sided ideal into another carries all actual powers. -/
theorem map_mem_adicPower (φ : A →ₐ[R] B) (I : TwoSidedIdeal A) (J : TwoSidedIdeal B)
    (hIJ : I ≤ TwoSidedIdeal.comap φ J) (n : ℕ) {x : A}
    (hx : x ∈ adicPower R A I n) : φ x ∈ adicPower R B J n := by
  have h₁ {z : A} (hz : z ∈ adicPower R A I 1) : φ z ∈ adicPower R B J 1 := by
    change z ∈ I.asIdeal ^ 1 at hz
    change φ z ∈ J.asIdeal ^ 1
    have hzI : z ∈ I := by simpa only [Submodule.pow_one, TwoSidedIdeal.mem_asIdeal] using hz
    have hzJ : φ z ∈ J := (TwoSidedIdeal.mem_comap φ).mp (hIJ hzI)
    simpa only [Submodule.pow_one, TwoSidedIdeal.mem_asIdeal] using hzJ
  induction n generalizing x with
  | zero => rw [adicPower_zero]; exact Submodule.mem_top
  | succ n ih =>
    rw [adicPower_mul] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [map_mul, adicPower_mul]
      exact Submodule.mul_mem_mul (ih ha) (h₁ hb)
    · intro a b ha hb
      simpa only [map_add] using Submodule.add_mem _ ha hb

/-- Reciprocal ideal preservation gives equality of all powers under an actual equivalence. -/
theorem map_adicPower_eq (φ : A ≃ₐ[R] B) (I : TwoSidedIdeal A) (J : TwoSidedIdeal B)
    (hIJ : I ≤ TwoSidedIdeal.comap φ J) (hJI : J ≤ TwoSidedIdeal.comap φ.symm I) (n : ℕ) :
    (adicPower R A I n).map φ.toLinearMap = adicPower R B J n := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact map_mem_adicPower φ.toAlgHom I J hIJ n hx
  · intro y hy
    exact Submodule.mem_map.mpr ⟨φ.symm y,
      map_mem_adicPower φ.symm.toAlgHom J I hJI n hy, φ.apply_symm_apply y⟩

end Associative

/-- The first layer and its inverse determine the actual enveloping-ideal powers. -/
theorem map_enveloping_adicPower_eq
    (φ : UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R M)
    (N : LieIdeal R L) (N' : LieIdeal R M)
    (h₁ : N.toSubmodule ≤ leadingApproximation φ.toAlgHom N' 1)
    (h₁' : N'.toSubmodule ≤ leadingApproximation φ.symm.toAlgHom N 1) (d : ℕ) :
    (adicPower R _ (envelopingIdeal N) d).map φ.toLinearMap =
      adicPower R _ (envelopingIdeal N') d :=
  map_adicPower_eq φ (envelopingIdeal N) (envelopingIdeal N')
    (envelopingIdeal_le_comap_of_leadingApproximation φ.toAlgHom N N' h₁)
    (envelopingIdeal_le_comap_of_leadingApproximation φ.symm.toAlgHom N' N h₁') d

/-- The error of a proposed linear lift, as a linear map into the actual UEA. -/
def leadingError
    (φ : UniversalEnvelopingAlgebra R L →ₐ[R] UniversalEnvelopingAlgebra R M)
    (f : L →ₗ[R] M) : L →ₗ[R] UniversalEnvelopingAlgebra R M :=
  φ.toLinearMap.comp (ι R).toLinearMap - (ι R).toLinearMap.comp f

@[simp]
theorem leadingError_apply
    (φ : UniversalEnvelopingAlgebra R L →ₐ[R] UniversalEnvelopingAlgebra R M)
    (f : L →ₗ[R] M) (x : L) : leadingError φ f x = φ (ι R x) - ι R (f x) := rfl

/-- A linear map lifts the actual leading terms in every filtration degree. -/
def IsLeadingLift
    (φ : UniversalEnvelopingAlgebra R L →ₐ[R] UniversalEnvelopingAlgebra R M)
    (N : LieIdeal R L) (N' : LieIdeal R M) (f : L →ₗ[R] M) : Prop :=
  ∀ d x, x ∈ lowerCentralFiltration N d →
    f x ∈ lowerCentralFiltration N' d ∧
      leadingError φ f x ∈ adicPower R _ (envelopingIdeal N') (d + 1)

/-- Choosing witnesses on an adapted basis gives one linear leading lift for all layers. -/
theorem exists_leadingLift_of_adapted {α : Type*} [LinearOrder α]
    (b : Module.Basis α R L) (ω : α → ℕ)
    (φ : UniversalEnvelopingAlgebra R L →ₐ[R] UniversalEnvelopingAlgebra R M)
    (N : LieIdeal R L) (N' : LieIdeal R M) (ha : IsLowerCentralAdapted b ω N)
    (h : ∀ d, (lowerCentralFiltration N d).toSubmodule ≤ leadingApproximation φ N' d) :
    ∃ f : L →ₗ[R] M, IsLeadingLift φ N N' f := by
  classical
  have hi (i : α) : ∃ y ∈ lowerCentralFiltration N' (ω i),
      φ (ι R (b i)) - ι R y ∈ adicPower R _ (envelopingIdeal N') (ω i + 1) :=
    h (ω i) (adapted_basis_mem b ω N ha i)
  choose y hy he using hi
  let f : L →ₗ[R] M := b.constr R y
  have hf (i : α) : f (b i) = y i := b.constr_basis R y i
  refine ⟨f, ?_⟩
  intro d x hx
  have hle : (lowerCentralFiltration N d).toSubmodule ≤
      (lowerCentralFiltration N' d).toSubmodule.comap f ⊓
        (adicPower R _ (envelopingIdeal N') (d + 1)).comap (leadingError φ f) := by
    rw [← ha d]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    constructor
    · change f (b i) ∈ lowerCentralFiltration N' d
      rw [hf]
      exact lowerCentralFiltration_antitone N' hi (hy i)
    · change leadingError φ f (b i) ∈ adicPower R _ (envelopingIdeal N') (d + 1)
      rw [leadingError_apply, hf]
      exact adicPower_antitone (envelopingIdeal N') (Nat.add_le_add_right hi 1) (he i)
  exact hle hx

section Field

variable {k L₁ L₂ : Type*} [Field k]
  [LieRing L₁] [LieAlgebra k L₁] [Module.Finite k L₁]
  [LieRing L₂] [LieAlgebra k L₂]

/-- Reciprocal leading lifts compose to the identity modulo the next Lie-filtration layer. -/
theorem leadingLift_comp_sub_mem
    (φ : UniversalEnvelopingAlgebra k L₁ ≃ₐ[k] UniversalEnvelopingAlgebra k L₂)
    (N : LieIdeal k L₁) (N' : LieIdeal k L₂) [LieRing.IsNilpotent N]
    (hJI : envelopingIdeal N' ≤ TwoSidedIdeal.comap φ.symm (envelopingIdeal N))
    (f : L₁ →ₗ[k] L₂) (g : L₂ →ₗ[k] L₁)
    (hf : IsLeadingLift φ.toAlgHom N N' f) (hg : IsLeadingLift φ.symm.toAlgHom N' N g)
    (d : ℕ) {x : L₁} (hx : x ∈ lowerCentralFiltration N d) :
    g (f x) - x ∈ lowerCentralFiltration N (d + 1) := by
  have ha := map_mem_adicPower φ.symm.toAlgHom (envelopingIdeal N') (envelopingIdeal N)
    hJI (d + 1) (hf d x hx).2
  have hb := (hg d (f x) (hf d x hx).1).2
  have hc := Submodule.neg_mem _ (Submodule.add_mem _ ha hb)
  have hι : ι k (g (f x) - x) ∈ adicPower k _ (envelopingIdeal N) (d + 1) := by
    convert hc using 1
    simp only [leadingError_apply, map_sub, AlgEquiv.coe_toAlgHom,
      AlgEquiv.symm_apply_apply]
    abel
  change g (f x) - x ∈ (lowerCentralSeriesOfIdeal N d).toSubmodule
  rw [← comap_ι_adicPower_succ_of_nilpotent N d]
  exact hι

/-- Reciprocal leading lifts reflect every filtration layer. -/
theorem leadingLift_reflects_filtration
    (φ : UniversalEnvelopingAlgebra k L₁ ≃ₐ[k] UniversalEnvelopingAlgebra k L₂)
    (N : LieIdeal k L₁) (N' : LieIdeal k L₂) [LieRing.IsNilpotent N]
    (hJI : envelopingIdeal N' ≤ TwoSidedIdeal.comap φ.symm (envelopingIdeal N))
    (f : L₁ →ₗ[k] L₂) (g : L₂ →ₗ[k] L₁)
    (hf : IsLeadingLift φ.toAlgHom N N' f) (hg : IsLeadingLift φ.symm.toAlgHom N' N g)
    (d : ℕ) {x : L₁} (hx : f x ∈ lowerCentralFiltration N' d) :
    x ∈ lowerCentralFiltration N d := by
  induction d with
  | zero => exact LieSubmodule.mem_top x
  | succ d ih =>
    have hx₀ := ih (lowerCentralFiltration_antitone N' (Nat.le_succ d) hx)
    have hdiff := leadingLift_comp_sub_mem φ N N' hJI f g hf hg d hx₀
    have hgf := (hg (d + 1) (f x) hx).1
    simpa only [sub_sub_cancel, LieSubmodule.mem_toSubmodule] using
      (lowerCentralFiltration N (d + 1)).sub_mem hgf hdiff

/-- A leading lift with a reciprocal leading lift is injective. -/
theorem leadingLift_injective
    (φ : UniversalEnvelopingAlgebra k L₁ ≃ₐ[k] UniversalEnvelopingAlgebra k L₂)
    (N : LieIdeal k L₁) (N' : LieIdeal k L₂) [LieRing.IsNilpotent N]
    (hJI : envelopingIdeal N' ≤ TwoSidedIdeal.comap φ.symm (envelopingIdeal N))
    (f : L₁ →ₗ[k] L₂) (g : L₂ →ₗ[k] L₁)
    (hf : IsLeadingLift φ.toAlgHom N N' f) (hg : IsLeadingLift φ.symm.toAlgHom N' N g) :
    Function.Injective f := by
  apply LinearMap.ker_eq_bot.mp
  apply le_bot_iff.mp
  intro x hx
  obtain ⟨c, hc⟩ := exists_lowerCentralFiltration_eq_bot N
  have hfx : f x ∈ lowerCentralFiltration N' (c + 1) := by
    rw [LinearMap.mem_ker.mp hx]
    exact Submodule.zero_mem _
  have h := leadingLift_reflects_filtration φ N N' hJI f g hf hg (c + 1) hfx
  simpa only [hc, LieSubmodule.mem_bot, Submodule.mem_bot] using h

variable [Module.Finite k L₂]

omit [Module.Finite k L₁] in
/-- A leading linear lift preserves Lie brackets modulo the next filtration layer.
This is the graded Lie compatibility, stated without constructing an associated graded object. -/
theorem leadingLift_bracket_error
    (φ : UniversalEnvelopingAlgebra k L₁ →ₐ[k] UniversalEnvelopingAlgebra k L₂)
    (N : LieIdeal k L₁) (N' : LieIdeal k L₂) [LieRing.IsNilpotent N']
    (f : L₁ →ₗ[k] L₂) (hf : IsLeadingLift φ N N' f)
    (d e : ℕ) {x z : L₁}
    (hx : x ∈ lowerCentralFiltration N d) (hz : z ∈ lowerCentralFiltration N e) :
    f ⁅x, z⁆ - ⁅f x, f z⁆ ∈ lowerCentralFiltration N' (d + e + 1) := by
  have hx' := hf d x hx
  have hz' := hf e z hz
  have himage := map_mem_adicPower_of_leadingApproximation φ N' e
    (show z ∈ leadingApproximation φ N' e from ⟨f z, hz'.1, hz'.2⟩)
  have h₁ := lie_mem_adicPower (envelopingIdeal N') hx'.2 himage
  have h₂ := lie_mem_adicPower (envelopingIdeal N')
    (ι_mem_adicPower_of_mem_filtration N' d hx'.1) hz'.2
  have hsum := Submodule.add_mem (adicPower k _ (envelopingIdeal N') (d + e + 1))
    (by simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h₁)
    (by simpa only [Nat.add_assoc] using h₂)
  have hbr : φ (ι k ⁅x, z⁆) - ι k ⁅f x, f z⁆ ∈
      adicPower k _ (envelopingIdeal N') (d + e + 1) := by
    convert hsum using 1
    simp only [leadingError_apply, LieHom.map_lie, Ring.lie_def, map_mul, map_sub]
    noncomm_ring
  have hsrc := lowerCentralFiltration_lie_le N d e (LieSubmodule.lie_mem_lie hx hz)
  have hfl := (hf (d + e) ⁅x, z⁆ hsrc).2
  have hι : ι k (f ⁅x, z⁆ - ⁅f x, f z⁆) ∈
      adicPower k _ (envelopingIdeal N') (d + e + 1) := by
    convert Submodule.sub_mem _ hbr hfl using 1
    simp only [leadingError_apply, map_sub]
    abel
  change f ⁅x, z⁆ - ⁅f x, f z⁆ ∈ (lowerCentralSeriesOfIdeal N' (d + e)).toSubmodule
  rw [← comap_ι_adicPower_succ_of_nilpotent N' (d + e)]
  exact hι

/-- Reciprocal leading lifts are bijective in finite dimension. -/
theorem leadingLift_bijective
    (φ : UniversalEnvelopingAlgebra k L₁ ≃ₐ[k] UniversalEnvelopingAlgebra k L₂)
    (N : LieIdeal k L₁) (N' : LieIdeal k L₂)
    [LieRing.IsNilpotent N] [LieRing.IsNilpotent N']
    (hIJ : envelopingIdeal N ≤ TwoSidedIdeal.comap φ (envelopingIdeal N'))
    (hJI : envelopingIdeal N' ≤ TwoSidedIdeal.comap φ.symm (envelopingIdeal N))
    (f : L₁ →ₗ[k] L₂) (g : L₂ →ₗ[k] L₁)
    (hf : IsLeadingLift φ.toAlgHom N N' f) (hg : IsLeadingLift φ.symm.toAlgHom N' N g) :
    Function.Bijective f := by
  have hfi := leadingLift_injective φ N N' hJI f g hf hg
  have hgi := leadingLift_injective φ.symm N' N hIJ g f hg hf
  have hfg : Function.Surjective (f.comp g) :=
    LinearMap.injective_iff_surjective.mp (hfi.comp hgi)
  refine ⟨hfi, fun y => ?_⟩
  obtain ⟨x, hx⟩ := hfg y
  exact ⟨g x, hx⟩

/-- The first two approximation layers and their reciprocals supply a filtered linear equivalence.

These are hypotheses about an actual associative equivalence, not assumptions
that a Lie equivalence or a graded isomorphism already exists.
-/
theorem exists_leadingLinearEquiv
    (φ : UniversalEnvelopingAlgebra k L₁ ≃ₐ[k] UniversalEnvelopingAlgebra k L₂)
    (N : LieIdeal k L₁) (N' : LieIdeal k L₂)
    [LieRing.IsNilpotent N] [LieRing.IsNilpotent N']
    (h₀ : (⊤ : Submodule k L₁) ≤ leadingApproximation φ.toAlgHom N' 0)
    (h₁ : N.toSubmodule ≤ leadingApproximation φ.toAlgHom N' 1)
    (h₀' : (⊤ : Submodule k L₂) ≤ leadingApproximation φ.symm.toAlgHom N 0)
    (h₁' : N'.toSubmodule ≤ leadingApproximation φ.symm.toAlgHom N 1) :
    ∃ e : L₁ ≃ₗ[k] L₂,
      IsLeadingLift φ.toAlgHom N N' e.toLinearMap ∧
      IsLeadingLift φ.symm.toAlgHom N' N e.symm.toLinearMap ∧
      ∀ d, (lowerCentralFiltration N d).toSubmodule.map e.toLinearMap =
        (lowerCentralFiltration N' d).toSubmodule := by
  obtain ⟨n, b, ω, ha⟩ := exists_lowerCentral_adapted N
  obtain ⟨m, c, ν, hc⟩ := exists_lowerCentral_adapted N'
  obtain ⟨f, hf⟩ := exists_leadingLift_of_adapted b ω φ.toAlgHom N N' ha
    (filtration_le_leadingApproximation φ.toAlgHom N N' h₀ h₁)
  obtain ⟨g, hg⟩ := exists_leadingLift_of_adapted c ν φ.symm.toAlgHom N' N hc
    (filtration_le_leadingApproximation φ.symm.toAlgHom N' N h₀' h₁')
  have hIJ := envelopingIdeal_le_comap_of_leadingApproximation φ.toAlgHom N N' h₁
  have hJI := envelopingIdeal_le_comap_of_leadingApproximation φ.symm.toAlgHom N' N h₁'
  let e : L₁ ≃ₗ[k] L₂ := LinearEquiv.ofBijective f
    (leadingLift_bijective φ N N' hIJ hJI f g hf hg)
  have hback (d : ℕ) {y : L₂} (hy : y ∈ lowerCentralFiltration N' d) :
      e.symm y ∈ lowerCentralFiltration N d := by
    apply leadingLift_reflects_filtration φ N N' hJI f g hf hg d
    change e (e.symm y) ∈ lowerCentralFiltration N' d
    simpa only [e.apply_symm_apply] using hy
  refine ⟨e, hf, ?_, ?_⟩
  · intro d y hy
    refine ⟨hback d hy, ?_⟩
    have herr := (hf d (e.symm y) (hback d hy)).2
    change φ (ι k (e.symm y)) - ι k (e (e.symm y)) ∈ _ at herr
    rw [e.apply_symm_apply] at herr
    have hmap := map_mem_adicPower φ.symm.toAlgHom (envelopingIdeal N') (envelopingIdeal N)
      hJI (d + 1) herr
    change φ.symm (ι k y) - ι k (e.symm y) ∈ adicPower k _ (envelopingIdeal N) (d + 1)
    simpa only [leadingError_apply, map_sub, AlgEquiv.coe_toAlgHom,
      AlgEquiv.symm_apply_apply, neg_sub] using Submodule.neg_mem _ hmap
  · intro d
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (hf d x hx).1
    · intro y hy
      exact Submodule.mem_map.mpr ⟨e.symm y, hback d hy, e.apply_symm_apply y⟩

omit [Module.Finite k L₁] [Module.Finite k L₂] in
/-- A filtered linear equivalence transports an adapted basis with unchanged weights. -/
theorem adapted_basis_map {α : Type*} [LinearOrder α]
    (b : Module.Basis α k L₁) (ω : α → ℕ) (e : L₁ ≃ₗ[k] L₂)
    (N : LieIdeal k L₁) (N' : LieIdeal k L₂) (ha : IsLowerCentralAdapted b ω N)
    (hmap : ∀ d, (lowerCentralFiltration N d).toSubmodule.map e.toLinearMap =
      (lowerCentralFiltration N' d).toSubmodule) :
    IsLowerCentralAdapted (b.map e) ω N' := by
  intro d
  change Submodule.span k ((fun i => e (b i)) '' {i | d ≤ ω i}) = _
  rw [← Set.image_image e b {i | d ≤ ω i}]
  change Submodule.span k (e.toLinearMap '' (b '' {i | d ≤ ω i})) = _
  rw [← Submodule.map_span, ha d, hmap d]

/-- The actual equivalence has reciprocal leading congruences on matched adapted bases.

The two bases have one common index type and one common weight function, exactly
the finite data needed to construct the associative Rees isomorphism.
-/
theorem exists_matched_adapted_leading_bases
    (φ : UniversalEnvelopingAlgebra k L₁ ≃ₐ[k] UniversalEnvelopingAlgebra k L₂)
    (N : LieIdeal k L₁) (N' : LieIdeal k L₂)
    [LieRing.IsNilpotent N] [LieRing.IsNilpotent N']
    (h₀ : (⊤ : Submodule k L₁) ≤ leadingApproximation φ.toAlgHom N' 0)
    (h₁ : N.toSubmodule ≤ leadingApproximation φ.toAlgHom N' 1)
    (h₀' : (⊤ : Submodule k L₂) ≤ leadingApproximation φ.symm.toAlgHom N 0)
    (h₁' : N'.toSubmodule ≤ leadingApproximation φ.symm.toAlgHom N 1) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k L₁) (c : Module.Basis (Fin n) k L₂)
      (ω : Fin n → ℕ) (e : L₁ ≃ₗ[k] L₂),
      c = b.map e ∧ IsLowerCentralAdapted b ω N ∧ IsLowerCentralAdapted c ω N' ∧
      IsLeadingLift φ.toAlgHom N N' e.toLinearMap ∧
      IsLeadingLift φ.symm.toAlgHom N' N e.symm.toLinearMap ∧
      (∀ i, φ (ι k (b i)) - ι k (c i) ∈ weightedLower c ω (ω i + 1)) ∧
      (∀ i, φ.symm (ι k (c i)) - ι k (b i) ∈ weightedLower b ω (ω i + 1)) := by
  obtain ⟨e, hf, hg, hmap⟩ := exists_leadingLinearEquiv φ N N' h₀ h₁ h₀' h₁'
  obtain ⟨n, b, ω, hb⟩ := exists_lowerCentral_adapted N
  let c := b.map e
  have hc : IsLowerCentralAdapted c ω N' := adapted_basis_map b ω e N N' hb hmap
  refine ⟨n, b, c, ω, e, rfl, hb, hc, hf, hg, ?_, ?_⟩
  · intro i
    rw [← adicPower_eq_weightedLower c ω N' hc]
    exact (hf (ω i) (b i) (adapted_basis_mem b ω N hb i)).2
  · intro i
    rw [← adicPower_eq_weightedLower b ω N hb]
    have h := (hg (ω i) (c i) (adapted_basis_mem c ω N' hc i)).2
    change φ.symm (ι k (c i)) - ι k (e.symm (e (b i))) ∈ _ at h
    simpa only [e.symm_apply_apply] using h

end Field

end EnvelopingIsomorphism.Identification
