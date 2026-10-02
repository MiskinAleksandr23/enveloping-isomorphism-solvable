import EnvelopingIsomorphism.Identification.LocallyFinite
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-! A positive leading operator of a locally finite operator is locally nilpotent.
The split filtration is represented in basis coordinates, so neither finite
dimensional filtration pieces nor a categorical associated graded is needed. -/

noncomputable section

namespace EnvelopingIsomorphism.Identification

universe u v w
variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable {ι : Type w} (b : Module.Basis ι R V) (ω : ι → ℕ)

/-- Coordinate submodule supported on a prescribed subset of basis indices. -/
def basisSupport (s : Set ι) : Submodule R V := Submodule.span R (b '' s)

theorem mem_basisSupport (s : Set ι) (x : V) :
    x ∈ basisSupport b s ↔ ∀ i ∈ (b.repr x).support, i ∈ s :=
  b.mem_span_image

theorem basisSupport_mono {s t : Set ι} (hst : s ⊆ t) :
    basisSupport b s ≤ basisSupport b t := Submodule.span_mono (Set.image_mono hst)

theorem basis_mem_basisSupport {s : Set ι} {i : ι} (hi : i ∈ s) :
    b i ∈ basisSupport b s := Submodule.subset_span ⟨i, hi, rfl⟩

/-- The increasing filtration obtained from weights of basis vectors. -/
def basisUpper (n : ℕ) : Submodule R V := basisSupport b {i | ω i ≤ n}

/-- Strictly lower weight terms, also at weight zero. -/
def basisStrict (n : ℕ) : Submodule R V := basisSupport b {i | ω i < n}

/-- Homogeneous vectors of one weight. -/
def basisHomogeneous (n : ℕ) : Submodule R V := basisSupport b {i | ω i = n}

theorem basisUpper_mono : Monotone (basisUpper b ω) :=
  fun _ _ h => basisSupport_mono b fun _ hi => hi.trans h

theorem exists_mem_basisUpper (x : V) : ∃ n, x ∈ basisUpper b ω n := by
  classical
  refine ⟨(b.repr x).support.sup ω, ?_⟩
  exact (mem_basisSupport b _ x).mpr fun _ hi => Finset.le_sup (f := ω) hi

theorem fg_le_some_basisUpper {P : Submodule R V} (hP : P.FG) :
    ∃ n, P ≤ basisUpper b ω n := by
  classical
  obtain ⟨s, hs⟩ := hP
  choose bound hbound using exists_mem_basisUpper b ω
  refine ⟨s.sup bound, ?_⟩
  rw [← hs]
  apply Submodule.span_le.mpr
  intro x hx
  exact basisUpper_mono b ω (Finset.le_sup hx) (hbound x)

theorem locallyFinite_orbit_bounded (D : Module.End R V) (hD : IsLocallyFinite D)
    (x : V) : ∃ n, ∀ m : ℕ, (D ^ m) x ∈ basisUpper b ω n := by
  obtain ⟨n, hn⟩ := fg_le_some_basisUpper b ω (hD x)
  exact ⟨n, fun m => hn (Submodule.subset_span ⟨m, rfl⟩)⟩

theorem eq_zero_of_homogeneous_and_strict {n : ℕ} {x : V}
    (hh : x ∈ basisHomogeneous b ω n) (hs : x ∈ basisStrict b ω n) : x = 0 := by
  apply b.repr.injective
  rw [map_zero]
  ext i
  by_contra hi
  have hm : i ∈ (b.repr x).support := Finsupp.mem_support_iff.mpr hi
  have heq := (mem_basisSupport b _ x).mp hh i hm
  have hlt := (mem_basisSupport b _ x).mp hs i hm
  exact (ne_of_lt hlt) heq

theorem mapsTo_basisSupport (D : Module.End R V) {s t : Set ι}
    (hD : ∀ i ∈ s, D (b i) ∈ basisSupport b t) :
    ∀ x ∈ basisSupport b s, D x ∈ basisSupport b t := by
  change basisSupport b s ≤ (basisSupport b t).comap D
  apply Submodule.span_le.mpr
  rintro _ ⟨i, hi, rfl⟩
  exact hD i hi

theorem shifts_strict_of_shifts_basis (D : Module.End R V) (r : ℕ)
    (hD : ∀ i, D (b i) ∈ basisUpper b ω (ω i + r)) (n : ℕ) :
    ∀ x ∈ basisStrict b ω n, D x ∈ basisStrict b ω (n + r) := by
  apply mapsTo_basisSupport b D
  intro i hi
  apply basisSupport_mono b _ (hD i)
  intro j hj
  dsimp only [Set.mem_setOf_eq] at hi hj ⊢
  omega

theorem shifts_homogeneous_of_shifts_basis (E : Module.End R V) (r : ℕ)
    (hE : ∀ i, E (b i) ∈ basisHomogeneous b ω (ω i + r)) (n : ℕ) :
    ∀ x ∈ basisHomogeneous b ω n, E x ∈ basisHomogeneous b ω (n + r) := by
  apply mapsTo_basisSupport b E
  intro i hi
  change ω i = n at hi
  simpa only [basisHomogeneous, hi] using hE i

theorem remainder_strict_of_basis (D E : Module.End R V) (r : ℕ)
    (hDE : ∀ i, D (b i) - E (b i) ∈ basisStrict b ω (ω i + r)) (n : ℕ) :
    ∀ x ∈ basisHomogeneous b ω n, D x - E x ∈ basisStrict b ω (n + r) := by
  apply mapsTo_basisSupport b (D - E)
  intro i hi
  change ω i = n at hi
  simpa only [LinearMap.sub_apply, basisStrict, hi] using hDE i

theorem leading_pow_homogeneous (E : Module.End R V) (r : ℕ)
    (hE : ∀ i, E (b i) ∈ basisHomogeneous b ω (ω i + r))
    {x : V} {d : ℕ} (hx : x ∈ basisHomogeneous b ω d) (n : ℕ) :
    (E ^ n) x ∈ basisHomogeneous b ω (d + n * r) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    simpa only [pow_succ', Module.End.mul_apply, Nat.succ_mul, Nat.add_assoc] using
      shifts_homogeneous_of_shifts_basis b ω E r hE (d + n * r) _ ih

/-- The iterates of the two operators agree modulo strictly lower weight. -/
theorem leading_pow_remainder (D E : Module.End R V) (r : ℕ)
    (hD : ∀ i, D (b i) ∈ basisUpper b ω (ω i + r))
    (hE : ∀ i, E (b i) ∈ basisHomogeneous b ω (ω i + r))
    (hDE : ∀ i, D (b i) - E (b i) ∈ basisStrict b ω (ω i + r))
    {x : V} {d : ℕ} (hx : x ∈ basisHomogeneous b ω d) (n : ℕ) :
    (D ^ n) x - (E ^ n) x ∈ basisStrict b ω (d + n * r) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h₁ := shifts_strict_of_shifts_basis b ω D r hD (d + n * r) _ ih
    have h₂ := remainder_strict_of_basis b ω D E r hDE (d + n * r) _
      (leading_pow_homogeneous b ω E r hE hx n)
    have h := (basisStrict b ω (d + n * r + r)).add_mem h₁ h₂
    simpa only [map_sub, sub_add_sub_cancel, pow_succ', Module.End.mul_apply,
      Nat.succ_mul, Nat.add_assoc] using h

/-- Pointwise nilpotence is a linear subspace, without a uniform exponent. -/
def nilpotentVectors (D : Module.End R V) : Submodule R V where
  carrier := {x | ∃ n : ℕ, (D ^ n) x = 0}
  zero_mem' := ⟨0, rfl⟩
  add_mem' := by
    rintro x y ⟨n, hn⟩ ⟨m, hm⟩
    exact ⟨n + m, by rw [map_add,
      pow_apply_eq_zero_of_le D hn (Nat.le_add_right n m),
      pow_apply_eq_zero_of_le D hm (Nat.le_add_left m n), add_zero]⟩
  smul_mem' := by
    rintro a x ⟨n, hn⟩
    exact ⟨n, by rw [map_smul, hn, smul_zero]⟩

theorem locallyNilpotent_of_basis (D : Module.End R V)
    (hD : ∀ i, ∃ n : ℕ, (D ^ n) (b i) = 0) : IsLocallyNilpotent D := by
  have hspan : Submodule.span R (Set.range b) ≤ nilpotentVectors D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hD i
  rw [b.span_eq] at hspan
  exact fun x => hspan (Submodule.mem_top : x ∈ (⊤ : Submodule R V))

/-- A homogeneous leading operator of positive degree is locally nilpotent
whenever the original operator is locally finite. No filtration piece is
assumed finite dimensional, and zero weights are allowed. -/
theorem locallyNilpotent_leading_of_locallyFinite (D E : Module.End R V)
    (r : ℕ) (hr : 0 < r) (hLF : IsLocallyFinite D)
    (hD : ∀ i, D (b i) ∈ basisUpper b ω (ω i + r))
    (hE : ∀ i, E (b i) ∈ basisHomogeneous b ω (ω i + r))
    (hDE : ∀ i, D (b i) - E (b i) ∈ basisStrict b ω (ω i + r)) :
    IsLocallyNilpotent E := by
  apply locallyNilpotent_of_basis b E
  intro i
  obtain ⟨B, hB⟩ := locallyFinite_orbit_bounded b ω D hLF (b i)
  let n := B + 1
  have hn : B < ω i + n * r := by
    have hmul : n ≤ n * r := by simpa using Nat.mul_le_mul_left n hr
    dsimp [n] at *
    omega
  have hi : b i ∈ basisHomogeneous b ω (ω i) := basis_mem_basisSupport b rfl
  have htop := leading_pow_homogeneous b ω E r hE hi n
  have hrem := leading_pow_remainder b ω D E r hD hE hDE hi n
  have hlow : (D ^ n) (b i) ∈ basisStrict b ω (ω i + n * r) := by
    apply basisSupport_mono b _ (hB n)
    intro j hj
    exact lt_of_le_of_lt hj hn
  have hlowE : (E ^ n) (b i) ∈ basisStrict b ω (ω i + n * r) := by
    simpa only [sub_sub_cancel] using (basisStrict b ω (ω i + n * r)).sub_mem hlow hrem
  exact ⟨n, eq_zero_of_homogeneous_and_strict b ω htop hlowE⟩

/-- The actual homogeneous leading operator: retain precisely the output
coordinates of weight `ω i + r` on each input basis vector `b i`. -/
def leadingOperator (D : Module.End R V) (r : ℕ) : Module.End R V :=
  b.constr R (fun i => b.repr.symm ((b.repr (D (b i))).filter (fun j => ω j = ω i + r)))

@[simp] theorem leadingOperator_basis (D : Module.End R V) (r : ℕ) (i : ι) :
    leadingOperator b ω D r (b i) =
      b.repr.symm ((b.repr (D (b i))).filter (fun j => ω j = ω i + r)) := by
  simp [leadingOperator]

@[simp] theorem repr_leadingOperator_basis (D : Module.End R V) (r : ℕ) (i : ι) :
    b.repr (leadingOperator b ω D r (b i)) =
      (b.repr (D (b i))).filter (fun j => ω j = ω i + r) := by
  rw [leadingOperator_basis, LinearEquiv.apply_symm_apply]

theorem leadingOperator_basis_homogeneous (D : Module.End R V) (r : ℕ) (i : ι) :
    leadingOperator b ω D r (b i) ∈ basisHomogeneous b ω (ω i + r) := by
  apply (mem_basisSupport b _ _).mpr
  intro j hj
  rw [repr_leadingOperator_basis, Finsupp.support_filter] at hj
  exact (Finset.mem_filter.mp hj).2

theorem leadingOperator_basis_remainder (D : Module.End R V) (r : ℕ)
    (hD : ∀ i, D (b i) ∈ basisUpper b ω (ω i + r)) (i : ι) :
    D (b i) - leadingOperator b ω D r (b i) ∈ basisStrict b ω (ω i + r) := by
  apply (mem_basisSupport b _ _).mpr
  intro j hj
  have hcoeff := Finsupp.mem_support_iff.mp hj
  rw [map_sub, Finsupp.sub_apply, repr_leadingOperator_basis, Finsupp.filter_apply] at hcoeff
  split_ifs at hcoeff with heq
  · exact (hcoeff (sub_self _)).elim
  · have hne : b.repr (D (b i)) j ≠ 0 := by simpa using hcoeff
    have hle := (mem_basisSupport b _ _).mp (hD i) j (Finsupp.mem_support_iff.mpr hne)
    exact lt_of_le_of_ne hle heq

/-- Block B2 in split filtration coordinates: the canonically extracted
positive-degree leading operator of a locally finite operator is locally nilpotent. -/
theorem leadingOperator_isLocallyNilpotent (D : Module.End R V) (r : ℕ)
    (hr : 0 < r) (hLF : IsLocallyFinite D)
    (hD : ∀ i, D (b i) ∈ basisUpper b ω (ω i + r)) :
    IsLocallyNilpotent (leadingOperator b ω D r) :=
  locallyNilpotent_leading_of_locallyFinite b ω D (leadingOperator b ω D r) r hr hLF hD
    (leadingOperator_basis_homogeneous b ω D r)
    (leadingOperator_basis_remainder b ω D r hD)

/-- Preservation of finite weighted pieces proves local finiteness. This is
the converse estimate used for the easy LF inclusion in HQ2. -/
theorem locallyFinite_of_preserves_finite_basisUpper [IsNoetherianRing R]
    (D : Module.End R V) (hfinite : ∀ n, {i | ω i ≤ n}.Finite)
    (hD : ∀ i, D (b i) ∈ basisUpper b ω (ω i)) : IsLocallyFinite D := by
  have hstable (n : ℕ) : ∀ x ∈ basisUpper b ω n, D x ∈ basisUpper b ω n := by
    apply mapsTo_basisSupport b D
    intro i hi
    exact basisUpper_mono b ω hi (hD i)
  intro x
  obtain ⟨n, hn⟩ := exists_mem_basisUpper b ω x
  have hpow (m : ℕ) : (D ^ m) x ∈ basisUpper b ω n := by
    induction m with
    | zero => exact hn
    | succ m ih =>
      simpa only [pow_succ', Module.End.mul_apply] using hstable n _ ih
  have hfg : (basisUpper b ω n).FG := Submodule.fg_span ((hfinite n).image b)
  apply hfg.of_le
  apply Submodule.span_le.mpr
  rintro _ ⟨m, rfl⟩
  exact hpow m

end EnvelopingIsomorphism.Identification
