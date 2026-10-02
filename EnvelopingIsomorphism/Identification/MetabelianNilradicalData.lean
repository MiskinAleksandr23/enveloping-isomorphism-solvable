import EnvelopingIsomorphism.Identification.NilradicalWeights
import EnvelopingIsomorphism.Identification.HQ2

/-! The actual metabelian nilradical quotient supplies the eigenweight inputs of HQ2. -/

noncomputable section

namespace EnvelopingIsomorphism.Identification

open EnvelopingIsomorphism.Lie

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The natural quotient map between two nested Lie-ideal quotients. -/
def quotientBetweenIdeals (I J : LieIdeal R L) (hIJ : I ≤ J) :
    (L ⧸ I) →ₗ⁅R⁆ L ⧸ J where
  toLinearMap := I.toSubmodule.liftQ (quotientLieHom J).toLinearMap (by
    intro x hx
    change quotientLieHom J x = 0
    exact LieSubmodule.Quotient.mk_eq_zero'.mpr (hIJ hx))
  map_lie' := by
    intro x y
    induction x, y using Quotient.inductionOn₂' with
    | _ x y => exact (quotientLieHom J).map_lie x y

@[simp] theorem quotientBetweenIdeals_mk (I J : LieIdeal R L) (hIJ : I ≤ J) (x : L) :
    quotientBetweenIdeals I J hIJ (quotientLieHom I x) = quotientLieHom J x := rfl

theorem quotientBetweenIdeals_surjective (I J : LieIdeal R L) (hIJ : I ≤ J) :
    Function.Surjective (quotientBetweenIdeals I J hIJ) := by
  intro y
  obtain ⟨x, rfl⟩ := quotientLieHom_surjective J y
  exact ⟨quotientLieHom I x, rfl⟩

theorem quotientBetweenIdeals_ker (I J : LieIdeal R L) (hIJ : I ≤ J) :
    (quotientBetweenIdeals I J hIJ).ker = J.map (quotientLieHom I) := by
  ext y
  induction y using Quotient.inductionOn' with
  | _ x =>
    constructor
    · intro hx
      have hxJ : x ∈ J := LieSubmodule.Quotient.mk_eq_zero'.mp (LieHom.mem_ker.mp hx)
      exact LieIdeal.mem_map hxJ
    · intro hx
      obtain ⟨z, hz⟩ := LieIdeal.mem_map_of_surjective (quotientLieHom_surjective I) hx
      apply LieHom.mem_ker.mpr
      rw [← hz, quotientBetweenIdeals_mk]
      exact LieSubmodule.Quotient.mk_eq_zero'.mpr z.property

/-- The third isomorphism theorem, preserving the native Lie brackets. -/
def quotientByImageEquiv (I J : LieIdeal R L) (hIJ : I ≤ J) :
    ((L ⧸ I) ⧸ J.map (quotientLieHom I)) ≃ₗ⁅R⁆ L ⧸ J :=
  let f := quotientBetweenIdeals I J hIJ
  let hk : LinearMap.ker f.toLinearMap = (J.map (quotientLieHom I)).toSubmodule := by
    rw [← LieHom.ker_toSubmodule, quotientBetweenIdeals_ker]
  let e := (Submodule.quotEquivOfEq _ _ hk.symm).trans
    (f.toLinearMap.quotKerEquivOfSurjective (quotientBetweenIdeals_surjective I J hIJ))
  { e with
    map_lie' := by
      intro x y
      induction x, y using Quotient.inductionOn₂' with
      | _ x y => exact f.map_lie x y }

@[simp] theorem quotientByImageEquiv_mk_mk (I J : LieIdeal R L) (hIJ : I ≤ J) (x : L) :
    quotientByImageEquiv I J hIJ
      (quotientLieHom (J.map (quotientLieHom I)) (quotientLieHom I x)) = quotientLieHom J x := rfl

/-- Quotient by the internal commutators of the chosen ideal. -/
abbrev idealDerivedQuotient (N : LieIdeal R L) := L ⧸ ⁅N, N⁆

/-- The actual ideal image in this quotient. -/
def idealAbelianImage (N : LieIdeal R L) : LieIdeal R (idealDerivedQuotient N) :=
  N.map (quotientLieHom ⁅N, N⁆)

instance idealAbelianImage_isLieAbelian (N : LieIdeal R L) : IsLieAbelian (idealAbelianImage N) := by
  constructor
  intro x y
  apply Subtype.ext
  obtain ⟨u, hu⟩ := LieIdeal.mem_map_of_surjective (quotientLieHom_surjective ⁅N, N⁆) x.property
  obtain ⟨v, hv⟩ := LieIdeal.mem_map_of_surjective (quotientLieHom_surjective ⁅N, N⁆) y.property
  change ⁅(x : idealDerivedQuotient N), (y : idealDerivedQuotient N)⁆ = 0
  rw [← hu, ← hv, ← LieHom.map_lie]
  exact LieSubmodule.Quotient.mk_eq_zero'.mpr (LieSubmodule.lie_mem_lie u.property v.property)

/-- The quotient of the actual abelian ideal extension is the original `L/N`. -/
def idealDerivedQuotientEquiv (N : LieIdeal R L) :
    ((idealDerivedQuotient N) ⧸ idealAbelianImage N) ≃ₗ⁅R⁆ L ⧸ N :=
  quotientByImageEquiv ⁅N, N⁆ N (LieSubmodule.lie_le_left N N)

@[simp] theorem idealDerivedQuotientEquiv_mk_mk (N : LieIdeal R L) (x : L) :
    idealDerivedQuotientEquiv N
      (quotientLieHom (idealAbelianImage N) (quotientLieHom ⁅N, N⁆ x)) = quotientLieHom N x := rfl

instance idealDerivedQuotient_quotient_isLieAbelian (N : LieIdeal R L) [IsLieAbelian (L ⧸ N)] :
    IsLieAbelian ((idealDerivedQuotient N) ⧸ idealAbelianImage N) := by
  constructor
  intro x y
  apply (idealDerivedQuotientEquiv N).injective
  rw [LieHom.map_lie, trivial_lie_zero, map_zero]

/-- The intrinsic commutator submodule of `N` is the pullback of its ambient commutator ideal. -/
theorem mem_ideal_commutator_iff (N : LieIdeal R L) (x : N) :
    (x : L) ∈ ⁅N, N⁆ ↔ x ∈ ⁅N, (⊤ : LieSubmodule R L N)⁆ := by
  have hmap : (⁅N, (⊤ : LieSubmodule R L N)⁆).map (LieSubmodule.incl N) = ⁅N, N⁆ := by
    rw [LieSubmodule.map_bracket_eq, LieSubmodule.map_incl_top]
  rw [← hmap]
  constructor
  · intro hx
    rw [LieSubmodule.mem_map] at hx
    obtain ⟨y, hy, heq⟩ := hx
    have hxy : y = x := Subtype.ext heq
    exact hxy ▸ hy
  · exact fun hx ↦ LieSubmodule.mem_map_of_mem hx

/-- Restriction of the ambient quotient map to its actual ideal image. -/
def idealToAbelianImage (N : LieIdeal R L) : N →ₗ[R] idealAbelianImage N :=
  (EnvelopingIsomorphism.Lie.idealMapHom (quotientLieHom ⁅N, N⁆) N).toLinearMap

@[simp] theorem idealToAbelianImage_coe (N : LieIdeal R L) (x : N) :
    (idealToAbelianImage N x : idealDerivedQuotient N) = quotientLieHom ⁅N, N⁆ (x : L) := rfl

theorem idealToAbelianImage_surjective (N : LieIdeal R L) :
    Function.Surjective (idealToAbelianImage N) :=
  EnvelopingIsomorphism.Lie.idealMapHom_surjective _ (quotientLieHom_surjective _) N

theorem idealToAbelianImage_ker (N : LieIdeal R L) :
    LinearMap.ker (idealToAbelianImage N) = (⁅N, (⊤ : LieSubmodule R L N)⁆).toSubmodule := by
  ext x
  rw [LinearMap.mem_ker]
  change idealToAbelianImage N x = 0 ↔ x ∈ ⁅N, (⊤ : LieSubmodule R L N)⁆
  rw [← mem_ideal_commutator_iff]
  constructor
  · intro hx
    exact LieSubmodule.Quotient.mk_eq_zero'.mp (congrArg Subtype.val hx)
  · intro hx
    apply Subtype.ext
    exact LieSubmodule.Quotient.mk_eq_zero'.mpr hx

/-- The module used by B1 is the actual abelian ideal in the metabelian quotient. -/
def idealAbelianizationEquivImage (N : LieIdeal R L) :
    IdealAbelianization N ≃ₗ[R] idealAbelianImage N :=
  (Submodule.quotEquivOfEq _ _ (idealToAbelianImage_ker N).symm).trans
    ((idealToAbelianImage N).quotKerEquivOfSurjective (idealToAbelianImage_surjective N))

@[simp] theorem idealAbelianizationEquivImage_mk (N : LieIdeal R L) (x : N) :
    idealAbelianizationEquivImage N
      (LieSubmodule.Quotient.mk (N := ⁅N, (⊤ : LieSubmodule R L N)⁆) x) =
        idealToAbelianImage N x := rfl

/-- The comparison preserves the actual adjoint actions of ambient Lie vectors. -/
theorem idealAbelianizationEquivImage_lie (N : LieIdeal R L) (x : L) (v : IdealAbelianization N) :
    (idealAbelianizationEquivImage N ⁅x, v⁆ : idealDerivedQuotient N) =
      ⁅quotientLieHom ⁅N, N⁆ x, (idealAbelianizationEquivImage N v : idealDerivedQuotient N)⁆ := by
  induction v using Quotient.inductionOn' with
  | _ v =>
    change quotientLieHom ⁅N, N⁆ ⁅x, (v : L)⁆ =
      ⁅quotientLieHom ⁅N, N⁆ x, quotientLieHom ⁅N, N⁆ (v : L)⁆
    exact (quotientLieHom ⁅N, N⁆).map_lie x (v : L)

/-- Transport a quotient weight through the actual third-isomorphism equivalence. -/
def idealImageWeight (N : LieIdeal R L) (ψ : Module.Dual R (L ⧸ N)) :
    Module.Dual R ((idealDerivedQuotient N) ⧸ idealAbelianImage N) :=
  ψ.comp (idealDerivedQuotientEquiv N).toLinearEquiv.toLinearMap

@[simp] theorem idealImageWeight_mk_mk (N : LieIdeal R L) (ψ : Module.Dual R (L ⧸ N)) (x : L) :
    idealImageWeight N ψ
      (quotientLieHom (idealAbelianImage N) (quotientLieHom ⁅N, N⁆ x)) = ψ (quotientLieHom N x) := by
  change ψ (idealDerivedQuotientEquiv N
    (quotientLieHom (idealAbelianImage N) (quotientLieHom ⁅N, N⁆ x))) = _
  rw [idealDerivedQuotientEquiv_mk_mk]

theorem idealAbelianizationEquivImage_eigenvector (N : LieIdeal R L)
    (ψ : Module.Dual R (L ⧸ N)) (v : IdealAbelianization N)
    (hv : ∀ q : L ⧸ N, ⁅q, v⁆ = ψ q • v) (y : idealDerivedQuotient N) :
    ⁅y, (idealAbelianizationEquivImage N v : idealDerivedQuotient N)⁆ =
      idealImageWeight N ψ (quotientLieHom (idealAbelianImage N) y) •
        (idealAbelianizationEquivImage N v : idealDerivedQuotient N) := by
  induction y using Quotient.inductionOn' with
  | _ x =>
    change ⁅quotientLieHom ⁅N, N⁆ x, (idealAbelianizationEquivImage N v : idealDerivedQuotient N)⁆ =
      idealImageWeight N ψ (quotientLieHom (idealAbelianImage N) (quotientLieHom ⁅N, N⁆ x)) •
        (idealAbelianizationEquivImage N v : idealDerivedQuotient N)
    rw [← idealAbelianizationEquivImage_lie, idealImageWeight_mk_mk]
    have hx := hv (quotientLieHom N x)
    rw [quotientAbelianizationAction_apply_mk] at hx
    rw [hx, map_smul]
    rfl

section Nilradical

variable {k M : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [LieRing M] [LieAlgebra k M] [Module.Finite k M] [LieAlgebra.IsSolvable M]

local notation "N" => nilradical k M
local notation "g" => idealDerivedQuotient N
local notation "H" => idealAbelianImage N

/-- B1 supplies genuine separating eigenweights of the actual quotient extension used in C1. -/
theorem exists_full_metabelian_nilradical_weights :
    ∃ n : ℕ, ∃ ψ : Fin n → Module.Dual k (g ⧸ H), ∃ w : Fin n → H,
      (∀ j, w j ≠ 0) ∧
      (∀ j x, ⁅x, (w j : g)⁆ = ψ j (quotientLieHom H x) • (w j : g)) ∧
      Function.Injective (fun q : g ⧸ H ↦ fun j ↦ ψ j q) := by
  obtain ⟨n, ψ, w, hw, heigen, hψ⟩ := exists_full_nilradical_weights (k := k) (L := M)
  refine ⟨n, fun j ↦ idealImageWeight N (ψ j),
    fun j ↦ idealAbelianizationEquivImage N (w j), ?_, ?_, ?_⟩
  · intro j hj
    apply hw j
    apply (idealAbelianizationEquivImage N).injective
    simpa using hj
  · intro j x
    exact idealAbelianizationEquivImage_eigenvector N (ψ j) (w j) (heigen j) x
  · intro q r hqr
    apply (idealDerivedQuotientEquiv N).injective
    apply hψ
    funext j
    exact congrFun hqr j

/-- HQ2 applies to the actual nilradical metabelian quotient with no supplied weight data. -/
theorem hq2_nilradical_derivedQuotient (a : UniversalEnvelopingAlgebra k g) :
    (a ∈ LN k (UniversalEnvelopingAlgebra k g) ↔ a ∈ idealPolynomialPart H) ∧
      (a ∈ LF k (UniversalEnvelopingAlgebra k g) ↔
        ∃ x : g, ∃ p, p ∈ idealPolynomialPart H ∧ a = UniversalEnvelopingAlgebra.ι k x + p) := by
  obtain ⟨n, ψ, w, hw, heigen, hψ⟩ := exists_full_metabelian_nilradical_weights (k := k) (M := M)
  exact hq2_of_quotientEigenweights H ψ hψ w hw heigen a

theorem LN_eq_polynomialPart_nilradical_derivedQuotient :
    LN k (UniversalEnvelopingAlgebra k g) = (idealPolynomialPart H : Set _) := by
  ext a
  exact (hq2_nilradical_derivedQuotient a).1

attribute [local instance 100] LieRing.ofAssociativeRing

/-- This is the commutativity fact required for the reverse inclusion in C1. -/
theorem lie_eq_zero_of_LN_nilradical_derivedQuotient
    (a b : UniversalEnvelopingAlgebra k g) (ha : a ∈ LN k (UniversalEnvelopingAlgebra k g))
    (hb : b ∈ LN k (UniversalEnvelopingAlgebra k g)) : ⁅a, b⁆ = 0 :=
  lie_eq_zero_of_mem_idealPolynomialPart H ((hq2_nilradical_derivedQuotient a).1.mp ha)
    ((hq2_nilradical_derivedQuotient b).1.mp hb)

end Nilradical

end EnvelopingIsomorphism.Identification
