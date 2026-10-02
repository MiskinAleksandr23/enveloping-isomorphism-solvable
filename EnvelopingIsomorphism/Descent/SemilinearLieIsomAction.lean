import EnvelopingIsomorphism.Descent.SemilinearLieAction
import EnvelopingIsomorphism.Descent.FixedPointDescent

/-! The marked-isomorphism cocycle and its finite unipotent correction. -/

namespace EnvelopingIsomorphism.Descent

universe u v w z
variable {k : Type u} [Field k]
variable {L : Type v} [LieRing L] [LieAlgebra k L]
variable {M : Type w} [LieRing M] [LieAlgebra k M]

local instance (κ : k ≃+* k) : RingHomInvPair κ.toRingHom κ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv κ

/-- Reindex a semilinear equivalence along an equality of its scalar automorphisms.
Its forward and inverse functions are unchanged. -/
def sameScalarEquiv {κ κ' : k ≃+* k} (h : κ = κ')
    (e : M ≃ₛₗ[κ'.toRingHom] M) : M ≃ₛₗ[κ.toRingHom] M where
  toFun := e
  invFun := e.symm
  left_inv := e.symm_apply_apply
  right_inv := e.apply_symm_apply
  map_add' := map_add e
  map_smul' a x := by
    change e (a • x) = κ a • e x
    rw [h]
    exact e.map_smulₛₗ a x

/-- Transport a Lie isomorphism by compatible semilinear changes on its two sides. -/
def semilinearConjugateIsom {κ : k ≃+* k}
    (eL : L ≃ₛₗ[κ.toRingHom] L) (eM : M ≃ₛₗ[κ.toRingHom] M)
    (hL : ∀ x y, eL ⁅x, y⁆ = ⁅eL x, eL y⁆)
    (hM : ∀ x y, eM ⁅x, y⁆ = ⁅eM x, eM y⁆)
    (f : L ≃ₗ⁅k⁆ M) : L ≃ₗ⁅k⁆ M where
  __ := (eL.symm.trans f.toLinearEquiv).trans eM
  map_lie' := by
    intro x y
    change eM (f (eL.symm ⁅x, y⁆)) = ⁅eM (f (eL.symm x)), eM (f (eL.symm y))⁆
    rw [semilinear_symm_map_lie eL hL, f.map_lie, hM]

/-- Difference of two isomorphisms, as an automorphism of their common target. -/
def isomDifference (f g : L ≃ₗ⁅k⁆ M) : M ≃ₗ⁅k⁆ M := g.symm.trans f

@[simp] theorem isomDifference_apply (f g : L ≃ₗ⁅k⁆ M) (x : M) :
    isomDifference f g x = f (g.symm x) := rfl

theorem isomDifference_mul (f g h : L ≃ₗ⁅k⁆ M) :
    isomDifference f g * isomDifference g h = isomDifference f h := by
  ext x
  simp

/-- Agreement on every graded layer makes the difference filtration-trivial.
The hypothesis is written directly on vectors so no associated-graded construction is needed. -/
theorem isomDifference_mem_of_same_graded
    (FL : FiniteFiltration k L) (FM : FiniteFiltration k M)
    (f g : L ≃ₗ⁅k⁆ M)
    (hg : ∀ i y, y ∈ FM.step i → g.symm y ∈ FL.step i)
    (hfg : ∀ i x, x ∈ FL.step i → f x - g x ∈ FM.step (i + 1)) :
    isomDifference f g ∈ FM.automorphismSubgroup 0 := by
  intro i y hy
  change f (g.symm y) - y ∈ FM.step (i + 1)
  simpa only [LieEquiv.apply_symm_apply] using hfg i (g.symm y) (hg i y hy)

namespace SemilinearLieAction

variable {Γ : Type z} [Group Γ]
variable (A : SemilinearLieAction Γ k L) (B : SemilinearLieAction Γ k M)
variable (hscalar : ∀ σ, A.scalar σ = B.scalar σ)

/-- The natural action on isomorphisms between two semilinear Lie spaces. -/
def isomAction (σ : Γ) (f : L ≃ₗ⁅k⁆ M) : L ≃ₗ⁅k⁆ M :=
  semilinearConjugateIsom (A.equiv σ) (sameScalarEquiv (hscalar σ) (B.equiv σ))
    (A.map_lie σ) (B.map_lie σ) f

@[simp] theorem isomAction_apply (σ : Γ) (f : L ≃ₗ⁅k⁆ M) (x : L) :
    A.isomAction B hscalar σ f x = B.equiv σ (f ((A.equiv σ).symm x)) := rfl

@[simp] theorem isomAction_symm_apply (σ : Γ) (f : L ≃ₗ⁅k⁆ M) (x : M) :
    (A.isomAction B hscalar σ f).symm x = A.equiv σ (f.symm ((B.equiv σ).symm x)) := rfl

@[simp] theorem isomAction_one (f : L ≃ₗ⁅k⁆ M) : A.isomAction B hscalar 1 f = f := by
  ext x
  simp only [isomAction_apply, B.one_apply, A.symm_one_apply]

theorem isomAction_mul (σ τ : Γ) (f : L ≃ₗ⁅k⁆ M) :
    A.isomAction B hscalar (σ * τ) f =
      A.isomAction B hscalar σ (A.isomAction B hscalar τ f) := by
  ext x
  simp only [isomAction_apply, B.mul_apply, A.symm_mul_apply]

theorem isomAction_difference (σ : Γ) (f g : L ≃ₗ⁅k⁆ M) :
    B.automorphismAction σ (isomDifference f g) =
      isomDifference (A.isomAction B hscalar σ f) (A.isomAction B hscalar σ g) := by
  ext x
  simp only [automorphismAction_apply, isomDifference_apply, isomAction_apply,
    isomAction_symm_apply, LinearEquiv.symm_apply_apply]

/-- The cocycle associated to an isomorphism over the extension field. -/
def isomCocycle (f : L ≃ₗ⁅k⁆ M) (σ : Γ) : M ≃ₗ⁅k⁆ M :=
  isomDifference f (A.isomAction B hscalar σ f)

theorem isomCocycle_isCocycle (f : L ≃ₗ⁅k⁆ M) :
    IsGroupCocycle B.automorphismAction (A.isomCocycle B hscalar f) := by
  intro σ τ
  dsimp only [isomCocycle]
  rw [A.isomAction_difference B hscalar, ← A.isomAction_mul B hscalar,
    isomDifference_mul]

theorem isomAction_target_comp (σ : Γ) (f : L ≃ₗ⁅k⁆ M) (b : M ≃ₗ⁅k⁆ M) :
    A.isomAction B hscalar σ (f.trans b) =
      (A.isomAction B hscalar σ f).trans (B.automorphismAction σ b) := by
  ext x
  simp only [isomAction_apply, LieEquiv.trans_apply, automorphismAction_apply,
    LinearEquiv.symm_apply_apply]

/-- The coboundary correction makes the isomorphism fixed; the multiplication order
matches the left action of target automorphisms. -/
theorem isomAction_corrected_fixed (f : L ≃ₗ⁅k⁆ M) (b : M ≃ₗ⁅k⁆ M)
    (hb : ∀ σ, A.isomCocycle B hscalar f σ = b⁻¹ * B.automorphismAction σ b) :
    ∀ σ, A.isomAction B hscalar σ (f.trans b) = f.trans b := by
  intro σ
  rw [A.isomAction_target_comp B hscalar]
  ext x
  have h : (b⁻¹ * B.automorphismAction σ b) (A.isomAction B hscalar σ f x) = f x := by
    rw [← hb σ]
    exact congrArg f ((A.isomAction B hscalar σ f).symm_apply_apply x)
  have h' := congrArg b h
  simpa only [lieEquiv_mul_apply, lieEquiv_inv_apply, LieEquiv.apply_symm_apply,
    LieEquiv.trans_apply] using h'

variable [CharZero k] [LieAlgebra ℚ M]

/-- A finite semilinear action permits a filtration-trivial correction of every
isomorphism whose associated isomorphism cocycle is filtration-trivial. -/
theorem exists_fixed_isom [Fintype Γ]
    (F : FiniteFiltration k M)
    (hF : ∀ σ i x, x ∈ F.step i → B.equiv σ x ∈ F.step i)
    (f : L ≃ₗ⁅k⁆ M)
    (hmark : ∀ σ, A.isomCocycle B hscalar f σ ∈ F.automorphismSubgroup 0) :
    ∃ b ∈ F.automorphismSubgroup 0,
      ∀ σ x, B.equiv σ (b (f x)) = b (f (A.equiv σ x)) := by
  obtain ⟨b, hbF, hb⟩ := B.exists_coboundary F hF (A.isomCocycle B hscalar f)
    (A.isomCocycle_isCocycle B hscalar f) hmark
  refine ⟨b, hbF, fun σ x => ?_⟩
  have h := congrArg (fun g : L ≃ₗ⁅k⁆ M => g (A.equiv σ x))
    (A.isomAction_corrected_fixed B hscalar f b hb σ)
  simpa only [isomAction_apply, LieEquiv.trans_apply, LinearEquiv.symm_apply_apply] using h

section BaseField

variable (R : Type*) [Field R] [Algebra R k]
variable [LieAlgebra R L] [LieAlgebra R M]
variable [IsScalarTower R k L] [IsScalarTower R k M]
variable {L₀ M₀ : Type*} [LieRing L₀] [LieAlgebra R L₀]
variable [LieRing M₀] [LieAlgebra R M₀]

/-- The explicit marked descent theorem: a semilinear isomorphism cocycle is
removed by a filtration-trivial target automorphism, and the corrected map
restricts to a Lie equivalence of the base algebras. -/
theorem exists_descended_marked_isom [Fintype Γ]
    (jL : L₀ →ₗ⁅R⁆ L) (jM : M₀ →ₗ⁅R⁆ M)
    (hjL : Function.Injective jL) (hjM : Function.Injective jM)
    (hL : ∀ x, x ∈ Set.range jL ↔ ∀ σ, A.equiv σ x = x)
    (hM : ∀ y, y ∈ Set.range jM ↔ ∀ σ, B.equiv σ y = y)
    (F : FiniteFiltration k M)
    (hF : ∀ σ i x, x ∈ F.step i → B.equiv σ x ∈ F.step i)
    (f : L ≃ₗ⁅k⁆ M)
    (hmark : ∀ σ, A.isomCocycle B hscalar f σ ∈ F.automorphismSubgroup 0) :
    ∃ b ∈ F.automorphismSubgroup 0, ∃ g : L₀ ≃ₗ⁅R⁆ M₀,
      ∀ x, jM (g x) = b (f (jL x)) := by
  obtain ⟨b, hbF, hb⟩ := A.exists_fixed_isom B hscalar F hF f hmark
  obtain ⟨g, hg⟩ := exists_descended_lieEquiv_of_fixed jL jM hjL hjM
    (fun σ => A.equiv σ) (fun σ => B.equiv σ) hL hM
    (restrictLieEquiv R (f.trans b)) hb
  exact ⟨b, hbF, g, hg⟩

end BaseField

end SemilinearLieAction

end EnvelopingIsomorphism.Descent
