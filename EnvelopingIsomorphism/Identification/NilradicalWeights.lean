import EnvelopingIsomorphism.Lie.SolvableNilradical
import EnvelopingIsomorphism.Lie.DerivationAbelianization
import EnvelopingIsomorphism.Identification.Solvability.AbelianExtension
import Mathlib.Algebra.Lie.Weights.Linear

/-!
# Weights of the nilradical abelianization

The quotient `I / [I,I]` retains its ambient Lie algebra action. The ideal I
acts trivially, so this action descends canonically to `L / I`.
-/

namespace EnvelopingIsomorphism.Identification

open EnvelopingIsomorphism.Lie

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The abelianization of an ideal, retaining the action of its ambient algebra. -/
abbrev IdealAbelianization (I : LieIdeal R L) :=
  I ⧸ ⁅I, (⊤ : LieSubmodule R L I)⁆

/-- An ideal acts trivially on its own abelianization. -/
theorem ideal_le_ker_abelianization (I : LieIdeal R L) :
    I ≤ (LieModule.toEnd R L (IdealAbelianization I)).ker := by
  intro x hx
  apply LieHom.mem_ker.mpr
  ext v
  induction v using Quotient.inductionOn' with
  | _ v =>
    change LieSubmodule.Quotient.mk (N := ⁅I, (⊤ : LieSubmodule R L I)⁆) ⁅x, v⁆ = 0
    apply LieSubmodule.Quotient.mk_eq_zero'.mpr
    exact LieSubmodule.lie_mem_lie hx (LieSubmodule.mem_top v)

/-- The representation of `L/I` on the abelianization of I. -/
def quotientAbelianizationAction (I : LieIdeal R L) :
    L ⧸ I →ₗ⁅R⁆ Module.End R (IdealAbelianization I) where
  toLinearMap := I.toSubmodule.liftQ
    (LieModule.toEnd R L (IdealAbelianization I)).toLinearMap
    (ideal_le_ker_abelianization I)
  map_lie' := by
    intro x y
    induction x, y using Quotient.inductionOn₂' with
    | _ x y => exact (LieModule.toEnd R L (IdealAbelianization I)).map_lie x y

instance quotientAbelianizationLieRingModule (I : LieIdeal R L) :
    LieRingModule (L ⧸ I) (IdealAbelianization I) :=
  LieRingModule.compLieHom (IdealAbelianization I) (quotientAbelianizationAction I)

instance quotientAbelianizationLieModule (I : LieIdeal R L) :
    LieModule R (L ⧸ I) (IdealAbelianization I) :=
  LieModule.compLieHom (IdealAbelianization I) (quotientAbelianizationAction I)

@[simp]
theorem quotientAbelianizationAction_apply_mk (I : LieIdeal R L) (x : L)
    (v : IdealAbelianization I) :
    ⁅quotientLieHom I x, v⁆ = ⁅x, v⁆ := rfl

section WeightDetection

variable {k Q M : Type*} [Field k] [LieRing Q] [LieAlgebra k Q] [LieRing.IsNilpotent Q]
  [AddCommGroup M] [Module k M] [LieRingModule Q M] [LieModule k Q M]
  [Module.Finite k M] [LieModule.IsTriangularizable k Q M]

/-- Vanishing of all generalized weights at an element detects a nilpotent action. -/
theorem isNilpotent_toEnd_of_weight_zero (x : Q)
    (hx : ∀ χ : LieModule.Weight k Q M, χ x = 0) :
    IsNilpotent (LieModule.toEnd k Q M x) := by
  have htop : (⊤ : LieSubmodule k Q M) ≤ LieModule.genWeightSpaceOf M (0 : k) x := by
    rw [← LieModule.iSup_genWeightSpace_eq_top' k Q M]
    apply iSup_le
    intro χ
    rw [← hx χ]
    exact LieModule.genWeightSpace_le_genWeightSpaceOf M x χ
  apply Module.End.isNilpotent_iff_of_finite.mpr
  intro m
  have hm := htop (LieSubmodule.mem_top m)
  simpa only [LieModule.mem_genWeightSpaceOf, zero_smul, sub_zero] using hm

end WeightDetection

section WeightEvaluation

variable {k Q M : Type*} [Field k] [LieRing Q] [LieAlgebra k Q] [LieRing.IsNilpotent Q]
  [AddCommGroup M] [Module k M] [LieRingModule Q M] [LieModule k Q M]
  [LieModule.LinearWeights k Q M]

/-- Simultaneous evaluation of all weights, as a Lie map to an abelian algebra. -/
def weightEvaluation : Q →ₗ⁅k⁆ (LieModule.Weight k Q M → k) where
  toLinearMap := LinearMap.pi (fun χ => LieModule.Weight.toLinear k Q M χ)
  map_lie' := by
    intro x y
    ext χ
    change χ ⁅x, y⁆ = χ x * χ y - χ y * χ x
    rw [LieModule.LinearWeights.map_lie χ χ.genWeightSpace_ne_bot, mul_comm, sub_self]

end WeightEvaluation

section Nilradical

variable {k L : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [LieRing L] [LieAlgebra k L] [Module.Finite k L] [LieAlgebra.IsSolvable L]

local notation "N" => nilradical k L
local notation "Q₀" => L ⧸ N
local notation "V" => IdealAbelianization N

/-- An element whose action on the nilradical abelianization has only zero weights
already belongs to the nilradical. -/
theorem mem_nilradical_of_weights_zero (x : L)
    (hx : ∀ χ : LieModule.Weight k Q₀ V, χ (quotientLieHom N x) = 0) : x ∈ N := by
  let F : L →ₗ⁅k⁆ (LieModule.Weight k Q₀ V → k) :=
    (weightEvaluation (k := k) (Q := Q₀) (M := V)).comp (quotientLieHom N)
  let H : LieIdeal k L := F.ker
  have hnil (y : H) : IsNilpotent (LieAlgebra.ad k L (y : L)) := by
    have hy : ∀ χ : LieModule.Weight k Q₀ V, χ (quotientLieHom N (y : L)) = 0 := by
      intro χ
      exact congrFun (LieHom.mem_ker.mp y.property) χ
    have hq := isNilpotent_toEnd_of_weight_zero (M := V) (quotientLieHom N (y : L)) hy
    have heq : LieModule.toEnd k Q₀ V (quotientLieHom N (y : L)) =
        LieModule.toEnd k L V (y : L) := by ext v; rfl
    rw [heq] at hq
    have hn := isNilpotent_ideal_action_of_abelianization N (y : L) hq
    exact isNilpotent_ad_of_ideal_action N derived_le_nilradical (y : L) hn
  haveI : LieModule.IsNilpotent H L :=
    (LieModule.isNilpotent_iff_forall' (R := k)).mpr hnil
  haveI := isNilpotent_of_ideal_action H
  apply le_nilradical H
  apply LieHom.mem_ker.mpr
  funext χ
  exact hx χ

/-- The weights of the nilradical abelianization separate points of `L/N`. -/
theorem nilradical_weightEvaluation_injective :
    Function.Injective (weightEvaluation (k := k) (Q := Q₀) (M := V)) := by
  rw [← LieHom.ker_eq_bot]
  apply le_bot_iff.mp
  intro q hq
  induction q using Quotient.inductionOn' with
  | _ x =>
    apply LieSubmodule.Quotient.mk_eq_zero'.mpr
    apply mem_nilradical_of_weights_zero x
    intro χ
    exact congrFun (LieHom.mem_ker.mp hq) χ

/-- A finite family of true common eigenvectors has weights separating `L/N`.

Zero weights are allowed; every eigenvector itself is nonzero.
-/
theorem exists_full_nilradical_weights :
    ∃ (n : ℕ) (weights : Fin n → Module.Dual k Q₀) (w : Fin n → V),
      (∀ j, w j ≠ 0) ∧
      (∀ j q, ⁅q, w j⁆ = weights j q • w j) ∧
      Function.Injective (fun q : Q₀ => fun j => weights j q) := by
  classical
  let W := LieModule.Weight k Q₀ V
  choose w hw hweight using fun χ : W => LieModule.exists_forall_lie_eq_smul k Q₀ V χ
  let e : Fin (Fintype.card W) ≃ W := (Fintype.equivFin W).symm
  refine ⟨Fintype.card W, (fun i => LieModule.Weight.toLinear k Q₀ V (e i)),
    (fun i => w (e i)), (fun i => hw (e i)), ?_, ?_⟩
  · intro i q
    exact hweight (e i) q
  · intro q r h
    apply nilradical_weightEvaluation_injective
    funext χ
    change χ q = χ r
    have hχ := congrFun h (e.symm χ)
    simpa using hχ

end Nilradical

end EnvelopingIsomorphism.Identification
