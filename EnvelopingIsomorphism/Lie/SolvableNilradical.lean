import EnvelopingIsomorphism.Lie.NilradicalBaseChange
import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The derived ideal of a solvable Lie algebra lies in its nilradical

Lie's theorem is applied recursively to quotient modules. The derived ideal
acts trivially on each common weight space and nilpotently on the full module.
-/

namespace EnvelopingIsomorphism.Lie

attribute [local instance 100] LieRing.ofAssociativeRing
open scoped TensorProduct

variable {k L V : Type*} [Field k] [LieRing L] [LieAlgebra k L]
  [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]

/-- The derived ideal acts trivially on every ordinary common weight space. -/
theorem derived_le_ker_weightSpace (χ : L → k) :
    LieAlgebra.derivedSeries k L 1 ≤
      (LieModule.toEnd k L (LieModule.weightSpace V χ)).ker := by
  change ⁅(⊤ : LieIdeal k L), ⊤⁆ ≤ _
  apply (LieSubmodule.lie_le_iff _ _ _).mpr
  intro x hx y hy
  apply LieHom.mem_ker.mpr
  ext w
  change ⁅⁅x, y⁆, (w : V)⁆ = 0
  rw [lie_lie]
  have hw := (LieModule.mem_weightSpace χ (w : V)).mp w.property
  rw [hw y, hw x, lie_smul, lie_smul, hw x, hw y, smul_comm, sub_self]

/-- The common weight space is a trivial submodule for the derived ideal. -/
theorem weightSpace_restr_le_maxTriv (χ : L → k) :
    (LieModule.weightSpace V χ).restr
        (LieAlgebra.derivedSeries k L 1).toLieSubalgebra ≤
      LieModule.maxTrivSubmodule k (LieAlgebra.derivedSeries k L 1) V := by
  intro v hv
  change ∀ x : LieAlgebra.derivedSeries k L 1, ⁅x, v⁆ = 0
  intro x
  have hx := derived_le_ker_weightSpace (V := V) χ x.property
  have h := LinearMap.congr_fun (LieHom.mem_ker.mp hx) ⟨v, hv⟩
  exact congrArg Subtype.val h

/-- Over an algebraically closed field of characteristic zero, the derived ideal
of a solvable Lie algebra acts nilpotently on every finite-dimensional module. -/
theorem derived_acts_nilpotently_of_isAlgClosed [CharZero k] [IsAlgClosed k]
    [LieAlgebra.IsSolvable L] (V : Type*) [AddCommGroup V] [Module k V]
    [LieRingModule L V] [LieModule k L V] [Module.Finite k V] :
    LieModule.IsNilpotent (LieAlgebra.derivedSeries k L 1) V := by
  classical
  obtain h | h := subsingleton_or_nontrivial V
  · haveI := h
    infer_instance
  · haveI := h
    obtain ⟨χ, hχ⟩ := LieModule.exists_nontrivial_weightSpace_of_isSolvable k L V
    let W := LieModule.weightSpace V χ
    haveI : Nontrivial W := hχ
    have hq : LieModule.IsNilpotent (LieAlgebra.derivedSeries k L 1) (V ⧸ W) :=
      derived_acts_nilpotently_of_isAlgClosed (V ⧸ W)
    exact LieModule.nilpotentOfNilpotentQuotient k (LieAlgebra.derivedSeries k L 1) V
      (N := W.restr (LieAlgebra.derivedSeries k L 1).toLieSubalgebra)
      (weightSpace_restr_le_maxTriv χ) hq
termination_by Module.finrank k V
decreasing_by
  have hd := (LieModule.weightSpace V χ).toSubmodule.finrank_quotient_add_finrank
  have hp : 0 < Module.finrank k (LieModule.weightSpace V χ) := Module.finrank_pos
  change 0 < Module.finrank k (LieModule.weightSpace V χ).toSubmodule at hp
  change Module.finrank k (V ⧸ (LieModule.weightSpace V χ).toSubmodule) < Module.finrank k V
  omega

/-- The derived ideal of a finite-dimensional solvable Lie algebra in characteristic zero
is nilpotent, over the original field. -/
theorem isNilpotent_derived_of_isSolvable [CharZero k] [LieAlgebra.IsSolvable L]
    [Module.Finite k L] : LieRing.IsNilpotent (LieAlgebra.derivedSeries k L 1) := by
  let K := AlgebraicClosure k
  have h : LieRing.IsNilpotent ((LieAlgebra.derivedSeries k L 1).baseChange K) := by
    rw [← LieAlgebra.derivedSeries_baseChange]
    haveI := derived_acts_nilpotently_of_isAlgClosed (k := K) (L := K ⊗[k] L) (K ⊗[k] L)
    exact isNilpotent_of_ideal_action (LieAlgebra.derivedSeries K (K ⊗[k] L) 1)
  exact (isNilpotent_baseChange_iff K (LieAlgebra.derivedSeries k L 1)).mp h

/-- The derived ideal of a finite-dimensional solvable Lie algebra lies in its nilradical. -/
theorem derived_le_nilradical [CharZero k] [LieAlgebra.IsSolvable L] [Module.Finite k L] :
    LieAlgebra.derivedSeries k L 1 ≤ nilradical k L := by
  haveI := isNilpotent_derived_of_isSolvable (k := k) (L := L)
  exact le_nilradical (LieAlgebra.derivedSeries k L 1)

/-- A quotient by an ideal containing the derived ideal is abelian. -/
theorem quotient_isLieAbelian_of_derived_le (I : LieIdeal k L)
    (hI : LieAlgebra.derivedSeries k L 1 ≤ I) : IsLieAbelian (L ⧸ I) := by
  constructor
  intro x y
  induction x, y using Quotient.inductionOn₂' with
  | _ x y =>
    change LieSubmodule.Quotient.mk (N := I) ⁅x, y⁆ = 0
    apply LieSubmodule.Quotient.mk_eq_zero'.mpr
    apply hI
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) (LieSubmodule.mem_top y)

/-- The quotient of a finite-dimensional solvable Lie algebra by its nilradical is abelian. -/
instance nilradicalQuotientIsLieAbelian [CharZero k] [LieAlgebra.IsSolvable L]
    [Module.Finite k L] : IsLieAbelian (L ⧸ nilradical k L) :=
  quotient_isLieAbelian_of_derived_le (nilradical k L) derived_le_nilradical

/-- If the derived ideal lies in I, nilpotence of an adjoint operator on I
implies nilpotence on the whole algebra. -/
theorem isNilpotent_ad_of_ideal_action (I : LieIdeal k L)
    (hI : LieAlgebra.derivedSeries k L 1 ≤ I) (x : L)
    (hx : IsNilpotent (LieModule.toEnd k L I x)) : IsNilpotent (LieAlgebra.ad k L x) := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n + 1, LinearMap.ext fun y => ?_⟩
  rw [pow_succ, Module.End.mul_apply]
  have hxy : ⁅x, y⁆ ∈ I :=
    hI (LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) (LieSubmodule.mem_top y))
  have h := congrArg Subtype.val (LinearMap.congr_fun hn ⟨⁅x, y⁆, hxy⟩)
  simpa only [LieSubmodule.coe_toEnd_pow, LinearMap.zero_apply, ZeroMemClass.coe_zero,
    LieAlgebra.ad, LieModule.toEnd_apply_apply] using h

end EnvelopingIsomorphism.Lie
