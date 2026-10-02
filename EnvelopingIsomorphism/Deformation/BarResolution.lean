import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Tactic.Abel

/-!
# The two-sided bar resolution

The tensor terms are built recursively. The differential multiplies adjacent
factors with alternating signs; insertion of a unit supplies the contraction
of the augmented complex over the coefficient ring.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Bar

open scoped TensorProduct

universe u

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

/-- The coefficient ring acting on the two endpoints of a bar tensor. -/
abbrev Enveloping := A ⊗[k] A

/-- The actual diagonal module, with action induced by multiplication. -/
def diagonal : ModuleCat (Enveloping k A) :=
  letI := Module.compHom A (Algebra.TensorProduct.lmul' k (S := A)).toRingHom
  ModuleCat.of (Enveloping k A) A

/-- There are `n+1` tensor factors; bundling retains the recursive instances. -/
@[reducible] def tensorObj : ℕ → ModuleCat.{u} k
  | 0 => ModuleCat.of k A
  | n + 1 => ModuleCat.of k (A ⊗[k] tensorObj n)

abbrev Tensor (n : ℕ) : Type u := tensorObj k A n

/-- The bar term in chain degree `n` has `n+2` factors. -/
abbrev Term (n : ℕ) : Type u := Tensor k A (n + 1)

/-- The augmented bar differential; index zero is multiplication onto `A`. -/
def differential : (n : ℕ) → Tensor k A (n + 1) →ₗ[k] Tensor k A n
  | 0 => (Algebra.TensorProduct.lmul' k (S := A)).toLinearMap
  | n + 1 =>
    (TensorProduct.map (Algebra.TensorProduct.lmul' k (S := A)).toLinearMap
      (LinearMap.id : Tensor k A n →ₗ[k] Tensor k A n)).comp
      (TensorProduct.assoc k A A (Tensor k A n)).symm.toLinearMap -
    TensorProduct.map (LinearMap.id : A →ₗ[k] A) (differential n)

@[simp] theorem differential_zero_tmul (a b : A) :
    differential k A 0 (a ⊗ₜ[k] b) = a * b := rfl

@[simp] theorem differential_succ_tmul (n : ℕ) (a b : A) (x : Tensor k A n) :
    differential k A (n + 1) (a ⊗ₜ[k] (b ⊗ₜ[k] x)) =
      (a * b) ⊗ₜ[k] x - a ⊗ₜ[k] differential k A n (b ⊗ₜ[k] x) := rfl

/-- Unit insertion is coefficient-linear; it need not preserve both endpoint actions. -/
def contraction (n : ℕ) : Tensor k A n →ₗ[k] Tensor k A (n + 1) :=
  TensorProduct.mk k A (Tensor k A n) 1

@[simp] theorem contraction_apply (n : ℕ) (x : Tensor k A n) :
    contraction k A n x = 1 ⊗ₜ[k] x := rfl

@[simp] theorem differential_zero_contraction (a : A) :
    differential k A 0 (contraction k A 0 a) = a := by
  change 1 * a = a
  exact one_mul a

/-- The explicit contracting identity for the augmented tensor complex. -/
theorem contraction_identity (n : ℕ) (x : Tensor k A (n + 1)) :
    differential k A (n + 1) (contraction k A (n + 1) x) +
      contraction k A n (differential k A n x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    change (1 * a) ⊗ₜ[k] x - 1 ⊗ₜ[k] (differential k A n (a ⊗ₜ[k] x)) +
      1 ⊗ₜ[k] (differential k A n (a ⊗ₜ[k] x)) = a ⊗ₜ[k] x
    rw [one_mul, sub_add_cancel]
  | add x y hx hy =>
    simpa only [map_add, add_add_add_comm] using congrArg₂ (· + ·) hx hy

theorem differential_sq : ∀ n, (differential k A n).comp (differential k A (n + 1)) = 0 := by
  intro n
  induction n with
  | zero =>
    ext a b c
    change differential k A 0 (differential k A 1 (a ⊗ₜ[k] (b ⊗ₜ[k] c))) = 0
    rw [differential_succ_tmul k A 0, map_sub, differential_zero_tmul,
      differential_zero_tmul, differential_zero_tmul, mul_assoc, sub_self]
  | succ n ih =>
    ext a b c x
    change differential k A (n + 1)
      (differential k A (n + 2) (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] x)))) = 0
    have h := LinearMap.congr_fun ih (b ⊗ₜ[k] (c ⊗ₜ[k] x))
    change differential k A n (differential k A (n + 1) (b ⊗ₜ[k] (c ⊗ₜ[k] x))) = 0 at h
    rw [differential_succ_tmul k A n, map_sub] at h
    rw [differential_succ_tmul k A (n + 1), map_sub,
      differential_succ_tmul k A n, differential_succ_tmul k A n,
      TensorProduct.tmul_sub, map_sub, differential_succ_tmul k A n,
      differential_succ_tmul k A n, mul_assoc]
    rw [sub_eq_zero] at h
    rw [h]
    abel

/-- Exactness follows from unit insertion, with no assumed exactness premise. -/
theorem range_eq_ker (n : ℕ) :
    LinearMap.range (differential k A (n + 1)) = LinearMap.ker (differential k A n) := by
  apply le_antisymm
  · exact LinearMap.range_le_ker_iff.mpr (differential_sq k A n)
  · intro x hx
    refine ⟨contraction k A (n + 1) x, ?_⟩
    have h := contraction_identity k A n x
    change differential k A n x = 0 at hx
    simpa [hx] using h

theorem augmentation_surjective : Function.Surjective (differential k A 0) :=
  fun a ↦ ⟨contraction k A 0 a, differential_zero_contraction k A a⟩

/-- Multiplication on the first tensor factor. -/
def leftRepresentation : (n : ℕ) → A →ₐ[k] Module.End k (Tensor k A n)
  | 0 => Algebra.lsmul k k A
  | n + 1 => (Module.End.rTensorAlgHom k A (Tensor k A n)).comp (Algebra.lsmul k k A)

/-- Multiplication on the final tensor factor. -/
def rightRepresentation : (n : ℕ) → A →ₐ[k] Module.End k (Tensor k A n)
  | 0 => Algebra.lsmul k k A
  | n + 1 => (Module.End.lTensorAlgHom k (Tensor k A n) A).comp (rightRepresentation n)

@[simp] theorem leftRepresentation_zero (a x : A) :
    leftRepresentation k A 0 a x = a * x := rfl

@[simp] theorem rightRepresentation_zero (a x : A) :
    rightRepresentation k A 0 a x = a * x := rfl

@[simp] theorem leftRepresentation_tmul (n : ℕ) (a b : A) (x : Tensor k A n) :
    leftRepresentation k A (n + 1) a (b ⊗ₜ[k] x) = (a * b) ⊗ₜ[k] x := rfl

@[simp] theorem rightRepresentation_tmul (n : ℕ) (a b : A) (x : Tensor k A n) :
    rightRepresentation k A (n + 1) a (b ⊗ₜ[k] x) =
      b ⊗ₜ[k] rightRepresentation k A n a x := rfl

theorem left_right_commute (n : ℕ) (a b : A) :
    Commute (leftRepresentation k A n a) (rightRepresentation k A n b) := by
  cases n with
  | zero =>
    apply LinearMap.ext
    intro x
    change a * (b * x) = b * (a * x)
    exact mul_left_comm a b x
  | succ n =>
    ext c x
    rfl

/-- The two commuting endpoint actions form a representation of `A ⊗ A`. -/
def endpointRepresentation (n : ℕ) : Enveloping k A →ₐ[k] Module.End k (Tensor k A n) :=
  Algebra.TensorProduct.lift (leftRepresentation k A n) (rightRepresentation k A n)
    (left_right_commute k A n)

@[simp] theorem endpointRepresentation_tmul (n : ℕ) (a b : A) (x : Tensor k A n) :
    endpointRepresentation k A n (a ⊗ₜ[k] b) x =
      leftRepresentation k A n a (rightRepresentation k A n b x) := rfl

theorem differential_leftRepresentation (n : ℕ) (a : A) (x : Tensor k A (n + 1)) :
    differential k A n (leftRepresentation k A (n + 1) a x) =
      leftRepresentation k A n a (differential k A n x) := by
  cases n with
  | zero =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b c => exact mul_assoc a b c
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | succ n =>
    suffices h : (differential k A (n + 1)).comp (leftRepresentation k A (n + 2) a) =
        (leftRepresentation k A (n + 1) a).comp (differential k A (n + 1)) from
      LinearMap.congr_fun h x
    ext b c y
    change differential k A (n + 1) ((a * b) ⊗ₜ[k] (c ⊗ₜ[k] y)) =
      leftRepresentation k A (n + 1) a
        (differential k A (n + 1) (b ⊗ₜ[k] (c ⊗ₜ[k] y)))
    rw [differential_succ_tmul k A n, differential_succ_tmul k A n, map_sub,
      leftRepresentation_tmul k A n, leftRepresentation_tmul k A n, mul_assoc]

theorem differential_rightRepresentation : ∀ (n : ℕ) (a : A) (x : Tensor k A (n + 1)),
    differential k A n (rightRepresentation k A (n + 1) a x) =
      rightRepresentation k A n a (differential k A n x) := by
  intro n
  induction n with
  | zero =>
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b c => exact mul_left_comm b a c
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | succ n ih =>
    intro a x
    suffices h : (differential k A (n + 1)).comp (rightRepresentation k A (n + 2) a) =
        (rightRepresentation k A (n + 1) a).comp (differential k A (n + 1)) from
      LinearMap.congr_fun h x
    ext b c y
    change differential k A (n + 1)
      (b ⊗ₜ[k] (c ⊗ₜ[k] rightRepresentation k A n a y)) =
      rightRepresentation k A (n + 1) a
        (differential k A (n + 1) (b ⊗ₜ[k] (c ⊗ₜ[k] y)))
    rw [differential_succ_tmul k A n, differential_succ_tmul k A n, map_sub,
      rightRepresentation_tmul k A n, rightRepresentation_tmul k A n]
    rw [← rightRepresentation_tmul k A n a c y, ih]

theorem differential_endpointRepresentation (n : ℕ) (r : Enveloping k A)
    (x : Tensor k A (n + 1)) :
    differential k A n (endpointRepresentation k A (n + 1) r x) =
      endpointRepresentation k A n r (differential k A n x) := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    change differential k A n (leftRepresentation k A (n + 1) a
      (rightRepresentation k A (n + 1) b x)) =
      leftRepresentation k A n a (rightRepresentation k A n b (differential k A n x))
    rw [differential_leftRepresentation, differential_rightRepresentation]
  | add r s hr hs =>
    simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hr hs

@[implicit_reducible] def endpointModule (n : ℕ) : Module (Enveloping k A) (Tensor k A n) :=
  Module.compHom (Tensor k A n) (endpointRepresentation k A n).toRingHom

/-- The actual bar term as a module over the enveloping coefficient ring. -/
def termObj (n : ℕ) : ModuleCat.{u} (Enveloping k A) :=
  letI := endpointModule k A (n + 1)
  ModuleCat.of (Enveloping k A) (Term k A n)

/-- The tensor differential preserves both endpoint actions. -/
def termDifferential (n : ℕ) : termObj k A (n + 1) →ₗ[Enveloping k A] termObj k A n where
  toFun := differential k A (n + 1)
  map_add' := (differential k A (n + 1)).map_add
  map_smul' r x := differential_endpointRepresentation k A (n + 1) r x

/-- The internal factors, with the zero-fold tensor product equal to `k`. -/
@[reducible] def internalObj : ℕ → ModuleCat.{u} k
  | 0 => ModuleCat.of k k
  | n + 1 => ModuleCat.of k (A ⊗[k] internalObj n)

abbrev Internal (n : ℕ) : Type u := internalObj k A n

/-- Move the right endpoint to the first position among the tail factors. -/
def rightFreeEquiv : (n : ℕ) → Tensor k A n ≃ₗ[k] A ⊗[k] Internal k A n
  | 0 => (TensorProduct.rid k A).symm
  | n + 1 =>
    (TensorProduct.congr (LinearEquiv.refl k A) (rightFreeEquiv n)).trans
      (TensorProduct.leftComm k A A (Internal k A n))

theorem rightFreeEquiv_succ_tmul (n : ℕ) (a : A) (x : Tensor k A n) :
    rightFreeEquiv k A (n + 1) (a ⊗ₜ[k] x) =
      TensorProduct.leftComm k A A (Internal k A n) (a ⊗ₜ[k] rightFreeEquiv k A n x) := rfl

private theorem leftComm_endpoint (n : ℕ) (a b : A) (z : A ⊗[k] Internal k A n) :
    TensorProduct.leftComm k A A (Internal k A n) (b ⊗ₜ[k] (a • z)) =
      a • TensorProduct.leftComm k A A (Internal k A n) (b ⊗ₜ[k] z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c x => rfl
  | add z z' hz hz' =>
    simpa only [smul_add, TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hz hz'

theorem rightFreeEquiv_rightRepresentation : ∀ (n : ℕ) (a : A) (x : Tensor k A n),
    rightFreeEquiv k A n (rightRepresentation k A n a x) = a • rightFreeEquiv k A n x := by
  intro n
  induction n with
  | zero => intro a x; rfl
  | succ n ih =>
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b y =>
      rw [rightRepresentation_tmul k A n, rightFreeEquiv_succ_tmul k A n,
        rightFreeEquiv_succ_tmul k A n, ih]
      exact leftComm_endpoint k A n a b _
    | add x y hx hy => simpa only [map_add, smul_add] using congrArg₂ (· + ·) hx hy

/-- Reorder only the endpoints: the internal factors retain their order. -/
def freeEquiv (n : ℕ) : Term k A n ≃ₗ[k] Enveloping k A ⊗[k] Internal k A n :=
  (TensorProduct.congr (LinearEquiv.refl k A) (rightFreeEquiv k A n)).trans
    (TensorProduct.assoc k A A (Internal k A n)).symm

theorem freeEquiv_tmul (n : ℕ) (a : A) (x : Tensor k A n) :
    freeEquiv k A n (a ⊗ₜ[k] x) =
      (TensorProduct.assoc k A A (Internal k A n)).symm (a ⊗ₜ[k] rightFreeEquiv k A n x) := rfl

private theorem assoc_endpoints (n : ℕ) (a b c : A) (z : A ⊗[k] Internal k A n) :
    (TensorProduct.assoc k A A (Internal k A n)).symm ((a * c) ⊗ₜ[k] (b • z)) =
      (a ⊗ₜ[k] b) • (TensorProduct.assoc k A A (Internal k A n)).symm (c ⊗ₜ[k] z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e x =>
    simp only [TensorProduct.smul_tmul', TensorProduct.assoc_symm_tmul,
      smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul]
  | add z z' hz hz' =>
    simpa only [smul_add, TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hz hz'

theorem freeEquiv_endpointRepresentation (n : ℕ) (r : Enveloping k A) (x : Term k A n) :
    freeEquiv k A n (endpointRepresentation k A (n + 1) r x) = r • freeEquiv k A n x := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c y =>
      change freeEquiv k A n ((a * c) ⊗ₜ[k] rightRepresentation k A n b y) =
        (a ⊗ₜ[k] b) • freeEquiv k A n (c ⊗ₜ[k] y)
      rw [freeEquiv_tmul, freeEquiv_tmul, rightFreeEquiv_rightRepresentation]
      exact assoc_endpoints k A n a b c _
    | add x y hx hy => simpa only [map_add, smul_add] using congrArg₂ (· + ·) hx hy
  | add r s hr hs =>
    simpa only [map_add, LinearMap.add_apply, add_smul] using congrArg₂ (· + ·) hr hs

/-- Each bar term is a free scalar extension of its internal tensor factors. -/
def freeEquivEnveloping (n : ℕ) :
    termObj k A n ≃ₗ[Enveloping k A] Enveloping k A ⊗[k] Internal k A n where
  toEquiv := (freeEquiv k A n).toEquiv
  map_add' := (freeEquiv k A n).map_add
  map_smul' := freeEquiv_endpointRepresentation k A n

theorem internal_free [Module.Free k A] : ∀ n, Module.Free k (Internal k A n) := by
  intro n
  induction n with
  | zero => infer_instance
  | succ n ih =>
    letI := ih
    infer_instance

instance term_free [Module.Free k A] (n : ℕ) : Module.Free (Enveloping k A) (termObj k A n) := by
  letI := internal_free k A n
  exact Module.Free.of_equiv (freeEquivEnveloping k A n).symm

theorem termDifferential_sq (n : ℕ) :
    (termDifferential k A n).comp (termDifferential k A (n + 1)) = 0 := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (differential_sq k A (n + 1)) x

/-- The bar complex in modules over the actual enveloping coefficient ring. -/
def complex : ChainComplex (ModuleCat.{u} (Enveloping k A)) ℕ :=
  ChainComplex.of (termObj k A) (fun n ↦ ModuleCat.ofHom
    (X := termObj k A (n + 1)) (Y := termObj k A n) (termDifferential k A n)) (by
    intro n
    apply ModuleCat.hom_ext
    exact termDifferential_sq k A n)

theorem term_range_eq_ker (n : ℕ) :
    LinearMap.range (termDifferential k A (n + 1)) =
      LinearMap.ker (termDifferential k A n) := by
  ext x
  change x ∈ LinearMap.range (differential k A (n + 2)) ↔
    x ∈ LinearMap.ker (differential k A (n + 1))
  rw [range_eq_ker k A (n + 1)]

theorem endpointRepresentation_zero (r : Enveloping k A) (x : A) :
    endpointRepresentation k A 0 r x = Algebra.TensorProduct.lmul' k (S := A) r * x := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => exact (mul_assoc a b x).symm
  | add r s hr hs =>
    simpa only [map_add, LinearMap.add_apply, add_mul] using congrArg₂ (· + ·) hr hs

/-- The multiplication augmentation is linear for the genuine diagonal action. -/
def augmentation : termObj k A 0 →ₗ[Enveloping k A] diagonal k A where
  toFun := differential k A 0
  map_add' := (differential k A 0).map_add
  map_smul' r x := by
    change differential k A 0 (endpointRepresentation k A 1 r x) =
      Algebra.TensorProduct.lmul' k (S := A) r * differential k A 0 x
    rw [differential_endpointRepresentation, endpointRepresentation_zero]

theorem augmentation_exact :
    LinearMap.range (termDifferential k A 0) = LinearMap.ker (augmentation k A) := by
  ext x
  change x ∈ LinearMap.range (differential k A 1) ↔ x ∈ LinearMap.ker (differential k A 0)
  rw [range_eq_ker k A 0]

theorem augmentation_comp_d : (augmentation k A).comp (termDifferential k A 0) = 0 :=
  LinearMap.range_le_ker_iff.mp (augmentation_exact k A).le

theorem augmentation_ae_surjective : Function.Surjective (augmentation k A) :=
  augmentation_surjective k A

theorem complex_exactAt_succ (n : ℕ) : (complex k A).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
    CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker]
  simpa [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', complex,
    ChainComplex.of.d] using term_range_eq_ker k A n

open CategoryTheory

/-- The augmented complex as a chain map onto the diagonal in degree zero. -/
def augmentationChainMap : complex k A ⟶ (ChainComplex.single₀ _).obj (diagonal k A) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (X := termObj k A 0) (Y := diagonal k A) (augmentation k A), by
      apply ModuleCat.hom_ext
      simpa [complex, ChainComplex.of.d] using augmentation_comp_d k A⟩

@[simp] theorem augmentationChainMap_f_zero :
    (augmentationChainMap k A).f 0 = ModuleCat.ofHom (augmentation k A) := by
  unfold augmentationChainMap
  apply ChainComplex.toSingle₀Equiv_symm_apply_f_zero

instance augmentation_epi : Epi (ModuleCat.ofHom (augmentation k A)) :=
  (ModuleCat.epi_iff_surjective _).mpr (augmentation_ae_surjective k A)

instance augmentationChainMap_quasiIso : QuasiIso (augmentationChainMap k A) := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · constructor
      · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
        change LinearMap.range ((complex k A).d 1 0).hom =
          LinearMap.ker ((augmentationChainMap k A).f 0).hom
        rw [augmentationChainMap_f_zero]
        simpa [complex, ChainComplex.of.d] using augmentation_exact k A
      · simpa [augmentationChainMap, HomologicalComplex.shortComplexFunctor'] using
          augmentation_epi k A
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · exact complex_exactAt_succ k A n
    · apply ChainComplex.exactAt_succ_single_obj

/-- The actual bar projective resolution. Over a field, `Module.Free k A`
is automatic; exactness was proved by the coefficient-linear contraction. -/
def resolution [Module.Free k A] : ProjectiveResolution (diagonal k A) where
  complex := complex k A
  projective n := by
    change Projective (termObj k A n)
    infer_instance
  π := augmentationChainMap k A

end EnvelopingIsomorphism.Deformation.Bar
