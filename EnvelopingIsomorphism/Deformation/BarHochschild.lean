import EnvelopingIsomorphism.Deformation.BarResolution
import EnvelopingIsomorphism.Deformation.Hochschild
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# The Hom complex of the actual bar resolution and full Hochschild cochains
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Bar

open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

universe u
variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

/-- The diagonal's restricted coefficient action is the original one. -/
def diagonalLinearEquiv : diagonal k A ≃ₗ[k] A where
  toEquiv := Equiv.refl A
  map_add' _ _ := rfl
  map_smul' c x := by
    change Algebra.TensorProduct.lmul' k (S := A)
      (algebraMap k (Enveloping k A) c) * (show A from x) = c • (show A from x)
    rw [AlgHom.commutes]
    exact (Algebra.smul_def c (show A from x)).symm

/-- Tensor-Hom currying for every internal arity, including arity zero. -/
def internalHomEquiv : (n : ℕ) → (Internal k A n →ₗ[k] A) ≃ₗ[k] Curried k A n
  | 0 => LinearMap.ringLmapEquivSelf k k A
  | n + 1 =>
    (TensorProduct.lift.equiv (RingHom.id k) A (Internal k A n) A).symm.trans
      ((LinearEquiv.refl k A).arrowCongr (internalHomEquiv n))

/-- Every enveloping-linear map on a bar term is an arbitrary full cochain. -/
def homCochainEquiv (n : ℕ) : (termObj k A n ⟶ diagonal k A) ≃ₗ[k] Cochain k A n :=
  (ModuleCat.homLinearEquiv).trans
    ((((freeEquivEnveloping k A n).arrowCongr
      (LinearEquiv.refl (Enveloping k A) (diagonal k A))).restrictScalars k).trans
        (((LinearMap.liftBaseChangeEquiv (R := k) (M := Internal k A n)
          (N := diagonal k A) (Enveloping k A)).symm.restrictScalars k).trans
            (((LinearEquiv.refl k (Internal k A n)).arrowCongr (diagonalLinearEquiv k A)).trans
              ((internalHomEquiv k A n).trans (cochainCurriedEquiv k A n).symm))))

/-- Forget the endpoint action while retaining the original coefficient-module structure. -/
def homLinear (n : ℕ) (f : termObj k A n ⟶ diagonal k A) : Term k A n →ₗ[k] A where
  toFun := f.hom
  map_add' := f.hom.map_add
  map_smul' c x := by
    have hc : endpointRepresentation k A (n + 1) (algebraMap k (Enveloping k A) c) x =
        c • x := by
      rw [AlgHom.commutes]
      rfl
    have h := f.hom.map_smul (algebraMap k (Enveloping k A) c) x
    change f.hom (endpointRepresentation k A (n + 1)
      (algebraMap k (Enveloping k A) c) x) =
      Algebra.TensorProduct.lmul' k (S := A) (algebraMap k (Enveloping k A) c) *
        (show A from f.hom x) at h
    rw [hc, AlgHom.commutes] at h
    exact h.trans (Algebra.smul_def c (show A from f.hom x)).symm

/-- An internal pure tensor, with `1 : k` in arity zero. -/
def internalPure : (n : ℕ) → (Fin n → A) → Internal k A n
  | 0, _ => 1
  | n + 1, x => x 0 ⊗ₜ[k] internalPure n (Fin.tail x)

/-- The internal factors followed by the right endpoint. -/
def tailPure : (n : ℕ) → (Fin n → A) → A → Tensor k A n
  | 0, _, b => b
  | n + 1, x, b => x 0 ⊗ₜ[k] tailPure n (Fin.tail x) b

def barPure (n : ℕ) (a b : A) (x : Fin n → A) : Term k A n :=
  a ⊗ₜ[k] tailPure k A n x b

theorem internalHomEquiv_eval : ∀ (n : ℕ) (f : Internal k A n →ₗ[k] A) (x : Fin n → A),
    curriedEval n (internalHomEquiv k A n f) x = f (internalPure k A n x) := by
  intro n
  induction n with
  | zero => intro f x; rfl
  | succ n ih =>
    intro f x
    change curriedEval n (internalHomEquiv k A n (TensorProduct.curry f (x 0)))
      (Fin.tail x) = f (x 0 ⊗ₜ[k] internalPure k A n (Fin.tail x))
    rw [ih]
    rfl

theorem rightFreeEquiv_tailPure : ∀ (n : ℕ) (x : Fin n → A) (b : A),
    rightFreeEquiv k A n (tailPure k A n x b) = b ⊗ₜ[k] internalPure k A n x := by
  intro n
  induction n with
  | zero => intro x b; rfl
  | succ n ih =>
    intro x b
    change rightFreeEquiv k A (n + 1) (x 0 ⊗ₜ[k] tailPure k A n (Fin.tail x) b) = _
    rw [rightFreeEquiv_succ_tmul, ih]
    rfl

theorem freeEquiv_barPure (n : ℕ) (a b : A) (x : Fin n → A) :
    freeEquiv k A n (barPure k A n a b x) = (a ⊗ₜ[k] b) ⊗ₜ[k] internalPure k A n x := by
  rw [barPure, freeEquiv_tmul, rightFreeEquiv_tailPure]
  rfl

theorem freeEquiv_symm_normalized (n : ℕ) (x : Fin n → A) :
    (freeEquiv k A n).symm (1 ⊗ₜ[k] internalPure k A n x) = barPure k A n 1 1 x := by
  apply (freeEquiv k A n).injective
  rw [LinearEquiv.apply_symm_apply, freeEquiv_barPure]
  rfl

/-- The cochain corresponding to a bar Hom is its evaluation with both endpoints equal to one. -/
theorem homCochainEquiv_apply (n : ℕ) (f : termObj k A n ⟶ diagonal k A) (x : Fin n → A) :
    homCochainEquiv k A n f x = homLinear k A n f (barPure k A n 1 1 x) := by
  simp only [homCochainEquiv, LinearEquiv.trans_apply]
  rw [cochainCurriedEquiv_symm_apply, internalHomEquiv_eval]
  change f.hom ((freeEquiv k A n).symm (1 ⊗ₜ[k] internalPure k A n x)) = _
  rw [freeEquiv_symm_normalized]
  rfl

theorem barPure_endpoint (n : ℕ) (a b : A) (x : Fin n → A) :
    barPure k A n a b x = endpointRepresentation k A (n + 1) (a ⊗ₜ[k] b)
      (barPure k A n 1 1 x) := by
  apply (freeEquiv k A n).injective
  rw [freeEquiv_endpointRepresentation, freeEquiv_barPure, freeEquiv_barPure]
  change (a ⊗ₜ[k] b) ⊗ₜ[k] internalPure k A n x =
    (a ⊗ₜ[k] b) • ((1 : Enveloping k A) ⊗ₜ[k] internalPure k A n x)
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem homLinear_barPure (n : ℕ) (f : termObj k A n ⟶ diagonal k A)
    (a b : A) (x : Fin n → A) :
    homLinear k A n f (barPure k A n a b x) = a * homCochainEquiv k A n f x * b := by
  rw [barPure_endpoint, homCochainEquiv_apply]
  have h := f.hom.map_smul (a ⊗ₜ[k] b) (barPure k A n 1 1 x)
  change homLinear k A n f (endpointRepresentation k A (n + 1)
    (a ⊗ₜ[k] b) (barPure k A n 1 1 x)) =
      (a * b) * homLinear k A n f (barPure k A n 1 1 x) at h
  rw [h]
  ring

theorem homLinear_symm_barPure (n : ℕ) (f : Cochain k A n)
    (a b : A) (x : Fin n → A) :
    homLinear k A n ((homCochainEquiv k A n).symm f) (barPure k A n a b x) =
      a * f x * b := by
  rw [homLinear_barPure, LinearEquiv.apply_symm_apply]

theorem tensor_hom_ext : ∀ (n : ℕ) (f g : Tensor k A n →ₗ[k] A),
    (∀ (x : Fin n → A) (b : A), f (tailPure k A n x b) = g (tailPure k A n x b)) → f = g := by
  intro n
  induction n with
  | zero =>
    intro f g h
    apply LinearMap.ext
    intro b
    exact h Fin.elim0 b
  | succ n ih =>
    intro f g h
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply ih
    intro x b
    exact h (Fin.cons a x) b

theorem homLinear_slice (n : ℕ) (f : Cochain k A (n + 1)) (a : A) (y : Tensor k A n) :
    homLinear k A (n + 1) ((homCochainEquiv k A (n + 1)).symm f)
      (1 ⊗ₜ[k] (a ⊗ₜ[k] y)) =
    homLinear k A n ((homCochainEquiv k A n).symm (f.curryLeft a)) (1 ⊗ₜ[k] y) := by
  have h :
      ((homLinear k A (n + 1) ((homCochainEquiv k A (n + 1)).symm f)).comp
        (TensorProduct.mk k A (Tensor k A (n + 1)) 1)).comp
          (TensorProduct.mk k A (Tensor k A n) a) =
      (homLinear k A n ((homCochainEquiv k A n).symm (f.curryLeft a))).comp
        (TensorProduct.mk k A (Tensor k A n) 1) := by
    apply tensor_hom_ext k A n
    intro x b
    change homLinear k A (n + 1) ((homCochainEquiv k A (n + 1)).symm f)
      (barPure k A (n + 1) 1 b (Fin.cons a x)) =
      homLinear k A n ((homCochainEquiv k A n).symm (f.curryLeft a)) (barPure k A n 1 b x)
    rw [homLinear_symm_barPure, homLinear_symm_barPure]
    rfl
  exact LinearMap.congr_fun h y

/-- Differential on the actual enveloping-linear Hom modules, by precomposition. -/
def homDifferential (n : ℕ) (f : termObj k A n ⟶ diagonal k A) :
    termObj k A (n + 1) ⟶ diagonal k A :=
  ModuleCat.ofHom (X := termObj k A (n + 1)) (Y := termObj k A n)
    (termDifferential k A n) ≫ f

@[simp] theorem homLinear_homDifferential (n : ℕ) (f : termObj k A n ⟶ diagonal k A)
    (x : Term k A (n + 1)) :
    homLinear k A (n + 1) (homDifferential k A n f) x =
      homLinear k A n f (differential k A (n + 1) x) := rfl

private theorem cochain_ext_cons_cons {n : ℕ} {f g : Cochain k A (n + 2)}
    (h : ∀ a b x, f (Fin.cons a (Fin.cons b x)) = g (Fin.cons a (Fin.cons b x))) : f = g := by
  ext x
  simpa only [Fin.cons_self_tail] using h (x 0) (Fin.tail x 0) (Fin.tail (Fin.tail x))

/-- The actual Hom differential is the full ordinary Hochschild differential,
including both endpoint terms and arity zero. -/
theorem homCochainEquiv_differential : ∀ (n : ℕ) (f : Cochain k A n),
    homCochainEquiv k A (n + 1)
      (homDifferential k A n ((homCochainEquiv k A n).symm f)) =
      barDifferential (LinearMap.mul k A) n f := by
  intro n
  induction n with
  | zero =>
    intro f
    ext x
    rw [homCochainEquiv_apply, homLinear_homDifferential, barDifferential_eval]
    change homLinear k A 0 ((homCochainEquiv k A 0).symm f)
      (differential k A 1 (1 ⊗ₜ[k] (x 0 ⊗ₜ[k] (1 : A)))) =
        x 0 * f Fin.elim0 - f Fin.elim0 * x 0
    rw [differential_succ_tmul k A 0, differential_zero_tmul, one_mul, mul_one, map_sub]
    change homLinear k A 0 ((homCochainEquiv k A 0).symm f) (barPure k A 0 (x 0) 1 Fin.elim0) -
      homLinear k A 0 ((homCochainEquiv k A 0).symm f) (barPure k A 0 1 (x 0) Fin.elim0) = _
    rw [homLinear_symm_barPure, homLinear_symm_barPure]
    simp
  | succ n ih =>
    intro f
    apply cochain_ext_cons_cons
    intro a b x
    let y := tailPure k A n x 1
    have hi := congrArg (fun g : Cochain k A (n + 1) ↦ g (Fin.cons b x)) (ih (f.curryLeft a))
    rw [homCochainEquiv_apply, homLinear_homDifferential] at hi
    change homLinear k A n ((homCochainEquiv k A n).symm (f.curryLeft a))
      (differential k A (n + 1) (1 ⊗ₜ[k] (b ⊗ₜ[k] y))) = _ at hi
    rw [differential_succ_tmul k A n, one_mul, map_sub] at hi
    change homLinear k A n ((homCochainEquiv k A n).symm (f.curryLeft a))
        (barPure k A n b 1 x) -
      homLinear k A n ((homCochainEquiv k A n).symm (f.curryLeft a))
        (1 ⊗ₜ[k] differential k A n (b ⊗ₜ[k] y)) = _ at hi
    rw [homLinear_symm_barPure, mul_one] at hi
    rw [homCochainEquiv_apply, homLinear_homDifferential, barDifferential_cons_cons]
    change homLinear k A (n + 1) ((homCochainEquiv k A (n + 1)).symm f)
      (differential k A (n + 2) (1 ⊗ₜ[k] (a ⊗ₜ[k] (b ⊗ₜ[k] y)))) =
        a * f (Fin.cons b x) - f (Fin.cons (a * b) x) + b * f (Fin.cons a x) -
          barDifferential (LinearMap.mul k A) n (f.curryLeft a) (Fin.cons b x)
    rw [differential_succ_tmul k A (n + 1), one_mul, differential_succ_tmul k A n,
      TensorProduct.tmul_sub, map_sub, map_sub]
    change homLinear k A (n + 1) ((homCochainEquiv k A (n + 1)).symm f)
        (barPure k A (n + 1) a 1 (Fin.cons b x)) -
      (homLinear k A (n + 1) ((homCochainEquiv k A (n + 1)).symm f)
        (barPure k A (n + 1) 1 1 (Fin.cons (a * b) x)) -
       homLinear k A (n + 1) ((homCochainEquiv k A (n + 1)).symm f)
        (1 ⊗ₜ[k] (a ⊗ₜ[k] differential k A n (b ⊗ₜ[k] y)))) = _
    rw [homLinear_symm_barPure, homLinear_symm_barPure, one_mul, mul_one, mul_one,
      homLinear_slice]
    have hslice : f.curryLeft a x = f (Fin.cons a x) := rfl
    rw [hslice] at hi
    rw [← hi]
    abel

/-- The actual Hom complex of the bar resolution is the full Hochschild
cochain complex, with its original differential in every degree. -/
def hochschildComplexIso :
    (complex k A).linearYonedaObj k (diagonal k A) ≅
      barComplex (LinearMap.mul k A) (fun a b c ↦ mul_assoc a b c) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (homCochainEquiv k A n).toModuleIso) ?_
  rintro i j (h : i + 1 = j)
  subst j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  symm
  simp only [ChainComplex.linearYonedaObj_d, complex, ChainComplex.of.d,
    barComplex, CochainComplex.of.d]
  change homCochainEquiv k A (i + 1) (homDifferential k A i f) =
    barDifferential (LinearMap.mul k A) i (homCochainEquiv k A i f)
  simpa only [LinearEquiv.symm_apply_apply] using
    homCochainEquiv_differential k A i (homCochainEquiv k A i f)

namespace OverAlgebra

/-- Residual coefficients act through the right endpoint, matching the Koszul presentation. -/
scoped instance coefficientAlgebra : Algebra A (Enveloping k A) :=
  Algebra.TensorProduct.rightAlgebra

theorem homLinear_smul (n : ℕ) (a : A) (f : termObj k A n ⟶ diagonal k A)
    (x : Term k A n) : homLinear k A n (a • f) x = a * homLinear k A n f x := by
  change ((1 : A) * a) * homLinear k A n f x = a * homLinear k A n f x
  rw [one_mul]

/-- The full Hom/cochain equivalence is linear over the coefficient algebra itself. -/
def homCochainEquivOverA (n : ℕ) : (termObj k A n ⟶ diagonal k A) ≃ₗ[A] Cochain k A n where
  toEquiv := (homCochainEquiv k A n).toEquiv
  map_add' := (homCochainEquiv k A n).map_add
  map_smul' a f := by
    ext x
    change homCochainEquiv k A n (a • f) x = a * homCochainEquiv k A n f x
    rw [homCochainEquiv_apply, homCochainEquiv_apply, homLinear_smul]

def homDifferentialLinear (n : ℕ) :
    (termObj k A n ⟶ diagonal k A) →ₗ[A] (termObj k A (n + 1) ⟶ diagonal k A) :=
  CategoryTheory.Linear.leftComp A (diagonal k A)
    (ModuleCat.ofHom (X := termObj k A (n + 1)) (Y := termObj k A n) (termDifferential k A n))

/-- Ordinary Hochschild differential bundled with its full `A`-linearity. -/
def barDifferentialOverA (n : ℕ) : Cochain k A n →ₗ[A] Cochain k A (n + 1) :=
  (homCochainEquivOverA k A (n + 1)).toLinearMap.comp
    ((homDifferentialLinear k A n).comp (homCochainEquivOverA k A n).symm.toLinearMap)

@[simp] theorem barDifferentialOverA_apply (n : ℕ) (f : Cochain k A n) :
    barDifferentialOverA k A n f = barDifferential (LinearMap.mul k A) n f :=
  homCochainEquiv_differential k A n f

/-- Full Hochschild cochains as a complex of modules over the commutative algebra. -/
def barComplexOverA : CochainComplex (ModuleCat.{u} A) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of A (Cochain k A n))
    (fun n ↦ ModuleCat.ofHom (barDifferentialOverA k A n)) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        ModuleCat.hom_zero, LinearMap.zero_apply]
      rw [barDifferentialOverA_apply, barDifferentialOverA_apply]
      exact barDifferential_sq (LinearMap.mul k A) (fun a b c ↦ mul_assoc a b c) n f)

/-- Actual complex isomorphism over `A`, suitable for finite-free rank comparisons. -/
def hochschildComplexIsoOverA :
    (complex k A).linearYonedaObj A (diagonal k A) ≅ barComplexOverA k A := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (homCochainEquivOverA k A n).toModuleIso) ?_
  rintro i j (h : i + 1 = j)
  subst j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  symm
  simp only [ChainComplex.linearYonedaObj_d, complex, ChainComplex.of.d,
    barComplexOverA, CochainComplex.of.d]
  change homCochainEquiv k A (i + 1) (homDifferential k A i f) =
    barDifferentialOverA k A i (homCochainEquiv k A i f)
  rw [barDifferentialOverA_apply]
  simpa only [LinearEquiv.symm_apply_apply] using
    homCochainEquiv_differential k A i (homCochainEquiv k A i f)

/-- Restricting the pointwise `A` action recovers the original `k`-cochain module. -/
def restrictCochainEquiv (n : ℕ) :
    (ModuleCat.restrictScalars (algebraMap k A)).obj (ModuleCat.of A (Cochain k A n)) ≃ₗ[k]
      Cochain k A n where
  toEquiv := Equiv.refl _
  map_add' _ _ := rfl
  map_smul' c f := by
    ext x
    change algebraMap k A c * (show Cochain k A n from f) x = c • (show Cochain k A n from f) x
    exact (Algebra.smul_def c _).symm

/-- The coefficient-algebra complex restricts to exactly the previously
constructed full Hochschild complex. -/
def restrictComplexIso :
    ((ModuleCat.restrictScalars (algebraMap k A)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (barComplexOverA k A) ≅ barComplex (LinearMap.mul k A) (fun a b c ↦ mul_assoc a b c) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (restrictCochainEquiv k A n).toModuleIso) ?_
  rintro i j (h : i + 1 = j)
  subst j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  simp only [barComplexOverA, barComplex, CochainComplex.of.d,
    CategoryTheory.Functor.mapHomologicalComplex_obj_d, dif_pos trivial,
    eqToHom_refl, Category.comp_id]
  change barDifferential (LinearMap.mul k A) i (show Cochain k A i from f) =
    barDifferentialOverA k A i (show Cochain k A i from f)
  exact (barDifferentialOverA_apply k A i _).symm

end OverAlgebra

end EnvelopingIsomorphism.Deformation.Bar
