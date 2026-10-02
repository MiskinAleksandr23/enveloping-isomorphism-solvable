import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Algebra.Order.Antidiag.Pi

/-! Formal power series of vectors. The coefficient type is only a module;
no ring or multiplication on coefficient vectors is used. -/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries

/-- Vector-valued formal power series, with the usual convolution scalar action. -/
abbrev PowerSeriesModule (k V : Type*) [Semiring k] [AddCommMonoid V] [Module k V] :=
  HahnModule ℕ k V

namespace PowerSeriesModule

section Basic

variable {k V W X : Type*} [Semiring k]
variable [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
variable [AddCommMonoid X] [Module k X]

instance instPowerSeriesModule : Module (PowerSeries k) (PowerSeriesModule k V) :=
  Module.compHom _ HahnSeries.toPowerSeries.symm.toRingHom

/-- The coefficient vector at a natural-number exponent. -/
def coeffV (n : ℕ) (p : PowerSeriesModule k V) : V := ((HahnModule.of k).symm p).coeff n

@[ext] theorem ext {p q : PowerSeriesModule k V} (h : ∀ n, coeffV n p = coeffV n q) : p = q :=
  HahnModule.ext _ _ (funext h)

/-- An arbitrary sequence of vectors is a formal power series. -/
def mk (f : ℕ → V) : PowerSeriesModule k V :=
  HahnModule.of k ⟨f, .of_linearOrder _⟩

@[simp] theorem coeffV_mk (f : ℕ → V) (n : ℕ) : coeffV n (mk (k := k) f) = f n := rfl

@[simp] theorem mk_coeffV (p : PowerSeriesModule k V) : mk (fun n ↦ coeffV n p) = p := by
  ext n
  rfl

@[simp] theorem coeffV_zero (n : ℕ) : coeffV n (0 : PowerSeriesModule k V) = 0 := rfl

@[simp] theorem coeffV_add (p q : PowerSeriesModule k V) (n : ℕ) :
    coeffV n (p + q) = coeffV n p + coeffV n q := rfl

@[simp] theorem coeffV_smul (a : k) (p : PowerSeriesModule k V) (n : ℕ) :
    coeffV n (a • p) = a • coeffV n p := rfl

@[simp] theorem coeffV_sum {ι : Type*} (s : Finset ι) (p : ι → PowerSeriesModule k V) (n : ℕ) :
    coeffV n (∑ i ∈ s, p i) = ∑ i ∈ s, coeffV n (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

/-- Scalar convolution has a finite antidiagonal coefficient formula. -/
theorem coeffV_series_smul (a : PowerSeries k) (p : PowerSeriesModule k V) (n : ℕ) :
    coeffV n (a • p) = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      PowerSeries.coeff ij.1 a • coeffV ij.2 p := by
  change ((HahnModule.of k).symm (HahnSeries.toPowerSeries.symm a • p)).coeff n = _
  rw [HahnModule.coeff_smul]
  classical
  refine (Finset.sum_filter_ne_zero _).symm.trans
    ((Finset.sum_congr ?_ fun _ _ ↦ rfl).trans (Finset.sum_filter_ne_zero _))
  ext ij
  simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal,
    Finset.mem_vaddAntidiagonal, HahnSeries.mem_support,
    HahnSeries.coeff_toPowerSeries_symm, vadd_eq_add]
  change ((PowerSeries.coeff ij.1 a ≠ 0 ∧ coeffV ij.2 p ≠ 0 ∧ ij.1 + ij.2 = n) ∧
      PowerSeries.coeff ij.1 a • coeffV ij.2 p ≠ 0) ↔
    (ij.1 + ij.2 = n ∧ PowerSeries.coeff ij.1 a • coeffV ij.2 p ≠ 0)
  constructor
  · exact fun h ↦ ⟨h.1.2.2, h.2⟩
  · intro h
    refine ⟨⟨?_, ?_, h.1⟩, h.2⟩
    · intro hz
      exact h.2 (by rw [hz, zero_smul])
    · intro hz
      exact h.2 (by rw [hz, smul_zero])

instance instScalarTower : IsScalarTower k (PowerSeries k) (PowerSeriesModule k V) where
  smul_assoc r a p := by
    ext n
    simp only [coeffV_series_smul, coeffV_smul, PowerSeries.coeff_smul,
      smul_assoc, Finset.smul_sum]

/-- Coefficient extraction as a linear map over the original scalar ring. -/
def coefficient (n : ℕ) : PowerSeriesModule k V →ₗ[k] V where
  toFun := coeffV n
  map_add' := fun _ _ ↦ rfl
  map_smul' := fun _ _ ↦ rfl

/-- Coefficientwise extension of a linear map, linear over formal scalar series. -/
def map (f : V →ₗ[k] W) : PowerSeriesModule k V →ₗ[PowerSeries k] PowerSeriesModule k W where
  toFun p := mk (fun n ↦ f (coeffV n p))
  map_add' p q := by ext n; simp
  map_smul' a p := by
    ext n
    simp only [coeffV_mk, coeffV_series_smul, map_sum, map_smul, RingHom.id_apply]

@[simp] theorem coeffV_map (f : V →ₗ[k] W) (p : PowerSeriesModule k V) (n : ℕ) :
    coeffV n (map f p) = f (coeffV n p) := rfl

@[simp] theorem map_id : map (LinearMap.id : V →ₗ[k] V) = LinearMap.id := by
  ext p n
  rfl

@[simp] theorem map_comp (g : W →ₗ[k] X) (f : V →ₗ[k] W) :
    map (g.comp f) = (map g).comp (map f) := by
  ext p n
  rfl

/-- A single vector coefficient. -/
def single (n : ℕ) (x : V) : PowerSeriesModule k V :=
  HahnModule.of k (HahnSeries.single n x)

@[simp] theorem coeffV_single (n m : ℕ) (x : V) :
    coeffV m (single (k := k) n x) = if m = n then x else 0 := by
  classical
  by_cases h : m = n <;> simp [coeffV, single, h]

@[simp] theorem map_single (f : V →ₗ[k] W) (n : ℕ) (x : V) :
    map f (single n x) = single n (f x) := by
  ext m
  simp only [coeffV_map, coeffV_single]
  split <;> simp_all

end Basic

section EndomorphismAction

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]

@[simp] theorem coeffV_neg (p : PowerSeriesModule k V) (n : ℕ) :
    coeffV n (-p) = -coeffV n p := rfl

@[simp] theorem coeffV_sub (p q : PowerSeriesModule k V) (n : ℕ) :
    coeffV n (p - q) = coeffV n p - coeffV n q := rfl

/-- The scalar parameter of `HahnModule` changes no coefficient vectors or addition. -/
def endModuleEquiv : PowerSeriesModule k V ≃+ PowerSeriesModule (Module.End k V) V where
  toEquiv := (HahnModule.of k).symm.trans (HahnModule.of (Module.End k V))
  map_add' _ _ := rfl

/-- A formal endomorphism series acts on vector-valued formal series by convolution. -/
def actV (F : PowerSeries (Module.End k V)) (p : PowerSeriesModule k V) : PowerSeriesModule k V :=
  endModuleEquiv.symm (F • endModuleEquiv p)

theorem coeffV_actV (F : PowerSeries (Module.End k V)) (p : PowerSeriesModule k V) (n : ℕ) :
    coeffV n (actV F p) = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      (PowerSeries.coeff ij.1 F) (coeffV ij.2 p) :=
  coeffV_series_smul F (endModuleEquiv p) n

@[simp] theorem actV_one (p : PowerSeriesModule k V) :
    actV (1 : PowerSeries (Module.End k V)) p = p := by simp [actV]

theorem actV_mul (F G : PowerSeries (Module.End k V)) (p : PowerSeriesModule k V) :
    actV (F * G) p = actV F (actV G p) := by simp [actV, mul_smul]

@[simp] theorem actV_zero_left (p : PowerSeriesModule k V) :
    actV (0 : PowerSeries (Module.End k V)) p = 0 := by simp [actV]

@[simp] theorem actV_zero_right (F : PowerSeries (Module.End k V)) : actV F 0 = 0 := by
  simp [actV]

theorem actV_add_left (F G : PowerSeries (Module.End k V)) (p : PowerSeriesModule k V) :
    actV (F + G) p = actV F p + actV G p := by simp [actV, add_smul]

theorem actV_add_right (F : PowerSeries (Module.End k V)) (p q : PowerSeriesModule k V) :
    actV F (p + q) = actV F p + actV F q := by simp [actV, smul_add]

theorem actV_smul_right (F : PowerSeries (Module.End k V)) (r : k) (p : PowerSeriesModule k V) :
    actV F (r • p) = r • actV F p := by
  ext n
  simp only [coeffV_actV, coeffV_smul, map_smul, Finset.smul_sum]

/-- Multiplication of operator series acts as composition on the completed vector module. -/
def actionHom : PowerSeries (Module.End k V) →+* Module.End k (PowerSeriesModule k V) where
  toFun F :=
    { toFun := actV F
      map_add' := actV_add_right F
      map_smul' := actV_smul_right F }
  map_one' := LinearMap.ext fun p ↦ actV_one p
  map_mul' F G := LinearMap.ext fun p ↦ actV_mul F G p
  map_zero' := LinearMap.ext fun p ↦ actV_zero_left p
  map_add' F G := LinearMap.ext fun p ↦ actV_add_left F G p

@[simp] theorem actionHom_apply (F : PowerSeries (Module.End k V)) (p : PowerSeriesModule k V) :
    actionHom F p = actV F p := rfl

end EndomorphismAction

section BilinearConvolution

variable {k V W X Y : Type*} [CommRing k]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]

/-- Associativity of finite convolution indices, independently of coefficient multiplication. -/
theorem sum_antidiagonal_assoc {A : Type*} [AddCommMonoid A]
    (f : ℕ → ℕ → ℕ → A) (n : ℕ) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal ij.1, f ab.1 ab.2 ij.2) =
    ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      ∑ bc ∈ Finset.HasAntidiagonal.antidiagonal ij.2, f ij.1 bc.1 bc.2 := by
  classical
  simp only [Finset.sum_sigma']
  apply Finset.sum_nbij'
    (fun ⟨⟨_i, j⟩, ⟨a, b⟩⟩ ↦ ⟨(a, b + j), (b, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨b, c⟩⟩ ↦ ⟨(i + b, c), (i, b)⟩) <;>
    aesop (add simp [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal, add_assoc])

/-- Apply a fixed bilinear map to vector-valued series by finite convolution. -/
def applyBilinear (f : V →ₗ[k] W →ₗ[k] X)
    (p : PowerSeriesModule k V) (q : PowerSeriesModule k W) : PowerSeriesModule k X :=
  mk fun n ↦ ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, f (coeffV ij.1 p) (coeffV ij.2 q)

@[simp] theorem coeffV_applyBilinear (f : V →ₗ[k] W →ₗ[k] X)
    (p : PowerSeriesModule k V) (q : PowerSeriesModule k W) (n : ℕ) :
    coeffV n (applyBilinear f p q) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, f (coeffV ij.1 p) (coeffV ij.2 q) := rfl

theorem applyBilinear_flip (f : V →ₗ[k] W →ₗ[k] X)
    (p : PowerSeriesModule k V) (q : PowerSeriesModule k W) :
    applyBilinear f p q = applyBilinear f.flip q p := by
  ext n
  exact (Finset.Nat.sum_antidiagonal_swap (n := n)
    (f := fun ij ↦ f (coeffV ij.1 p) (coeffV ij.2 q))).symm

theorem applyBilinear_series_smul_left (f : V →ₗ[k] W →ₗ[k] X)
    (a : PowerSeries k) (p : PowerSeriesModule k V) (q : PowerSeriesModule k W) :
    applyBilinear f (a • p) q = a • applyBilinear f p q := by
  ext n
  simp only [coeffV_applyBilinear, coeffV_series_smul, map_sum, LinearMap.sum_apply,
    map_smul, LinearMap.smul_apply, Finset.smul_sum]
  exact sum_antidiagonal_assoc
    (fun i j l ↦ PowerSeries.coeff i a • f (coeffV j p) (coeffV l q)) n

theorem applyBilinear_series_smul_right (f : V →ₗ[k] W →ₗ[k] X)
    (a : PowerSeries k) (p : PowerSeriesModule k V) (q : PowerSeriesModule k W) :
    applyBilinear f p (a • q) = a • applyBilinear f p q := by
  rw [applyBilinear_flip, applyBilinear_series_smul_left, ← applyBilinear_flip]

/-- A bilinear map extends as a bilinear map over the full formal scalar ring. -/
def extendBilinear (f : V →ₗ[k] W →ₗ[k] X) :
    PowerSeriesModule k V →ₗ[PowerSeries k]
      PowerSeriesModule k W →ₗ[PowerSeries k] PowerSeriesModule k X where
  toFun p :=
    { toFun := applyBilinear f p
      map_add' q r := by ext n; simp [Finset.sum_add_distrib]
      map_smul' a q := applyBilinear_series_smul_right f a p q }
  map_add' p q := by ext r n; simp [Finset.sum_add_distrib]
  map_smul' a p := LinearMap.ext fun q ↦ applyBilinear_series_smul_left f a p q

@[simp] theorem extendBilinear_apply (f : V →ₗ[k] W →ₗ[k] X)
    (p : PowerSeriesModule k V) (q : PowerSeriesModule k W) :
    extendBilinear f p q = applyBilinear f p q := rfl

/-- Evaluation of a series of linear maps on a series of vectors. -/
def linearApply : PowerSeriesModule k (V →ₗ[k] W) →ₗ[PowerSeries k]
    PowerSeriesModule k V →ₗ[PowerSeries k] PowerSeriesModule k W :=
  extendBilinear (LinearMap.id : (V →ₗ[k] W) →ₗ[k] V →ₗ[k] W)

@[simp] theorem coeffV_linearApply (F : PowerSeriesModule k (V →ₗ[k] W))
    (p : PowerSeriesModule k V) (n : ℕ) :
    coeffV n (linearApply F p) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (coeffV ij.1 F) (coeffV ij.2 p) := rfl

/-- A series of bilinear operations extends to a bilinear operation on full vector series. -/
def extendBinary (F : PowerSeriesModule k (V →ₗ[k] W →ₗ[k] X)) :
    PowerSeriesModule k V →ₗ[PowerSeries k]
      PowerSeriesModule k W →ₗ[PowerSeries k] PowerSeriesModule k X :=
  linearApply.comp (linearApply F)

theorem coeffV_extendBinary (F : PowerSeriesModule k (V →ₗ[k] W →ₗ[k] X))
    (p : PowerSeriesModule k V) (q : PowerSeriesModule k W) (n : ℕ) :
    coeffV n (extendBinary F p q) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal ij.1,
          (coeffV ab.1 F) (coeffV ab.2 p) (coeffV ij.2 q) := by
  simp only [extendBinary, LinearMap.comp_apply, coeffV_linearApply, LinearMap.sum_apply]

theorem applyBilinear_postcomp (f : V →ₗ[k] W →ₗ[k] X) (g : X →ₗ[k] Y)
    (p : PowerSeriesModule k V) (q : PowerSeriesModule k W) :
    map g (applyBilinear f p q) =
      applyBilinear ((LinearMap.llcomp k W X Y g).comp f) p q := by
  ext n
  simp [map_sum]

/-- Composition of series of linear maps with possibly different source and target. -/
def linearCompose : PowerSeriesModule k (W →ₗ[k] X) →ₗ[PowerSeries k]
    PowerSeriesModule k (V →ₗ[k] W) →ₗ[PowerSeries k] PowerSeriesModule k (V →ₗ[k] X) :=
  extendBilinear (LinearMap.llcomp k V W X)

theorem linearApply_comp (G : PowerSeriesModule k (W →ₗ[k] X))
    (F : PowerSeriesModule k (V →ₗ[k] W)) (p : PowerSeriesModule k V) :
    linearApply (linearCompose G F) p = linearApply G (linearApply F p) := by
  ext n
  simp only [linearCompose, extendBilinear_apply, coeffV_applyBilinear, coeffV_linearApply,
    LinearMap.sum_apply, LinearMap.llcomp_apply, map_sum]
  exact sum_antidiagonal_assoc
    (fun i j l ↦ (coeffV i G) ((coeffV j F) (coeffV l p))) n

theorem actV_eq_linearApply (F : PowerSeries (Module.End k V)) (p : PowerSeriesModule k V) :
    actV F p = linearApply (mk (fun n ↦ PowerSeries.coeff n F)) p := by
  ext n
  simp only [coeffV_actV, coeffV_linearApply, coeffV_mk]

theorem actV_series_smul (F : PowerSeries (Module.End k V))
    (a : PowerSeries k) (p : PowerSeriesModule k V) : actV F (a • p) = a • actV F p := by
  rw [actV_eq_linearApply, actV_eq_linearApply, map_smul]

theorem extendBinary_apply (F : PowerSeriesModule k (V →ₗ[k] W →ₗ[k] X))
    (p : PowerSeriesModule k V) (q : PowerSeriesModule k W) :
    extendBinary F p q = linearApply (linearApply F p) q := rfl

/-- Swap the inputs of every coefficient operation. -/
def flipBinarySeries (F : PowerSeriesModule k (V →ₗ[k] W →ₗ[k] X)) :
    PowerSeriesModule k (W →ₗ[k] V →ₗ[k] X) :=
  map (LinearMap.lflip (R₀ := k)).toLinearMap F

@[simp] theorem coeffV_flipBinarySeries (F : PowerSeriesModule k (V →ₗ[k] W →ₗ[k] X)) (n : ℕ) :
    coeffV n (flipBinarySeries F) = (coeffV n F).flip := rfl

theorem extendBinary_flip (F : PowerSeriesModule k (V →ₗ[k] W →ₗ[k] X))
    (p : PowerSeriesModule k V) (q : PowerSeriesModule k W) :
    extendBinary F p q = extendBinary (flipBinarySeries F) q p := by
  ext n
  simp only [coeffV_extendBinary, coeffV_flipBinarySeries, LinearMap.flip_apply]
  rw [sum_antidiagonal_assoc (fun i j l ↦ (coeffV i F) (coeffV j p) (coeffV l q)) n,
    sum_antidiagonal_assoc (fun i j l ↦ (coeffV i F) (coeffV l p) (coeffV j q)) n]
  apply Finset.sum_congr rfl
  intro ij _
  exact (Finset.Nat.sum_antidiagonal_swap (n := ij.2)
    (f := fun ab ↦ (coeffV ij.1 F) (coeffV ab.1 p) (coeffV ab.2 q))).symm

theorem extendBinary_precomp_left {V' : Type*} [AddCommGroup V'] [Module k V']
    (F : PowerSeriesModule k (V →ₗ[k] W →ₗ[k] X))
    (G : PowerSeriesModule k (V' →ₗ[k] V))
    (p : PowerSeriesModule k V') (q : PowerSeriesModule k W) :
    extendBinary (linearCompose F G) p q = extendBinary F (linearApply G p) q := by
  rw [extendBinary_apply, linearApply_comp, ← extendBinary_apply]

/-- Formal operator precomposition in the second input slot. -/
def precomposeBinaryRight {W' : Type*} [AddCommGroup W'] [Module k W']
    (F : PowerSeriesModule k (V →ₗ[k] W →ₗ[k] X))
    (G : PowerSeriesModule k (W' →ₗ[k] W)) :
    PowerSeriesModule k (V →ₗ[k] W' →ₗ[k] X) :=
  flipBinarySeries (linearCompose (flipBinarySeries F) G)

theorem extendBinary_precomp_right {W' : Type*} [AddCommGroup W'] [Module k W']
    (F : PowerSeriesModule k (V →ₗ[k] W →ₗ[k] X))
    (G : PowerSeriesModule k (W' →ₗ[k] W))
    (p : PowerSeriesModule k V) (q : PowerSeriesModule k W') :
    extendBinary (precomposeBinaryRight F G) p q = extendBinary F p (linearApply G q) := by
  change extendBinary (flipBinarySeries (linearCompose (flipBinarySeries F) G)) p q = _
  rw [← extendBinary_flip, extendBinary_precomp_left, ← extendBinary_flip]

/-- Coefficient convolution for postcomposition of a formal binary operation. -/
def postcomposeBinary (G : PowerSeriesModule k (X →ₗ[k] Y))
    (F : PowerSeriesModule k (V →ₗ[k] W →ₗ[k] X)) :
    PowerSeriesModule k (V →ₗ[k] W →ₗ[k] Y) :=
  linearCompose (map (LinearMap.llcomp k W X Y) G) F

theorem extendBinary_postcomp (G : PowerSeriesModule k (X →ₗ[k] Y))
    (F : PowerSeriesModule k (V →ₗ[k] W →ₗ[k] X))
    (p : PowerSeriesModule k V) (q : PowerSeriesModule k W) :
    extendBinary (postcomposeBinary G F) p q = linearApply G (extendBinary F p q) := by
  rw [extendBinary_apply, postcomposeBinary, linearApply_comp]
  have h : linearApply (map (LinearMap.llcomp k W X Y) G) (linearApply F p) =
      linearCompose G (linearApply F p) := by
    ext n
    rfl
  rw [h, linearApply_comp, ← extendBinary_apply]

end BilinearConvolution

section MultilinearConvolution

open scoped Classical

variable {k ι N P : Type*} [CommRing k] [Fintype ι]
variable {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]
variable [AddCommGroup N] [Module k N] [AddCommGroup P] [Module k P]

/-- Splitting a chosen exponent in a finite multi-antidiagonal. -/
theorem sum_piAntidiag_split {A : Type*} [AddCommMonoid A]
    (g : ℕ → (ι → ℕ) → A) (n : ℕ) (i : ι) :
    (∑ a ∈ Finset.piAntidiag Finset.univ n,
      ∑ rs ∈ Finset.HasAntidiagonal.antidiagonal (a i), g rs.1 (Function.update a i rs.2)) =
    ∑ rd ∈ Finset.HasAntidiagonal.antidiagonal n,
      ∑ a ∈ Finset.piAntidiag Finset.univ rd.2, g rd.1 a := by
  classical
  simp only [Finset.sum_sigma']
  apply Finset.sum_nbij'
    (fun ⟨a, ⟨r, s⟩⟩ ↦ ⟨(r, ∑ j, Function.update a i s j), Function.update a i s⟩)
    (fun ⟨⟨r, _d⟩, a⟩ ↦ ⟨Function.update a i (r + a i), (r, a i)⟩)
  · rintro ⟨a, r, s⟩ h
    simp only [Finset.mem_sigma, Finset.mem_piAntidiag, Finset.mem_univ, implies_true,
      and_true, Finset.HasAntidiagonal.mem_antidiagonal] at h ⊢
    rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
    simp only [Finset.sdiff_singleton_eq_erase]
    have hs := Finset.sum_erase_add Finset.univ a (Finset.mem_univ i)
    have hs' := hs.trans h.1
    omega
  · rintro ⟨⟨r, d⟩, a⟩ h
    simp only [Finset.mem_sigma, Finset.mem_piAntidiag, Finset.mem_univ, implies_true,
      and_true, Finset.HasAntidiagonal.mem_antidiagonal] at h ⊢
    refine ⟨?_, by simp⟩
    rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
    simp only [Finset.sdiff_singleton_eq_erase]
    have hs := Finset.sum_erase_add Finset.univ a (Finset.mem_univ i)
    have hs' := hs.trans h.2
    omega
  · rintro ⟨a, r, s⟩ h
    simp only [Finset.mem_sigma, Finset.mem_piAntidiag, Finset.mem_univ, implies_true,
      and_true, Finset.HasAntidiagonal.mem_antidiagonal] at h
    simp [h.2]
  · rintro ⟨⟨r, d⟩, a⟩ h
    simp only [Finset.mem_sigma, Finset.mem_piAntidiag, Finset.mem_univ, implies_true,
      and_true, Finset.HasAntidiagonal.mem_antidiagonal] at h
    simp [h.2]
  · rintro ⟨a, r, s⟩ _
    rfl

omit [Fintype ι] in
private theorem coeffV_update_input [DecidableEq ι] (p : ∀ i, PowerSeriesModule k (M i))
    (i : ι) (x : PowerSeriesModule k (M i)) (a : ι → ℕ) :
    (fun j ↦ coeffV (a j) (Function.update p i x j)) =
      Function.update (fun j ↦ coeffV (a j) (p j)) i (coeffV (a i) x) := by
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [h]

omit [Fintype ι] in
private theorem coeffV_update_index [DecidableEq ι] (p : ∀ i, PowerSeriesModule k (M i))
    (i : ι) (r : ℕ) (a : ι → ℕ) :
    (fun j ↦ coeffV (Function.update a i r j) (p j)) =
      Function.update (fun j ↦ coeffV (a j) (p j)) i (coeffV r (p i)) := by
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [h]

/-- Finite multi-antidiagonal convolution for an arbitrary fixed finite-arity map. -/
def applyMultilinear (f : MultilinearMap k M N) (p : ∀ i, PowerSeriesModule k (M i)) :
    PowerSeriesModule k N :=
  mk fun n ↦ ∑ a ∈ Finset.piAntidiag Finset.univ n, f (fun i ↦ coeffV (a i) (p i))

@[simp] theorem coeffV_applyMultilinear (f : MultilinearMap k M N)
    (p : ∀ i, PowerSeriesModule k (M i)) (n : ℕ) :
    coeffV n (applyMultilinear f p) =
      ∑ a ∈ Finset.piAntidiag Finset.univ n, f (fun i ↦ coeffV (a i) (p i)) := rfl

theorem applyMultilinear_series_smul_coord (f : MultilinearMap k M N)
    (p : ∀ i, PowerSeriesModule k (M i)) (i : ι) (a : PowerSeries k) :
    applyMultilinear f (Function.update p i (a • p i)) = a • applyMultilinear f p := by
  ext n
  simp only [coeffV_applyMultilinear, coeffV_series_smul]
  simp_rw [coeffV_update_input, coeffV_series_smul, f.map_update_sum, f.map_update_smul,
    ← coeffV_update_index, Finset.smul_sum]
  exact sum_piAntidiag_split
    (fun r b ↦ PowerSeries.coeff r a • f (fun j ↦ coeffV (b j) (p j))) n i

/-- Fixed multilinear operations extend over the full formal scalar ring. -/
def extendMultilinear (f : MultilinearMap k M N) :
    MultilinearMap (PowerSeries k) (fun i ↦ PowerSeriesModule k (M i)) (PowerSeriesModule k N) where
  toFun := applyMultilinear f
  map_update_add' p i x y := by
    ext n
    simp only [coeffV_add, coeffV_applyMultilinear, coeffV_update_input,
      f.map_update_add, Finset.sum_add_distrib]
  map_update_smul' p i a x := by
    have h := applyMultilinear_series_smul_coord f (Function.update p i x) i a
    convert h using 1
    congr 1
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [hj]

@[simp] theorem extendMultilinear_apply (f : MultilinearMap k M N)
    (p : ∀ i, PowerSeriesModule k (M i)) : extendMultilinear f p = applyMultilinear f p := rfl

theorem applyMultilinear_postcomp (f : MultilinearMap k M N) (g : N →ₗ[k] P)
    (p : ∀ i, PowerSeriesModule k (M i)) :
    map g (applyMultilinear f p) = applyMultilinear (g.compMultilinearMap f) p := by
  ext n
  simp only [coeffV_map, coeffV_applyMultilinear, map_sum, LinearMap.compMultilinearMap_apply]

theorem applyMultilinear_precomp {M' : ι → Type*}
    [∀ i, AddCommGroup (M' i)] [∀ i, Module k (M' i)]
    (f : MultilinearMap k M N) (g : ∀ i, M' i →ₗ[k] M i)
    (p : ∀ i, PowerSeriesModule k (M' i)) :
    applyMultilinear f (fun i ↦ map (g i) (p i)) = applyMultilinear (f.compLinearMap g) p := by
  ext n
  simp only [coeffV_applyMultilinear, coeffV_map, MultilinearMap.compLinearMap_apply]

end MultilinearConvolution

end PowerSeriesModule

end EnvelopingIsomorphism.FormalSeries
