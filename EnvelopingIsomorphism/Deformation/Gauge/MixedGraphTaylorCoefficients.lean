import EnvelopingIsomorphism.Deformation.Gauge.GraphTaylorCoefficients
import EnvelopingIsomorphism.Deformation.Gauge.TaylorLaurentEvaluation
import EnvelopingIsomorphism.Deformation.Gauge.Tangent
import EnvelopingIsomorphism.Deformation.Kontsevich.WeightNormalization
import EnvelopingIsomorphism.FormalSeries.LaurentBinaryComposition

/-! Actual graph coefficients with one distinguished polyvector input and any
number of bivector inputs. The distinguished input is always vertex zero.
The effective weight for n other inputs is the geometric weight divided by n!,
not by (n+1)!. The Laurent tangent data below twist only the bivector slots. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge.MixedGraphTaylorCoefficients

open MvPolynomial
open FormalSeries
open scoped BigOperators

variable {k : Type*} [CommRing k] {d n r : ℕ}

local instance unaryAddCommGroup : AddCommGroup (Unary k (MvPolynomial (Fin d) k)) :=
  @LinearMap.addCommGroup k k (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) k)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance (RingHom.id k)

local instance binaryAddCommGroup : AddCommGroup (Binary k (MvPolynomial (Fin d) k)) :=
  @LinearMap.addCommGroup k k (MvPolynomial (Fin d) k) (Unary k (MvPolynomial (Fin d) k))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance (RingHom.id k)

local instance ternaryAddCommGroup : AddCommGroup (Ternary k (MvPolynomial (Fin d) k)) :=
  @LinearMap.addCommGroup k k (MvPolynomial (Fin d) k) (Binary k (MvPolynomial (Fin d) k))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance (RingHom.id k)

/-- The coordinate tensor of an actual polyvector of any arity. -/
def coordinateTensor (r : ℕ) : Multiderivation k (MvPolynomial (Fin d) k) r →ₗ[k]
    KontsevichGraph.General.Tensor r d k where
  toFun F lab := F (fun i ↦ X (lab i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coordinateTensor_apply (r : ℕ)
    (F : Multiderivation k (MvPolynomial (Fin d) k) r) (lab : Fin r → Fin d) :
    coordinateTensor r F lab = F (fun i ↦ X (lab i)) := rfl

@[simp] theorem coordinateTensor_two : coordinateTensor (k := k) (d := d) 2 =
    GraphTaylorCoefficients.coordinateTensor := rfl

/-- An arity-r distinguished vertex followed by n ordinary bivector vertices. -/
abbrev arities (r n : ℕ) : Fin (n + 1) → ℕ := Fin.cons r (fun _ ↦ 2)

/-- These genuine general graphs have r external vertices as well. -/
abbrev Graph (r n : ℕ) := KontsevichGraph.General.Graph (arities r n) r

/-- Exchange a linear distinguished input with a finite multilinear input family. -/
def flipLinearMultilinear {A B C : Type*} [AddCommMonoid A] [Module k A]
    [AddCommMonoid B] [Module k B] [AddCommMonoid C] [Module k C]
    (f : A →ₗ[k] MultilinearMap k (fun _ : Fin n ↦ B) C) :
    MultilinearMap k (fun _ : Fin n ↦ B) (A →ₗ[k] C) where
  toFun b :=
    { toFun a := f a b
      map_add' a a' := congrArg (fun g : MultilinearMap k (fun _ : Fin n ↦ B) C ↦ g b) (f.map_add a a')
      map_smul' c a := congrArg (fun g : MultilinearMap k (fun _ : Fin n ↦ B) C ↦ g b) (f.map_smul c a) }
  map_update_add' b i x y := by
    apply LinearMap.ext
    intro a
    exact (f a).map_update_add b i x y
  map_update_smul' b i c x := by
    apply LinearMap.ext
    intro a
    exact (f a).map_update_smul b i c x

@[simp] theorem flipLinearMultilinear_apply {A B C : Type*}
    [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B]
    [AddCommMonoid C] [Module k C]
    (f : A →ₗ[k] MultilinearMap k (fun _ : Fin n ↦ B) C) (b : Fin n → B) (a : A) :
    flipLinearMultilinear f b a = f a b := rfl

/-- The actual graph contraction, retaining a linear distinguished-input slot. -/
def graphCoefficient (Γ : Graph r n) :
    MultilinearMap k (fun _ : Fin n ↦ Multiderivation k (MvPolynomial (Fin d) k) 2)
      (Multiderivation k (MvPolynomial (Fin d) k) r →ₗ[k] Cochain k (MvPolynomial (Fin d) k) r) :=
  flipLinearMultilinear (k := k) (n := n)
    (Γ.cochainOperator.compLinearMap (fun v ↦ coordinateTensor (arities r n v))).curryLeft

@[simp] theorem graphCoefficient_apply (Γ : Graph r n)
    (F : Fin n → Multiderivation k (MvPolynomial (Fin d) k) 2)
    (D : Multiderivation k (MvPolynomial (Fin d) k) r) :
    graphCoefficient Γ F D = Γ.cochainOperator
      (fun v ↦ coordinateTensor (arities r n v) ((Fin.cons D F : ∀ v, Multiderivation k (MvPolynomial (Fin d) k) (arities r n v)) v)) := rfl

/-- The finite effective graph sum with the distinguished input uncontracted. -/
def weightedCoefficient (s : Finset (Graph r n)) (w : Graph r n → k) :
    MultilinearMap k (fun _ : Fin n ↦ Multiderivation k (MvPolynomial (Fin d) k) 2)
      (Multiderivation k (MvPolynomial (Fin d) k) r →ₗ[k] Cochain k (MvPolynomial (Fin d) k) r) :=
  ∑ Γ ∈ s, w Γ • graphCoefficient Γ

@[simp] theorem weightedCoefficient_apply (s : Finset (Graph r n)) (w : Graph r n → k)
    (F : Fin n → Multiderivation k (MvPolynomial (Fin d) k) 2)
    (D : Multiderivation k (MvPolynomial (Fin d) k) r) :
    weightedCoefficient s w F D = ∑ Γ ∈ s, w Γ • graphCoefficient Γ F D := by
  simp only [weightedCoefficient, sum_apply, smul_apply, LinearMap.sum_apply, LinearMap.smul_apply]

/-- The full family is indexed by the number of bivectors; n=0 still contains
one actual distinguished vertex. It does not receive an artificial constant term. -/
def effectiveFamily (s : (n : ℕ) → Finset (Graph r n)) (w : (n : ℕ) → Graph r n → k) :
    GraphTaylorFamily (k := k) (V := Multiderivation k (MvPolynomial (Fin d) k) 2)
      (W := Multiderivation k (MvPolynomial (Fin d) k) r →ₗ[k] Cochain k (MvPolynomial (Fin d) k) r) :=
  fun n ↦ weightedCoefficient (s n) (w n)

/-- Genuine conversion of the external cochain representation, leaving every
input and weight untouched. -/
def mapOutput {O : Type*} [AddCommGroup O] [Module k O]
    (e : Cochain k (MvPolynomial (Fin d) k) r →ₗ[k] O)
    (s : (n : ℕ) → Finset (Graph r n)) (w : (n : ℕ) → Graph r n → k) :
    GraphTaylorFamily (k := k) (V := Multiderivation k (MvPolynomial (Fin d) k) 2)
      (W := Multiderivation k (MvPolynomial (Fin d) k) r →ₗ[k] O) :=
  fun n ↦ (LinearMap.llcomp k _ _ _ e).compMultilinearMap (effectiveFamily s w n)

@[simp] theorem mapOutput_apply {O : Type*} [AddCommGroup O] [Module k O]
    (e : Cochain k (MvPolynomial (Fin d) k) r →ₗ[k] O)
    (s : (n : ℕ) → Finset (Graph r n)) (w : (n : ℕ) → Graph r n → k) (n : ℕ)
    (F : Fin n → Multiderivation k (MvPolynomial (Fin d) k) 2)
    (D : Multiderivation k (MvPolynomial (Fin d) k) r) :
    mapOutput e s w n F D = e (effectiveFamily s w n F D) := rfl

/-- Velocity coefficients with their existing unary-cochain output. -/
def velocityFamily (s : (n : ℕ) → Finset (Graph 1 n)) (w : (n : ℕ) → Graph 1 n → k) :=
  mapOutput (d := d) (O := Unary k (MvPolynomial (Fin d) k)) (cochainOneEquiv k (MvPolynomial (Fin d) k)).toLinearMap s w

/-- Curvature coefficients with their existing ternary-cochain output. -/
def curvatureFamily (s : (n : ℕ) → Finset (Graph 3 n)) (w : (n : ℕ) → Graph 3 n → k) :=
  mapOutput (d := d) (O := Ternary k (MvPolynomial (Fin d) k)) (cochainThreeEquiv k (MvPolynomial (Fin d) k)).toLinearMap s w

section Normalization

variable [Algebra ℚ k]

/-- Normalize labelled geometric weights exactly once, for one distinguished
vertex and n additional bivector vertices. -/
def geometricFamily (s : (n : ℕ) → Finset (Graph r n))
    (W : (n : ℕ) → Graph r n → k) :=
  effectiveFamily (d := d) s (fun n Γ ↦ Kontsevich.distinguishedWeight (n + 1) (W n Γ))

theorem geometricFamily_apply (s : (n : ℕ) → Finset (Graph r n))
    (W : (n : ℕ) → Graph r n → k) (n : ℕ)
    (F : Fin n → Multiderivation k (MvPolynomial (Fin d) k) 2)
    (D : Multiderivation k (MvPolynomial (Fin d) k) r) :
    geometricFamily s W n F D =
      ∑ Γ ∈ s n, ((n.factorial : ℚ)⁻¹ • W n Γ) • graphCoefficient Γ F D := by
  exact weightedCoefficient_apply _ _ F D

end Normalization

section LaurentTwist

universe u
variable {K : Type u} [Field K]
variable {V D O : Type u} [AddCommGroup V] [Module K V]
  [AddCommGroup D] [Module K D] [AddCommGroup O] [Module K O]

/-- The zero-varying-slot h-coefficient operators, with all bivector inputs set
at the chosen base. The distinguished argument remains a genuine linear map. -/
def baseOperatorSeries (C : GraphTaylorFamily (k := K) (V := V) (W := D →ₗ[K] O)) (π₀ : V) :
    PowerSeriesModule K (D →ₗ[K] O) :=
  PowerSeriesModule.mk fun j ↦ C j (fun _ ↦ π₀)

/-- With zero varying slots the unique placement fixes every bivector at the base. -/
theorem placementComponent_zero_apply
    (C : GraphTaylorFamily (k := K) (V := V) (W := D →ₗ[K] O)) (π₀ : V) (m : ℕ) :
    placementComponent C π₀ 0 m Fin.elim0 = C m (fun _ ↦ π₀) := by
  classical
  letI : Unique {s : Finset (Fin m) // s.card = 0} :=
    { default := ⟨∅, rfl⟩
      uniq s := Subtype.ext (Finset.card_eq_zero.mp s.property) }
  have hempty : (Fin.elim0 : Fin 0 → V) = fun _ ↦ π₀ := funext fun i ↦ Fin.elim0 i
  rw [hempty, placementComponent_diagonal, Fintype.sum_unique]
  rfl

/-- Actual Laurent tangent data from placement coefficients. Only the bivector
slots are twisted; the distinguished Laurent input is evaluated by F4 linearApply. -/
def tangentFamily (C : GraphTaylorFamily (k := K) (V := V) (W := D →ₗ[K] O)) (π₀ : V) :
    TangentFamily (k := LaurentSeries K) (V₀ := LaurentModule K D)
      (V₁ := LaurentModule K V) (W₀ := LaurentModule K O) where
  linear := LaurentModule.linearApply (MiddleExactPerturbation.toLaurent (baseOperatorSeries C π₀))
  higher n := LaurentModule.linearApply.compMultilinearMap (laurentPlacementTaylorFamily C π₀ n)

@[simp] theorem tangentFamily_linear_apply
    (C : GraphTaylorFamily (k := K) (V := V) (W := D →ₗ[K] O)) (π₀ : V) (x : LaurentModule K D) :
    (tangentFamily C π₀).linear x =
      LaurentModule.linearApply (MiddleExactPerturbation.toLaurent (baseOperatorSeries C π₀)) x := rfl

@[simp] theorem tangentFamily_higher_apply
    (C : GraphTaylorFamily (k := K) (V := V) (W := D →ₗ[K] O)) (π₀ : V) (n : ℕ)
    (b : Fin (n + 1) → LaurentModule K V) (x : LaurentModule K D) :
    (tangentFamily C π₀).higher n b x =
      LaurentModule.linearApply (laurentPlacementTaylorFamily C π₀ n b) x := rfl

/-- The base operator has the prescribed actual nonnegative h coefficients. -/
@[simp] theorem coeff_baseOperatorSeries (C : GraphTaylorFamily (k := K) (V := V) (W := D →ₗ[K] O))
    (π₀ : V) (j : ℕ) :
    LaurentModule.coeff (MiddleExactPerturbation.toLaurent (baseOperatorSeries C π₀)) (j : ℤ) =
      C j (fun _ ↦ π₀) := MiddleExactPerturbation.coeff_toLaurent_nat _ _

/-- The actual higher operator uses precisely the finite placements among the
bivector slots; its extra h exponent is the number of base insertions. -/
@[simp] theorem coeff_higherOperatorSeries
    (C : GraphTaylorFamily (k := K) (V := V) (W := D →ₗ[K] O)) (π₀ : V) (n j : ℕ) :
    LaurentModule.coeff (MiddleExactPerturbation.toLaurent (placementOperatorCoefficients C π₀ n))
      (j : ℤ) = placementComponent C π₀ (n + 1) (n + 1 + j) :=
  MiddleExactPerturbation.coeff_toLaurent_nat _ _

local instance laurentMultiderivationAddCommGroup (r : ℕ) :
    AddCommGroup (LaurentModule K (Multiderivation K (MvPolynomial (Fin d) K) r)) :=
  @HahnModule.instAddCommGroup ℤ K (Multiderivation K (MvPolynomial (Fin d) K) r)
    inferInstance inferInstance inferInstance

local instance laurentUnaryAddCommGroup :
    AddCommGroup (LaurentModule K (Unary K (MvPolynomial (Fin d) K))) :=
  @HahnModule.instAddCommGroup ℤ K (Unary K (MvPolynomial (Fin d) K))
    inferInstance inferInstance inferInstance

local instance laurentTernaryAddCommGroup :
    AddCommGroup (LaurentModule K (Ternary K (MvPolynomial (Fin d) K))) :=
  @HahnModule.instAddCommGroup ℤ K (Ternary K (MvPolynomial (Fin d) K))
    inferInstance inferInstance inferInstance

local instance laurentMultiderivationModule (r : ℕ) :
    @Module (LaurentSeries K) (LaurentModule K (Multiderivation K (MvPolynomial (Fin d) K) r))
      inferInstance (laurentMultiderivationAddCommGroup (K := K) (d := d) r).toAddCommMonoid :=
  HahnModule.instModule (Γ := ℤ) (Γ' := ℤ) (R := K)
    (V := Multiderivation K (MvPolynomial (Fin d) K) r)

local instance laurentUnaryModule :
    @Module (LaurentSeries K) (LaurentModule K (Unary K (MvPolynomial (Fin d) K)))
      inferInstance (laurentUnaryAddCommGroup (K := K) (d := d)).toAddCommMonoid :=
  HahnModule.instModule (Γ := ℤ) (Γ' := ℤ) (R := K) (V := Unary K (MvPolynomial (Fin d) K))

local instance laurentTernaryModule :
    @Module (LaurentSeries K) (LaurentModule K (Ternary K (MvPolynomial (Fin d) K)))
      inferInstance (laurentTernaryAddCommGroup (K := K) (d := d)).toAddCommMonoid :=
  HahnModule.instModule (Γ := ℤ) (Γ' := ℤ) (R := K) (V := Ternary K (MvPolynomial (Fin d) K))

/-- Concrete velocity tangent coefficients obtained from the actual mixed graphs. -/
def velocityTangentFamily
    (s : (n : ℕ) → Finset (Graph 1 n)) (w : (n : ℕ) → Graph 1 n → K)
    (π₀ : Multiderivation K (MvPolynomial (Fin d) K) 2) :
    TangentFamily (k := LaurentSeries K)
      (V₀ := LaurentModule K (Multiderivation K (MvPolynomial (Fin d) K) 1))
      (V₁ := LaurentModule K (Multiderivation K (MvPolynomial (Fin d) K) 2))
      (W₀ := LaurentModule K (Unary K (MvPolynomial (Fin d) K))) :=
  tangentFamily (K := K) (V := Multiderivation K (MvPolynomial (Fin d) K) 2)
    (D := Multiderivation K (MvPolynomial (Fin d) K) 1)
    (O := Unary K (MvPolynomial (Fin d) K)) (velocityFamily s w) π₀

/-- Concrete curvature tangent coefficients obtained from the actual mixed graphs. -/
def curvatureTangentFamily
    (s : (n : ℕ) → Finset (Graph 3 n)) (w : (n : ℕ) → Graph 3 n → K)
    (π₀ : Multiderivation K (MvPolynomial (Fin d) K) 2) :
    TangentFamily (k := LaurentSeries K)
      (V₀ := LaurentModule K (Multiderivation K (MvPolynomial (Fin d) K) 3))
      (V₁ := LaurentModule K (Multiderivation K (MvPolynomial (Fin d) K) 2))
      (W₀ := LaurentModule K (Ternary K (MvPolynomial (Fin d) K))) :=
  tangentFamily (K := K) (V := Multiderivation K (MvPolynomial (Fin d) K) 2)
    (D := Multiderivation K (MvPolynomial (Fin d) K) 3)
    (O := Ternary K (MvPolynomial (Fin d) K)) (curvatureFamily s w) π₀

end LaurentTwist

end EnvelopingIsomorphism.Deformation.Gauge.MixedGraphTaylorCoefficients
