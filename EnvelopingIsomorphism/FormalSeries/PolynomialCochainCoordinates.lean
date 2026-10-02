import EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators
import EnvelopingIsomorphism.FormalSeries.CompletedBinaryComposition

/-!
# Genuine coordinate transport of polynomial cochains and completed families

Native multivariate polynomials are an `AddMonoidAlgebra` structure, while
monomial coordinates are finitely supported functions. All transport below
uses actual linear equivalences, including at both completion levels.
-/

noncomputable section

set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.FormalSeries.PolynomialCochainCoordinates

open EnvelopingIsomorphism.Deformation
open scoped BigOperators

namespace Transport

universe u v
variable {k : Type u} [CommRing k]
variable {V W : Type v} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

local instance unaryGroupV : AddCommGroup (Module.End k V) :=
  @LinearMap.addCommGroup k k V V inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance (RingHom.id k)
local instance unaryGroupW : AddCommGroup (Module.End k W) :=
  @LinearMap.addCommGroup k k W W inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance (RingHom.id k)

def unaryEquiv (e : V ≃ₗ[k] W) : Module.End k V ≃ₐ[k] Module.End k W := e.conjAlgEquiv k

def binaryEquiv (e : V ≃ₗ[k] W) : Binary k V ≃ₗ[k] Binary k W :=
  e.arrowCongr (e.arrowCongr e)

@[simp] theorem unaryEquiv_apply (e : V ≃ₗ[k] W) (f : Module.End k V) (x : W) :
    unaryEquiv e f x = e (f (e.symm x)) := rfl

@[simp] theorem binaryEquiv_apply (e : V ≃ₗ[k] W) (B : Binary k V) (x y : W) :
    binaryEquiv e B x y = e (B (e.symm x) (e.symm y)) := rfl

/-- Coefficientwise extension of a genuine linear equivalence to Laurent modules. -/
def laurentEquiv (e : V ≃ₗ[k] W) : LaurentModule k V ≃ₗ[LaurentSeries k] LaurentModule k W where
  __ := LaurentModule.map e.toLinearMap
  invFun := LaurentModule.map e.symm.toLinearMap
  left_inv x := by
    apply LaurentModule.ext
    intro j
    exact e.symm_apply_apply (LaurentModule.coeff x j)
  right_inv x := by
    apply LaurentModule.ext
    intro j
    exact e.apply_symm_apply (LaurentModule.coeff x j)

@[simp] theorem coeff_laurentEquiv (e : V ≃ₗ[k] W) (x : LaurentModule k V) (j : ℤ) :
    LaurentModule.coeff (laurentEquiv e x) j = e (LaurentModule.coeff x j) := rfl

/-- Coefficientwise extension through the outer vector-valued power series. -/
def seriesEquiv (e : V ≃ₗ[k] W) : PowerSeriesModule k V ≃ₗ[PowerSeries k] PowerSeriesModule k W where
  __ := PowerSeriesModule.map e.toLinearMap
  invFun := PowerSeriesModule.map e.symm.toLinearMap
  left_inv x := by
    apply PowerSeriesModule.ext
    intro n
    exact e.symm_apply_apply (PowerSeriesModule.coeffV n x)
  right_inv x := by
    apply PowerSeriesModule.ext
    intro n
    exact e.apply_symm_apply (PowerSeriesModule.coeffV n x)

@[simp] theorem coeff_seriesEquiv (e : V ≃ₗ[k] W) (x : PowerSeriesModule k V) (n : ℕ) :
    PowerSeriesModule.coeffV n (seriesEquiv e x) = e (PowerSeriesModule.coeffV n x) := rfl

def vectorEquiv (e : V ≃ₗ[k] W) :
    CompletedOperator.Vectors k V ≃ₗ[PowerSeries (LaurentSeries k)] CompletedOperator.Vectors k W :=
  seriesEquiv (laurentEquiv e)

def familyEquiv (e : V ≃ₗ[k] W) :
    CompletedBinary.Families k V ≃ₗ[PowerSeries (LaurentSeries k)] CompletedBinary.Families k W :=
  seriesEquiv (laurentEquiv (binaryEquiv e))

@[simp] theorem coeff_familyEquiv (e : V ≃ₗ[k] W) (B : CompletedBinary.Families k V)
    (n : ℕ) (j : ℤ) :
    LaurentModule.coeff (PowerSeriesModule.coeffV n (familyEquiv e B)) j =
      binaryEquiv e (LaurentModule.coeff (PowerSeriesModule.coeffV n B) j) := rfl

/-- Hahn coefficient transport is a ring homomorphism even for noncommutative coefficients. -/
def laurentRingMap {P Q : Type*} [Ring P] [Ring Q] (f : P →+* Q) :
    LaurentSeries P →+* LaurentSeries Q where
  toFun x := x.map f
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' x y := by ext; simp
  map_mul' x y := HahnSeries.map_mul f.toNonUnitalRingHom

def laurentOperatorEquiv (e : V ≃ₗ[k] W) :
    LaurentSeries (Module.End k V) ≃+* LaurentSeries (Module.End k W) where
  __ := laurentRingMap (unaryEquiv e).toRingHom
  invFun := laurentRingMap (unaryEquiv e).symm.toRingHom
  left_inv F := by
    apply HahnSeries.ext
    funext j
    exact (unaryEquiv e).symm_apply_apply (F.coeff j)
  right_inv F := by
    apply HahnSeries.ext
    funext j
    exact (unaryEquiv e).apply_symm_apply (F.coeff j)

@[simp] theorem coeff_laurentOperatorEquiv (e : V ≃ₗ[k] W)
    (F : LaurentSeries (Module.End k V)) (j : ℤ) :
    (laurentOperatorEquiv e F).coeff j = unaryEquiv e (F.coeff j) := rfl

/-- Genuine conjugation of the full two-parameter operator ring. -/
def operatorEquiv (e : V ≃ₗ[k] W) : CompletedOperator.Operators k V ≃+* CompletedOperator.Operators k W where
  __ := PowerSeries.map (laurentOperatorEquiv e).toRingHom
  invFun := PowerSeries.map (laurentOperatorEquiv e).symm.toRingHom
  left_inv F := by
    apply PowerSeries.ext
    intro n
    change PowerSeries.coeff n (PowerSeries.map (laurentOperatorEquiv e).symm.toRingHom
      (PowerSeries.map (laurentOperatorEquiv e).toRingHom F)) = _
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map]
    exact (laurentOperatorEquiv e).symm_apply_apply _
  right_inv F := by
    apply PowerSeries.ext
    intro n
    change PowerSeries.coeff n (PowerSeries.map (laurentOperatorEquiv e).toRingHom
      (PowerSeries.map (laurentOperatorEquiv e).symm.toRingHom F)) = _
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map]
    exact (laurentOperatorEquiv e).apply_symm_apply _

@[simp] theorem coeff_operatorEquiv (e : V ≃ₗ[k] W) (F : CompletedOperator.Operators k V)
    (n : ℕ) (j : ℤ) :
    (PowerSeries.coeff n (operatorEquiv e F)).coeff j = unaryEquiv e ((PowerSeries.coeff n F).coeff j) := by
  change (PowerSeries.coeff n (PowerSeries.map (laurentOperatorEquiv e).toRingHom F)).coeff j = _
  rw [PowerSeries.coeff_map]
  rfl

def unitMap (e : V ≃ₗ[k] W) : (CompletedOperator.Operators k V)ˣ →* (CompletedOperator.Operators k W)ˣ :=
  Units.map (operatorEquiv e).toMonoidHom

section BilinearNaturality

variable {X Y Z X' Y' Z' : Type v}
  [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y] [AddCommGroup Z] [Module k Z]
  [AddCommGroup X'] [Module k X'] [AddCommGroup Y'] [Module k Y'] [AddCommGroup Z'] [Module k Z']

/-- Naturality of the existing finite Laurent convolution, not a new convolution construction. -/
theorem laurent_map_bilinear_natural (f : X →ₗ[k] Y →ₗ[k] Z) (g : X' →ₗ[k] Y' →ₗ[k] Z')
    (a : X →ₗ[k] X') (b : Y →ₗ[k] Y') (c : Z →ₗ[k] Z')
    (h : ∀ x y, c (f x y) = g (a x) (b y)) (x : LaurentModule k X) (y : LaurentModule k Y) :
    LaurentModule.map c (LaurentModule.extendBilinear f x y) =
      LaurentModule.extendBilinear g (LaurentModule.map a x) (LaurentModule.map b y) := by
  rw [LaurentModule.extendBilinear_postcomp]
  apply LaurentModule.ext
  intro d
  rw [LaurentModule.coeff_extendBilinear, LaurentModule.coeff_extendBilinear]
  apply finsum_congr
  intro z
  simp only [LaurentModule.coeff_map, LinearMap.compr₂_apply]
  split_ifs
  · exact h _ _
  · rfl

/-- Naturality of the existing outer finite coefficient convolution. -/
theorem series_map_bilinear_natural (f : X →ₗ[k] Y →ₗ[k] Z) (g : X' →ₗ[k] Y' →ₗ[k] Z')
    (a : X →ₗ[k] X') (b : Y →ₗ[k] Y') (c : Z →ₗ[k] Z')
    (h : ∀ x y, c (f x y) = g (a x) (b y)) (x : PowerSeriesModule k X) (y : PowerSeriesModule k Y) :
    PowerSeriesModule.map c (PowerSeriesModule.applyBilinear f x y) =
      PowerSeriesModule.applyBilinear g (PowerSeriesModule.map a x) (PowerSeriesModule.map b y) := by
  apply PowerSeriesModule.ext
  intro n
  rw [PowerSeriesModule.coeffV_map, PowerSeriesModule.coeffV_applyBilinear,
    PowerSeriesModule.coeffV_applyBilinear, map_sum]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [PowerSeriesModule.coeffV_map, h]

end BilinearNaturality

open EnvelopingIsomorphism.Deformation.Gauge

theorem operatorCoefficients_transport (e : V ≃ₗ[k] W) (F : CompletedOperator.Operators k V) :
    LaurentConjugation.operatorCoefficients (operatorEquiv e F) =
      PowerSeriesModule.map (LaurentModule.map (unaryEquiv e).toLinearEquiv.toLinearMap)
        (LaurentConjugation.operatorCoefficients F) := by
  apply PowerSeriesModule.ext
  intro n
  apply LaurentModule.ext
  intro j
  change (PowerSeries.coeff n (operatorEquiv e F)).coeff j = _
  rw [coeff_operatorEquiv]
  rfl

theorem map_preLeftCoefficient (e : V ≃ₗ[k] W)
    (B : LaurentModule k (Binary k V)) (F : LaurentModule k (Module.End k V)) :
    LaurentModule.map (binaryEquiv e).toLinearMap (LaurentConjugation.preLeftCoefficient B F) =
      LaurentConjugation.preLeftCoefficient
        (LaurentModule.map (binaryEquiv e).toLinearMap B)
        (LaurentModule.map (unaryEquiv e).toLinearEquiv.toLinearMap F) := by
  apply laurent_map_bilinear_natural
  intro B F
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change e (B (F (e.symm x)) (e.symm y)) =
    e (B (e.symm (e (F (e.symm x)))) (e.symm y))
  rw [e.symm_apply_apply]

theorem map_flipBinarySeries (e : V ≃ₗ[k] W) (B : LaurentModule k (Binary k V)) :
    LaurentModule.map (binaryEquiv e).toLinearMap (LaurentModule.flipBinarySeries B) =
      LaurentModule.flipBinarySeries (LaurentModule.map (binaryEquiv e).toLinearMap B) := by
  apply LaurentModule.ext
  intro j
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rfl

private theorem postCoefficient_eq (F : LaurentModule k (Module.End k V))
    (B : LaurentModule k (Binary k V)) :
    LaurentConjugation.postCoefficient F B =
      LaurentModule.extendBilinear
        ((LinearMap.llcomp k V (Module.End k V) (Module.End k V)).comp
          (LinearMap.llcomp k V V V)) F B := by
  apply LaurentModule.ext
  intro j
  rfl

theorem map_postCoefficient (e : V ≃ₗ[k] W)
    (F : LaurentModule k (Module.End k V)) (B : LaurentModule k (Binary k V)) :
    LaurentModule.map (binaryEquiv e).toLinearMap (LaurentConjugation.postCoefficient F B) =
      LaurentConjugation.postCoefficient
        (LaurentModule.map (unaryEquiv e).toLinearEquiv.toLinearMap F)
        (LaurentModule.map (binaryEquiv e).toLinearMap B) := by
  rw [postCoefficient_eq, postCoefficient_eq]
  apply laurent_map_bilinear_natural
  intro F B
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change e (F (B (e.symm x) (e.symm y))) =
    e (F (e.symm (e (B (e.symm x) (e.symm y)))))
  rw [e.symm_apply_apply]

theorem familyEquiv_preLeft (e : V ≃ₗ[k] W) (B : CompletedBinary.Families k V)
    (F : CompletedOperator.Operators k V) :
    familyEquiv e (LaurentConjugation.preLeft B F) =
      LaurentConjugation.preLeft (familyEquiv e B) (operatorEquiv e F) := by
  change PowerSeriesModule.map (LaurentModule.map (binaryEquiv e).toLinearMap)
    (PowerSeriesModule.applyBilinear LaurentConjugation.preLeftCoefficient B
      (LaurentConjugation.operatorCoefficients F)) =
    PowerSeriesModule.applyBilinear LaurentConjugation.preLeftCoefficient
      (PowerSeriesModule.map (LaurentModule.map (binaryEquiv e).toLinearMap) B)
      (LaurentConjugation.operatorCoefficients (operatorEquiv e F))
  rw [operatorCoefficients_transport]
  apply series_map_bilinear_natural
  intro B F
  exact map_preLeftCoefficient e B F

theorem familyEquiv_flip (e : V ≃ₗ[k] W) (B : CompletedBinary.Families k V) :
    familyEquiv e (LaurentConjugation.flipCoefficients B) =
      LaurentConjugation.flipCoefficients (familyEquiv e B) := by
  apply PowerSeriesModule.ext
  intro n
  change LaurentModule.map (binaryEquiv e).toLinearMap
      (LaurentModule.flipBinarySeries (PowerSeriesModule.coeffV n B)) =
    LaurentModule.flipBinarySeries
      (LaurentModule.map (binaryEquiv e).toLinearMap (PowerSeriesModule.coeffV n B))
  exact map_flipBinarySeries e _

theorem familyEquiv_preRight (e : V ≃ₗ[k] W) (B : CompletedBinary.Families k V)
    (F : CompletedOperator.Operators k V) :
    familyEquiv e (LaurentConjugation.preRight B F) =
      LaurentConjugation.preRight (familyEquiv e B) (operatorEquiv e F) := by
  simp only [LaurentConjugation.preRight, familyEquiv_flip, familyEquiv_preLeft]

theorem familyEquiv_post (e : V ≃ₗ[k] W) (F : CompletedOperator.Operators k V)
    (B : CompletedBinary.Families k V) :
    familyEquiv e (LaurentConjugation.post F B) =
      LaurentConjugation.post (operatorEquiv e F) (familyEquiv e B) := by
  change PowerSeriesModule.map (LaurentModule.map (binaryEquiv e).toLinearMap)
    (PowerSeriesModule.applyBilinear LaurentConjugation.postCoefficient
      (LaurentConjugation.operatorCoefficients F) B) =
    PowerSeriesModule.applyBilinear LaurentConjugation.postCoefficient
      (LaurentConjugation.operatorCoefficients (operatorEquiv e F))
      (PowerSeriesModule.map (LaurentModule.map (binaryEquiv e).toLinearMap) B)
  rw [operatorCoefficients_transport]
  apply series_map_bilinear_natural
  intro F B
  exact map_postCoefficient e F B

/-- Genuine coordinate conjugation commutes with the actual closed Laurent gauge action. -/
theorem familyEquiv_conjugateFamily (e : V ≃ₗ[k] W)
    (G : (CompletedOperator.Operators k V)ˣ) (B : CompletedBinary.Families k V) :
    familyEquiv e (LaurentConjugation.conjugateFamily G B) =
      LaurentConjugation.conjugateFamily (unitMap e G) (familyEquiv e B) := by
  unfold LaurentConjugation.conjugateFamily
  rw [familyEquiv_post, familyEquiv_preRight, familyEquiv_preLeft]
  rfl

@[simp] theorem operatorEquiv_coeff (e : V ≃ₗ[k] W) (F : CompletedOperator.Operators k V) (n : ℕ) :
    PowerSeries.coeff n (operatorEquiv e F) = laurentOperatorEquiv e (PowerSeries.coeff n F) := by
  change PowerSeries.coeff n (PowerSeries.map (laurentOperatorEquiv e).toRingHom F) = _
  rw [PowerSeries.coeff_map]
  rfl

theorem nearIdentity_operatorEquiv (e : V ≃ₗ[k] W) {N : ℕ} {F : CompletedOperator.Operators k V}
    (hF : NearIdentity N F) : NearIdentity N (operatorEquiv e F) := by
  change toJet N (operatorEquiv e F) = 1
  rw [← map_one (toJet N), toJet_eq_iff]
  intro n hn
  rw [operatorEquiv_coeff, hF.coeff n hn, PowerSeries.coeff_one, PowerSeries.coeff_one]
  split_ifs <;> simp only [map_one, map_zero]

@[simp] theorem familyEquiv_symm_apply (e : V ≃ₗ[k] W) (B : CompletedBinary.Families k W) :
    (familyEquiv e).symm B = familyEquiv e.symm B := by
  apply PowerSeriesModule.ext
  intro n
  apply LaurentModule.ext
  intro j
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rfl

end Transport

variable {k : Type*} [CommRing k] {d : ℕ}

abbrev Poly (d : ℕ) (k : Type*) [CommRing k] := MvPolynomial (Fin d) k
abbrev Coords (d : ℕ) (k : Type*) [Zero k] := Rees.PolynomialCoefficientOperators.Coordinates (Fin d) k

/-- Pin the existing native unary additive group before forming polynomial binary cochains. -/
scoped instance polynomialUnaryGroup : AddCommGroup (Module.End k (Poly d k)) :=
  @LinearMap.addCommGroup k k (Poly d k) (Poly d k)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance (RingHom.id k)

scoped instance coordinateUnaryGroup : AddCommGroup (Module.End k (Coords d k)) :=
  @LinearMap.addCommGroup k k (Coords d k) (Coords d k)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance (RingHom.id k)

/-- Select the native outer Hahn additive group explicitly on completed polynomial cochains. -/
scoped instance polynomialFamilyGroup : AddCommGroup (CompletedBinary.Families k (Poly d k)) :=
  @HahnModule.instAddCommGroup ℕ (LaurentSeries k) (LaurentModule k (Binary k (Poly d k)))
    inferInstance inferInstance inferInstance

scoped instance coordinateFamilyGroup : AddCommGroup (CompletedBinary.Families k (Coords d k)) :=
  @HahnModule.instAddCommGroup ℕ (LaurentSeries k) (LaurentModule k (Binary k (Coords d k)))
    inferInstance inferInstance inferInstance

def coordinateEquiv : Poly d k ≃ₗ[k] Coords d k := (MvPolynomial.basisMonomials (Fin d) k).repr

def unaryCoordinates : Module.End k (Poly d k) ≃ₐ[k] Module.End k (Coords d k) :=
  Transport.unaryEquiv coordinateEquiv

def binaryCoordinates : Binary k (Poly d k) ≃ₗ[k] Binary k (Coords d k) :=
  Transport.binaryEquiv coordinateEquiv

theorem binaryCoordinates_apply (B : Binary k (Poly d k)) (p q : Poly d k) (m : Fin d →₀ ℕ) :
    binaryCoordinates B (coordinateEquiv p) (coordinateEquiv q) m = MvPolynomial.coeff m (B p q) := by
  simp only [binaryCoordinates, Transport.binaryEquiv_apply, LinearEquiv.symm_apply_apply]
  rfl

def laurentBinaryCoordinates : LaurentModule k (Binary k (Poly d k)) ≃ₗ[LaurentSeries k]
    LaurentModule k (Binary k (Coords d k)) := Transport.laurentEquiv binaryCoordinates

def familyCoordinates : CompletedBinary.Families k (Poly d k) ≃ₗ[PowerSeries (LaurentSeries k)]
    CompletedBinary.Families k (Coords d k) := Transport.familyEquiv coordinateEquiv

def operatorCoordinates : CompletedOperator.Operators k (Poly d k) ≃+*
    CompletedOperator.Operators k (Coords d k) := Transport.operatorEquiv coordinateEquiv

@[simp] theorem familyCoordinates_apply (B : CompletedBinary.Families k (Poly d k)) :
    familyCoordinates B = PowerSeriesModule.map
      (LaurentModule.map (k := k) (X := Binary k (Poly d k)) (Y := Binary k (Coords d k))
        binaryCoordinates.toLinearMap) B := rfl

theorem familyCoordinates_symm_apply (B : CompletedBinary.Families k (Coords d k)) :
    familyCoordinates.symm B = PowerSeriesModule.map
      (LaurentModule.map (k := k) (X := Binary k (Coords d k)) (Y := Binary k (Poly d k))
        binaryCoordinates.symm.toLinearMap) B := rfl

theorem familyCoordinates_coeff (B : CompletedBinary.Families k (Poly d k))
    (n : ℕ) (j : ℤ) (p q : Poly d k) (m : Fin d →₀ ℕ) :
    LaurentModule.coeff (PowerSeriesModule.coeffV n (familyCoordinates B)) j
      (coordinateEquiv p) (coordinateEquiv q) m =
        MvPolynomial.coeff m
          (LaurentModule.coeff (PowerSeriesModule.coeffV n B) j p q) := by
  change binaryCoordinates (LaurentModule.coeff (PowerSeriesModule.coeffV n B) j)
    (coordinateEquiv p) (coordinateEquiv q) m = _
  exact binaryCoordinates_apply _ p q m

def unitCoordinates : (CompletedOperator.Operators k (Poly d k))ˣ →*
    (CompletedOperator.Operators k (Coords d k))ˣ := Transport.unitMap coordinateEquiv

theorem familyCoordinates_conjugateFamily
    (G : (CompletedOperator.Operators k (Poly d k))ˣ) (B : CompletedBinary.Families k (Poly d k)) :
    familyCoordinates (k := k) (d := d)
      (Deformation.Gauge.LaurentConjugation.conjugateFamily (k := k) (A := Poly d k) G B) =
      Deformation.Gauge.LaurentConjugation.conjugateFamily (k := k) (A := Coords d k)
        (unitCoordinates (k := k) (d := d) G) (familyCoordinates (k := k) (d := d) B) :=
  Transport.familyEquiv_conjugateFamily (k := k) (V := Poly d k) (W := Coords d k)
    (coordinateEquiv (k := k) (d := d)) G B

end EnvelopingIsomorphism.FormalSeries.PolynomialCochainCoordinates
