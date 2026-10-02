import EnvelopingIsomorphism.Deformation.Koszul
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
import EnvelopingIsomorphism.Deformation.BarHochschild
import EnvelopingIsomorphism.Deformation.HKRCocycle
import Mathlib.Order.Hom.PowersetCard
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# The Koszul side of the polynomial HKR comparison

The polynomial Koszul resolution is proved in `Koszul.lean`. Here its dual
complex with diagonal coefficients is computed: the differential is zero and
the degree-`p` module has one coordinate per exterior monomial. The full
Hochschild comparison is developed separately from this computation.
-/

namespace EnvelopingIsomorphism.Deformation.HKR

noncomputable section

open CategoryTheory Limits
open Koszul

universe u
variable {R : Type u} [CommRing R]

/-- Polynomial-linear cochains on the Koszul resolution with diagonal coefficients. -/
abbrev KoszulCochain (R : Type u) [CommRing R] (n p : ℕ) :=
  polynomialTerm R n p →ₗ[coefficientRing R n] diagonal R n

/-- Coordinates of a Koszul cochain on the canonical exterior-monomial basis. -/
def koszulCoordinates (R : Type u) [CommRing R] (n p : ℕ) :
    KoszulCochain R n p ≃ₗ[R] (ExteriorIndex n p → diagonal R n) :=
  ((termBasis (R := R) n p).constr R).symm

@[simp] theorem koszulCoordinates_apply (n p : ℕ) (f : KoszulCochain R n p)
    (i : ExteriorIndex n p) : koszulCoordinates R n p f i = f (termBasis n p i) := rfl

/-- The actual differential induced by precomposition with the Koszul differential. -/
def koszulDifferential (n p : ℕ) :
    KoszulCochain R n p →ₗ[R] KoszulCochain R n (p + 1) where
  toFun f := f.comp (polynomialTermD n p)
  map_add' f g := by ext x; rfl
  map_smul' r f := by ext x; rfl

@[simp] theorem koszulDifferential_eq_zero (n p : ℕ) :
    koszulDifferential (R := R) n p = 0 := by
  ext f x
  exact LinearMap.congr_fun (hom_comp_d_eq_zero n p f) x

/-- The Koszul cochain complex, formed using the actual dual differential. -/
def koszulComplex (R : Type u) [CommRing R] (n : ℕ) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun p => ModuleCat.of _ (KoszulCochain R n p))
    (fun p => ModuleCat.ofHom (koszulDifferential n p)) (fun _ => by simp)

@[simp] theorem koszulComplex_d (n i j : ℕ) : (koszulComplex R n).d i j = 0 := by
  simp [koszulComplex, CochainComplex.of.d]
  rfl

/-- Koszul cohomology is its degreewise cochain module, since the dual differential vanishes. -/
def koszulHomologyIso (R : Type u) [CommRing R] (n p : ℕ) :
    (koszulComplex R n).homology p ≅ ModuleCat.of _ (KoszulCochain R n p) :=
  (ShortComplex.LeftHomologyData.ofZeros ((koszulComplex R n).sc p)
    (by simp [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor]; rfl)
    (by simp [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor]; rfl)).homologyIso

/-- Explicit exterior-monomial coordinates for the computed Koszul cohomology. -/
def koszulHomologyCoordinates (R : Type u) [CommRing R] (n p : ℕ) :
    (koszulComplex R n).homology p ≅ ModuleCat.of _ (ExteriorIndex n p → diagonal R n) :=
  koszulHomologyIso R n p ≪≫ (koszulCoordinates R n p).toModuleIso

instance koszulCochainFree (n p : ℕ) : Module.Free R (KoszulCochain R n p) :=
  .of_equiv (koszulCoordinates R n p).symm

instance koszulCochainFinite (n p : ℕ) : Module.Finite R (KoszulCochain R n p) :=
  Module.Finite.equiv (koszulCoordinates R n p).symm

theorem koszulCochain_finrank [Nontrivial R] (n p : ℕ) :
    Module.finrank R (KoszulCochain R n p) = n.choose p := by
  rw [(koszulCoordinates R n p).finrank_eq]
  change Module.finrank R (ExteriorIndex n p → R) = n.choose p
  rw [Module.finrank_fintype_fun_eq_card, exteriorIndex_card]

instance koszulHomologyFree (n p : ℕ) : Module.Free R ((koszulComplex R n).homology p) :=
  .of_equiv (koszulHomologyIso R n p).toLinearEquiv.symm

instance koszulHomologyFinite (n p : ℕ) : Module.Finite R ((koszulComplex R n).homology p) :=
  Module.Finite.equiv (koszulHomologyIso R n p).toLinearEquiv.symm

theorem koszulHomology_finrank [Nontrivial R] (n p : ℕ) :
    Module.finrank R ((koszulComplex R n).homology p) = n.choose p := by
  rw [(koszulHomologyIso R n p).toLinearEquiv.finrank_eq, koszulCochain_finrank]

/-- A split map between finite free modules of the same rank is an isomorphism.
This is over the coefficient ring itself; no finite-dimensionality over the
ground field is asserted for polynomial coefficient modules. -/
theorem bijective_of_split_of_finrank_eq [Nontrivial R]
    {V W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [Module.Free R V] [Module.Finite R V] [Module.Free R W] [Module.Finite R W]
    (i : V →ₗ[R] W) (p : W →ₗ[R] V) (hpi : p.comp i = LinearMap.id)
    (hrank : Module.finrank R V = Module.finrank R W) : Function.Bijective i := by
  obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hrank
  have hleft (v : V) : p (i v) = v := LinearMap.congr_fun hpi v
  have hsurj : Function.Surjective p := fun v => ⟨i v, hleft v⟩
  have hinj := Module.End.injective_of_surjective R V (f := p.comp e.toLinearMap)
    (hsurj.comp e.surjective)
  have hp : Function.Injective p := by
    intro x y hxy
    apply e.symm.injective
    apply hinj
    simpa using hxy
  refine ⟨fun x y hxy => ?_, fun w => ⟨p w, hp (hleft (p w))⟩⟩
  simpa only [hleft] using congrArg p hxy


section ExtComparison

open scoped ModuleCat.Algebra

/-- Degreewise identification of the categorical Hom complex with Koszul cochains. -/
def koszulYonedaTermEquiv (R : Type u) [CommRing R] (n p : ℕ) :
    ((polynomialComplex R n).linearYonedaObj R (diagonal R n)).X p ≃ₗ[R]
      KoszulCochain R n p where
  toFun f := f.hom
  invFun f := ModuleCat.ofHom (X := polynomialTerm R n p) (Y := diagonal R n) f
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r f := by
    ext x
    let y : R := f.hom x
    change coefficientEval n (algebraMap R (coefficientRing R n) r) * y = r * y
    rw [coefficientEval_algebraMap]

set_option backward.isDefEq.respectTransparency false in
theorem koszulYoneda_d (n i j : ℕ) :
    ((polynomialComplex R n).linearYonedaObj R (diagonal R n)).d i j = 0 := by
  apply ModuleCat.hom_ext
  ext f
  apply ModuleCat.hom_ext
  ext x
  change f.hom (((polynomialComplex R n).d j i).hom x) = 0
  by_cases h : j = i + 1
  · subst j
    rw [show (polynomialComplex R n).d (i + 1) i =
      ModuleCat.ofHom (polynomialTermD (R := R) n i) by
        simp [polynomialComplex, ChainComplex.of.d]]
    exact LinearMap.congr_fun (hom_comp_d_eq_zero n i f.hom) x
  · simp [polynomialComplex, ChainComplex.of.d, h]

/-- The Hom complex of the actual Koszul resolution is the explicitly computed dual complex. -/
def koszulYonedaIso (R : Type u) [CommRing R] (n : ℕ) :
    (polynomialComplex R n).linearYonedaObj R (diagonal R n) ≅ koszulComplex R n :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (koszulYonedaTermEquiv R n p).toModuleIso)
    (fun i j _ => by rw [koszulYoneda_d, koszulComplex_d, comp_zero, zero_comp])

/-- The computed `Ext` module of the polynomial diagonal, over its coefficient ring. -/
def koszulExtCoordinates (R : Type u) [CommRing R] (n p : ℕ) :
    ((Ext R (ModuleCat (coefficientRing R n)) p).obj (Opposite.op (diagonal R n))).obj
      (diagonal R n) ≅ ModuleCat.of R (ExteriorIndex n p → diagonal R n) :=
  (resolution R n).isoExt p (diagonal R n) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) p).mapIso
      (koszulYonedaIso R n) ≪≫ koszulHomologyCoordinates R n p

end ExtComparison

section FunctorComparison

variable {C D : Type*} [Category C] [Abelian C] [Linear R C]
  [Category D] [Abelian D] [Linear R D]

/-- A linear fully faithful functor preserves the Hom cochain complex. -/
def yonedaMapIso (F : C ⥤ D) [F.Additive] [F.Linear R] [F.Full] [F.Faithful]
    (X : ChainComplex C ℕ) (Y : C) :
    X.linearYonedaObj R Y ≅
      ChainComplex.linearYonedaObj ((F.mapHomologicalComplex _).obj X) R (F.obj Y) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (LinearEquiv.ofBijective (F.mapLinearMap R)
      ((Functor.FullyFaithful.ofFullyFaithful F).map_bijective (X.X p) Y)).toModuleIso)
    (fun i j _ => by
      apply ModuleCat.hom_ext
      ext f
      simp only [ChainComplex.linearYonedaObj_d]
      change F.map (X.d j i) ≫ F.map f = F.map (X.d j i ≫ f)
      exact (F.map_comp _ _).symm)

/-- Changing the coefficient target by an isomorphism changes the Hom complex by an isomorphism. -/
def yonedaTargetIso (X : ChainComplex C ℕ) {Y Z : C} (e : Y ≅ Z) :
    X.linearYonedaObj R Y ≅ X.linearYonedaObj R Z :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (CategoryTheory.Linear.homCongr R (Iso.refl (X.X p)) e).toModuleIso)
    (fun i j _ => by
      apply ModuleCat.hom_ext
      ext f
      simp only [ChainComplex.linearYonedaObj_d]
      change X.d j i ≫ ((𝟙 _ ≫ f) ≫ e.hom) = (𝟙 _ ≫ (X.d j i ≫ f)) ≫ e.hom
      simp only [Category.id_comp, Category.assoc])

end FunctorComparison

section PolynomialComparison

open scoped TensorProduct ModuleCat.Algebra EnvelopingIsomorphism.Deformation.Bar.OverAlgebra

variable (K : Type u) [Field K]

/-- The coefficient-linear Hom complex of the Koszul resolution over `A ⊗ A`. -/
def envelopingKoszulYonedaIso (n : ℕ) :
    (directEnvelopingResolution K n).complex.linearYonedaObj (MvPolynomial (Fin n) K)
      (envelopingDiagonal K n) ≅ koszulComplex (MvPolynomial (Fin n) K) n := by
  let A := MvPolynomial (Fin n) K
  let F := ModuleCat.restrictScalars
    (coefficientEnvelopingAlgEquiv K n).symm.toAlgHom.toRingHom
  haveI : F.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
    (coefficientEnvelopingAlgEquiv K n).symm.toRingEquiv
  let X := polynomialComplex A n
  let Y := diagonal A n
  exact (yonedaTargetIso (R := A) ((F.mapHomologicalComplex _).obj X)
      (directEnvelopingDiagonalIso K n)).symm ≪≫
    (yonedaMapIso (R := A) F X Y).symm ≪≫ koszulYonedaIso A n

/-- The full Hochschild cohomology of a polynomial algebra is the computed
Koszul cohomology, as a module over the polynomial algebra itself. -/
def hochschildKoszulHomologyIso (n p : ℕ) :
    (Bar.OverAlgebra.barComplexOverA K (MvPolynomial (Fin n) K)).homology p ≅
      (koszulComplex (MvPolynomial (Fin n) K) n).homology p := by
  let A := MvPolynomial (Fin n) K
  let H := HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.up ℕ) p
  exact (H.mapIso (Bar.OverAlgebra.hochschildComplexIsoOverA K A)).symm ≪≫
    ((Bar.resolution K A).isoExt (R := A) p (Bar.diagonal K A)).symm ≪≫
    (directEnvelopingResolution K n).isoExt (R := A) p (envelopingDiagonal K n) ≪≫
    H.mapIso (envelopingKoszulYonedaIso K n)

instance hochschildHomologyFree (n p : ℕ) :
    Module.Free (MvPolynomial (Fin n) K)
      ((Bar.OverAlgebra.barComplexOverA K (MvPolynomial (Fin n) K)).homology p) :=
  .of_equiv (hochschildKoszulHomologyIso K n p).toLinearEquiv.symm

instance hochschildHomologyFinite (n p : ℕ) :
    Module.Finite (MvPolynomial (Fin n) K)
      ((Bar.OverAlgebra.barComplexOverA K (MvPolynomial (Fin n) K)).homology p) :=
  Module.Finite.equiv (hochschildKoszulHomologyIso K n p).toLinearEquiv.symm

theorem hochschildHomology_finrank (n p : ℕ) :
    Module.finrank (MvPolynomial (Fin n) K)
      ((Bar.OverAlgebra.barComplexOverA K (MvPolynomial (Fin n) K)).homology p) = n.choose p := by
  rw [(hochschildKoszulHomologyIso K n p).toLinearEquiv.finrank_eq, koszulHomology_finrank]

end PolynomialComparison

section CoefficientLinearHKR

variable (K : Type u) [Field K] {n p : ℕ}

/-- Coordinate HKR is linear over the polynomial coefficient algebra. -/
def coordinateHKROverA (u : Fin p → Fin n) :
    MvPolynomial (Fin n) K →ₗ[MvPolynomial (Fin n) K]
      Cochain K (MvPolynomial (Fin n) K) p where
  toFun f := coordinateHKR f u
  map_add' f g := (coordinateHKRLinearMap u).map_add f g
  map_smul' a f := by
    apply MultilinearMap.ext
    intro x
    simp only [coordinateHKR, hkrCochain_apply, smul_apply, smul_eq_mul, mul_assoc]
    simp only [Algebra.smul_def, RingHom.id_apply]
    ring

@[simp] theorem coordinateHKR_zero (u : Fin p → Fin n) :
    coordinateHKR (0 : MvPolynomial (Fin n) K) u = 0 :=
  (coordinateHKRLinearMap u).map_zero

/-- Alternating evaluation is likewise linear over the coefficient algebra. -/
def alternatingEvaluationOverA (a : Fin p → MvPolynomial (Fin n) K) :
    Cochain K (MvPolynomial (Fin n) K) p →ₗ[MvPolynomial (Fin n) K]
      MvPolynomial (Fin n) K where
  toFun f := alternatingEvaluation f a
  map_add' f g := (alternatingEvaluationLinearMap a).map_add f g
  map_smul' r f := by
    simp only [alternatingEvaluation_apply, smul_apply, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    exact smul_comm (Equiv.Perm.sign σ) r _

variable {ι : Type*} [Fintype ι]

/-- A finite sum of the normalized HKR maps on coordinate exterior monomials. -/
def coordinateFamilyHKR (u : ι → Fin p → Fin n) :
    (ι → MvPolynomial (Fin n) K) →ₗ[MvPolynomial (Fin n) K]
      Cochain K (MvPolynomial (Fin n) K) p :=
  ∑ i, (coordinateHKROverA K (u i)).comp (LinearMap.proj i)

/-- Alternating coordinate evaluations, one for each exterior monomial. -/
def coordinateFamilyEvaluation (u : ι → Fin p → Fin n) :
    Cochain K (MvPolynomial (Fin n) K) p →ₗ[MvPolynomial (Fin n) K]
      (ι → MvPolynomial (Fin n) K) :=
  LinearMap.pi fun i => alternatingEvaluationOverA K (fun j => MvPolynomial.X (u i j))

@[simp] theorem coordinateFamilyHKR_apply (u : ι → Fin p → Fin n)
    (f : ι → MvPolynomial (Fin n) K) :
    coordinateFamilyHKR K u f = ∑ i, coordinateHKR (f i) (u i) := by
  simp [coordinateFamilyHKR, coordinateHKROverA]

theorem coordinateFamilyHKR_single (u : ι → Fin p → Fin n) (i : ι)
    (a : MvPolynomial (Fin n) K) [DecidableEq ι] :
    coordinateFamilyHKR K u (Pi.single i a) = coordinateHKR a (u i) := by
  rw [coordinateFamilyHKR_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

omit [Fintype ι] in
@[simp] theorem coordinateFamilyEvaluation_apply (u : ι → Fin p → Fin n)
    (f : Cochain K (MvPolynomial (Fin n) K) p) (i : ι) :
    coordinateFamilyEvaluation K u f i =
      alternatingEvaluation f (fun j => MvPolynomial.X (u i j)) := rfl

theorem coordinateFamilyHKR_cocycle (u : ι → Fin p → Fin n)
    (f : ι → MvPolynomial (Fin n) K) :
    Bar.OverAlgebra.barDifferentialOverA K (MvPolynomial (Fin n) K) p
      (coordinateFamilyHKR K u f) = 0 := by
  rw [Bar.OverAlgebra.barDifferentialOverA_apply, coordinateFamilyHKR_apply, map_sum]
  simp only [barDifferential_coordinateHKR, Finset.sum_const_zero]

omit [Fintype ι] in
theorem coordinateFamilyEvaluation_boundary (u : ι → Fin (p + 1) → Fin n)
    (f : Cochain K (MvPolynomial (Fin n) K) p) :
    coordinateFamilyEvaluation K u
      (Bar.OverAlgebra.barDifferentialOverA K (MvPolynomial (Fin n) K) p f) = 0 := by
  apply funext
  intro i
  rw [coordinateFamilyEvaluation_apply, Bar.OverAlgebra.barDifferentialOverA_apply]
  exact alternatingEvaluation_barDifferential p f _

end CoefficientLinearHKR

section CoordinateComplex

open scoped TensorProduct

variable (K : Type u) [Field K]

/-- Polynomial polyvectors in exterior-monomial coordinates. -/
abbrev CoordinatePolyvector (n p : ℕ) :=
  Set.powersetCard (Fin n) p → MvPolynomial (Fin n) K

/-- The increasing list of indices of an exterior monomial. -/
def exteriorTuple {n p : ℕ} (s : Set.powersetCard (Fin n) p) : Fin p → Fin n :=
  Set.powersetCard.ofFinEmbEquiv.symm s

theorem exteriorTuple_injective {n p : ℕ} (s : Set.powersetCard (Fin n) p) :
    Function.Injective (exteriorTuple s) :=
  (Set.powersetCard.ofFinEmbEquiv.symm s).injective

/-- The zero-differential complex of polynomial polyvectors in coordinates. -/
def coordinatePolyvectorComplex (n : ℕ) :
    CochainComplex (ModuleCat.{u} (MvPolynomial (Fin n) K)) ℕ :=
  CochainComplex.of (fun p => ModuleCat.of _ (CoordinatePolyvector K n p))
    (fun _ => 0) (fun _ => by simp)

@[simp] theorem coordinatePolyvectorComplex_d (n i j : ℕ) :
    (coordinatePolyvectorComplex K n).d i j = 0 := by
  simp [coordinatePolyvectorComplex, CochainComplex.of.d]; rfl

/-- The normalized coordinate HKR morphism into all Hochschild cochains. -/
def polynomialHKR (n : ℕ) :
    coordinatePolyvectorComplex K n ⟶ Bar.OverAlgebra.barComplexOverA K (MvPolynomial (Fin n) K) where
  f p := ModuleCat.ofHom (coordinateFamilyHKR K (exteriorTuple (n := n) (p := p)))
  comm' i j h := by
    rcases h with (rfl : i + 1 = j)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    simp only [coordinatePolyvectorComplex_d, zero_comp, Bar.OverAlgebra.barComplexOverA,
      CochainComplex.of.d]
    change Bar.OverAlgebra.barDifferentialOverA K (MvPolynomial (Fin n) K) i
      (coordinateFamilyHKR K (exteriorTuple (n := n) (p := i)) f) = 0
    exact coordinateFamilyHKR_cocycle K _ f

/-- Alternating evaluation on coordinate generators as a morphism of complexes. -/
def polynomialAlternatingEvaluation (n : ℕ) :
    Bar.OverAlgebra.barComplexOverA K (MvPolynomial (Fin n) K) ⟶ coordinatePolyvectorComplex K n where
  f p := ModuleCat.ofHom (coordinateFamilyEvaluation K (exteriorTuple (n := n) (p := p)))
  comm' i j h := by
    rcases h with (rfl : i + 1 = j)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    simp only [coordinatePolyvectorComplex_d, comp_zero, Bar.OverAlgebra.barComplexOverA,
      CochainComplex.of.d]
    change 0 = coordinateFamilyEvaluation K (exteriorTuple (n := n) (p := i + 1))
      (Bar.OverAlgebra.barDifferentialOverA K (MvPolynomial (Fin n) K) i f)
    exact (coordinateFamilyEvaluation_boundary K _ f).symm

/-- The cohomology of the coordinate polyvector complex is its coefficient module. -/
def coordinatePolyvectorHomologyIso (n p : ℕ) :
    (coordinatePolyvectorComplex K n).homology p ≅ ModuleCat.of _ (CoordinatePolyvector K n p) :=
  (ShortComplex.LeftHomologyData.ofZeros ((coordinatePolyvectorComplex K n).sc p)
    (by simp [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor]; rfl)
    (by simp [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor]; rfl)).homologyIso

instance coordinatePolyvectorHomologyFree (n p : ℕ) :
    Module.Free (MvPolynomial (Fin n) K) ((coordinatePolyvectorComplex K n).homology p) :=
  .of_equiv (coordinatePolyvectorHomologyIso K n p).toLinearEquiv.symm

instance coordinatePolyvectorHomologyFinite (n p : ℕ) :
    Module.Finite (MvPolynomial (Fin n) K) ((coordinatePolyvectorComplex K n).homology p) :=
  Module.Finite.equiv (coordinatePolyvectorHomologyIso K n p).toLinearEquiv.symm

theorem coordinatePolyvectorHomology_finrank (n p : ℕ) :
    Module.finrank (MvPolynomial (Fin n) K) ((coordinatePolyvectorComplex K n).homology p) =
      n.choose p := by
  rw [(coordinatePolyvectorHomologyIso K n p).toLinearEquiv.finrank_eq]
  change Module.finrank (MvPolynomial (Fin n) K)
    (Set.powersetCard (Fin n) p → MvPolynomial (Fin n) K) = n.choose p
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_eq_nat_card, Set.powersetCard.card]
  simp

/-- Alternating evaluation is a left inverse to the complete normalized HKR map. -/
theorem coordinateFamily_split [CharZero K] (n p : ℕ) (f : CoordinatePolyvector K n p) :
    coordinateFamilyEvaluation K (exteriorTuple (n := n) (p := p))
      (coordinateFamilyHKR K (exteriorTuple (n := n) (p := p)) f) = f := by
  classical
  funext t
  change alternatingEvaluationOverA K (fun j => MvPolynomial.X (exteriorTuple t j))
    (coordinateFamilyHKR K (exteriorTuple (n := n) (p := p)) f) = f t
  rw [coordinateFamilyHKR_apply, map_sum, Finset.sum_eq_single t]
  · exact alternatingEvaluation_coordinateHKR_self (f t) (exteriorTuple t) (exteriorTuple_injective t)
  · intro s _ hst
    exact alternatingEvaluation_coordinateHKR_powersetCard_ne (f s) s t hst
  · simp

theorem polynomialHKR_comp_alternatingEvaluation [CharZero K] (n : ℕ) :
    polynomialHKR K n ≫ polynomialAlternatingEvaluation K n = 𝟙 (coordinatePolyvectorComplex K n) := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact coordinateFamily_split K n p f

set_option backward.isDefEq.respectTransparency false in
/-- Polynomial HKR is a quasi-isomorphism into the full Hochschild complex.
The proof uses the actual bar and Koszul projective resolutions, their
coefficient-linear cohomology comparison, and the explicit HKR retraction. -/
instance polynomialHKR_quasiIso [CharZero K] (n : ℕ) : QuasiIso (polynomialHKR K n) := by
  constructor
  intro p
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  apply bijective_of_split_of_finrank_eq
    (HomologicalComplex.homologyMap (polynomialHKR K n) p).hom
    (HomologicalComplex.homologyMap (polynomialAlternatingEvaluation K n) p).hom
  · have h : HomologicalComplex.homologyMap (polynomialHKR K n) p ≫
        HomologicalComplex.homologyMap (polynomialAlternatingEvaluation K n) p =
        𝟙 ((coordinatePolyvectorComplex K n).homology p) := by
      rw [← HomologicalComplex.homologyMap_comp, polynomialHKR_comp_alternatingEvaluation,
        HomologicalComplex.homologyMap_id]
    exact congrArg ModuleCat.Hom.hom h
  · rw [coordinatePolyvectorHomology_finrank, hochschildHomology_finrank]

end CoordinateComplex

section ExteriorPolyvectors

variable (K : Type u) [Field K]

/-- Polynomial vector fields are exactly polynomial tuples of coordinate partial derivatives. -/
def polynomialVectorFieldEquiv (n : ℕ) :
    (Fin n → MvPolynomial (Fin n) K) ≃ₗ[MvPolynomial (Fin n) K]
      Derivation K (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K) where
  toEquiv := (MvPolynomial.mkDerivationEquiv K).toEquiv
  map_add' := (MvPolynomial.mkDerivationEquiv K).map_add
  map_smul' a f := by
    apply MvPolynomial.derivation_ext
    intro i
    change MvPolynomial.mkDerivation K (a • f) (MvPolynomial.X i) =
      a • MvPolynomial.mkDerivation K f (MvPolynomial.X i)
    simp [MvPolynomial.mkDerivation_X]

/-- The coordinate partial derivatives form a basis over the polynomial algebra. -/
def polynomialVectorFieldBasis (n : ℕ) :
    Module.Basis (Fin n) (MvPolynomial (Fin n) K)
      (Derivation K (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K)) :=
  (Pi.basisFun (MvPolynomial (Fin n) K) (Fin n)).map (polynomialVectorFieldEquiv K n)

theorem polynomialVectorFieldBasis_apply (n : ℕ) (i : Fin n) :
    polynomialVectorFieldBasis K n i = MvPolynomial.pderiv i := by
  apply MvPolynomial.derivation_ext
  intro j
  change MvPolynomial.mkDerivation K
    ((Pi.basisFun (MvPolynomial (Fin n) K) (Fin n)) i) (MvPolynomial.X j) =
      MvPolynomial.pderiv i (MvPolynomial.X j)
  rw [MvPolynomial.mkDerivation_X, MvPolynomial.pderiv_X]
  simp [Pi.basisFun_apply, Pi.single_apply, eq_comm]

/-- Polynomial polyvectors, using Mathlib's actual exterior power of derivations. -/
abbrev Polyvector (n p : ℕ) :=
  ⋀[MvPolynomial (Fin n) K]^p
    (Derivation K (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K))

def polyvectorCoordinates (n p : ℕ) :
    Polyvector K n p ≃ₗ[MvPolynomial (Fin n) K] CoordinatePolyvector K n p :=
  ((polynomialVectorFieldBasis K n).exteriorPower p).equivFun

/-- The ordinary zero-differential complex of polynomial polyvector fields. -/
def polyvectorComplex (n : ℕ) : CochainComplex (ModuleCat.{u} (MvPolynomial (Fin n) K)) ℕ :=
  CochainComplex.of (fun p => ModuleCat.of _ (Polyvector K n p)) (fun _ => 0) (fun _ => by simp)

@[simp] theorem polyvectorComplex_d (n i j : ℕ) : (polyvectorComplex K n).d i j = 0 := by
  simp [polyvectorComplex, CochainComplex.of.d]; rfl

def polyvectorCoordinatesIso (n : ℕ) : polyvectorComplex K n ≅ coordinatePolyvectorComplex K n :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (polyvectorCoordinates K n p).toModuleIso)
    (fun i j _ => by rw [polyvectorComplex_d, coordinatePolyvectorComplex_d, comp_zero, zero_comp])

/-- HKR from actual polynomial polyvectors to the full Hochschild complex. -/
def hkr (n : ℕ) :
    polyvectorComplex K n ⟶ Bar.OverAlgebra.barComplexOverA K (MvPolynomial (Fin n) K) :=
  (polyvectorCoordinatesIso K n).hom ≫ polynomialHKR K n

@[simp] theorem hkr_f_apply (n p : ℕ) (v : Polyvector K n p) :
    (hkr K n).f p v =
      coordinateFamilyHKR K (exteriorTuple (n := n) (p := p)) (polyvectorCoordinates K n p v) := rfl

/-- On every exterior basis monomial, this map is the factorial-normalized HKR formula. -/
theorem hkr_f_apply_basis (n p : ℕ) (s : Set.powersetCard (Fin n) p)
    (a : MvPolynomial (Fin n) K) :
    (hkr K n).f p (a • (polynomialVectorFieldBasis K n).exteriorPower p s) =
      coordinateHKR a (exteriorTuple s) := by
  classical
  rw [hkr_f_apply]
  have hc : polyvectorCoordinates K n p (a • (polynomialVectorFieldBasis K n).exteriorPower p s) =
      Pi.single s a := by
    funext t
    change ((polynomialVectorFieldBasis K n).exteriorPower p).equivFun
      (a • (polynomialVectorFieldBasis K n).exteriorPower p s) t =
        (Pi.single s a : Set.powersetCard (Fin n) p → MvPolynomial (Fin n) K) t
    simp only [map_smul, Pi.smul_apply, Module.Basis.equivFun_self, Pi.single_apply, smul_eq_mul]
    by_cases h : s = t <;> simp [h, eq_comm]
  rw [hc, coordinateFamilyHKR_single]

/-- HKR from the exterior powers of polynomial derivations to all Hochschild cochains is a quasi-isomorphism. -/
instance hkr_quasiIso [CharZero K] (n : ℕ) : QuasiIso (hkr K n) := by
  dsimp [hkr]
  infer_instance

/-- The explicit coefficient-linear retraction of HKR. -/
def hkrRetraction (n : ℕ) :
    Bar.OverAlgebra.barComplexOverA K (MvPolynomial (Fin n) K) ⟶ polyvectorComplex K n :=
  polynomialAlternatingEvaluation K n ≫ (polyvectorCoordinatesIso K n).inv

theorem hkr_comp_retraction [CharZero K] (n : ℕ) :
    hkr K n ≫ hkrRetraction K n = 𝟙 (polyvectorComplex K n) := by
  simp only [hkr, hkrRetraction, Category.assoc]
  rw [← Category.assoc (polynomialHKR K n), polynomialHKR_comp_alternatingEvaluation,
    Category.id_comp, Iso.hom_inv_id]

/-- HKR is the identity on functions, i.e. on cochain arity zero. -/
theorem hkr_arity_zero (n : ℕ) (a : MvPolynomial (Fin n) K) :
    (hkr K n).f 0
      ((exteriorPower.zeroEquiv (MvPolynomial (Fin n) K)
        (Derivation K (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K))).symm a) =
      (cochainZeroEquiv K (MvPolynomial (Fin n) K)).symm a := by
  let s : Set.powersetCard (Fin n) 0 := ⟨∅, rfl⟩
  have h0 : (exteriorPower.zeroEquiv (MvPolynomial (Fin n) K)
      (Derivation K (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K))).symm a =
      a • (polynomialVectorFieldBasis K n).exteriorPower 0 s := by
    apply (exteriorPower.zeroEquiv (MvPolynomial (Fin n) K)
      (Derivation K (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K))).injective
    simp [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  rw [h0, hkr_f_apply_basis]
  exact hkrCochain_zero a _

/-- The same polyvector complex regarded over the original ground field. -/
def polyvectorComplexOverK (n : ℕ) : CochainComplex (ModuleCat.{u} K) ℕ :=
  ((ModuleCat.restrictScalars (algebraMap K (MvPolynomial (Fin n) K))).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (polyvectorComplex K n)

/-- Polynomial HKR into the original full `K`-multilinear Hochschild complex. -/
def hkrOverK (n : ℕ) :
    polyvectorComplexOverK K n ⟶
      barComplex (LinearMap.mul K (MvPolynomial (Fin n) K)) (fun a b c => mul_assoc a b c) :=
  ((ModuleCat.restrictScalars (algebraMap K (MvPolynomial (Fin n) K))).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (hkr K n) ≫
      (Bar.OverAlgebra.restrictComplexIso K (MvPolynomial (Fin n) K)).hom

@[simp] theorem hkrOverK_f_apply (n p : ℕ) (v : (polyvectorComplexOverK K n).X p) :
    (hkrOverK K n).f p v = (hkr K n).f p (show Polyvector K n p from v) := rfl

/-- The same explicit retraction over the ground field. -/
def hkrRetractionOverK (n : ℕ) :
    barComplex (LinearMap.mul K (MvPolynomial (Fin n) K)) (fun a b c => mul_assoc a b c) ⟶
      polyvectorComplexOverK K n :=
  (Bar.OverAlgebra.restrictComplexIso K (MvPolynomial (Fin n) K)).inv ≫
    ((ModuleCat.restrictScalars (algebraMap K (MvPolynomial (Fin n) K))).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (hkrRetraction K n)

set_option backward.isDefEq.respectTransparency false in
theorem hkrOverK_comp_retraction [CharZero K] (n : ℕ) :
    hkrOverK K n ≫ hkrRetractionOverK K n = 𝟙 (polyvectorComplexOverK K n) := by
  simp only [hkrOverK, hkrRetractionOverK, Category.assoc, Iso.hom_inv_id_assoc]
  dsimp [polyvectorComplexOverK]
  rw [← CategoryTheory.Functor.map_comp, hkr_comp_retraction, CategoryTheory.Functor.map_id]

/-- The full-ground-field formulation of polynomial HKR, including arity zero. -/
instance hkrOverK_quasiIso [CharZero K] (n : ℕ) : QuasiIso (hkrOverK K n) := by
  dsimp [hkrOverK, polyvectorComplexOverK]
  infer_instance

end ExteriorPolyvectors

section CycleCorrection

/-- A morphism inducing zero on homology sends every cycle to an actual boundary. -/
theorem image_cycle_mem_boundaries (S : ShortComplex (ModuleCat.{u} R)) (φ : S ⟶ S)
    (hφ : ShortComplex.homologyMap φ = 0) (x : S.X₂) (hx : S.g x = 0) :
    ∃ y : S.X₁, S.f y = φ.τ₂ x := by
  apply (S.moduleCat_pOpcycles_eq_zero_iff (φ.τ₂ x)).mp
  let z : S.cycles := S.moduleCatCyclesIso.inv ⟨x, hx⟩
  have hz : S.iCycles z = x := by
    have h := congrArg (fun q : S.moduleCatLeftHomologyData.K ⟶ S.X₂ => q ⟨x, hx⟩)
      S.moduleCatCyclesIso_inv_iCycles
    exact h
  have h := congrArg (fun q : S.cycles ⟶ S.opcycles => q z) (ShortComplex.π_homologyMap_ι φ)
  rw [hφ] at h
  change S.homologyι 0 = S.pOpcycles (φ.τ₂ (S.iCycles z)) at h
  rw [hz] at h
  simpa using h.symm

variable (K : Type u) [Field K] [CharZero K]

/-- The explicit HKR representative of a full cochain. -/
def hkrRepresentative (n p : ℕ) (c : Cochain K (MvPolynomial (Fin n) K) p) :
    Cochain K (MvPolynomial (Fin n) K) p :=
  (hkrOverK K n).f p ((hkrRetractionOverK K n).f p c)

/-- The cochain correction from a full cochain to its HKR representative. -/
def hkrCorrection (n : ℕ) :
    barComplex (LinearMap.mul K (MvPolynomial (Fin n) K)) (fun a b c => mul_assoc a b c) ⟶
      barComplex (LinearMap.mul K (MvPolynomial (Fin n) K)) (fun a b c => mul_assoc a b c) :=
  𝟙 _ - hkrRetractionOverK K n ≫ hkrOverK K n

theorem hkrCorrection_homologyMap (n p : ℕ) :
    HomologicalComplex.homologyMap (hkrCorrection K n) p = 0 := by
  have hl : HomologicalComplex.homologyMap (hkrOverK K n) p ≫
      HomologicalComplex.homologyMap (hkrRetractionOverK K n) p =
      𝟙 ((polyvectorComplexOverK K n).homology p) := by
    rw [← HomologicalComplex.homologyMap_comp, hkrOverK_comp_retraction,
      HomologicalComplex.homologyMap_id]
  have hr : HomologicalComplex.homologyMap (hkrRetractionOverK K n) p ≫
      HomologicalComplex.homologyMap (hkrOverK K n) p = 𝟙 _ := by
    apply (cancel_epi (HomologicalComplex.homologyMap (hkrOverK K n) p)).mp
    rw [← Category.assoc, hl]
    simp
  rw [hkrCorrection, HomologicalComplex.homologyMap_sub, HomologicalComplex.homologyMap_id,
    HomologicalComplex.homologyMap_comp, hr, sub_self]

set_option backward.isDefEq.respectTransparency false in
/-- Every positive-arity Hochschild cocycle differs from its HKR representative by a boundary. -/
theorem cocycle_correction_boundary (n p : ℕ)
    (c : Cochain K (MvPolynomial (Fin n) K) (p + 1))
    (hc : barDifferential (LinearMap.mul K (MvPolynomial (Fin n) K)) (p + 1) c = 0) :
    ∃ b : Cochain K (MvPolynomial (Fin n) K) p,
      barDifferential (LinearMap.mul K (MvPolynomial (Fin n) K)) p b =
        c - hkrRepresentative K n (p + 1) c := by
  let C := barComplex (LinearMap.mul K (MvPolynomial (Fin n) K)) (fun a b c => mul_assoc a b c)
  let S := C.sc (p + 1)
  let φ := (HomologicalComplex.shortComplexFunctor (ModuleCat K) (ComplexShape.up ℕ) (p + 1)).map
    (hkrCorrection K n)
  have hn : (ComplexShape.up ℕ).next (p + 1) = (p + 1) + 1 := by simp
  have hp : (ComplexShape.up ℕ).prev (p + 1) = p := by simp
  have hφ : ShortComplex.homologyMap φ = 0 := hkrCorrection_homologyMap K n (p + 1)
  have hx : S.g c = 0 := by
    simp only [S, C, HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor', barComplex, CochainComplex.of.d]
    split_ifs <;> simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      ModuleCat.hom_zero, LinearMap.zero_apply, hc, map_zero]
  have hb := image_cycle_mem_boundaries S φ hφ c hx
  let incoming (q : ℕ) (y : Cochain K (MvPolynomial (Fin n) K) q) :
      Cochain K (MvPolynomial (Fin n) K) (p + 1) := (C.d q (p + 1)).hom y
  have hb' : ∃ y : Cochain K (MvPolynomial (Fin n) K) ((ComplexShape.up ℕ).prev (p + 1)),
      incoming ((ComplexShape.up ℕ).prev (p + 1)) y = c - hkrRepresentative K n (p + 1) c := hb
  rw [hp] at hb'
  simpa [incoming, C, barComplex, CochainComplex.of.d] using hb'

set_option backward.isDefEq.respectTransparency false in
/-- In arity zero there are no incoming boundaries, so a cocycle equals its HKR representative. -/
theorem cocycle_correction_zero (n : ℕ) (c : Cochain K (MvPolynomial (Fin n) K) 0)
    (hc : barDifferential (LinearMap.mul K (MvPolynomial (Fin n) K)) 0 c = 0) :
    c = hkrRepresentative K n 0 c := by
  let C := barComplex (LinearMap.mul K (MvPolynomial (Fin n) K)) (fun a b c => mul_assoc a b c)
  let S := C.sc 0
  let φ := (HomologicalComplex.shortComplexFunctor (ModuleCat K) (ComplexShape.up ℕ) 0).map
    (hkrCorrection K n)
  have hn : (ComplexShape.up ℕ).next 0 = 1 := by simp
  have hp : (ComplexShape.up ℕ).prev 0 = 0 := by simp
  have hφ : ShortComplex.homologyMap φ = 0 := hkrCorrection_homologyMap K n 0
  have hx : S.g c = 0 := by
    simp only [S, C, HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor', barComplex, CochainComplex.of.d]
    split_ifs <;> simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      ModuleCat.hom_zero, LinearMap.zero_apply, hc, map_zero]
  have hb := image_cycle_mem_boundaries S φ hφ c hx
  let incoming (q : ℕ) (y : Cochain K (MvPolynomial (Fin n) K) q) :
      Cochain K (MvPolynomial (Fin n) K) 0 := (C.d q 0).hom y
  have hb' : ∃ y : Cochain K (MvPolynomial (Fin n) K) ((ComplexShape.up ℕ).prev 0),
      incoming ((ComplexShape.up ℕ).prev 0) y = c - hkrRepresentative K n 0 c := hb
  rw [hp] at hb'
  obtain ⟨b, hb'⟩ := hb'
  have h : 0 = c - hkrRepresentative K n 0 c := by
    simpa [incoming, C, barComplex, CochainComplex.of.d] using hb'
  exact sub_eq_zero.mp h.symm

end CycleCorrection


end

end EnvelopingIsomorphism.Deformation.HKR
