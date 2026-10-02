import EnvelopingIsomorphism.Deformation.HKR
import Mathlib.LinearAlgebra.Alternating.Curry

/-!
# Polynomial polyvectors as alternating multiderivations

The exterior-power source is the existing `HKR.Polyvector`. This file supplies
its concrete evaluation on polynomial functions, using alternating maps which
satisfy the Leibniz rule in every argument.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation

open scoped BigOperators

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

instance alternatingMapIsScalarTower (n : ℕ) : IsScalarTower k A (A [⋀^Fin n]→ₗ[k] A) :=
  IsScalarTower.of_algebraMap_smul (fun r F => by
    apply AlternatingMap.ext
    intro a
    exact (Algebra.smul_def r (F a)).symm)

instance cochainIsScalarTower (n : ℕ) : IsScalarTower k A (Cochain k A n) :=
  IsScalarTower.of_algebraMap_smul (fun r F => by
    apply MultilinearMap.ext
    intro a
    exact (Algebra.smul_def r (F a)).symm)

/-- Alternating multilinear maps which are derivations in every argument. -/
def multiderivationSubmodule (k A : Type*) [CommRing k] [CommRing A] [Algebra k A] (n : ℕ) :
    Submodule A (A [⋀^Fin n]→ₗ[k] A) where
  carrier := {F | ∀ (i : Fin n) a b c,
    F (Function.update a i (b * c)) =
      b * F (Function.update a i c) + c * F (Function.update a i b)}
  zero_mem' := by simp
  add_mem' := by
    intro F G hF hG i a b c
    change F (Function.update a i (b * c)) + G (Function.update a i (b * c)) =
      b * (F (Function.update a i c) + G (Function.update a i c)) +
        c * (F (Function.update a i b) + G (Function.update a i b))
    rw [hF, hG]
    ring
  smul_mem' := by
    intro r F hF i a b c
    change r * F (Function.update a i (b * c)) =
      b * (r * F (Function.update a i c)) + c * (r * F (Function.update a i b))
    rw [hF]
    ring

/-- The concrete arity-n polyvector model. Arity zero is retained. -/
abbrev Multiderivation (k A : Type*) [CommRing k] [CommRing A] [Algebra k A] (n : ℕ) : Type _ :=
  ↥(multiderivationSubmodule k A n)

namespace Multiderivation

variable {n : ℕ}

instance instModuleBase : Module k (Multiderivation k A n) :=
  (multiderivationSubmodule k A n |>.restrictScalars k).module

instance instIsScalarTower : IsScalarTower k A (Multiderivation k A n) :=
  IsScalarTower.of_algebraMap_smul (fun r F => by
    apply Subtype.ext
    apply AlternatingMap.ext
    intro a
    exact (Algebra.smul_def r (F.val a)).symm)

instance : CoeFun (Multiderivation k A n) (fun _ => (Fin n → A) → A) :=
  ⟨fun F => F.val⟩

@[ext] theorem ext {F G : Multiderivation k A n} (h : ∀ a, F a = G a) : F = G :=
  Subtype.ext (AlternatingMap.ext h)

/-- Evaluation is linear over the coefficient algebra. -/
def evaluation (a : Fin n → A) : Multiderivation k A n →ₗ[A] A where
  toFun F := F a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem evaluation_apply (a : Fin n → A) (F : Multiderivation k A n) :
    evaluation a F = F a := rfl

theorem leibniz (F : Multiderivation k A n) (i : Fin n) (a : Fin n → A) (b c : A) :
    F (Function.update a i (b * c)) =
      b * F (Function.update a i c) + c * F (Function.update a i b) := F.property i a b c

/-- Holding all other arguments fixed gives a genuine algebra derivation. -/
def slotDerivation (F : Multiderivation k A n) (i : Fin n) (a : Fin n → A) :
    Derivation k A A where
  toLinearMap := F.val.toMultilinearMap.toLinearMap a i
  map_one_eq_zero' := by
    have h := F.leibniz i a 1 1
    simp only [one_mul] at h
    exact add_eq_left.mp h.symm
  leibniz' b c := F.leibniz i a b c

@[simp] theorem slotDerivation_apply (F : Multiderivation k A n) (i : Fin n)
    (a : Fin n → A) (b : A) : F.slotDerivation i a b = F (Function.update a i b) := rfl

/-- Fixing the first argument preserves the derivation rules in all remaining arguments. -/
def curryLeft (F : Multiderivation k A (n + 1)) (b : A) : Multiderivation k A n :=
  ⟨F.val.curryLeft b, by
    intro i a c d
    change F (Fin.cons b (Function.update a i (c * d))) =
      c * F (Fin.cons b (Function.update a i d)) + d * F (Fin.cons b (Function.update a i c))
    simpa only [Fin.cons_update] using
      F.leibniz i.succ (Fin.cons b a) c d⟩

@[simp] theorem curryLeft_apply (F : Multiderivation k A (n + 1)) (b : A) (a : Fin n → A) :
    F.curryLeft b a = F (Fin.cons b a) := rfl

/-- Functions are the arity-zero multiderivations. -/
def constant (f : A) : Multiderivation k A 0 :=
  ⟨AlternatingMap.constOfIsEmpty k A (Fin 0) f, by intro i; exact Fin.elim0 i⟩

@[simp] theorem constant_apply (f : A) (a : Fin 0 → A) : constant (k := k) f a = f := rfl

/-- The degree-minus-one component is exactly the coefficient algebra. -/
def zeroEquiv : Multiderivation k A 0 ≃ₗ[A] A where
  toFun F := F Fin.elim0
  invFun := constant
  left_inv F := by
    apply Multiderivation.ext
    intro a
    exact congrArg F (Subsingleton.elim _ _)
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A usual derivation gives an arity-one multiderivation. -/
def ofDerivation (D : Derivation k A A) : Multiderivation k A 1 :=
  ⟨AlternatingMap.ofSubsingleton k A A (0 : Fin 1) D.toLinearMap, by
    intro i a b c
    have hi := Fin.eq_zero i
    subst i
    change D (Function.update a 0 (b * c) 0) =
      b * D (Function.update a 0 c 0) + c * D (Function.update a 0 b 0)
    simp only [Function.update_self]
    exact D.leibniz b c⟩

@[simp] theorem ofDerivation_apply (D : Derivation k A A) (a : Fin 1 → A) :
    ofDerivation D a = D (a 0) := rfl

/-- The degree-zero component is exactly the module of vector fields. -/
def oneEquiv : Multiderivation k A 1 ≃ₗ[A] Derivation k A A where
  toFun F := F.slotDerivation 0 (fun _ => 0)
  invFun := ofDerivation
  left_inv F := by
    apply Multiderivation.ext
    intro a
    change F (Function.update (fun _ => 0) 0 (a 0)) = F a
    congr 1
    funext i
    rw [Fin.eq_zero i, Function.update_self]
  right_inv D := by apply Derivation.ext; intro b; simp
  map_add' _ _ := by apply Derivation.ext; intro b; rfl
  map_smul' _ _ := by apply Derivation.ext; intro b; rfl

@[simp] theorem oneEquiv_ofDerivation (D : Derivation k A A) : oneEquiv (ofDerivation D) = D :=
  oneEquiv.apply_symm_apply D

@[simp] theorem ofDerivation_oneEquiv (F : Multiderivation k A 1) : ofDerivation (oneEquiv F) = F :=
  oneEquiv.symm_apply_apply F

/-- Inserting a function into the first slot, retaining the zero-arity output. -/
def contract (F : Multiderivation k A (n + 1)) (f : A) : Multiderivation k A n := F.curryLeft f

@[simp] theorem contract_apply (F : Multiderivation k A (n + 1)) (f : A) (a : Fin n → A) :
    F.contract f a = F (Fin.cons f a) := rfl

/-- Contracting twice with the same function is zero. -/
theorem contract_contract_self (F : Multiderivation k A (n + 1 + 1)) (f : A) :
    (F.contract f).contract f = 0 := by
  apply Subtype.ext
  exact F.val.curryLeft_same f

end Multiderivation

/-- Differentiating one input row of the evaluation determinant gives the Leibniz rule. -/
theorem determinant_derivation_update_mul {n : ℕ} (D : Fin n → Derivation k A A)
    (a : Fin n → A) (i : Fin n) (b c : A) :
    Matrix.det (fun r j => D j (Function.update a i (b * c) r)) =
      b * Matrix.det (fun r j => D j (Function.update a i c r)) +
        c * Matrix.det (fun r j => D j (Function.update a i b r)) := by
  classical
  have hrow (x : A) : (fun r j => D j (Function.update a i x r)) =
      Function.update (fun r j => D j (a r)) i (fun j => D j x) := by
    funext r j
    by_cases h : r = i <;> simp [h]
  simp only [hrow]
  have hD : (fun j => D j (b * c)) = b • (fun j => D j c) + c • (fun j => D j b) := by
    ext j
    simp [Derivation.leibniz, smul_eq_mul]
  rw [hD]
  change Matrix.detRowAlternating _ = _
  rw [AlternatingMap.map_update_add, AlternatingMap.map_update_smul,
    AlternatingMap.map_update_smul]
  rfl

/-- Wedges of genuine derivations act as determinant multiderivations. -/
def wedgeDerivations {n : ℕ} (D : Fin n → Derivation k A A) : Multiderivation k A n :=
  ⟨MultilinearMap.alternatization (derivationProduct 1 D), by
    intro i a b c
    change alternatingEvaluation (derivationProduct 1 D) (Function.update a i (b * c)) =
      b * alternatingEvaluation (derivationProduct 1 D) (Function.update a i c) +
        c * alternatingEvaluation (derivationProduct 1 D) (Function.update a i b)
    simp only [alternatingEvaluation_derivationProduct, one_mul]
    exact determinant_derivation_update_mul D a i b c⟩

@[simp] theorem wedgeDerivations_apply {n : ℕ} (D : Fin n → Derivation k A A) (a : Fin n → A) :
    wedgeDerivations D a = Matrix.det (fun i j => D j (a i)) := by
  change alternatingEvaluation (derivationProduct 1 D) a = _
  rw [alternatingEvaluation_derivationProduct, one_mul]

namespace Multiderivation

open MvPolynomial

variable {K : Type*} [Field K] {d : ℕ}

/-- Polynomial multiderivations are determined by their values on coordinate tuples. -/
theorem ext_coordinates (n : ℕ) {F G : Multiderivation K (MvPolynomial (Fin d) K) n}
    (h : ∀ u : Fin n → Fin d, F (fun i => X (u i)) = G (fun i => X (u i))) : F = G := by
  induction n with
  | zero =>
    apply Multiderivation.ext
    intro a
    have hh := h (fun i => Fin.elim0 i)
    convert hh using 1 <;> congr 1 <;> exact Subsingleton.elim _ _
  | succ n ih =>
    apply Multiderivation.ext
    intro a
    have hd : F.slotDerivation 0 a = G.slotDerivation 0 a := by
      apply MvPolynomial.derivation_ext
      intro j
      have hc : F.curryLeft (X j) = G.curryLeft (X j) := by
        apply ih
        intro u
        have hh := h (Fin.cons j u)
        change F (X ∘ Fin.cons j u) = G (X ∘ Fin.cons j u) at hh
        rw [Fin.comp_cons] at hh
        exact hh
      have hh := congrArg (fun H => H (Fin.tail a)) hc
      have hupdate : Function.update a 0 (X j) = Fin.cons (X j) (Fin.tail a) := by
        nth_rw 1 [← Fin.cons_self_tail a]
        rw [Fin.update_cons_zero]
      simpa only [slotDerivation_apply, hupdate, curryLeft_apply] using hh
    have hh := congrArg (fun D : Derivation K (MvPolynomial (Fin d) K) _ => D (a 0)) hd
    simpa only [slotDerivation_apply, Function.update_eq_self] using hh

/-- Sorted coordinate subsets suffice, since the maps are alternating. -/
theorem ext_sortedCoordinates {n : ℕ}
    {F G : Multiderivation K (MvPolynomial (Fin d) K) n}
    (h : ∀ s : Set.powersetCard (Fin d) n,
      F (fun i => X (Set.powersetCard.ofFinEmbEquiv.symm s i)) =
        G (fun i => X (Set.powersetCard.ofFinEmbEquiv.symm s i))) : F = G := by
  classical
  apply ext_coordinates n
  intro u
  by_cases hu : Function.Injective u
  · have hcard : (Finset.image u Finset.univ).card = n := by
      simpa using Finset.card_image_of_injective Finset.univ hu
    let s : Set.powersetCard (Fin d) n := ⟨Finset.image u Finset.univ, hcard⟩
    let σ : Equiv.Perm (Fin n) :=
      (Finset.orderIsoOfFin s.val s.prop).toEquiv.trans
        ((Equiv.setCongr Fintype.coe_image_univ).trans (Equiv.ofInjective u hu).symm)
    have hσ : u ∘ σ = Set.powersetCard.ofFinEmbEquiv.symm s := by
      funext i
      simp [σ, Equiv.apply_ofInjective_symm]
      rfl
    have he := h s
    change F.val (X ∘ Set.powersetCard.ofFinEmbEquiv.symm s) =
      G.val (X ∘ Set.powersetCard.ofFinEmbEquiv.symm s) at he
    rw [← hσ, ← Function.comp_assoc, F.val.map_perm, G.val.map_perm] at he
    have hh := congrArg (fun x => Equiv.Perm.sign σ • x) he
    simpa only [smul_smul, Int.units_mul_self, one_smul, Function.comp_def] using hh
  · have hxu : ¬ Function.Injective (fun i => (X (u i) : MvPolynomial (Fin d) K)) :=
      fun hx => hu (fun i j hij => hx (congrArg (fun q => (X q : MvPolynomial (Fin d) K)) hij))
    rw [F.val.map_eq_zero_of_not_injective _ hxu, G.val.map_eq_zero_of_not_injective _ hxu]

variable [CharZero K]

/-- The coordinate wedge corresponding to a sorted subset of variables. -/
def coordinateWedge (s : Set.powersetCard (Fin d) n) :
    Multiderivation K (MvPolynomial (Fin d) K) n :=
  wedgeDerivations (fun i => pderiv (Set.powersetCard.ofFinEmbEquiv.symm s i))

theorem coordinateWedge_apply_sorted (s t : Set.powersetCard (Fin d) n) :
    coordinateWedge (K := K) s (fun i => X (Set.powersetCard.ofFinEmbEquiv.symm t i)) =
      if s = t then 1 else 0 := by
  have hpair : coordinateWedge (K := K) s
      (fun i => X (Set.powersetCard.ofFinEmbEquiv.symm t i)) =
      alternatingEvaluation
        (coordinateHKR (1 : MvPolynomial (Fin d) K) (Set.powersetCard.ofFinEmbEquiv.symm s))
        (fun i => X (Set.powersetCard.ofFinEmbEquiv.symm t i)) := by
    rw [coordinateHKR, alternatingEvaluation_hkrCochain]
    simp only [coordinateWedge, wedgeDerivations_apply, one_mul]
  rw [hpair]
  by_cases hst : s = t
  · subst t
    rw [alternatingEvaluation_coordinateHKR_self _ _
      (Set.powersetCard.ofFinEmbEquiv.symm s).injective, if_pos rfl]
  · rw [alternatingEvaluation_coordinateHKR_powersetCard_ne _ s t hst, if_neg hst]

/-- Evaluation on the sorted coordinate wedges. -/
def coordinates : Multiderivation K (MvPolynomial (Fin d) K) n →ₗ[MvPolynomial (Fin d) K]
    (Set.powersetCard (Fin d) n → MvPolynomial (Fin d) K) where
  toFun F s := F (fun i => X (Set.powersetCard.ofFinEmbEquiv.symm s i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Reconstruct a multiderivation by a finite sum of coordinate wedges. -/
def ofCoordinates : (Set.powersetCard (Fin d) n → MvPolynomial (Fin d) K)
    →ₗ[MvPolynomial (Fin d) K] Multiderivation K (MvPolynomial (Fin d) K) n where
  toFun c := ∑ s, c s • coordinateWedge s
  map_add' c e := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c e := by simp [Pi.smul_apply, Finset.smul_sum, smul_smul]

omit [CharZero K] in
@[simp] theorem coordinates_apply (F : Multiderivation K (MvPolynomial (Fin d) K) n)
    (s : Set.powersetCard (Fin d) n) :
    coordinates F s = F (fun i => X (Set.powersetCard.ofFinEmbEquiv.symm s i)) := rfl

omit [CharZero K] in
theorem ofCoordinates_apply (c : Set.powersetCard (Fin d) n → MvPolynomial (Fin d) K)
    (a : Fin n → MvPolynomial (Fin d) K) :
    ofCoordinates c a = ∑ s, c s * coordinateWedge s a := by
  change evaluation a (∑ s, c s • coordinateWedge s) = _
  rw [map_sum]
  simp only [map_smul, evaluation_apply, smul_eq_mul]

@[simp] theorem coordinates_ofCoordinates (c : Set.powersetCard (Fin d) n → MvPolynomial (Fin d) K) :
    coordinates (ofCoordinates c) = c := by
  classical
  funext t
  rw [coordinates_apply, ofCoordinates_apply]
  simp [coordinateWedge_apply_sorted]

@[simp] theorem ofCoordinates_coordinates (F : Multiderivation K (MvPolynomial (Fin d) K) n) :
    ofCoordinates (coordinates F) = F := by
  apply ext_sortedCoordinates
  intro s
  exact congrFun (coordinates_ofCoordinates (coordinates F)) s

/-- Polynomial multiderivations are a finite free module in the expected exterior coordinates. -/
def coordinatesEquiv : Multiderivation K (MvPolynomial (Fin d) K) n
    ≃ₗ[MvPolynomial (Fin d) K] (Set.powersetCard (Fin d) n → MvPolynomial (Fin d) K) :=
  LinearEquiv.ofLinear coordinates ofCoordinates
    (by apply LinearMap.ext; intro c; exact coordinates_ofCoordinates c)
    (by apply LinearMap.ext; exact ofCoordinates_coordinates)

/-- The existing exterior-power polyvectors and concrete multiderivations are the same module. -/
def exteriorEquiv (K : Type*) [Field K] [CharZero K] (d n : ℕ) :
    HKR.Polyvector K d n ≃ₗ[MvPolynomial (Fin d) K]
      Multiderivation K (MvPolynomial (Fin d) K) n :=
  (HKR.polyvectorCoordinates K d n).trans coordinatesEquiv.symm

instance instModuleFree : Module.Free (MvPolynomial (Fin d) K)
    (Multiderivation K (MvPolynomial (Fin d) K) n) :=
  Module.Free.of_equiv coordinatesEquiv.symm

instance instModuleFinite : Module.Finite (MvPolynomial (Fin d) K)
    (Multiderivation K (MvPolynomial (Fin d) K) n) :=
  Module.Finite.equiv coordinatesEquiv.symm

theorem finrank_eq_choose : Module.finrank (MvPolynomial (Fin d) K)
    (Multiderivation K (MvPolynomial (Fin d) K) n) = d.choose n := by
  rw [coordinatesEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_eq_nat_card, Set.powersetCard.card]
  simp

end Multiderivation

namespace Multiderivation

variable {K : Type*} [Field K] {B : Type*} [CommRing B] [Algebra K B] {n : ℕ}

/-- The usual HKR inclusion is raw alternating evaluation divided by the factorial. -/
def toCochain : Multiderivation K B n →ₗ[B] Cochain K B n where
  toFun F := (n.factorial : K)⁻¹ • F.val.toMultilinearMap
  map_add' _ _ := by simp [AlternatingMap.coe_add, smul_add]
  map_smul' c F := by
    apply MultilinearMap.ext
    intro a
    change (n.factorial : K)⁻¹ • (c • F a) = c • ((n.factorial : K)⁻¹ • F a)
    exact smul_comm _ _ _

@[simp] theorem toCochain_apply (F : Multiderivation K B n) (a : Fin n → B) :
    toCochain F a = (n.factorial : K)⁻¹ • F a := rfl

theorem toCochain_wedgeDerivations (D : Fin n → Derivation K B B) :
    toCochain (wedgeDerivations D) = hkrCochain 1 D := rfl

open MvPolynomial

variable {d : ℕ} [CharZero K]

omit [CharZero K] in
theorem toCochain_smul_coordinateWedge (c : MvPolynomial (Fin d) K)
    (s : Set.powersetCard (Fin d) n) :
    toCochain (c • coordinateWedge s) =
      coordinateHKR c (Set.powersetCard.ofFinEmbEquiv.symm s) := by
  apply MultilinearMap.ext
  intro a
  rw [coordinateHKR, hkrCochain_apply, toCochain_apply]
  change (n.factorial : K)⁻¹ • (c * coordinateWedge s a) = _
  rw [coordinateWedge, wedgeDerivations_apply]

omit [CharZero K] in
theorem toCochain_ofCoordinates
    (c : Set.powersetCard (Fin d) n → MvPolynomial (Fin d) K) :
    toCochain (ofCoordinates c) = HKR.coordinateFamilyHKR K (HKR.exteriorTuple) c := by
  change toCochain (∑ s, c s • coordinateWedge s) = _
  rw [map_sum, HKR.coordinateFamilyHKR_apply]
  apply Finset.sum_congr rfl
  intro s hs
  exact toCochain_smul_coordinateWedge (c s) s

/-- The concrete multiderivation inclusion is exactly the already constructed exterior HKR map. -/
theorem toCochain_exteriorEquiv (v : HKR.Polyvector K d n) :
    toCochain (exteriorEquiv K d n v) = (HKR.hkr K d).f n v := by
  change toCochain (ofCoordinates (HKR.polyvectorCoordinates K d n v)) = _
  rw [toCochain_ofCoordinates, HKR.hkr_f_apply]

/-- Every normalized polynomial multiderivation is a full Hochschild cocycle. -/
theorem barDifferential_toCochain (F : Multiderivation K (MvPolynomial (Fin d) K) n) :
    barDifferential (LinearMap.mul K (MvPolynomial (Fin d) K)) n (toCochain F) = 0 := by
  rw [← ofCoordinates_coordinates F, toCochain_ofCoordinates, HKR.coordinateFamilyHKR_apply, map_sum]
  simp only [barDifferential_coordinateHKR, Finset.sum_const_zero]

/-- Coordinate antisymmetric evaluation followed by genuine multiderivation reconstruction. -/
def fromCochain : Cochain K (MvPolynomial (Fin d) K) n →ₗ[MvPolynomial (Fin d) K]
    Multiderivation K (MvPolynomial (Fin d) K) n :=
  ofCoordinates.comp (HKR.coordinateFamilyEvaluation K HKR.exteriorTuple)

theorem coordinates_fromCochain (c : Cochain K (MvPolynomial (Fin d) K) n)
    (s : Set.powersetCard (Fin d) n) :
    coordinates (fromCochain c) s =
      alternatingEvaluation c (fun i => X (Set.powersetCard.ofFinEmbEquiv.symm s i)) := by
  exact congrFun (coordinates_ofCoordinates (HKR.coordinateFamilyEvaluation K HKR.exteriorTuple c)) s

/-- Full alternation of a normalized multiderivation recovers raw alternating evaluation. -/
theorem alternatingEvaluation_toCochain (F : Multiderivation K (MvPolynomial (Fin d) K) n)
    (a : Fin n → MvPolynomial (Fin d) K) :
    alternatingEvaluation (toCochain F) a = F a := by
  change MultilinearMap.alternatization
    (((n.factorial : K)⁻¹ • F.val).toMultilinearMap) a = _
  rw [AlternatingMap.coe_alternatization]
  change (Fintype.card (Fin n)).factorial • ((n.factorial : K)⁻¹ • F a) = _
  rw [Fintype.card_fin, ← Nat.cast_smul_eq_nsmul K, smul_smul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_smul]

@[simp] theorem fromCochain_toCochain (F : Multiderivation K (MvPolynomial (Fin d) K) n) :
    fromCochain (toCochain F) = F := by
  apply ext_sortedCoordinates
  intro s
  change coordinates (fromCochain (toCochain F)) s = _
  rw [coordinates_fromCochain, alternatingEvaluation_toCochain]

/-- Projection of every genuine Hochschild boundary is zero. -/
theorem fromCochain_barDifferential
    (c : Cochain K (MvPolynomial (Fin d) K) n) :
    fromCochain (barDifferential (LinearMap.mul K (MvPolynomial (Fin d) K)) n c) = 0 := by
  apply ext_sortedCoordinates
  intro s
  change coordinates (fromCochain (barDifferential _ n c)) s = 0
  rw [coordinates_fromCochain, alternatingEvaluation_barDifferential]

/-- This projection is the explicit exterior HKR retraction in the concrete model. -/
theorem fromCochain_eq_exteriorEquiv_retraction
    (c : Cochain K (MvPolynomial (Fin d) K) n) :
    fromCochain c = exteriorEquiv K d n ((HKR.hkrRetractionOverK K d).f n c) := by
  change ofCoordinates (HKR.coordinateFamilyEvaluation K HKR.exteriorTuple c) =
    ofCoordinates (HKR.polyvectorCoordinates K d n
      ((HKR.polyvectorCoordinates K d n).symm
        (HKR.coordinateFamilyEvaluation K HKR.exteriorTuple c)))
  rw [LinearEquiv.apply_symm_apply]

theorem toCochain_fromCochain_eq_representative
    (c : Cochain K (MvPolynomial (Fin d) K) n) :
    toCochain (fromCochain c) = HKR.hkrRepresentative K d n c := by
  rw [fromCochain_eq_exteriorEquiv_retraction, toCochain_exteriorEquiv]
  rfl

/-- A closed positive-arity cochain differs from its concrete multiderivation representative
by an actual boundary. -/
theorem cocycle_correction (c : Cochain K (MvPolynomial (Fin d) K) (n + 1))
    (hc : barDifferential (LinearMap.mul K (MvPolynomial (Fin d) K)) (n + 1) c = 0) :
    ∃ b : Cochain K (MvPolynomial (Fin d) K) n,
      barDifferential (LinearMap.mul K (MvPolynomial (Fin d) K)) n b =
        c - toCochain (fromCochain c) := by
  simpa only [toCochain_fromCochain_eq_representative] using HKR.cocycle_correction_boundary K d n c hc

/-- Alternation of a closed cochain is its genuine multiderivation representative on all inputs. -/
theorem fromCochain_apply_of_closed (c : Cochain K (MvPolynomial (Fin d) K) n)
    (hc : barDifferential (LinearMap.mul K (MvPolynomial (Fin d) K)) n c = 0)
    (a : Fin n → MvPolynomial (Fin d) K) : fromCochain c a = alternatingEvaluation c a := by
  cases n with
  | zero =>
    have he : c = toCochain (fromCochain c) := by
      rw [toCochain_fromCochain_eq_representative]
      exact HKR.cocycle_correction_zero K d c hc
    calc
      _ = alternatingEvaluation (toCochain (fromCochain c)) a :=
        (alternatingEvaluation_toCochain _ _).symm
      _ = _ := congrArg (fun F => alternatingEvaluation F a) he.symm
  | succ n =>
    obtain ⟨b, hb⟩ := cocycle_correction c hc
    have he := congrArg (alternatingEvaluationLinearMap a) hb
    rw [map_sub] at he
    simp only [alternatingEvaluationLinearMap_apply, alternatingEvaluation_barDifferential,
      alternatingEvaluation_toCochain] at he
    exact (sub_eq_zero.mp he.symm).symm

/-- In particular, alternation of any polynomial Hochschild cocycle satisfies every Leibniz rule. -/
theorem fromCochain_val_of_closed (c : Cochain K (MvPolynomial (Fin d) K) n)
    (hc : barDifferential (LinearMap.mul K (MvPolynomial (Fin d) K)) n c = 0) :
    (fromCochain c).val = MultilinearMap.alternatization c := by
  apply AlternatingMap.ext
  intro a
  exact fromCochain_apply_of_closed c hc a

end Multiderivation

end EnvelopingIsomorphism.Deformation
