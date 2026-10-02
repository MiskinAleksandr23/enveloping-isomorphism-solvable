import EnvelopingIsomorphism.PBW.CriticalPairs
import EnvelopingIsomorphism.Enveloping.UniversalProperties
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.RingTheory.Congruence.Basic

/-! The presentation by contextual word relations agrees with the standard UEA.
The constructions in this file do not use compatibility or confluence of reduction. -/

noncomputable section

namespace EnvelopingIsomorphism.PBW

open Finsupp

variable {R L α : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable (b : Module.Basis α R L)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Evaluation of a word in the free associative algebra. -/
def freeWord (w : List α) : FreeAlgebra R α := (w.map (FreeAlgebra.ι R)).prod

@[simp] theorem freeWord_nil : freeWord (R := R) ([] : List α) = 1 := rfl

@[simp] theorem freeWord_cons (i : α) (w : List α) :
    freeWord (R := R) (i :: w) = FreeAlgebra.ι R i * freeWord w := rfl

@[simp] theorem freeWord_append (p s : List α) :
    freeWord (R := R) (p ++ s) = freeWord p * freeWord s := by
  simp [freeWord]

/-- The standard word basis identifies word coefficients with the free algebra. -/
def wordEquiv : (List α →₀ R) ≃ₗ[R] FreeAlgebra R α :=
  (MonoidAlgebra.coeffLinearEquiv R).symm.trans
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearEquiv.symm)

private theorem freeWord_image (w : List α) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid (freeWord (R := R) w) =
      MonoidAlgebra.single (FreeMonoid.ofList w) 1 := by
  induction w with
  | nil => simp [freeWord, MonoidAlgebra.one_def]
  | cons i w ih =>
    rw [freeWord_cons, map_mul, ih]
    change (FreeAlgebra.lift R (fun x ↦ MonoidAlgebra.of R (FreeMonoid α)
      (FreeMonoid.of x))) (FreeAlgebra.ι R i) * _ = _
    simp [MonoidAlgebra.single_mul_single]

@[simp] theorem wordEquiv_single_one (w : List α) :
    wordEquiv (R := R) (single w 1) = freeWord w := by
  apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective
  rw [freeWord_image]
  change FreeAlgebra.equivMonoidAlgebraFreeMonoid
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.ofCoeff (single w 1))) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

@[simp] theorem wordEquiv_single (w : List α) (r : R) :
    wordEquiv (single w r) = r • freeWord (R := R) w := by
  rw [← smul_single_one w r, map_smul, wordEquiv_single_one]

theorem wordEquiv_insert (p s : List α) (x : L) :
    wordEquiv (insert b p s x) = freeWord p * basisFreeLinear b x * freeWord s := by
  have h : wordEquiv.toLinearMap.comp (insert b p s) =
      (LinearMap.mulRight R (freeWord s)).comp
        ((LinearMap.mulLeft R (freeWord p)).comp (basisFreeLinear b)) := by
    apply b.ext
    intro i
    simp [insert, mul_assoc]
  exact LinearMap.congr_fun h x

theorem wordEquiv_relation (p s : List α) (i j : α) :
    wordEquiv (relation b p i j s) =
      freeWord p * lieRelation (basisFreeLinear b) (b i) (b j) * freeWord s := by
  simp only [relation, rhs, map_sub, map_add, wordEquiv_single_one, wordEquiv_insert]
  simp only [freeWord_append, freeWord_cons, lieRelation, basisFreeLinear_basis]
  noncomm_ring

/-- The contextual relations transported to the free associative algebra. -/
def presentationRelations : Submodule R (FreeAlgebra R α) :=
  Submodule.span R {z | ∃ p i j s,
    z = freeWord p * lieRelation (basisFreeLinear b) (b i) (b j) * freeWord s}

section OrderedRelations

variable [LinearOrder α]

/-- All relations, including either orientation, belong to the reduction relation space. -/
theorem relation_mem_relations (p s : List α) (i j : α) :
    relation b p i j s ∈ (reductionSystem b).relations := by
  have descending (i j : α) (hji : j < i) :
      relation b p i j s ∈ (reductionSystem b).relations :=
    Submodule.subset_span ⟨p ++ i :: j :: s, rhs b p i j s,
      ⟨p, i, j, s, hji, rfl, rfl⟩, rfl⟩
  rcases lt_trichotomy j i with h | rfl | h
  · exact descending i j h
  · simp
  · rw [relation_swap]
    exact Submodule.neg_mem _ (descending j i h)

theorem map_relations_wordEquiv :
    (reductionSystem b).relations.map wordEquiv.toLinearMap = presentationRelations b := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro z ⟨w, q, ⟨p, i, j, s, _, rfl, rfl⟩, rfl⟩
    change wordEquiv (relation b p i j s) ∈ presentationRelations b
    rw [wordEquiv_relation]
    exact Submodule.subset_span ⟨p, i, j, s, rfl⟩
  · apply Submodule.span_le.mpr
    rintro z ⟨p, i, j, s, rfl⟩
    exact ⟨relation b p i j s, relation_mem_relations b p s i j,
      wordEquiv_relation b p s i j⟩

end OrderedRelations

theorem presentationRelations_mul_left (a : FreeAlgebra R α) {z : FreeAlgebra R α}
    (hz : z ∈ presentationRelations b) : a * z ∈ presentationRelations b := by
  induction a using FreeAlgebra.induction generalizing z with
  | grade0 r =>
    simpa only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] using
      (presentationRelations b).smul_mem r hz
  | grade1 k =>
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨p, i, j, s, rfl⟩ := hz
      exact Submodule.subset_span ⟨k :: p, i, j, s, by simp [mul_assoc]⟩
    | zero => simp
    | add x y _ _ hx hy => simpa only [mul_add] using add_mem hx hy
    | smul r x _ hx =>
      simpa only [Algebra.mul_smul_comm] using (presentationRelations b).smul_mem r hx
  | mul a c ha hc => rw [mul_assoc]; exact ha (hc hz)
  | add a c ha hc => simpa only [add_mul] using add_mem (ha hz) (hc hz)

theorem presentationRelations_mul_right (a : FreeAlgebra R α) {z : FreeAlgebra R α}
    (hz : z ∈ presentationRelations b) : z * a ∈ presentationRelations b := by
  induction a using FreeAlgebra.induction generalizing z with
  | grade0 r =>
    simpa only [Algebra.algebraMap_eq_smul_one, Algebra.mul_smul_comm, mul_one] using
      (presentationRelations b).smul_mem r hz
  | grade1 k =>
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨p, i, j, s, rfl⟩ := hz
      exact Submodule.subset_span ⟨p, i, j, s ++ [k], by simp [mul_assoc]⟩
    | zero => simp
    | add x y _ _ hx hy => simpa only [add_mul] using add_mem hx hy
    | smul r x _ hx =>
      simpa only [smul_mul_assoc] using (presentationRelations b).smul_mem r hx
  | mul a c ha hc => rw [← mul_assoc]; exact hc (ha hz)
  | add a c ha hc => simpa only [mul_add] using add_mem (ha hz) (hc hz)

/-- The linear space of contextual relations is a ring congruence. -/
def presentationCon : RingCon (FreeAlgebra R α) where
  r x y := x - y ∈ presentationRelations b
  iseqv :=
    { refl := fun x ↦ by simp
      symm := fun h ↦ by simpa using (presentationRelations b).neg_mem h
      trans := fun {x y z} hxy hyz ↦ by
        have h := (presentationRelations b).add_mem hxy hyz
        convert h using 1
        abel }
  add' {a b' c d} hab hcd := by
    have h := (presentationRelations b).add_mem hab hcd
    convert h using 1
    abel
  mul' {a b' c d} hab hcd := by
    have h := (presentationRelations b).add_mem
      (presentationRelations_mul_left b a hcd) (presentationRelations_mul_right b d hab)
    convert h using 1
    noncomm_ring

/-- Quotient map imposing just the defining relations. -/
def presentationMk : FreeAlgebra R α →ₐ[R] (presentationCon b).Quotient :=
  RingCon.mkₐ R (presentationCon b)

theorem presentationMk_eq_zero_iff (x : FreeAlgebra R α) :
    presentationMk b x = 0 ↔ x ∈ presentationRelations b := by
  change (presentationCon b).toQuotient x = (presentationCon b).toQuotient 0 ↔ _
  change Quotient.mk'' x = Quotient.mk'' (0 : FreeAlgebra R α) ↔ _
  rw [Quotient.eq'']
  change x - 0 ∈ presentationRelations b ↔ _
  rw [sub_zero]

theorem lieRelation_mem_presentationRelations (x y : L) :
    lieRelation (basisFreeLinear b) x y ∈ presentationRelations b := by
  have hx : x ∈ Submodule.span R (Set.range b) := by rw [b.span_eq]; trivial
  have hy : y ∈ Submodule.span R (Set.range b) := by rw [b.span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact Submodule.subset_span ⟨[], i, j, [], by simp⟩
    | zero => simp [lieRelation]
    | add y z _ _ hy hz => rw [lieRelation_add_right]; exact add_mem hy hz
    | smul r y _ hy =>
      rw [lieRelation_smul_right]
      exact (presentationRelations b).smul_mem r hy
  | zero => simp [lieRelation]
  | add x z _ _ hx hz => rw [lieRelation_add_left]; exact add_mem hx hz
  | smul r x _ hx =>
    rw [lieRelation_smul_left]
    exact (presentationRelations b).smul_mem r hx

/-- The original Lie algebra maps into the associative presentation quotient. -/
def presentationLieHom : L →ₗ⁅R⁆ (presentationCon b).Quotient where
  toLinearMap := (presentationMk b).toLinearMap.comp (basisFreeLinear b)
  map_lie' {x y} := by
    have h := (presentationMk_eq_zero_iff b _).mpr
      (lieRelation_mem_presentationRelations b x y)
    simp only [lieRelation, map_sub, map_mul, sub_eq_zero] at h
    exact h.symm

@[simp] theorem presentationLieHom_apply (x : L) :
    presentationLieHom b x = presentationMk b (basisFreeLinear b x) := rfl

/-- The standard map evaluating free generators in the native UEA. -/
def freeEval : FreeAlgebra R α →ₐ[R] UniversalEnvelopingAlgebra R L :=
  FreeAlgebra.lift R (UniversalEnvelopingAlgebra.ι R ∘ b)

@[simp] theorem freeEval_ι (i : α) :
    freeEval b (FreeAlgebra.ι R i) = UniversalEnvelopingAlgebra.ι R (b i) :=
  FreeAlgebra.lift_ι_apply _ i

@[simp] theorem freeEval_basisFreeLinear (x : L) :
    freeEval b (basisFreeLinear b x) = UniversalEnvelopingAlgebra.ι R x := by
  have h : (freeEval b).toLinearMap.comp (basisFreeLinear b) =
      (UniversalEnvelopingAlgebra.ι R).toLinearMap := by
    apply b.ext
    intro i
    simp
  exact LinearMap.congr_fun h x

@[simp] theorem freeEval_lieRelation (x y : L) :
    freeEval b (lieRelation (basisFreeLinear b) x y) = 0 := by
  simp only [lieRelation, map_sub, map_mul, freeEval_basisFreeLinear, LieHom.map_lie,
    LieRing.of_associative_ring_bracket, sub_self]

theorem freeEval_surjective : Function.Surjective (freeEval b) := by
  rw [← AlgHom.range_eq_top]
  apply top_unique
  rw [← EnvelopingIsomorphism.Enveloping.adjoin_range_ι]
  apply Algebra.adjoin_le_iff.mpr
  rintro _ ⟨x, rfl⟩
  exact ⟨basisFreeLinear b x, freeEval_basisFreeLinear b x⟩

theorem presentationLift_comp_freeEval :
    (UniversalEnvelopingAlgebra.lift R (presentationLieHom b)).comp (freeEval b) =
      presentationMk b := by
  apply FreeAlgebra.hom_ext
  funext i
  change UniversalEnvelopingAlgebra.lift R (presentationLieHom b)
    (freeEval b (FreeAlgebra.ι R i)) = presentationMk b (FreeAlgebra.ι R i)
  rw [freeEval_ι, UniversalEnvelopingAlgebra.lift_ι_apply,
    presentationLieHom_apply, basisFreeLinear_basis]

theorem ker_freeEval : LinearMap.ker (freeEval b).toLinearMap = presentationRelations b := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    apply (presentationMk_eq_zero_iff b x).mp
    have h := congrArg (UniversalEnvelopingAlgebra.lift R (presentationLieHom b)) hx
    change UniversalEnvelopingAlgebra.lift R (presentationLieHom b) (freeEval b x) =
      UniversalEnvelopingAlgebra.lift R (presentationLieHom b) 0 at h
    rw [← AlgHom.comp_apply, presentationLift_comp_freeEval, map_zero] at h
    exact h
  · apply Submodule.span_le.mpr
    rintro x ⟨p, i, j, s, rfl⟩
    change freeEval b (_ * _ * _) = 0
    rw [map_mul, map_mul, freeEval_lieRelation, mul_zero, zero_mul]

/-- Evaluation of arbitrary word coefficients in the native enveloping algebra. -/
def wordEval : (List α →₀ R) →ₗ[R] UniversalEnvelopingAlgebra R L :=
  (freeEval b).toLinearMap.comp wordEquiv.toLinearMap

@[simp] theorem wordEval_single_one (w : List α) :
    wordEval b (single w 1) =
      (w.map (UniversalEnvelopingAlgebra.ι R ∘ b)).prod := by
  change freeEval b (wordEquiv (single w 1)) = _
  rw [wordEquiv_single_one]
  induction w with
  | nil => simp
  | cons i w ih =>
    simp only [freeWord_cons, map_mul, freeEval_ι, ih, List.map_cons, List.prod_cons,
      Function.comp_apply]

theorem wordEval_surjective : Function.Surjective (wordEval b) :=
  (freeEval_surjective b).comp wordEquiv.surjective

variable [LinearOrder α]

/-- The contextual relation space is exactly the kernel of native word evaluation. -/
theorem ker_wordEval : LinearMap.ker (wordEval b) = (reductionSystem b).relations := by
  rw [wordEval, LinearMap.ker_comp, ker_freeEval, ← map_relations_wordEquiv]
  exact Submodule.comap_map_eq_of_injective wordEquiv.injective _

/-- Presentation by contextual word relations, independently of confluence or PBW. -/
def presentationEquiv : ((List α →₀ R) ⧸ (reductionSystem b).relations) ≃ₗ[R]
    UniversalEnvelopingAlgebra R L :=
  (Submodule.quotEquivOfEq _ _ (ker_wordEval b).symm).trans
    ((wordEval b).quotKerEquivOfSurjective (wordEval_surjective b))

@[simp] theorem presentationEquiv_mk (p : List α →₀ R) :
    presentationEquiv b (Submodule.Quotient.mk p) = wordEval b p := rfl

@[simp] theorem presentationEquiv_mk_single_one (w : List α) :
    presentationEquiv b (Submodule.Quotient.mk (single w 1)) =
      (w.map (UniversalEnvelopingAlgebra.ι R ∘ b)).prod := by
  rw [presentationEquiv_mk, wordEval_single_one]

end EnvelopingIsomorphism.PBW
