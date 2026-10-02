import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Data.Finsupp.Indicator
import Mathlib.Tactic.Abel

/-! Monic linear reduction, in the form needed for the PBW theorem. -/

noncomputable section

namespace EnvelopingIsomorphism.PBW

open Finsupp

variable {R W : Type*} [CommRing R]

/-- A well-founded collection of monic rewriting rules on a free module. -/
structure ReductionSystem (R W : Type*) [CommRing R] where
  smaller : W → W → Prop
  wellFounded : WellFounded smaller
  step : W → (W →₀ R) → Prop
  support_smaller : ∀ {w p}, step w p → ∀ v ∈ p.support, smaller v w

namespace ReductionSystem

variable (s : ReductionSystem R W)

/-- An irreducible basis index. -/
def Normal (w : W) : Prop := ¬ ∃ p, s.step w p

/-- All contextual relations, viewed as a submodule of the free module. -/
def relations : Submodule R (W →₀ R) :=
  Submodule.span R {r | ∃ w p, s.step w p ∧ r = single w 1 - p}

/-- Relations whose leading word is strictly smaller than `w`. -/
def lowerRelations (w : W) : Submodule R (W →₀ R) :=
  Submodule.span R {r | ∃ v p, s.smaller v w ∧ s.step v p ∧ r = single v 1 - p}

/-- The finite critical-pair condition. No termination of polynomial reductions is needed. -/
def Compatible : Prop :=
  ∀ w p q, s.step w p → s.step w q → p - q ∈ s.lowerRelations w

private def normalWordAux (w : W)
    (rec : ∀ v, s.smaller v w → {v // s.Normal v} →₀ R) :
    {v // s.Normal v} →₀ R := by
  classical
  exact if h : ∃ p, s.step w p then
    let p := h.choose
    ∑ v : p.support, p v • rec v (s.support_smaller h.choose_spec v v.property)
  else single ⟨w, h⟩ 1

/-- Normalize a word using one arbitrarily chosen applicable rule. -/
def normalWord : W → {v // s.Normal v} →₀ R := s.wellFounded.fix s.normalWordAux

/-- Linear extension of normalization. -/
def normalize : (W →₀ R) →ₗ[R] ({v // s.Normal v} →₀ R) :=
  Finsupp.linearCombination R s.normalWord

@[simp] theorem normalize_single (w : W) (a : R) :
    s.normalize (single w a) = a • s.normalWord w := by
  classical
  simp [normalize]

@[simp] theorem normalize_single_one (w : W) :
    s.normalize (single w 1) = s.normalWord w := by simp

theorem normalWord_eq (w : W) : s.normalWord w =
    s.normalWordAux w (fun v _ ↦ s.normalWord v) :=
  s.wellFounded.fix_eq s.normalWordAux w

theorem normalWord_of_normal {w : W} (h : s.Normal w) :
    s.normalWord w = single ⟨w, h⟩ 1 := by
  rw [s.normalWord_eq]
  simp only [normalWordAux, dif_neg h]

private theorem sum_normalWord (p : W →₀ R) :
    (∑ v : p.support, p v • s.normalWord v) = s.normalize p := by
  classical
  simp only [normalize, Finsupp.linearCombination_apply, Finsupp.sum]
  exact Finset.sum_attach p.support (fun v ↦ p v • s.normalWord v)

theorem normalWord_of_reducible {w : W} (h : ∃ p, s.step w p) :
    s.normalWord w = s.normalize h.choose := by
  rw [s.normalWord_eq]
  simp only [normalWordAux, dif_pos h]
  exact s.sum_normalWord _

theorem normalize_step (hc : s.Compatible) {w : W} {p : W →₀ R}
    (hp : s.step w p) : s.normalWord w = s.normalize p := by
  classical
  induction w using s.wellFounded.induction generalizing p with
  | h w ih =>
    have hw : ∃ q, s.step w q := ⟨p, hp⟩
    rw [s.normalWord_of_reducible hw]
    have hker : s.lowerRelations w ≤ LinearMap.ker s.normalize := by
      apply Submodule.span_le.mpr
      rintro r ⟨v, q, hv, hq, rfl⟩
      change s.normalize (single v 1 - q) = 0
      rw [map_sub, s.normalize_single_one, ih v hv hq, sub_self]
    have hdiff := hker (hc w hw.choose p hw.choose_spec hp)
    change s.normalize (hw.choose - p) = 0 at hdiff
    rwa [map_sub, sub_eq_zero] at hdiff

theorem relations_le_ker_normalize (hc : s.Compatible) :
    s.relations ≤ LinearMap.ker s.normalize := by
  apply Submodule.span_le.mpr
  rintro r ⟨w, p, hp, rfl⟩
  change s.normalize (single w 1 - p) = 0
  rw [map_sub, s.normalize_single_one, s.normalize_step hc hp, sub_self]

/-- Embed a linear combination of irreducible indices into the free module. -/
def embedNormal : ({v // s.Normal v} →₀ R) →ₗ[R] (W →₀ R) :=
  Finsupp.linearCombination R (fun v : {v // s.Normal v} ↦ single v.val 1)

@[simp] theorem embedNormal_single (w : {v // s.Normal v}) (a : R) :
    s.embedNormal (single w a) = single w.val a := by
  classical
  simp [embedNormal]

@[simp] theorem normalize_embedNormal (p : {v // s.Normal v} →₀ R) :
    s.normalize (s.embedNormal p) = p := by
  classical
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single w a => simp [s.normalWord_of_normal w.property]

theorem normalize_surjective : Function.Surjective s.normalize :=
  fun p ↦ ⟨s.embedNormal p, s.normalize_embedNormal p⟩

theorem word_sub_normal_mem_relations (w : W) :
    single w 1 - s.embedNormal (s.normalWord w) ∈ s.relations := by
  classical
  induction w using s.wellFounded.induction with
  | h w ih =>
    by_cases hw : s.Normal w
    · rw [s.normalWord_of_normal hw, s.embedNormal_single, sub_self]
      exact s.relations.zero_mem
    · have hw' : ∃ p, s.step w p := not_not.mp hw
      rw [s.normalWord_of_reducible hw']
      have hrel : single w 1 - hw'.choose ∈ s.relations :=
        Submodule.subset_span ⟨w, hw'.choose, hw'.choose_spec, rfl⟩
      have hsum : hw'.choose - s.embedNormal (s.normalize hw'.choose) ∈ s.relations := by
        have heq : hw'.choose - s.embedNormal (s.normalize hw'.choose) =
            hw'.choose.sum (fun v a ↦ a • (single v 1 - s.embedNormal (s.normalWord v))) := by
          simp only [Finsupp.sum, smul_sub, Finset.sum_sub_distrib,
            map_sum, map_smul, normalize, Finsupp.linearCombination_apply]
          simp only [smul_single, smul_eq_mul, mul_one]
          congr 1
          exact (Finsupp.sum_single _).symm
        rw [heq]
        exact Submodule.sum_mem _ (fun v hv ↦
          s.relations.smul_mem _ (ih v (s.support_smaller hw'.choose_spec v hv)))
      convert s.relations.add_mem hrel hsum using 1; abel

theorem sub_normal_mem_relations (p : W →₀ R) :
    p - s.embedNormal (s.normalize p) ∈ s.relations := by
  classical
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq =>
    convert s.relations.add_mem hp hq using 1; simp; abel
  | single w a =>
    simpa [smul_sub] using s.relations.smul_mem a (s.word_sub_normal_mem_relations w)

theorem relations_eq_ker_normalize (hc : s.Compatible) :
    s.relations = LinearMap.ker s.normalize := by
  apply le_antisymm (s.relations_le_ker_normalize hc)
  intro p hp
  have h := s.sub_normal_mem_relations p
  change s.normalize p = 0 at hp
  simpa [hp] using h

/-- The quotient by compatible monic relations has the irreducible words as coordinates. -/
def quotientEquiv (hc : s.Compatible) :
    ((W →₀ R) ⧸ s.relations) ≃ₗ[R] ({v // s.Normal v} →₀ R) :=
  (Submodule.quotEquivOfEq _ _ (s.relations_eq_ker_normalize hc)).trans
    (s.normalize.quotKerEquivOfSurjective s.normalize_surjective)

@[simp] theorem quotientEquiv_mk (hc : s.Compatible) (p : W →₀ R) :
    s.quotientEquiv hc (Submodule.Quotient.mk p) = s.normalize p := by
  simp [quotientEquiv]

/-- A basis of a module presented by compatible monic relations. -/
def quotientBasis (hc : s.Compatible) :
    Module.Basis {v // s.Normal v} R ((W →₀ R) ⧸ s.relations) :=
  Finsupp.basisSingleOne.map (s.quotientEquiv hc).symm

@[simp] theorem quotientBasis_apply (hc : s.Compatible) (w : {v // s.Normal v}) :
    s.quotientBasis hc w = Submodule.Quotient.mk (single w.val 1) := by
  apply (s.quotientEquiv hc).injective
  simp [quotientBasis, s.normalWord_of_normal w.property]

end ReductionSystem
end EnvelopingIsomorphism.PBW
