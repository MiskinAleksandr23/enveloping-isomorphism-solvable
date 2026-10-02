import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Acyclic complexes of vector spaces admit actual contracting homotopies,
without any restriction on dimension or boundedness of the complex. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.ContractibleComplex

open CategoryTheory HomologicalComplex

universe u v
variable {k : Type u} [Field k]

section LinearSplitting

variable {V W : Type v} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Every linear map of vector spaces admits a generalized inverse, obtained
by splitting its surjection onto its range and extending off that range. -/
theorem exists_generalizedInverse (f : V →ₗ[k] W) :
    ∃ g : W →ₗ[k] V, ∀ x, f (g (f x)) = f x := by
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨g, hg⟩ := s.exists_extend
  refine ⟨g, fun x ↦ ?_⟩
  have hgx := LinearMap.congr_fun hg (f.rangeRestrict x)
  have hsx := congrArg Subtype.val (LinearMap.congr_fun hs (f.rangeRestrict x))
  change f (g (f x)) = f x
  change g (f x) = s (f.rangeRestrict x) at hgx
  rw [hgx]
  exact hsx

def generalizedInverse (f : V →ₗ[k] W) : W →ₗ[k] V :=
  (exists_generalizedInverse f).choose

theorem generalizedInverse_apply (f : V →ₗ[k] W) (x : V) :
    f (generalizedInverse f (f x)) = f x :=
  (exists_generalizedInverse f).choose_spec x

theorem generalizedInverse_apply_of_mem_range (f : V →ₗ[k] W) {y : W}
    (hy : y ∈ LinearMap.range f) : f (generalizedInverse f y) = y := by
  obtain ⟨x, rfl⟩ := hy
  exact generalizedInverse_apply f x

end LinearSplitting

variable (C : CochainComplex (ModuleCat.{v} k) ℤ)

/-- Chosen generalized inverses of the differentials, for all index pairs. -/
def inverseDifferential (i j : ℤ) : C.X j →ₗ[k] C.X i :=
  generalizedInverse (C.d i j).hom

theorem differential_inverseDifferential (i j : ℤ) (x : C.X i) :
    C.d i j (inverseDifferential C i j (C.d i j x)) = C.d i j x :=
  generalizedInverse_apply (C.d i j).hom x

theorem differential_inverseDifferential_of_mem (i j : ℤ) {x : C.X j}
    (hx : x ∈ LinearMap.range (C.d i j).hom) : C.d i j (inverseDifferential C i j x) = x :=
  generalizedInverse_apply_of_mem_range (C.d i j).hom hx

theorem differential_squared (i j l : ℤ) (x : C.X i) : C.d j l (C.d i j x) = 0 := by
  have h := congrArg (fun f : C.X i ⟶ C.X l ↦ f x) (C.d_comp_d i j l)
  exact h

/-- Projection onto cycles determined by a splitting of the outgoing map. -/
def cycleProjection (i : ℤ) : Module.End k (C.X i) :=
  LinearMap.id - (inverseDifferential C i (i + 1)).comp (C.d i (i + 1)).hom

@[simp] theorem cycleProjection_apply (i : ℤ) (x : C.X i) :
    cycleProjection C i x = x - inverseDifferential C i (i + 1) (C.d i (i + 1) x) := rfl

theorem cycleProjection_mem_ker (i : ℤ) (x : C.X i) :
    cycleProjection C i x ∈ LinearMap.ker (C.d i (i + 1)).hom := by
  change C.d i (i + 1) (cycleProjection C i x) = 0
  rw [cycleProjection_apply, map_sub, differential_inverseDifferential, sub_self]

/-- The component of a contraction from degree i to degree j. -/
def homotopyMap (i j : ℤ) : C.X i ⟶ C.X j :=
  if j + 1 = i then ModuleCat.ofHom ((inverseDifferential C j i).comp (cycleProjection C i))
  else 0

theorem homotopyMap_apply {i j : ℤ} (hij : j + 1 = i) (x : C.X i) :
    homotopyMap C i j x = inverseDifferential C j i (cycleProjection C i x) := by
  rw [homotopyMap, if_pos hij]
  rfl

theorem exact_range_eq_ker (hC : C.Acyclic) (i : ℤ) :
    LinearMap.range (C.d (i - 1) i).hom = LinearMap.ker (C.d i (i + 1)).hom := by
  have h := (C.exactAt_iff' (i - 1) i (i + 1) (by simp) (by simp)).mp (hC i)
  exact h.moduleCat_range_eq_ker

/-- The contracting equation as an equality of actual vectors in each degree. -/
theorem contracting_equation (hC : C.Acyclic) (i : ℤ) (x : C.X i) :
    C.d (i - 1) i (homotopyMap C i (i - 1) x) +
      homotopyMap C (i + 1) i (C.d i (i + 1) x) = x := by
  rw [homotopyMap_apply C (sub_add_cancel i 1), homotopyMap_apply C rfl]
  have hp : cycleProjection C i x ∈ LinearMap.range (C.d (i - 1) i).hom := by
    rw [exact_range_eq_ker C hC i]
    exact cycleProjection_mem_ker C i x
  rw [differential_inverseDifferential_of_mem C (i - 1) i hp]
  rw [cycleProjection_apply C (i + 1), differential_squared, map_zero, sub_zero,
    cycleProjection_apply]
  exact sub_add_cancel _ _

/-- Every acyclic Z-indexed cochain complex of vector spaces is contractible,
as a standard mathlib homotopy of the identity map to zero. -/
def contraction (hC : C.Acyclic) : Homotopy (𝟙 C) 0 where
  hom := homotopyMap C
  zero i j hij := by
    change ¬ j + 1 = i at hij
    simp [homotopyMap, hij]
  comm i := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i from sub_add_cancel i 1)]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change x = homotopyMap C (i + 1) i (C.d i (i + 1) x) +
      C.d (i - 1) i (homotopyMap C i (i - 1) x) + 0
    simpa only [add_zero, zero_add, add_comm] using (contracting_equation C hC i x).symm

theorem nonempty_contraction (hC : C.Acyclic) : Nonempty (Homotopy (𝟙 C) 0) :=
  ⟨contraction C hC⟩

/-- Exactness on a total module implies degreewise exactness whenever individual
degrees embed and can be projected compatibly with the differential. This does
not identify localization of a product with a product of localizations. -/
theorem acyclic_of_exact_total {T : Type*} [AddCommGroup T] [Module k T]
    (d : Module.End k T) (ι : ∀ i, C.X i →ₗ[k] T) (π : ∀ i, T →ₗ[k] C.X i)
    (hπι : ∀ i x, π i (ι i x) = x)
    (hι : ∀ i x, d (ι i x) = ι (i + 1) (C.d i (i + 1) x))
    (hπ : ∀ i y, C.d (i - 1) i (π (i - 1) y) = π i (d y))
    (hex : LinearMap.range d = LinearMap.ker d) : C.Acyclic := by
  intro i
  apply (C.exactAt_iff' (i - 1) i (i + 1) (by simp) (by simp)).mpr
  apply (CategoryTheory.ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  change C.d i (i + 1) x = 0 at hx
  have hy : ι i x ∈ LinearMap.ker d := by
    change d (ι i x) = 0
    rw [hι, hx, map_zero]
  rw [← hex] at hy
  obtain ⟨y, hy⟩ := hy
  refine ⟨π (i - 1) y, ?_⟩
  change C.d (i - 1) i (π (i - 1) y) = x
  rw [hπ, hy, hπι]

end EnvelopingIsomorphism.Deformation.ContractibleComplex
