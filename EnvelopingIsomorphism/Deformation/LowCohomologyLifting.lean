import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Elementwise lifting under a quasi-isomorphism

These lemmas extract actual cycles and boundaries from the homology-map
properties of a chain map. No finite-dimensionality or extra lifting
assumption is used. The generic results apply over any ring and in every
integer degree; the final two lemmas specialize to H¹ injectivity and H⁰
surjectivity, including the genuine degree -1 correction in the latter.
-/

namespace EnvelopingIsomorphism.Deformation

noncomputable section

open CategoryTheory Limits

universe u v
variable {k : Type u} [Ring k]

namespace LowCohomology

variable (S T : ShortComplex (ModuleCat.{v} k))

/-- A concrete kernel element regarded as an abstract cycle. -/
def cycleLift (x : S.X₂) (hx : S.g x = 0) : S.cycles :=
  S.moduleCatCyclesIso.inv ⟨x, hx⟩

@[simp] theorem cycleLift_i (x : S.X₂) (hx : S.g x = 0) :
    S.iCycles (cycleLift S x hx) = x := by
  have h := congrArg (fun q : S.moduleCatLeftHomologyData.K ⟶ S.X₂ => q ⟨x, hx⟩)
    S.moduleCatCyclesIso_inv_iCycles
  exact h

/-- The homology class of a concrete cycle. -/
def cycleClass (x : S.X₂) (hx : S.g x = 0) : S.homology :=
  S.homologyπ (cycleLift S x hx)

@[simp] theorem cycleClass_ι (x : S.X₂) (hx : S.g x = 0) :
    S.homologyι (cycleClass S x hx) = S.pOpcycles x := by
  have h := congrArg (fun q : S.cycles ⟶ S.opcycles => q (cycleLift S x hx)) S.homology_π_ι
  simpa only [ModuleCat.comp_apply, cycleLift_i, cycleClass] using h

theorem cycleClass_eq_zero_iff (x : S.X₂) (hx : S.g x = 0) :
    cycleClass S x hx = 0 ↔ ∃ y : S.X₁, S.f y = x := by
  constructor
  · intro h
    apply (S.moduleCat_pOpcycles_eq_zero_iff x).mp
    rw [← cycleClass_ι S x hx, h, map_zero]
  · intro h
    apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
    rw [cycleClass_ι, map_zero]
    exact (S.moduleCat_pOpcycles_eq_zero_iff x).mpr h

theorem cycleClass_surjective (a : S.homology) :
    ∃ x : S.X₂, ∃ hx : S.g x = 0, cycleClass S x hx = a := by
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance a
  let x : S.X₂ := S.iCycles z
  have hx : S.g x = 0 := by
    have h := congrArg (fun q : S.cycles ⟶ S.X₃ => q z) S.iCycles_g
    exact h
  refine ⟨x, hx, ?_⟩
  have hl : cycleLift S x hx = z := by
    apply (ModuleCat.mono_iff_injective S.iCycles).mp inferInstance
    exact cycleLift_i S x hx
  change S.homologyπ (cycleLift S x hx) = a
  rw [hl, hz]

variable {S T}

theorem map_cycle (φ : S ⟶ T) (x : S.X₂) (hx : S.g x = 0) : T.g (φ.τ₂ x) = 0 := by
  have h := congrArg (fun q : S.X₂ ⟶ T.X₃ => q x) φ.comm₂₃
  simpa only [ModuleCat.comp_apply, hx, map_zero] using h

theorem cycleClass_natural (φ : S ⟶ T) (x : S.X₂) (hx : S.g x = 0) :
    ShortComplex.homologyMap φ (cycleClass S x hx) =
      cycleClass T (φ.τ₂ x) (map_cycle φ x hx) := by
  apply (ModuleCat.mono_iff_injective T.homologyι).mp inferInstance
  rw [cycleClass_ι]
  have h := congrArg (fun q : S.cycles ⟶ T.opcycles => q (cycleLift S x hx))
    (ShortComplex.π_homologyMap_ι φ)
  simpa only [ModuleCat.comp_apply, cycleLift_i, cycleClass] using h

/-- Injectivity on homology reflects boundaries among cycles. -/
theorem reflects_boundary (φ : S ⟶ T) [Mono (ShortComplex.homologyMap φ)]
    (x : S.X₂) (hx : S.g x = 0) (w : T.X₁) (hw : φ.τ₂ x = T.f w) :
    ∃ y : S.X₁, S.f y = x := by
  apply (cycleClass_eq_zero_iff S x hx).mp
  apply (ModuleCat.mono_iff_injective (ShortComplex.homologyMap φ)).mp inferInstance
  rw [map_zero, cycleClass_natural]
  apply (cycleClass_eq_zero_iff T _ _).mpr
  exact ⟨w, hw.symm⟩

/-- Surjectivity on homology lifts every cycle, up to an actual boundary. -/
theorem lifts_cocycle (φ : S ⟶ T) [Epi (ShortComplex.homologyMap φ)]
    (x : T.X₂) (hx : T.g x = 0) :
    ∃ y : S.X₂, S.g y = 0 ∧ ∃ u : T.X₁, x = φ.τ₂ y + T.f u := by
  obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective (ShortComplex.homologyMap φ)).mp
    inferInstance (cycleClass T x hx)
  obtain ⟨y, hy, hya⟩ := cycleClass_surjective S a
  have hclass : cycleClass T (φ.τ₂ y) (map_cycle φ y hy) = cycleClass T x hx := by
    rw [← cycleClass_natural φ y hy, hya, ha]
  have hop : T.pOpcycles x = T.pOpcycles (φ.τ₂ y) := by
    have h := congrArg (fun z => T.homologyι z) hclass
    simpa only [cycleClass_ι] using h.symm
  obtain ⟨u, hu⟩ := (T.moduleCat_pOpcycles_eq_iff x (φ.τ₂ y)).mp hop
  refine ⟨y, hy, u, ?_⟩
  rw [hu]
  rw [← add_sub_assoc, add_sub_cancel_left]

end LowCohomology

variable {C D : CochainComplex (ModuleCat.{v} k) ℤ} (φ : C ⟶ D)

/-- A quasi-isomorphism in degree `n` reflects boundaries among degree-`n` cycles. -/
theorem quasiIsoAt_reflects_boundary (n : ℤ) [QuasiIsoAt φ n]
    (z : C.X n) (hz : C.d n (n + 1) z = 0)
    (w : D.X (n - 1)) (hw : φ.f n z = D.d (n - 1) n w) :
    ∃ y : C.X (n - 1), C.d (n - 1) n y = z := by
  let ψ := (HomologicalComplex.shortComplexFunctor' (ModuleCat k) (ComplexShape.up ℤ)
    (n - 1) n (n + 1)).map φ
  haveI : ShortComplex.QuasiIso ψ :=
    (quasiIsoAt_iff' φ (n - 1) n (n + 1) (by simp) (by simp)).mp inferInstance
  haveI : IsIso (ShortComplex.homologyMap ψ) := (ShortComplex.quasiIso_iff ψ).mp inferInstance
  exact LowCohomology.reflects_boundary ψ z hz w hw

/-- A quasi-isomorphism in degree `n` lifts every degree-`n` cycle modulo boundaries. -/
theorem quasiIsoAt_lifts_cocycle (n : ℤ) [QuasiIsoAt φ n]
    (x : D.X n) (hx : D.d n (n + 1) x = 0) :
    ∃ y : C.X n, C.d n (n + 1) y = 0 ∧
      ∃ u : D.X (n - 1), x = φ.f n y + D.d (n - 1) n u := by
  let ψ := (HomologicalComplex.shortComplexFunctor' (ModuleCat k) (ComplexShape.up ℤ)
    (n - 1) n (n + 1)).map φ
  haveI : ShortComplex.QuasiIso ψ :=
    (quasiIsoAt_iff' φ (n - 1) n (n + 1) (by simp) (by simp)).mp inferInstance
  haveI : IsIso (ShortComplex.homologyMap ψ) := (ShortComplex.quasiIso_iff ψ).mp inferInstance
  exact LowCohomology.lifts_cocycle ψ x hx

/-- The boundary-reflection consequence of an actual quasi-isomorphism. -/
theorem quasiIso_reflects_boundary [QuasiIso φ] (n : ℤ)
    (z : C.X n) (hz : C.d n (n + 1) z = 0)
    (w : D.X (n - 1)) (hw : φ.f n z = D.d (n - 1) n w) :
    ∃ y : C.X (n - 1), C.d (n - 1) n y = z :=
  quasiIsoAt_reflects_boundary φ n z hz w hw

/-- The cycle-lifting consequence of an actual quasi-isomorphism. -/
theorem quasiIso_lifts_cocycle [QuasiIso φ] (n : ℤ)
    (x : D.X n) (hx : D.d n (n + 1) x = 0) :
    ∃ y : C.X n, C.d n (n + 1) y = 0 ∧
      ∃ u : D.X (n - 1), x = φ.f n y + D.d (n - 1) n u :=
  quasiIsoAt_lifts_cocycle φ n x hx

/-- H¹ injectivity in the form needed to remove a gauge obstruction. -/
theorem quasiIso_H1_injective [QuasiIso φ]
    (z : C.X 1) (hz : C.d 1 2 z = 0) (w : D.X 0) (hw : φ.f 1 z = D.d 0 1 w) :
    ∃ y : C.X 0, C.d 0 1 y = z := by
  exact quasiIsoAt_reflects_boundary φ 1 z hz w hw

/-- H⁰ surjectivity, retaining the degree -1 correction term. -/
theorem quasiIso_H0_surjective [QuasiIso φ] (x : D.X 0) (hx : D.d 0 1 x = 0) :
    ∃ y : C.X 0, C.d 0 1 y = 0 ∧ ∃ u : D.X (-1), x = φ.f 0 y + D.d (-1) 0 u := by
  exact quasiIsoAt_lifts_cocycle φ 0 x hx

end

end EnvelopingIsomorphism.Deformation
