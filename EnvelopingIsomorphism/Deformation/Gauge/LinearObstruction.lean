import EnvelopingIsomorphism.Deformation.LowCohomologyLifting
import Mathlib.Tactic.Abel

/-!
The cohomological step in gauge reflection.  A target gauge error lifting a
closed source displacement is removed by one source degree-zero correction,
up to a genuine target boundary from degree -1.
-/

namespace EnvelopingIsomorphism.Deformation.Gauge

open CategoryTheory

universe u v
variable {k : Type u} [Ring k]
variable {C D : CochainComplex (ModuleCat.{v} k) ℤ} (φ : C ⟶ D) [QuasiIso φ]

/-- H¹ injectivity and H⁰ surjectivity produce the two compatible gauge corrections.
The sign `d y = -δ` is the convention for gauge motion `[y,β]-dy`. -/
theorem remove_linear_obstruction (δ : C.X 1) (hδ : C.d 1 2 δ = 0)
    (x : D.X 0) (hx : φ.f 1 δ = -D.d 0 1 x) :
    ∃ y : C.X 0, ∃ u : D.X (-1),
      C.d 0 1 y = -δ ∧ x = φ.f 0 y + D.d (-1) 0 u := by
  obtain ⟨a, ha⟩ := quasiIso_H1_injective φ δ hδ (-x) (by simpa only [map_neg] using hx)
  have hc : D.d 0 1 (φ.f 0 a) = φ.f 1 δ := by
    have hm := congrArg (fun F : C.X 0 ⟶ D.X 1 => F a) (φ.comm 0 1)
    simpa only [ModuleCat.comp_apply, ha] using hm
  have hclosed : D.d 0 1 (x + φ.f 0 a) = 0 := by
    rw [map_add, hc, hx, add_neg_cancel]
  obtain ⟨b, hb, u, hu⟩ := quasiIso_H0_surjective φ (x + φ.f 0 a) hclosed
  refine ⟨b - a, u, ?_, ?_⟩
  · rw [map_sub, hb, ha, zero_sub]
  · rw [map_sub]
    calc
      x = (x + φ.f 0 a) - φ.f 0 a := by abel
      _ = (φ.f 0 b + D.d (-1) 0 u) - φ.f 0 a := by rw [hu]
      _ = φ.f 0 b - φ.f 0 a + D.d (-1) 0 u := by abel

end EnvelopingIsomorphism.Deformation.Gauge
