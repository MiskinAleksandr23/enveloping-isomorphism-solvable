import EnvelopingIsomorphism.Deformation.Kontsevich.CompactOrthantStokes

/-! Coordinate boundary hyperplanes are null, so orthant integrals can use
strictly positive radial coordinates without changing any integral. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.OrthantInteriorIntegration

open Set MeasureTheory BoxStokes CompactOrthantStokes

def strictOrthant {d : ℕ} (S : Finset (Fin d)) : Set (Coord d) :=
  {z | ∀ j ∈ S, 0 < z j}

theorem strictOrthant_ae_eq_orthant {d : ℕ} (S : Finset (Fin d)) :
    strictOrthant S =ᵐ[volume] orthant S := by
  rw [volume_pi]
  simpa only [Set.pi, strictOrthant, orthant, mem_Ioi, mem_Ici, Finset.mem_coe] using
    (Measure.pi_Ioi_ae_eq_pi_Ici (μ := fun _ : Fin d => (volume : Measure ℝ))
      (s := (S : Set (Fin d))) (f := fun _ => (0 : ℝ)))

theorem integral_orthant_eq_strictOrthant {d : ℕ} (S : Finset (Fin d)) (f : Coord d → ℝ) :
    (∫ z in orthant S, f z) = ∫ z in strictOrthant S, f z :=
  setIntegral_congr_set (strictOrthant_ae_eq_orthant S).symm

end EnvelopingIsomorphism.Deformation.Kontsevich.OrthantInteriorIntegration
