import EnvelopingIsomorphism.FormalSeries.BinaryAssociator

/-! Faithful coefficient embeddings detect the genuine complete MC equation.
This keeps completed Laurent cochains inside their own coefficient space while
testing associativity on actual Laurent-valued functions. -/

noncomputable section

set_option maxSynthPendingDepth 3

namespace EnvelopingIsomorphism.Deformation.Gauge

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule

variable {k C T A : Type*} [CommRing k]
variable [AddCommGroup C] [Module k C] [AddCommGroup T] [Module k T]
variable [AddCommGroup A] [Module k A]

theorem seriesMap_injective {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (f : V →ₗ[k] W) (hf : Function.Injective f) :
    Function.Injective (map f) := by
  intro p q h
  apply PowerSeriesModule.ext
  intro n
  apply hf
  exact congrArg (coeffV n) h

theorem curvature_embedding
    (d : C →ₗ[k] T) (I : C →ₗ[k] C →ₗ[k] T)
    (ι : C →ₗ[k] Binary k A) (κ : T →ₗ[k] Ternary k A) (μ : Binary k A)
    (hd : ∀ c, κ (d c) = differentialTwo μ (ι c))
    (hI : ∀ c e, κ (I c e) = insertBinary (ι c) (ι e))
    (b : PowerSeriesModule k C) :
    map κ (quadraticCurvature d I b) =
      quadraticCurvature (differentialTwoLinear μ) insertBinaryLinear (map ι b) := by
  apply PowerSeriesModule.ext
  intro n
  simp only [quadraticCurvature, coeffV_map, coeffV_add, map_add,
    coeffV_applyBilinear, map_sum, hd, differentialTwoLinear_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro ij hij
  exact hI _ _

/-- Associativity is detected by the faithful ternary coefficient embedding. -/
theorem quadratic_MC_iff_associative_of_embedding
    (d : C →ₗ[k] T) (I : C →ₗ[k] C →ₗ[k] T)
    (ι : C →ₗ[k] Binary k A) (κ : T →ₗ[k] Ternary k A) (hκ : Function.Injective κ)
    (μ : Binary k A) (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c))
    (hd : ∀ c, κ (d c) = differentialTwo μ (ι c))
    (hI : ∀ c e, κ (I c e) = insertBinary (ι c) (ι e))
    (b : PowerSeriesModule k C) :
    quadraticCurvature d I b = 0 ↔
      ∀ p q r, extendBinary (single 0 μ + map ι b)
          (extendBinary (single 0 μ + map ι b) p q) r =
        extendBinary (single 0 μ + map ι b) p (extendBinary (single 0 μ + map ι b) q r) := by
  rw [← quadratic_MC_iff_associative μ hμ]
  rw [← curvature_embedding d I ι κ μ hd hI]
  exact ((seriesMap_injective κ hκ).eq_iff' (map_zero (map κ))).symm

/-- A positive coefficient family gives a genuine associative product after evaluation. -/
def associativeMCEmbed
    (d : C →ₗ[k] T) (I : C →ₗ[k] C →ₗ[k] T)
    (ι : C →ₗ[k] Binary k A) (κ : T →ₗ[k] Ternary k A) (μ : Binary k A)
    (hd : ∀ c, κ (d c) = differentialTwo μ (ι c))
    (hI : ∀ c e, κ (I c e) = insertBinary (ι c) (ι e))
    (b : MCSeries d I) : MCSeries (differentialTwoLinear μ) insertBinaryLinear :=
  ⟨map ι b.val, by rw [coeffV_map, b.property.1, map_zero], by
    rw [← curvature_embedding d I ι κ μ hd hI, b.property.2, map_zero]⟩

theorem associativeMCEmbed_injective
    (d : C →ₗ[k] T) (I : C →ₗ[k] C →ₗ[k] T)
    (ι : C →ₗ[k] Binary k A) (hι : Function.Injective ι)
    (κ : T →ₗ[k] Ternary k A) (μ : Binary k A)
    (hd : ∀ c, κ (d c) = differentialTwo μ (ι c))
    (hI : ∀ c e, κ (I c e) = insertBinary (ι c) (ι e)) :
    Function.Injective (associativeMCEmbed d I ι κ μ hd hI) := by
  intro b c h
  apply Subtype.ext
  exact seriesMap_injective ι hι (congrArg Subtype.val h)

end EnvelopingIsomorphism.Deformation.Gauge
