import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCountableLocalization

/-! Actual compact local graph forms are integrable on their native strict
faces. Their countable product-coordinate decomposition therefore needs no
additional integrability premise. All lower-face orientation signs persist. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.NativePairedFaceIntegration

open Configuration BoxStokes CompactOrthantStokes MeasureTheory
open ForestGlobalGraphStokes ForestRadialFaceClassification ForestRadialFaceLocalization
open PairedForestCountableLocalization PairedForestSmoothProduct PairedForestProductChart
open ForestOrthantRealization
open scoped Classical

variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m)
  (o : ForestRadialFaceClassification.Orbit 0 x)
  (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
  (edges : Fin r → GraphForms.Edge n m)
  (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
  (κ : Ambient 0 x → ℝ)

def nativeDensity : Coord r → ℝ := fun z =>
  facePullback (localForm hdim x ρ edges hloop κ) (axis hdim x o) 0 z (standardBasis r)

theorem integrableOn_nativeDensity
    (hω : ContDiff ℝ 1 (localForm hdim x ρ edges hloop κ))
    (hc : HasCompactSupport (localForm hdim x ρ edges hloop κ)) :
    IntegrableOn (nativeDensity hdim x o ρ edges hloop κ) (source hdim x o) := by
  have h := integrableOn_lower_face (localForm hdim x ρ edges hloop κ)
    (radialIndices hdim x) hω.continuous hc (axis hdim x o)
  apply h.mono_set
  intro z hz j hj
  exact (hz.1 j hj).le

variable (ho : kind 0 x o = .paired)

def productDensity (j : Index hdim x o ho) : PairedForestSmoothProduct.Product x o ho → ℝ :=
  PairedForestCartesianChange.pushforward hdim x o ho j.val
    (nativeDensity hdim x o ρ edges hloop κ)

def productIntegral (j : Index hdim x o ho) : ℝ :=
  ∫ p in localChart hdim x o ho j.val '' piece hdim x o ho j,
    productDensity hdim x o ρ edges hloop κ ho j p

theorem integrableOn_productDensity
    (hω : ContDiff ℝ 1 (localForm hdim x ρ edges hloop κ))
    (hc : HasCompactSupport (localForm hdim x ρ edges hloop κ))
    (j : Index hdim x o ho) :
    IntegrableOn (productDensity hdim x o ρ edges hloop κ ho j)
      (localChart hdim x o ho j.val '' piece hdim x o ho j) :=
  integrableOn_product_piece hdim x o ho _
    (integrableOn_nativeDensity hdim x o ρ edges hloop κ hω hc) j

theorem hasSum_productIntegral
    (hω : ContDiff ℝ 1 (localForm hdim x ρ edges hloop κ))
    (hc : HasCompactSupport (localForm hdim x ρ edges hloop κ)) :
    HasSum (productIntegral hdim x o ρ edges hloop κ ho)
      (∫ z in source hdim x o, nativeDensity hdim x o ρ edges hloop κ z) :=
  hasSum_integral_product hdim x o ho _
    (integrableOn_nativeDensity hdim x o ρ edges hloop κ hω hc)

/-- The actual oriented native Stokes contribution is this convergent product
series, with integrability derived from the constructed local graph form. -/
theorem hasSum_signed_contribution
    (hω : ContDiff ℝ 1 (localForm hdim x ρ edges hloop κ))
    (hc : HasCompactSupport (localForm hdim x ρ edges hloop κ))
    (hmatch : LocalizationAgreement x ρ edges hloop κ) (ε : ℝ) :
    HasSum (fun j : Index hdim x o ho =>
      (ε * -((-1 : ℝ) ^ (axis hdim x o).val)) * productIntegral hdim x o ρ edges hloop κ ho j)
      (ε * contribution hdim x (localForm hdim x ρ edges hloop κ) o) := by
  have h := (hasSum_productIntegral hdim x o ρ edges hloop κ ho hω hc).mul_left
    (ε * -((-1 : ℝ) ^ (axis hdim x o).val))
  rw [contribution_eq_integral_source hdim x o ρ edges hloop κ hmatch]
  simpa only [smul_eq_mul, mul_assoc, nativeDensity] using h

end EnvelopingIsomorphism.Deformation.Kontsevich.NativePairedFaceIntegration
