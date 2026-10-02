import EnvelopingIsomorphism.Deformation.Gauge.CurvatureLeading
import EnvelopingIsomorphism.Deformation.Gauge.Tangent
import EnvelopingIsomorphism.Deformation.Gauge.UnitGroup
import EnvelopingIsomorphism.Deformation.Gauge.LowTangent

/-!
The elementary, forward-path interface used by gauge reflection.

The producer must construct actual gauge actions, an actual Taylor map taking
MC elements to MC elements, elementary source exponentials, their integrated
target path lifts, and the target boundary stabilizers.  In the Kontsevich
application the path-lift identities follow from the tangent/path identity and
PathOrderedExp.  This structure contains no reflection/existence-of-source-orbit
field; that conclusion is proved from middle exactness of the explicit low tangent sequence below.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open CategoryTheory
open EnvelopingIsomorphism.FormalSeries
open PowerSeriesModule

universe u v w
variable {k : Type u} [CommRing k]
variable {C D : CochainComplex (ModuleCat.{v} k) ℤ}
variable (φ : LowTangent C D)
variable (BC : C.X 1 →ₗ[k] C.X 1 →ₗ[k] C.X 2)
variable (BD : D.X 1 →ₗ[k] D.X 1 →ₗ[k] D.X 2)
variable (S : Type w) [Group S]
variable (RS RT : Type*) [Ring RS] [Ring RT]
variable [MulAction S (MCSeries (C.d 1 2).hom BC)]
variable [MulAction (GaugeUnit RT) (MCSeries (D.d 1 2).hom BD)]

structure ElementaryComparison where
  sourceOperators : S →* GaugeUnit RS
  targetCoordinates : RT ≃+ D.X 0
  taylor : TaylorFamily (k := k) (V := C.X 1) (W := D.X 1)
  linear_eq : taylorLinear taylor = φ.one
  quantize : MCSeries (C.d 1 2).hom BC → MCSeries (D.d 1 2).hom BD
  quantize_eq (b : MCSeries (C.d 1 2).hom BC) : (quantize b).val = taylorApply taylor b.val
  sourceElementary (N : ℕ) (hN : 0 < N) (y : C.X 0) : S
  source_near (N : ℕ) (hN : 0 < N) (y : C.X 0) :
    NearIdentity N (sourceOperators (sourceElementary N hN y)).series
  source_agree (N : ℕ) (hN : 0 < N) (y : C.X 0) (b : MCSeries (C.d 1 2).hom BC) :
    AgreeBelow N (sourceElementary N hN y • b).val b.val
  source_leading (N : ℕ) (hN : 0 < N) (y : C.X 0) (b : MCSeries (C.d 1 2).hom BC) :
    coeffV N (sourceElementary N hN y • b).val - coeffV N b.val = -C.d 0 1 y
  target_leading (N : ℕ) (hN : 0 < N) (G : GaugeUnit RT)
      (hG : NearIdentity N G.series) (b : MCSeries (D.d 1 2).hom BD) :
    coeffV N (G • b).val - coeffV N b.val = -D.d 0 1 (targetCoordinates (PowerSeries.coeff N G.series))
  pathLift (N : ℕ) (hN : 0 < N) (y : C.X 0) (b : MCSeries (C.d 1 2).hom BC) : GaugeUnit RT
  pathLift_near (N : ℕ) (hN : 0 < N) (y : C.X 0) (b : MCSeries (C.d 1 2).hom BC) :
    NearIdentity N (pathLift N hN y b).series
  pathLift_leading (N : ℕ) (hN : 0 < N) (y : C.X 0) (b : MCSeries (C.d 1 2).hom BC) :
    targetCoordinates (PowerSeries.coeff N (pathLift N hN y b).series) = φ.zero y
  pathLift_action (N : ℕ) (hN : 0 < N) (y : C.X 0) (b : MCSeries (C.d 1 2).hom BC) :
    pathLift N hN y b • quantize b = quantize (sourceElementary N hN y • b)
  boundary (N : ℕ) (hN : 0 < N) (u : D.X (-1)) (b : MCSeries (D.d 1 2).hom BD) : GaugeUnit RT
  boundary_near (N : ℕ) (hN : 0 < N) (u : D.X (-1)) (b : MCSeries (D.d 1 2).hom BD) :
    NearIdentity N (boundary N hN u b).series
  boundary_leading (N : ℕ) (hN : 0 < N) (u : D.X (-1)) (b : MCSeries (D.d 1 2).hom BD) :
    targetCoordinates (PowerSeries.coeff N (boundary N hN u b).series) = D.d (-1) 0 u
  boundary_fixes (N : ℕ) (hN : 0 < N) (u : D.X (-1)) (b : MCSeries (D.d 1 2).hom BD) :
    boundary N hN u b • b = b

/-- The original full chain-map interface is a special case. A quasi-isomorphism
supplies the needed middle exactness by `LowTangent.ofChainMap_isMiddleExact`. -/
abbrev ChainElementaryComparison (ψ : C ⟶ D) :=
  ElementaryComparison (LowTangent.ofChainMap ψ) BC BD S RS RT

variable {φ BC BD S RS RT}

theorem AgreeBelow.trans {V : Type*} [AddCommGroup V] [Module k V] {N : ℕ}
    {a b c : PowerSeriesModule k V} (hab : AgreeBelow N a b) (hbc : AgreeBelow N b c) :
    AgreeBelow N a c := fun i hi => (hab i hi).trans (hbc i hi)

theorem AgreeBelow.succ {V : Type*} [AddCommGroup V] [Module k V] {N : ℕ}
    {a b : PowerSeriesModule k V} (hab : AgreeBelow N a b) (hnext : coeffV N a = coeffV N b) :
    AgreeBelow (N + 1) a b := by
  intro i hi
  by_cases h : i < N
  · exact hab i h
  · have he : i = N := by omega
    simpa only [he] using hnext

/-- One genuine order of gauge reflection, including the degree -1 stabilizer correction. -/
theorem ElementaryComparison.improve [φ.IsMiddleExact]
    (F : ElementaryComparison φ BC BD S RS RT)
    (N : ℕ) (hN : 0 < N) (b c : MCSeries (C.d 1 2).hom BC)
    (G : GaugeUnit RT) (hG : NearIdentity N G.series)
    (hbc : AgreeBelow N b.val c.val) (hmap : G • F.quantize b = F.quantize c) :
    ∃ y : C.X 0, ∃ G' : GaugeUnit RT,
      NearIdentity (N + 1) G'.series ∧
      AgreeBelow (N + 1) (F.sourceElementary N hN y • b).val c.val ∧
      G' • F.quantize (F.sourceElementary N hN y • b) = F.quantize c := by
  let δ := coeffV N c.val - coeffV N b.val
  have hδ : C.d 1 2 δ = 0 := c.leading_closed b N hbc.symm
  have hQ : coeffV N (F.quantize c).val - coeffV N (F.quantize b).val = φ.one δ := by
    rw [F.quantize_eq, F.quantize_eq,
      taylorApply_leading_difference F.taylor N hN c.val b.val c.property.1 b.property.1 hbc.symm,
      F.linear_eq]
  have hx : φ.one δ = -D.d 0 1 (F.targetCoordinates (PowerSeries.coeff N G.series)) := by
    rw [← hQ, ← hmap]
    exact F.target_leading N hN G hG (F.quantize b)
  obtain ⟨y, u, hy, hu⟩ := φ.remove_obstruction δ hδ
    (F.targetCoordinates (PowerSeries.coeff N G.series)) hx
  let H := F.pathLift N hN y b
  let B := F.boundary N hN u (F.quantize c)
  have hcoeff : PowerSeries.coeff N G.series = PowerSeries.coeff N H.series + PowerSeries.coeff N B.series := by
    apply F.targetCoordinates.injective
    rw [map_add, F.pathLift_leading, F.boundary_leading]
    exact hu
  refine ⟨y, B⁻¹ * G * H⁻¹, ?_, ?_, ?_⟩
  · exact GaugeUnit.corrected_near hN G H B hG (F.pathLift_near N hN y b)
      (F.boundary_near N hN u (F.quantize c)) hcoeff
  · apply (F.source_agree N hN y b |>.trans hbc).succ
    have hs := F.source_leading N hN y b
    rw [hy] at hs
    dsimp [δ] at hs
    have ha := congrArg (fun z : C.X 1 => z + coeffV N b.val) hs
    simpa only [neg_neg, sub_add_cancel] using ha
  · have hB : B • F.quantize c = F.quantize c := F.boundary_fixes N hN u (F.quantize c)
    rw [mul_smul, mul_smul, ← F.pathLift_action N hN y b, inv_smul_smul, hmap]
    exact (inv_smul_eq_iff.mpr hB.symm)

end EnvelopingIsomorphism.Deformation.Gauge
