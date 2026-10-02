import EnvelopingIsomorphism.Rees.NativeGraphTaylorGauge
import EnvelopingIsomorphism.Deformation.Kontsevich.BinaryGeometricWeights

/-! Recover finite graph-product laws from the actual completed Maurer--Cartan equation. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 3

namespace EnvelopingIsomorphism.Rees.GraphProductAssociativity

open FormalSeries Deformation Deformation.Gauge
open PolynomialCochainCoordinates
open scoped PolynomialCochainCoordinates CompletedOperator CompletedPBWProduct
open scoped LaurentPolynomialCoefficients CompletedPolynomialInputs

section CoordinateTransport

universe u v
variable {k : Type u} [CommRing k]
    {V W X Y : Type v} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y]

theorem laurent_map_linearApply (e : V ≃ₗ[k] W) (f : X ≃ₗ[k] Y)
    (F : LaurentModule k (V →ₗ[k] X)) (x : LaurentModule k V) :
    LaurentModule.map f.toLinearMap (LaurentModule.linearApply F x) =
      LaurentModule.linearApply
        (LaurentModule.map (e.arrowCongr f).toLinearMap F) (LaurentModule.map e.toLinearMap x) := by
  apply Transport.laurent_map_bilinear_natural
  intro F x
  change f (F x) = f (F (e.symm (e x)))
  rw [e.symm_apply_apply]

theorem series_map_linearApply (e : V ≃ₗ[k] W) (f : X ≃ₗ[k] Y)
    (F : PowerSeriesModule k (V →ₗ[k] X)) (x : PowerSeriesModule k V) :
    PowerSeriesModule.map f.toLinearMap (PowerSeriesModule.linearApply F x) =
      PowerSeriesModule.linearApply
        (PowerSeriesModule.map (e.arrowCongr f).toLinearMap F) (PowerSeriesModule.map e.toLinearMap x) := by
  apply Transport.series_map_bilinear_natural
  intro F x
  change f (F x) = f (F (e.symm (e x)))
  rw [e.symm_apply_apply]

theorem laurent_map_extendBinary (e : V ≃ₗ[k] W)
    (B : LaurentModule k (Binary k V)) (x y : LaurentModule k V) :
    LaurentModule.map e.toLinearMap (LaurentModule.extendBinary B x y) =
      LaurentModule.extendBinary
        (LaurentModule.map (Transport.binaryEquiv e).toLinearMap B)
        (LaurentModule.map e.toLinearMap x) (LaurentModule.map e.toLinearMap y) := by
  simp only [LaurentModule.extendBinary_apply]
  rw [laurent_map_linearApply e e, laurent_map_linearApply e (e.arrowCongr e)]
  rfl

theorem series_map_extendBinary (e : V ≃ₗ[k] W)
    (B : PowerSeriesModule k (Binary k V)) (x y : PowerSeriesModule k V) :
    PowerSeriesModule.map e.toLinearMap (PowerSeriesModule.extendBinary B x y) =
      PowerSeriesModule.extendBinary
        (PowerSeriesModule.map (Transport.binaryEquiv e).toLinearMap B)
        (PowerSeriesModule.map e.toLinearMap x) (PowerSeriesModule.map e.toLinearMap y) := by
  simp only [PowerSeriesModule.extendBinary_apply]
  rw [series_map_linearApply e e, series_map_linearApply e (e.arrowCongr e)]
  rfl

theorem embed_familyEquiv (e : V ≃ₗ[k] W) (B : CompletedBinary.Families k V) :
    LaurentConjugation.embed (Transport.familyEquiv e B) =
      PowerSeriesModule.map (Transport.binaryEquiv (Transport.laurentEquiv e)).toLinearMap
        (LaurentConjugation.embed B) := by
  apply PowerSeriesModule.ext
  intro n
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  obtain ⟨a, rfl⟩ := (Transport.laurentEquiv e).surjective x
  obtain ⟨b, rfl⟩ := (Transport.laurentEquiv e).surjective y
  change LaurentModule.extendBinary
    (LaurentModule.map (Transport.binaryEquiv e).toLinearMap (PowerSeriesModule.coeffV n B))
    (Transport.laurentEquiv e a) (Transport.laurentEquiv e b) =
    Transport.laurentEquiv e
      (LaurentModule.extendBinary (PowerSeriesModule.coeffV n B)
        ((Transport.laurentEquiv e).symm (Transport.laurentEquiv e a))
        ((Transport.laurentEquiv e).symm (Transport.laurentEquiv e b)))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact (laurent_map_extendBinary e _ a b).symm

/-- Actual coordinate transport intertwines evaluation on every completed vector. -/
theorem vectorEquiv_binaryAction (e : V ≃ₗ[k] W) (B : CompletedBinary.Families k V)
    (x y : CompletedOperator.Vectors k V) :
    Transport.vectorEquiv e (CompletedBinary.binaryAction B x y) =
      CompletedBinary.binaryAction (Transport.familyEquiv e B)
        (Transport.vectorEquiv e x) (Transport.vectorEquiv e y) := by
  simp only [CompletedBinary.binaryAction_apply, embed_familyEquiv]
  exact series_map_extendBinary (Transport.laurentEquiv e) _ x y

theorem associative_familyEquiv (e : V ≃ₗ[k] W) (B : CompletedBinary.Families k V)
    (h : ∀ x y z, CompletedBinary.binaryAction B (CompletedBinary.binaryAction B x y) z =
      CompletedBinary.binaryAction B x (CompletedBinary.binaryAction B y z)) :
    ∀ x y z, CompletedBinary.binaryAction (Transport.familyEquiv e B)
        (CompletedBinary.binaryAction (Transport.familyEquiv e B) x y) z =
      CompletedBinary.binaryAction (Transport.familyEquiv e B) x
        (CompletedBinary.binaryAction (Transport.familyEquiv e B) y z) := by
  intro x y z
  obtain ⟨a, rfl⟩ := (Transport.vectorEquiv e).surjective x
  obtain ⟨b, rfl⟩ := (Transport.vectorEquiv e).surjective y
  obtain ⟨c, rfl⟩ := (Transport.vectorEquiv e).surjective z
  simpa only [vectorEquiv_binaryAction] using congrArg (Transport.vectorEquiv e) (h a b c)

end CoordinateTransport

section FiniteProduct

variable {k : Type*} [Field k] {d : ℕ}
    (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
    (w : (j : ℕ) → KontsevichGraph (j + 1) → Polynomial (Polynomial k))
    (c : Fin d → Fin d → Fin d → Polynomial (Polynomial k))

/-- Faithful evaluation in the genuine double completion reflects finite associativity. -/
theorem finiteProduct_associative_of_completed
    (h : ∀ x y z,
      CompletedBinary.binaryAction (CompletedGraphProduct.completedProduct s w c)
        (CompletedBinary.binaryAction (CompletedGraphProduct.completedProduct s w c) x y) z =
      CompletedBinary.binaryAction (CompletedGraphProduct.completedProduct s w c) x
        (CompletedBinary.binaryAction (CompletedGraphProduct.completedProduct s w c) y z)) :
    ∀ p q r, CompletedGraphProduct.finiteProduct s w c
        (CompletedGraphProduct.finiteProduct s w c p q) r =
      CompletedGraphProduct.finiteProduct s w c p
        (CompletedGraphProduct.finiteProduct s w c q r) := by
  intro p q r
  apply CompletedPolynomialInputs.embed_injective
  have he := h (CompletedPolynomialInputs.embed p) (CompletedPolynomialInputs.embed q)
    (CompletedPolynomialInputs.embed r)
  simpa only [CompletedGraphProduct.completedAction_polynomials] using he

end FiniteProduct

section NativeMaurerCartan

variable {k L : Type*} [Field k] {d : ℕ}
    [LieRing L] [LieAlgebra k L] {b : Module.Basis (Fin d) k L}
    (D : WeightData b)
    (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
    (w : (j : ℕ) → KontsevichGraph (j + 1) → k)
    (μ : LaurentModule k (Binary k (MvPolynomial (Fin d) k)))
    (hμ : ∀ a b c, LaurentConjugation.evaluateCoefficient μ
        (LaurentConjugation.evaluateCoefficient μ a b) c =
      LaurentConjugation.evaluateCoefficient μ a (LaurentConjugation.evaluateCoefficient μ b c))

include hμ

/-- The actual full Taylor evaluation is associative by its genuine closed-cochain MC equation. -/
theorem fullTaylor_associative_of_mc
    (hMC : quadraticCurvature (k := LaurentSeries k) (LaurentModule.differentialBinarySeries μ)
      (LaurentModule.insertBinarySeries (k := k) (A := MvPolynomial (Fin d) k))
      (GraphTaylorIdentification.fullTaylor D s w - PowerSeriesModule.single 0 μ) = 0) :
    ∀ x y z,
      CompletedBinary.binaryAction (GraphTaylorIdentification.fullTaylor D s w)
        (CompletedBinary.binaryAction (GraphTaylorIdentification.fullTaylor D s w) x y) z =
      CompletedBinary.binaryAction (GraphTaylorIdentification.fullTaylor D s w) x
        (CompletedBinary.binaryAction (GraphTaylorIdentification.fullTaylor D s w) y z) := by
  have h := (LaurentConjugation.mc_iff_associative μ hμ _).mp hMC
  have hadd : PowerSeriesModule.single 0 μ +
      (GraphTaylorIdentification.fullTaylor D s w - PowerSeriesModule.single 0 μ) =
        GraphTaylorIdentification.fullTaylor D s w := by abel
  rw [hadd] at h
  exact h

/-- Finite polynomial associativity is reflected through both faithful completions and
the actual monomial-coordinate equivalence, starting from the native Taylor MC equation. -/
theorem finiteProduct_associative_of_nativeMC
    (hMC : quadraticCurvature (k := LaurentSeries k) (LaurentModule.differentialBinarySeries μ)
      (LaurentModule.insertBinarySeries (k := k) (A := MvPolynomial (Fin d) k))
      (GraphTaylorIdentification.fullTaylor D s w - PowerSeriesModule.single 0 μ) = 0) :
    ∀ p q r,
      CompletedGraphProduct.finiteProduct s (GraphTaylorIdentification.parameterWeights w)
        (GraphStarComparison.tensor D)
        (CompletedGraphProduct.finiteProduct s (GraphTaylorIdentification.parameterWeights w)
          (GraphStarComparison.tensor D) p q) r =
      CompletedGraphProduct.finiteProduct s (GraphTaylorIdentification.parameterWeights w)
        (GraphStarComparison.tensor D) p
        (CompletedGraphProduct.finiteProduct s (GraphTaylorIdentification.parameterWeights w)
          (GraphStarComparison.tensor D) q r) := by
  apply finiteProduct_associative_of_completed
  have h := associative_familyEquiv
    (GraphTaylorIdentification.coordinateEquiv (k := k) (d := d))
    (GraphTaylorIdentification.fullTaylor D s w) (fullTaylor_associative_of_mc D s w μ hμ hMC)
  have heq : Transport.familyEquiv (GraphTaylorIdentification.coordinateEquiv (k := k) (d := d))
      (GraphTaylorIdentification.fullTaylor D s w) = GraphTaylorIdentification.graphFamily D s w :=
    GraphTaylorIdentification.coordinateFullTaylor_eq_graphFamily D s w
  rw [heq] at h
  exact h

end NativeMaurerCartan

section CanonicalWeights

variable {k L : Type*} [Field k] [Algebra ℝ k] {d : ℕ}
    [LieRing L] [LieAlgebra k L] {b : Module.Basis (Fin d) k L} (D : WeightData b)

theorem scalarMap_binaryWeight (j : ℕ) (Γ : KontsevichGraph (j + 1)) :
    GraphPBWScalarBridge.scalarMap k
      (GraphTaylorIdentification.parameterWeights (Kontsevich.GeometricWeights.binaryWeightOver k) j Γ) =
        Kontsevich.GeometricWeights.binaryWeightOver (LaurentPolynomialCoefficients.ScalarRing k) j Γ := by
  simpa only [GraphTaylorIdentification.parameterWeights, Kontsevich.GeometricWeights.binaryWeightOver,
    Polynomial.algebraMap_apply] using
      GeometricStarComparison.scalarMap_real (k := k) (Kontsevich.GeometricWeights.binaryWeight j Γ)

theorem geometricFirstSets_univ :
    KontsevichGraph.geometricFirstSets (fun _ => Finset.univ) = fun _ => Finset.univ := by
  funext j
  cases j <;> rfl

/-- The actual completed finite product uses exactly the canonical geometric weights
and the native scaled Rees Lie basis, over the faithful Laurent-polynomial coefficient ring. -/
theorem canonicalFiniteProduct_eq :
    CompletedGraphProduct.finiteProduct (fun _ => Finset.univ)
      (GraphTaylorIdentification.parameterWeights (Kontsevich.GeometricWeights.binaryWeightOver k))
      (GraphStarComparison.tensor D) =
    KontsevichGraph.polynomialProductBilinear (fun _ => Finset.univ)
      (Kontsevich.GeometricWeights.binaryWeightOver (LaurentPolynomialCoefficients.ScalarRing k))
      (Poisson.structureCoeff (GeometricStarComparison.scaledBasis D)) := by
  unfold CompletedGraphProduct.finiteProduct
  congr 1
  · funext j Γ
    exact scalarMap_binaryWeight j Γ
  · funext i j r
    exact (GeometricStarComparison.scaledBasis_coeff D i j r).symm

variable
    (μ : LaurentModule k (Binary k (MvPolynomial (Fin d) k)))
    (hμ : ∀ a b c, LaurentConjugation.evaluateCoefficient μ
        (LaurentConjugation.evaluateCoefficient μ a b) c =
      LaurentConjugation.evaluateCoefficient μ a (LaurentConjugation.evaluateCoefficient μ b c))

include hμ

/-- Both finite unit laws come from the actual geometric weights; finite associativity
comes from the native completed MC equation via the proved faithful embeddings. -/
theorem canonicalProductLaws_of_nativeMC
    (hMC : quadraticCurvature (k := LaurentSeries k) (LaurentModule.differentialBinarySeries μ)
      (LaurentModule.insertBinarySeries (k := k) (A := MvPolynomial (Fin d) k))
      (GraphTaylorIdentification.fullTaylor D (fun _ => Finset.univ)
          (Kontsevich.GeometricWeights.binaryWeightOver k) - PowerSeriesModule.single 0 μ) = 0) :
    KontsevichGraph.ProductLaws (fun _ => Finset.univ)
      (Kontsevich.GeometricWeights.binaryWeightOver (LaurentPolynomialCoefficients.ScalarRing k))
      (Poisson.structureCoeff (GeometricStarComparison.scaledBasis D)) := by
  apply Kontsevich.GeometricWeights.productLaws_of_associative
  have h := finiteProduct_associative_of_nativeMC D (fun _ => Finset.univ)
    (Kontsevich.GeometricWeights.binaryWeightOver k) μ hμ hMC
  rw [canonicalFiniteProduct_eq] at h
  exact h

/-- The law bundle in precisely the parameterized F11 interface of NativeGraphTaylorGauge. -/
theorem geometricProductLaws_of_nativeMC
    (hMC : quadraticCurvature (k := LaurentSeries k) (LaurentModule.differentialBinarySeries μ)
      (LaurentModule.insertBinarySeries (k := k) (A := MvPolynomial (Fin d) k))
      (GraphTaylorIdentification.fullTaylor D (fun _ => Finset.univ)
          (Kontsevich.GeometricWeights.binaryWeightOver k) - PowerSeriesModule.single 0 μ) = 0) :
    GeometricStarComparison.ProductLaws (fun _ => Finset.univ)
      (NativeGraphTaylorGauge.parameterHigher
        (fun j Γ => Kontsevich.GeometricWeights.binaryWeightOver k (j + 1) Γ)) D := by
  have hw : GeometricStarComparison.targetWeights
      (NativeGraphTaylorGauge.parameterHigher
        (fun j Γ => Kontsevich.GeometricWeights.binaryWeightOver k (j + 1) Γ)) =
      fun j Γ => Kontsevich.GeometricWeights.binaryWeightOver
        (LaurentPolynomialCoefficients.ScalarRing k) (j + 1) Γ := by
    funext j Γ
    exact scalarMap_binaryWeight (j + 1) Γ
  change KontsevichGraph.ProductLaws _ _ _
  rw [geometricFirstSets_univ, hw,
    Kontsevich.GeometricWeights.geometricFirstWeights_eq_binaryWeightOver]
  exact canonicalProductLaws_of_nativeMC D μ hμ hMC

end CanonicalWeights

end EnvelopingIsomorphism.Rees.GraphProductAssociativity
