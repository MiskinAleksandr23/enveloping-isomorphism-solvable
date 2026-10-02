import EnvelopingIsomorphism.Deformation.Kontsevich.OneVertexNormalization

/-! The ordered Pi-coordinate integral is the genuine one-vertex chart integral.
The change of coordinates preserves volume and transports integrability as well as integrals.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open MeasureTheory

/-- The one-dimensional normalized real-coordinate chart. -/
def oneVertexMeasureChartOne : ℝ ≃ᵐ (Fin 1 → ℝ) :=
  (MeasurableEquiv.funUnique (Fin 1) ℝ).symm

/-- The two-dimensional normalized real-coordinate chart. -/
def oneVertexMeasureChartTwo : (ℝ × ℝ) ≃ᵐ (Fin 2 → ℝ) :=
  MeasurableEquiv.finTwoArrow.symm

/-- The three-dimensional chart uses the same right-associated product as the existing integral. -/
def oneVertexMeasureChartThree : (ℝ × ℝ × ℝ) ≃ᵐ (Fin 3 → ℝ) :=
  ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.finTwoArrow.symm).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).symm

@[simp] theorem oneVertexMeasureChartOne_apply (x : ℝ) :
    oneVertexMeasureChartOne x = ![x] := by
  ext i
  fin_cases i
  rfl

@[simp] theorem oneVertexMeasureChartTwo_apply (x : ℝ × ℝ) :
    oneVertexMeasureChartTwo x = ![x.1, x.2] := rfl

@[simp] theorem oneVertexMeasureChartThree_apply (x : ℝ × ℝ × ℝ) :
    oneVertexMeasureChartThree x = ![x.1, x.2.1, x.2.2] := by
  ext i
  fin_cases i <;> rfl

theorem oneVertexMeasureChartOne_preserving : MeasurePreserving oneVertexMeasureChartOne :=
  (volume_preserving_funUnique (Fin 1) ℝ).symm _

theorem oneVertexMeasureChartTwo_preserving : MeasurePreserving oneVertexMeasureChartTwo :=
  (volume_preserving_finTwoArrow ℝ).symm _

theorem oneVertexMeasureChartThree_preserving : MeasurePreserving oneVertexMeasureChartThree :=
  ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).symm _).comp
    ((MeasurePreserving.id (volume : Measure ℝ)).prod
      ((volume_preserving_finTwoArrow ℝ).symm _))

theorem strictMono_domain_zero : {x : Fin 0 → ℝ | StrictMono x} = Set.univ := by
  ext x
  simp [StrictMono]

theorem strictMono_domain_one : {x : Fin 1 → ℝ | StrictMono x} = Set.univ := by
  ext x
  simp [Fin.strictMono_iff_lt_succ]

theorem oneVertexMeasureChartTwo_preimage :
    oneVertexMeasureChartTwo ⁻¹' {x : Fin 2 → ℝ | StrictMono x} = orderedPairSet := by
  ext x
  simp [Fin.strictMono_iff_lt_succ, Fin.forall_fin_one, orderedPairSet]

theorem oneVertexMeasureChartThree_preimage :
    oneVertexMeasureChartThree ⁻¹' {x : Fin 3 → ℝ | StrictMono x} = orderedTripleSet := by
  ext x
  simp [Fin.strictMono_iff_lt_succ, Fin.forall_fin_two, orderedTripleSet]

/-- Genuine standard-coordinate integration agrees with the previously defined charts. -/
theorem integral_strictMono_eq_oneVertexChartIntegral (m : Fin 4)
    (F : (Fin m.val → ℝ) → ℝ) :
    (∫ x in {x : Fin m.val → ℝ | StrictMono x}, F x) = oneVertexChartIntegral m F := by
  fin_cases m
  · simp only [strictMono_domain_zero, Measure.restrict_univ, oneVertexChartIntegral]
  · rw [strictMono_domain_one, Measure.restrict_univ]
    simpa only [oneVertexChartIntegral, oneVertexMeasureChartOne_apply] using
      (oneVertexMeasureChartOne_preserving.integral_comp'
        (f := oneVertexMeasureChartOne) F).symm
  · have h := oneVertexMeasureChartTwo_preserving.setIntegral_preimage_emb
      oneVertexMeasureChartTwo.measurableEmbedding F {x : Fin 2 → ℝ | StrictMono x}
    simpa only [oneVertexMeasureChartTwo_preimage, oneVertexMeasureChartTwo_apply,
      oneVertexChartIntegral] using h.symm
  · have h := oneVertexMeasureChartThree_preserving.setIntegral_preimage_emb
      oneVertexMeasureChartThree.measurableEmbedding F {x : Fin 3 → ℝ | StrictMono x}
    simpa only [oneVertexMeasureChartThree_preimage, oneVertexMeasureChartThree_apply,
      oneVertexChartIntegral] using h.symm

/-- Absolute integrability is transported by the same actual measure-preserving equivalences. -/
theorem integrableOn_strictMono_iff_oneVertexChartIntegrable (m : Fin 4)
    (F : (Fin m.val → ℝ) → ℝ) :
    IntegrableOn F {x : Fin m.val → ℝ | StrictMono x} ↔ OneVertexChartIntegrable m F := by
  fin_cases m
  · simp only [strictMono_domain_zero, integrableOn_univ, OneVertexChartIntegrable]
  · rw [strictMono_domain_one, integrableOn_univ]
    simpa only [OneVertexChartIntegrable, Function.comp_def, oneVertexMeasureChartOne_apply] using
      (oneVertexMeasureChartOne_preserving.integrable_comp_emb
        oneVertexMeasureChartOne.measurableEmbedding (g := F)).symm
  · simpa only [oneVertexMeasureChartTwo_preimage, Function.comp_def,
      oneVertexMeasureChartTwo_apply, OneVertexChartIntegrable] using
      (oneVertexMeasureChartTwo_preserving.integrableOn_comp_preimage
        oneVertexMeasureChartTwo.measurableEmbedding
        (f := F) (s := {x : Fin 2 → ℝ | StrictMono x})).symm
  · simpa only [oneVertexMeasureChartThree_preimage, Function.comp_def,
      oneVertexMeasureChartThree_apply, OneVertexChartIntegrable] using
      (oneVertexMeasureChartThree_preserving.integrableOn_comp_preimage
        oneVertexMeasureChartThree.measurableEmbedding
        (f := F) (s := {x : Fin 3 → ℝ | StrictMono x})).symm

end EnvelopingIsomorphism.Deformation.Kontsevich
