import EnvelopingIsomorphism.Deformation.MixedGraphTargetProfiles
import EnvelopingIsomorphism.Deformation.GraphGraftFibreCoefficients

/-! Exact fibres of the genuine mixed graft maps. The distinguished vector
placement, both factor graphs, and every incoming-edge choice are recovered
from the output. Thus fixed-block mixed grafts have no hidden multiplicity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedGraphTargetProfiles
open scoped BigOperators Classical
open KontsevichGraph.General MixedGraphProfileCarrier GraphCoefficientProfiles
open UniformBinaryGraphs
variable {a b n N m : ℕ}

theorem transportGraph_injective {q : Fin n → ℕ} (h : n = N)
    (e : Fin n ≃ Fin N) : Function.Injective (transportGraph (q := q) (m := m) h e) := by
  subst N
  exact (Graph.profileGraphEquiv q m e).injective

theorem ofProfile_injective {q : Fin (n + 1) → ℕ} (i : Fin (n + 1))
    (h : q = Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i) :
    Function.Injective (ofProfile (m := m) i h) := by
  subst q
  intro Γ Δ he
  exact (Sigma.mk.inj he).2.eq

/-- Fixed-block output grafts determine their actual labelled data uniquely. -/
theorem outputGraft_injective :
    Function.Injective (fun D : OutputIndex a b => outputGraft D.1 D.2.1 D.2.2) := by
  rintro ⟨⟨i, Γ⟩, Δ, χ⟩ ⟨⟨j, Γ'⟩, Δ', χ'⟩ h
  have hij : i = j := (vectorEmbedding a b).injective (congrArg VectorGraph.vertex h)
  subst j
  have hg := transportGraph_injective (outputCount a b) (outputVertexEquiv a b)
    (ofProfile_injective _ (outputArity i) h)
  have hd := Graph.graftDataGraph_injective (q := vectorArity i)
    (p := fun _ : Fin b => 2) (l := 1) 0
    (a₁ := ⟨Γ, Δ, χ⟩) (a₂ := ⟨Γ', Δ', χ'⟩) hg
  cases hd
  rfl

/-- The block exchange in input grafts also preserves all labelled data. -/
theorem inputGraft_injective (r : Fin 2) :
    Function.Injective (fun D : InputIndex a b r => inputGraft D.1 D.2.1 r D.2.2) := by
  rintro ⟨⟨i, Γ⟩, Δ, χ⟩ ⟨⟨j, Γ'⟩, Δ', χ'⟩ h
  have hij : i = j := (vectorEmbedding a b).injective (congrArg VectorGraph.vertex h)
  subst j
  have hg := transportGraph_injective (inputCount a b) (inputVertexEquiv a b)
    (ofProfile_injective _ (inputArity i) h)
  have hd := Graph.graftDataGraph_injective (q := fun _ : Fin b => 2)
    (p := vectorArity i) (l := 0) r
    (a₁ := ⟨Δ, Γ, χ⟩) (a₂ := ⟨Δ', Γ', χ'⟩) hg
  cases hd
  rfl

variable {k : Type*} [CommRing k]

private theorem pushforward_at_injective {I A : Type*} [Fintype I]
    (f : I → A) (hf : Function.Injective f) (w : I → k) (i : I) :
    pushforward f w (f i) = w i := by
  simp only [pushforward, hf.eq_iff]
  simp

/-- A mixed output fibre contributes exactly the two actual scalar weights. -/
theorem outputProfile_graft (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k)
    (Γ : VectorGraph a 1) (Δ : BinaryGraph b 2) (χ : OutputChoices (b := b) Γ) :
    outputProfile w v (outputGraft Γ Δ χ) = w Γ * v Δ := by
  exact pushforward_at_injective _ outputGraft_injective _ ⟨Γ, Δ, χ⟩

/-- A mixed input fibre has the same exact multiplicity one. -/
theorem inputProfile_graft (r : Fin 2) (w : VectorGraph a 1 → k)
    (v : BinaryGraph b 2 → k) (Γ : VectorGraph a 1) (Δ : BinaryGraph b 2)
    (χ : InputChoices (a := a) Δ r) :
    inputProfile r w v (inputGraft Γ Δ r χ) = w Γ * v Δ := by
  exact pushforward_at_injective _ (inputGraft_injective r) _ ⟨Γ, Δ, χ⟩

/-- Retain the vector placement while identifying native output-block graphs
with the common mixed carrier. -/
def outputCarrier (i : Fin (a + 1))
    (H : Graph (graftArity (vectorArity i) (fun _ : Fin b => 2)) 2) :
    VectorGraph (a + b) 2 :=
  ofProfile (vectorEmbedding a b i) (outputArity i)
    (transportGraph (outputCount a b) (outputVertexEquiv a b) H)

/-- Native input-block graphs use the actual exchange of the two vertex blocks. -/
def inputCarrier (i : Fin (a + 1))
    (H : Graph (graftArity (fun _ : Fin b => 2) (vectorArity i)) 2) :
    VectorGraph (a + b) 2 :=
  ofProfile (vectorEmbedding a b i) (inputArity i)
    (transportGraph (inputCount a b) (inputVertexEquiv a b) H)

private theorem pushforward_comp_apply {I A B : Type*} [Fintype I] [Fintype A]
    (f : I → A) (g : A → B) (w : I → k) (b : B) :
    pushforward g (pushforward f w) b = pushforward (g ∘ f) w b := by
  classical
  have h := evaluation_pushforward (fun a => if g a = b then (1 : k) else 0) f w
  simpa only [evaluation_apply, pushforward_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Function.comp_apply] using h

/-- Exact finite scalar bridge from the native output graft profiles supplied
by geometric boundary matching to the retained-placement mixed target table. -/
theorem outputProfile_eq_native (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k) :
    outputProfile w v = ∑ i : Fin (a + 1), pushforward (outputCarrier (b := b) i)
      (GraphGeneralWeightedGraft.graftProfile 0 (fun Γ => w ⟨i, Γ⟩) v) := by
  funext H
  simp only [Finset.sum_apply, GraphGeneralWeightedGraft.graftProfile]
  simp only [pushforward_comp_apply]
  simp only [outputProfile_apply, pushforward_apply,
    Fintype.sum_sigma, Function.comp_apply]
  rfl

/-- The two binary input slots share the same precise native scalar bridge. -/
theorem inputProfile_eq_native (r : Fin 2) (w : VectorGraph a 1 → k)
    (v : BinaryGraph b 2 → k) :
    inputProfile r w v = ∑ i : Fin (a + 1), pushforward (inputCarrier (b := b) i)
      (GraphGeneralWeightedGraft.graftProfile r v (fun Γ => w ⟨i, Γ⟩)) := by
  funext H
  simp only [Finset.sum_apply, GraphGeneralWeightedGraft.graftProfile]
  simp only [pushforward_comp_apply]
  simp only [inputProfile_apply, pushforward_apply,
    Fintype.sum_sigma, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Δ _
  apply Finset.sum_congr rfl
  intro Γ _
  apply Finset.sum_congr rfl
  intro χ _
  dsimp [inputCarrier, inputGraft]
  rw [mul_comm]

/-- At an admissible native boundary graph, the mixed output coefficient is
exactly the product of its genuinely extracted factors. -/
theorem outputProfile_carrier_extracted (i : Fin (a + 1))
    (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k)
    (H : Graph (graftArity (vectorArity i) (fun _ : Fin b => 2)) 2)
    (hc : H.InnerClosed (q := vectorArity i) (p := fun _ : Fin b => 2) (m := 0) (l := 1) 0)
    (hd : H.CoarseDistinct (q := vectorArity i) (p := fun _ : Fin b => 2) (m := 0) (l := 1) 0) :
    outputProfile w v (outputCarrier i H) =
      w ⟨i, H.extractedOuter (q := vectorArity i) (p := fun _ : Fin b => 2) (m := 0) (l := 1) 0 hd⟩ * v (H.extractedInner (q := vectorArity i) (p := fun _ : Fin b => 2) (m := 0) (l := 1) 0 hc) := by
  have hh := H.graft_extracted (q := vectorArity i) (p := fun _ : Fin b => 2) (m := 0) (l := 1) 0 hc hd
  have he := outputProfile_graft w v ⟨i, H.extractedOuter (q := vectorArity i) (p := fun _ : Fin b => 2) (m := 0) (l := 1) 0 hd⟩
    (H.extractedInner (q := vectorArity i) (p := fun _ : Fin b => 2) (m := 0) (l := 1) 0 hc) (H.extractedChoices (q := vectorArity i) (p := fun _ : Fin b => 2) (m := 0) (l := 1) 0 hd)
  change outputProfile w v (outputCarrier i
    ((H.extractedOuter (q := vectorArity i) (p := fun _ : Fin b => 2) (m := 0) (l := 1) 0 hd).graft (H.extractedInner (q := vectorArity i) (p := fun _ : Fin b => 2) (m := 0) (l := 1) 0 hc) 0 (H.extractedChoices (q := vectorArity i) (p := fun _ : Fin b => 2) (m := 0) (l := 1) 0 hd))) = _ at he
  rwa [hh] at he

/-- Actual extraction also determines the factor order for each input slot. -/
theorem inputProfile_carrier_extracted (i : Fin (a + 1)) (r : Fin 2)
    (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k)
    (H : Graph (graftArity (fun _ : Fin b => 2) (vectorArity i)) 2)
    (hc : H.InnerClosed (q := fun _ : Fin b => 2) (p := vectorArity i) (m := 1) (l := 0) r)
    (hd : H.CoarseDistinct (q := fun _ : Fin b => 2) (p := vectorArity i) (m := 1) (l := 0) r) :
    inputProfile r w v (inputCarrier i H) =
      w ⟨i, H.extractedInner (q := fun _ : Fin b => 2) (p := vectorArity i) (m := 1) (l := 0) r hc⟩ * v (H.extractedOuter (q := fun _ : Fin b => 2) (p := vectorArity i) (m := 1) (l := 0) r hd) := by
  have hh := H.graft_extracted (q := fun _ : Fin b => 2) (p := vectorArity i) (m := 1) (l := 0) r hc hd
  have he := inputProfile_graft r w v ⟨i, H.extractedInner (q := fun _ : Fin b => 2) (p := vectorArity i) (m := 1) (l := 0) r hc⟩
    (H.extractedOuter (q := fun _ : Fin b => 2) (p := vectorArity i) (m := 1) (l := 0) r hd) (H.extractedChoices (q := fun _ : Fin b => 2) (p := vectorArity i) (m := 1) (l := 0) r hd)
  change inputProfile r w v (inputCarrier i
    ((H.extractedOuter (q := fun _ : Fin b => 2) (p := vectorArity i) (m := 1) (l := 0) r hd).graft (H.extractedInner (q := fun _ : Fin b => 2) (p := vectorArity i) (m := 1) (l := 0) r hc) r (H.extractedChoices (q := fun _ : Fin b => 2) (p := vectorArity i) (m := 1) (l := 0) r hd))) = _ at he
  rwa [hh] at he

/-- A graft cannot move the retained vector out of the designated vector block. -/
theorem outputProfile_eq_zero_of_vector_outside (w : VectorGraph a 1 → k)
    (v : BinaryGraph b 2 → k) (H : VectorGraph (a + b) 2)
    (h : H.vertex ∉ Set.range (vectorEmbedding a b)) : outputProfile w v H = 0 := by
  rw [outputProfile_apply]
  apply Finset.sum_eq_zero
  intro Γ _
  apply Finset.sum_eq_zero
  intro Δ _
  apply Finset.sum_eq_zero
  intro χ _
  apply if_neg
  intro he
  exact h ⟨Γ.vertex, congrArg VectorGraph.vertex he⟩

/-- The input block exchange preserves the same vector-block support. -/
theorem inputProfile_eq_zero_of_vector_outside (r : Fin 2) (w : VectorGraph a 1 → k)
    (v : BinaryGraph b 2 → k) (H : VectorGraph (a + b) 2)
    (h : H.vertex ∉ Set.range (vectorEmbedding a b)) : inputProfile r w v H = 0 := by
  rw [inputProfile_apply]
  apply Finset.sum_eq_zero
  intro Γ _
  apply Finset.sum_eq_zero
  intro Δ _
  apply Finset.sum_eq_zero
  intro χ _
  apply if_neg
  intro he
  exact h ⟨Γ.vertex, congrArg VectorGraph.vertex he⟩

end EnvelopingIsomorphism.Deformation.MixedGraphTargetProfiles
