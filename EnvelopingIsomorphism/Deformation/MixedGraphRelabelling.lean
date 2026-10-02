import EnvelopingIsomorphism.Deformation.MixedGraphProfileTensors
import EnvelopingIsomorphism.Deformation.BinaryGraphAveraging

/-! Actual one-vector carrier relabelling with dependent tensors and independent background inputs. -/

noncomputable section
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedGraphAveraging
open scoped BigOperators Classical
open MixedGraphProfileCarrier KontsevichGraph.General GraphCoefficientProfiles
variable {n m d : ℕ}

theorem profileArity_placed (i : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1))) :
    profileArity (Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i) σ =
      Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 (σ i) := profileArity_oneExceptional 1 i σ

def internalGraphEquiv (σ : Equiv.Perm (Fin (n + 1))) (m : ℕ) : Equiv.Perm (VectorGraph n m) :=
  Equiv.sigmaCongr σ (fun i ↦ Graph.oneExceptionalGraphEquiv 1 i σ m)

@[simp] theorem internalGraphEquiv_vertex (σ : Equiv.Perm (Fin (n + 1))) (Γ : VectorGraph n m) :
    (internalGraphEquiv σ m Γ).vertex = σ Γ.vertex := rfl

def outsideEquiv (i : Fin (n + 1)) : Fin n ≃ {v : Fin (n + 1) // v ≠ i} :=
  ((Gauge.PlacedMixedGraphTaylorCoefficients.bivectorSlots i).orderIsoOfFin (Gauge.PlacedMixedGraphTaylorCoefficients.card_bivectorSlots i)).toEquiv.trans
    (Equiv.subtypeEquivRight (fun v ↦ by simp [Gauge.PlacedMixedGraphTaylorCoefficients.bivectorSlots]))

@[simp] theorem outsideEquiv_val (i : Fin (n + 1)) (j : Fin n) :
    (outsideEquiv i j).val = placementEquiv i (Sum.inl j) := rfl

def outsideVertexEquiv (i : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1))) :
    {v : Fin (n + 1) // v ≠ i} ≃ {v : Fin (n + 1) // v ≠ σ i} :=
  Equiv.subtypeEquiv σ (fun _ ↦ σ.injective.ne_iff.symm)

def backgroundPerm (i : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1))) : Equiv.Perm (Fin n) :=
  (outsideEquiv i).trans ((outsideVertexEquiv i σ).trans (outsideEquiv (σ i)).symm)

theorem placement_backgroundPerm (i : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1))) (j : Fin n) :
    placementEquiv (σ i) (Sum.inl (backgroundPerm i σ j)) = σ (placementEquiv i (Sum.inl j)) := by
  have h : outsideEquiv (σ i) (backgroundPerm i σ j) = outsideVertexEquiv i σ (outsideEquiv i j) := by
    simp [backgroundPerm]
  exact congrArg Subtype.val h

variable {k : Type*} [Field k]

def fillBackground (i : Fin (n + 1)) (R : Fin n → Bivector (k := k) (d := d)) :
    Fin (n + 1) → Bivector (k := k) (d := d) :=
  fun v ↦ Sum.elim R (fun _ : Fin 1 ↦ 0) ((placementEquiv i).symm v)

@[simp] theorem fillBackground_placement (i : Fin (n + 1))
    (R : Fin n → Bivector (k := k) (d := d)) (j : Fin n) :
    fillBackground i R (placementEquiv i (Sum.inl j)) = R j := by
  change Sum.elim R (fun _ : Fin 1 ↦ 0)
    ((placementEquiv i).symm (placementEquiv i (Sum.inl j))) = R j
  rw [Equiv.symm_apply_apply]
  rfl

private theorem transportTensors_heq {q q' : Fin (n + 1) → ℕ} (h : q = q')
    (T : (v : Fin (n + 1)) → Tensor (q v) d k) (v : Fin (n + 1)) :
    HEq ((h ▸ T : (w : Fin (n + 1)) → Tensor (q' w) d k) v) (T v) := by
  cases h
  rfl

theorem profileTensors_rawTensors (i : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1)))
    (B : Fin (n + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    (profileArity_placed i σ ▸
      profileTensors (Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i) σ (rawTensors i (B ∘ σ) X) :
        (v : Fin (n + 1)) → Tensor (Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 (σ i) v) d k) = rawTensors (σ i) B X := by
  funext v
  apply eq_of_heq
  refine (transportTensors_heq (profileArity_placed i σ) _ v).trans ?_
  change HEq (rawTensors i (B ∘ σ) X (σ.symm v)) (rawTensors (σ i) B X v)
  by_cases hv : v = σ i
  · subst v
    rw [σ.symm_apply_apply]
    exact (rawTensors_root_heq i (B ∘ σ) X).trans (rawTensors_root_heq (σ i) B X).symm
  · have hi : σ.symm v ≠ i := by
      intro h
      exact hv ((σ.symm_apply_eq).mp h)
    have ho := rawTensors_other_heq i (σ.symm v) hi (B ∘ σ) X
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at ho
    exact ho.trans (rawTensors_other_heq (σ i) v hv B X).symm

theorem rawValue_internalGraphEquiv (σ : Equiv.Perm (Fin (n + 1))) (Γ : VectorGraph n m)
    (B : Fin (n + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    rawValue (internalGraphEquiv σ m Γ) B X = rawValue Γ (B ∘ σ) X := by
  change (Graph.oneExceptionalGraphEquiv 1 Γ.vertex σ m Γ.graph).cochainOperator
    (rawTensors (σ Γ.vertex) B X) = Γ.graph.cochainOperator (rawTensors Γ.vertex (B ∘ σ) X)
  rw [← profileTensors_rawTensors Γ.vertex σ B X]
  exact (Graph.cochainOperator_castProfile (R := k) (d := d) (profileArity_placed Γ.vertex σ)
    (Γ.graph.permuteProfile σ) _).trans (Graph.cochainOperator_permuteProfile Γ.graph σ _)

theorem operator_eq_filled (Γ : VectorGraph n m)
    (R : Fin n → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    operator Γ R X = rawValue Γ (fillBackground Γ.vertex R) X := by
  simpa only [fillBackground_placement] using operator_eq_rawValue Γ (fillBackground Γ.vertex R) X

theorem operator_internalGraphEquiv (σ : Equiv.Perm (Fin (n + 1))) (Γ : VectorGraph n m)
    (R : Fin n → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    operator (internalGraphEquiv σ m Γ) R X = operator Γ (R ∘ backgroundPerm Γ.vertex σ) X := by
  rw [operator_eq_filled, internalGraphEquiv_vertex, rawValue_internalGraphEquiv]
  rw [← operator_eq_rawValue Γ (fillBackground (σ Γ.vertex) R ∘ σ) X]
  apply congrArg (fun F ↦ operator Γ F X)
  funext j
  simp only [Function.comp_apply, ← placement_backgroundPerm, fillBackground_placement]

end EnvelopingIsomorphism.Deformation.MixedGraphAveraging
