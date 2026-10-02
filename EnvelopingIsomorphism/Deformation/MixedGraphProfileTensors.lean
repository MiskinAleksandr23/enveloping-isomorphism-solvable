import EnvelopingIsomorphism.Deformation.MixedGraphProfileCarrier
import EnvelopingIsomorphism.Deformation.UniformCurvatureSplits

/-! Actual tensor identifications for the one-vector graph carrier. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedGraphProfileCarrier
open KontsevichGraph.General SchoutenGraphContraction
open scoped Classical

variable {k : Type*} [Field k] {n d : ℕ}

private theorem tensorCast_heq {a b : ℕ} (h : a = b) (T : Tensor a d k) :
    HEq (tensorCast h T) T := by cases h; rfl

private theorem cast_tensor_map_apply {A : Type*} [AddCommGroup A] [Module k A]
    {a b : ℕ} (h : a = b) (f : A →ₗ[k] Tensor a d k) (x : A) :
    (cast (congrArg (fun r ↦ A →ₗ[k] Tensor r d k) h) f) x = tensorCast h (f x) := by
  cases h
  rfl

theorem rawTensors_root_heq (i : Fin (n + 1))
    (B : Fin (n + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    HEq (rawTensors i B X i) (rawTensor X) := by
  have hcast := cast_tensor_map_apply
    (A := Gauge.PlacedMixedGraphTaylorCoefficients.PairInput k d 1)
    (show 1 = Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i i from (if_pos rfl).symm)
    ((Gauge.MixedGraphTaylorCoefficients.coordinateTensor (k := k) (d := d) 1).comp
      (LinearMap.fst k _ _)) (X, 0)
  have he : rawTensors i B X i = tensorCast
      (show 1 = Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i i from (if_pos rfl).symm)
      (rawTensor X) := by
    simp only [rawTensors, Gauge.PlacedMixedGraphTaylorCoefficients.vertexTensor]
    exact hcast
  exact (heq_of_eq he).trans (tensorCast_heq _ _)

theorem rawTensors_other_heq (i v : Fin (n + 1)) (hv : v ≠ i)
    (B : Fin (n + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    HEq (rawTensors i B X v) (rawTensor (B v)) := by
  have hcast := cast_tensor_map_apply
    (A := Gauge.PlacedMixedGraphTaylorCoefficients.PairInput k d 1)
    (show 2 = Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i v from (if_neg hv).symm)
    ((Gauge.MixedGraphTaylorCoefficients.coordinateTensor (k := k) (d := d) 2).comp
      (LinearMap.snd k _ _)) (0, B v)
  have he : rawTensors i B X v = tensorCast
      (show 2 = Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i v from (if_neg hv).symm)
      (rawTensor (B v)) := by
    simp only [rawTensors, if_neg hv, Gauge.PlacedMixedGraphTaylorCoefficients.vertexTensor,
      dif_neg hv]
    exact hcast
  exact (heq_of_eq he).trans (tensorCast_heq _ _)

end EnvelopingIsomorphism.Deformation.MixedGraphProfileCarrier
