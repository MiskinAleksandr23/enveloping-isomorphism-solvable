import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterData

/-! The natural topology on all primitive boundary-cluster parameters, with
continuous original, doubled, and pair coordinates. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration ComplexConjugate Topology

namespace BoundaryClusterData

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

@[ext] theorem ext {D E : BoundaryClusterData i a m S l u}
    (hcenter : D.center = E.center) (hbase : D.base = E.base)
    (hvelocity : D.velocity = E.velocity) (hboundaryBase : D.boundaryBase = E.boundaryBase)
    (hboundaryVelocity : D.boundaryVelocity = E.boundaryVelocity) : D = E := by
  cases D
  cases E
  cases hcenter
  cases hbase
  cases hvelocity
  cases hboundaryBase
  cases hboundaryVelocity
  rfl

/-- Real center, complex base/velocity arrays, and real boundary base/velocity arrays. -/
def coordinates (D : BoundaryClusterData i a m S l u) :
    ℝ × (Fin n → ℂ) × (Fin n → ℂ) × (Fin m → ℝ) × (Fin m → ℝ) :=
  (D.center, D.base, D.velocity, D.boundaryBase, D.boundaryVelocity)

theorem coordinates_injective :
    Function.Injective (coordinates : BoundaryClusterData i a m S l u → _) := by
  intro D E h
  exact ext (congrArg (fun x => x.1) h) (congrArg (fun x => x.2.1) h)
    (congrArg (fun x => x.2.2.1) h) (congrArg (fun x => x.2.2.2.1) h)
    (congrArg (fun x => x.2.2.2.2) h)

instance instTopologicalSpace : TopologicalSpace (BoundaryClusterData i a m S l u) :=
  TopologicalSpace.induced coordinates inferInstance

theorem isEmbedding_coordinates :
    IsEmbedding (coordinates : BoundaryClusterData i a m S l u → _) :=
  coordinates_injective.isEmbedding_induced

@[fun_prop] theorem continuous_coordinates :
    Continuous (coordinates : BoundaryClusterData i a m S l u → _) :=
  isEmbedding_coordinates.continuous

@[fun_prop] theorem continuous_center :
    Continuous (fun D : BoundaryClusterData i a m S l u => D.center) :=
  continuous_coordinates.fst

@[fun_prop] theorem continuous_base :
    Continuous (fun D : BoundaryClusterData i a m S l u => D.base) :=
  continuous_coordinates.snd.fst

@[fun_prop] theorem continuous_velocity :
    Continuous (fun D : BoundaryClusterData i a m S l u => D.velocity) :=
  continuous_coordinates.snd.snd.fst

@[fun_prop] theorem continuous_boundaryBase :
    Continuous (fun D : BoundaryClusterData i a m S l u => D.boundaryBase) :=
  continuous_coordinates.snd.snd.snd.fst

@[fun_prop] theorem continuous_boundaryVelocity :
    Continuous (fun D : BoundaryClusterData i a m S l u => D.boundaryVelocity) :=
  continuous_coordinates.snd.snd.snd.snd

@[fun_prop] theorem continuous_base_apply (j : Fin n) :
    Continuous (fun D : BoundaryClusterData i a m S l u => D.base j) :=
  (continuous_apply j).comp continuous_base

@[fun_prop] theorem continuous_velocity_apply (j : Fin n) :
    Continuous (fun D : BoundaryClusterData i a m S l u => D.velocity j) :=
  (continuous_apply j).comp continuous_velocity

@[fun_prop] theorem continuous_boundaryBase_apply (j : Fin m) :
    Continuous (fun D : BoundaryClusterData i a m S l u => D.boundaryBase j) :=
  (continuous_apply j).comp continuous_boundaryBase

@[fun_prop] theorem continuous_boundaryVelocity_apply (j : Fin m) :
    Continuous (fun D : BoundaryClusterData i a m S l u => D.boundaryVelocity j) :=
  (continuous_apply j).comp continuous_boundaryVelocity

@[fun_prop] theorem continuous_doubledBase (v : DoubledLabel n m) :
    Continuous (fun D : BoundaryClusterData i a m S l u => D.doubledBase v) := by
  cases v with
  | inl v =>
    cases v with
    | inl j => exact continuous_base_apply j
    | inr j => exact Complex.continuous_ofReal.comp (continuous_boundaryBase_apply j)
  | inr j => exact Complex.continuous_conj.comp (continuous_base_apply j)

@[fun_prop] theorem continuous_doubledVelocity (v : DoubledLabel n m) :
    Continuous (fun D : BoundaryClusterData i a m S l u => D.doubledVelocity v) := by
  cases v with
  | inl v =>
    cases v with
    | inl j => exact continuous_velocity_apply j
    | inr j => exact Complex.continuous_ofReal.comp (continuous_boundaryVelocity_apply j)
  | inr j => exact Complex.continuous_conj.comp (continuous_velocity_apply j)

@[fun_prop] theorem continuous_pairBase (p : DoubledPair n m) :
    Continuous (fun D : BoundaryClusterData i a m S l u => D.pairBase p) :=
  (continuous_doubledBase p.val.2).sub (continuous_doubledBase p.val.1)

@[fun_prop] theorem continuous_pairVelocity (p : DoubledPair n m) :
    Continuous (fun D : BoundaryClusterData i a m S l u => D.pairVelocity p) :=
  (continuous_doubledVelocity p.val.2).sub (continuous_doubledVelocity p.val.1)

end BoundaryClusterData

end EnvelopingIsomorphism.Deformation.Kontsevich
