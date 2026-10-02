import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterData

/-! The actual parameter topology for pure boundary clusters, with continuity
of original, doubled and pair coordinates while all primitive data vary. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration ComplexConjugate Topology
open scoped UpperHalfPlane

namespace PureBoundaryClusterData

variable {n m : ℕ} {i : Fin n} {l u : Fin (m + 1)} {a b : Fin m}

@[ext] theorem ext {D E : PureBoundaryClusterData i m l u a b}
    (hcenter : D.center = E.center) (hinterior : D.interior = E.interior)
    (hboundaryBase : D.boundaryBase = E.boundaryBase)
    (hboundaryVelocity : D.boundaryVelocity = E.boundaryVelocity) : D = E := by
  cases D
  cases E
  cases hcenter
  cases hinterior
  cases hboundaryBase
  cases hboundaryVelocity
  rfl

def coordinates (D : PureBoundaryClusterData i m l u a b) :
    ℝ × (Fin n → ℂ) × (Fin m → ℝ) × (Fin m → ℝ) :=
  (D.center, fun j => (D.interior j : ℂ), D.boundaryBase, D.boundaryVelocity)

theorem coordinates_injective :
    Function.Injective (coordinates : PureBoundaryClusterData i m l u a b → _) := by
  intro D E h
  apply ext
  · exact congrArg (fun x => x.1) h
  · funext j
    exact UpperHalfPlane.ext (congrArg (fun x => x.2.1 j) h)
  · exact congrArg (fun x => x.2.2.1) h
  · exact congrArg (fun x => x.2.2.2) h

instance instTopologicalSpace : TopologicalSpace (PureBoundaryClusterData i m l u a b) :=
  TopologicalSpace.induced coordinates inferInstance

theorem isEmbedding_coordinates :
    IsEmbedding (coordinates : PureBoundaryClusterData i m l u a b → _) :=
  coordinates_injective.isEmbedding_induced

@[fun_prop] theorem continuous_coordinates :
    Continuous (coordinates : PureBoundaryClusterData i m l u a b → _) :=
  isEmbedding_coordinates.continuous

@[fun_prop] theorem continuous_center :
    Continuous (fun D : PureBoundaryClusterData i m l u a b => D.center) :=
  continuous_coordinates.fst

theorem continuous_interiorCoordinates :
    Continuous (fun D : PureBoundaryClusterData i m l u a b => fun j => (D.interior j : ℂ)) :=
  continuous_coordinates.snd.fst

@[fun_prop] theorem continuous_boundaryBase :
    Continuous (fun D : PureBoundaryClusterData i m l u a b => D.boundaryBase) :=
  continuous_coordinates.snd.snd.fst

@[fun_prop] theorem continuous_boundaryVelocity :
    Continuous (fun D : PureBoundaryClusterData i m l u a b => D.boundaryVelocity) :=
  continuous_coordinates.snd.snd.snd

@[fun_prop] theorem continuous_interior_apply (j : Fin n) :
    Continuous (fun D : PureBoundaryClusterData i m l u a b => (D.interior j : ℂ)) :=
  (continuous_apply j).comp continuous_interiorCoordinates

@[fun_prop] theorem continuous_boundaryBase_apply (j : Fin m) :
    Continuous (fun D : PureBoundaryClusterData i m l u a b => D.boundaryBase j) :=
  (continuous_apply j).comp continuous_boundaryBase

@[fun_prop] theorem continuous_boundaryVelocity_apply (j : Fin m) :
    Continuous (fun D : PureBoundaryClusterData i m l u a b => D.boundaryVelocity j) :=
  (continuous_apply j).comp continuous_boundaryVelocity

@[fun_prop] theorem continuous_doubledBase (v : DoubledLabel n m) :
    Continuous (fun D : PureBoundaryClusterData i m l u a b => D.doubledBase v) := by
  cases v with
  | inl v =>
    cases v with
    | inl j => exact continuous_interior_apply j
    | inr j => exact Complex.continuous_ofReal.comp (continuous_boundaryBase_apply j)
  | inr j => exact Complex.continuous_conj.comp (continuous_interior_apply j)

@[fun_prop] theorem continuous_doubledVelocity (v : DoubledLabel n m) :
    Continuous (fun D : PureBoundaryClusterData i m l u a b => D.doubledVelocity v) := by
  cases v with
  | inl v =>
    cases v with
    | inl j => exact continuous_const
    | inr j => exact Complex.continuous_ofReal.comp (continuous_boundaryVelocity_apply j)
  | inr j => exact continuous_const

@[fun_prop] theorem continuous_pairBase (p : DoubledPair n m) :
    Continuous (fun D : PureBoundaryClusterData i m l u a b => D.pairBase p) :=
  (continuous_doubledBase p.val.2).sub (continuous_doubledBase p.val.1)

@[fun_prop] theorem continuous_pairVelocity (p : DoubledPair n m) :
    Continuous (fun D : PureBoundaryClusterData i m l u a b => D.pairVelocity p) :=
  (continuous_doubledVelocity p.val.2).sub (continuous_doubledVelocity p.val.1)

end PureBoundaryClusterData

end EnvelopingIsomorphism.Deformation.Kontsevich
