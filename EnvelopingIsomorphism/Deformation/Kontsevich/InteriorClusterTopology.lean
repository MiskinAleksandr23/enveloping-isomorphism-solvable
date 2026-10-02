import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterPattern

/-! Natural coordinate topologies on collision data and on the fixed-pattern
single-cluster data. All continuity statements vary the full data, not just scale. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration ComplexConjugate Topology
open scoped UpperHalfPlane

namespace InteriorCollisionData

variable {n m : ℕ} {i : Fin n}

@[ext] theorem ext {D E : InteriorCollisionData i m}
    (hbase : D.base = E.base) (hvelocity : D.velocity = E.velocity)
    (hboundary : D.boundary = E.boundary) : D = E := by
  cases D
  cases E
  cases hbase
  cases hvelocity
  cases hboundary
  rfl

/-- Complex base and velocity coordinates and real boundary coordinates. -/
def coordinates (D : InteriorCollisionData i m) :
    (Fin n → ℂ) × (Fin n → ℂ) × (Fin m → ℝ) :=
  (fun a => (D.base a : ℂ), D.velocity, D.boundary)

theorem coordinates_injective :
    Function.Injective (coordinates : InteriorCollisionData i m → _) := by
  intro D E h
  apply ext
  · funext a
    exact UpperHalfPlane.ext (congrFun (congrArg Prod.fst h) a)
  · exact congrArg (fun x => x.2.1) h
  · exact congrArg (fun x => x.2.2) h

instance instTopologicalSpace : TopologicalSpace (InteriorCollisionData i m) :=
  TopologicalSpace.induced coordinates inferInstance

theorem isEmbedding_coordinates :
    IsEmbedding (coordinates : InteriorCollisionData i m → _) :=
  coordinates_injective.isEmbedding_induced

@[fun_prop] theorem continuous_coordinates :
    Continuous (coordinates : InteriorCollisionData i m → _) :=
  isEmbedding_coordinates.continuous

theorem continuous_baseCoordinates :
    Continuous (fun D : InteriorCollisionData i m => fun a => (D.base a : ℂ)) :=
  continuous_coordinates.fst

@[fun_prop] theorem continuous_velocity :
    Continuous (fun D : InteriorCollisionData i m => D.velocity) :=
  continuous_coordinates.snd.fst

@[fun_prop] theorem continuous_boundary :
    Continuous (fun D : InteriorCollisionData i m => D.boundary) :=
  continuous_coordinates.snd.snd

@[fun_prop] theorem continuous_base (a : Fin n) :
    Continuous (fun D : InteriorCollisionData i m => (D.base a : ℂ)) :=
  (continuous_apply a).comp continuous_baseCoordinates

@[fun_prop] theorem continuous_velocity_apply (a : Fin n) :
    Continuous (fun D : InteriorCollisionData i m => D.velocity a) :=
  (continuous_apply a).comp continuous_velocity

@[fun_prop] theorem continuous_boundary_apply (a : Fin m) :
    Continuous (fun D : InteriorCollisionData i m => D.boundary a) :=
  (continuous_apply a).comp continuous_boundary

@[fun_prop] theorem continuous_doubledBase (v : DoubledLabel n m) :
    Continuous (fun D : InteriorCollisionData i m => D.doubledBase v) := by
  cases v with
  | inl v =>
    cases v with
    | inl a => exact continuous_base a
    | inr a => exact Complex.continuous_ofReal.comp (continuous_boundary_apply a)
  | inr a => exact Complex.continuous_conj.comp (continuous_base a)

@[fun_prop] theorem continuous_doubledVelocity (v : DoubledLabel n m) :
    Continuous (fun D : InteriorCollisionData i m => D.doubledVelocity v) := by
  cases v with
  | inl v =>
    cases v with
    | inl a => exact continuous_velocity_apply a
    | inr a => exact continuous_const
  | inr a => exact Complex.continuous_conj.comp (continuous_velocity_apply a)

@[fun_prop] theorem continuous_pairBase (p : DoubledPair n m) :
    Continuous (fun D : InteriorCollisionData i m => D.pairBase p) :=
  (continuous_doubledBase p.val.2).sub (continuous_doubledBase p.val.1)

@[fun_prop] theorem continuous_pairVelocity (p : DoubledPair n m) :
    Continuous (fun D : InteriorCollisionData i m => D.pairVelocity p) :=
  (continuous_doubledVelocity p.val.2).sub (continuous_doubledVelocity p.val.1)

end InteriorCollisionData

namespace SingleInteriorCluster

variable {n m : ℕ} {i : Fin n} {S : Finset (Fin n)}

@[ext] theorem ext {D E : SingleInteriorCluster i m S}
    (h : D.toInteriorCollisionData = E.toInteriorCollisionData) : D = E := by
  cases D
  cases E
  cases h
  rfl

theorem toInteriorCollisionData_injective :
    Function.Injective (toInteriorCollisionData : SingleInteriorCluster i m S → _) :=
  fun _ _ h => ext h

instance instTopologicalSpace : TopologicalSpace (SingleInteriorCluster i m S) :=
  TopologicalSpace.induced toInteriorCollisionData inferInstance

theorem isEmbedding_toInteriorCollisionData :
    IsEmbedding (toInteriorCollisionData : SingleInteriorCluster i m S → _) :=
  toInteriorCollisionData_injective.isEmbedding_induced

@[fun_prop] theorem continuous_toInteriorCollisionData :
    Continuous (toInteriorCollisionData : SingleInteriorCluster i m S → _) :=
  isEmbedding_toInteriorCollisionData.continuous

@[fun_prop] theorem continuous_base (a : Fin n) :
    Continuous (fun D : SingleInteriorCluster i m S => (D.base a : ℂ)) :=
  (InteriorCollisionData.continuous_base a).comp continuous_toInteriorCollisionData

@[fun_prop] theorem continuous_velocity_apply (a : Fin n) :
    Continuous (fun D : SingleInteriorCluster i m S => D.velocity a) :=
  (InteriorCollisionData.continuous_velocity_apply a).comp continuous_toInteriorCollisionData

@[fun_prop] theorem continuous_boundary_apply (a : Fin m) :
    Continuous (fun D : SingleInteriorCluster i m S => D.boundary a) :=
  (InteriorCollisionData.continuous_boundary_apply a).comp continuous_toInteriorCollisionData

@[fun_prop] theorem continuous_doubledBase (v : DoubledLabel n m) :
    Continuous (fun D : SingleInteriorCluster i m S => D.toInteriorCollisionData.doubledBase v) :=
  (InteriorCollisionData.continuous_doubledBase v).comp continuous_toInteriorCollisionData

@[fun_prop] theorem continuous_doubledVelocity (v : DoubledLabel n m) :
    Continuous (fun D : SingleInteriorCluster i m S => D.toInteriorCollisionData.doubledVelocity v) :=
  (InteriorCollisionData.continuous_doubledVelocity v).comp continuous_toInteriorCollisionData

@[fun_prop] theorem continuous_pairBase (p : DoubledPair n m) :
    Continuous (fun D : SingleInteriorCluster i m S => D.toInteriorCollisionData.pairBase p) :=
  (InteriorCollisionData.continuous_pairBase p).comp continuous_toInteriorCollisionData

@[fun_prop] theorem continuous_pairVelocity (p : DoubledPair n m) :
    Continuous (fun D : SingleInteriorCluster i m S => D.toInteriorCollisionData.pairVelocity p) :=
  (InteriorCollisionData.continuous_pairVelocity p).comp continuous_toInteriorCollisionData

end SingleInteriorCluster
end EnvelopingIsomorphism.Deformation.Kontsevich
