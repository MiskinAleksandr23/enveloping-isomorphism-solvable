import EnvelopingIsomorphism.Deformation.Kontsevich.StaticCollisionFaceDR
import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryGraphDomain
import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterCompactification

/-! Smooth actual full DR embedding of the pure external face in its native
coarse/shape coordinates, with the literal external collision mask. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryFaceDR
open Configuration ComplexConjugate PureBoundaryClusterForms
open scoped Classical
variable {n m : ℕ} (l u : Fin (m+1)) (a b : Fin m)
abbrev Face := PureBoundaryClusterForms.Face n (boundaryClusterBlock l u) a b

def base (y : Face (n := n) l u a b) : DoubledLabel (n+1) m → ℂ
  | Sum.inl (Sum.inl j) => GraphForms.interiorPoint j (coarseMap (boundaryClusterBlock l u) y.1)
  | Sum.inl (Sum.inr j) => boundaryBaseCLM (boundaryClusterBlock l u) j y.1
  | Sum.inr j => conj (GraphForms.interiorPoint j (coarseMap (boundaryClusterBlock l u) y.1))

def velocity (y : Face (n := n) l u a b) : DoubledLabel (n+1) m → ℂ
  | Sum.inl (Sum.inr j) => shapeVelocity (boundaryClusterBlock l u) a b y.2 j
  | _ => 0

def pairBase (p : DoubledPair (n+1) m) (y : Face (n := n) l u a b) : ℂ := base l u a b y p.val.2 - base l u a b y p.val.1
def pairVelocity (p : DoubledPair (n+1) m) (y : Face (n := n) l u a b) : ℂ := velocity l u a b y p.val.2 - velocity l u a b y p.val.1

theorem contDiff_base (j : DoubledLabel (n+1) m) : ContDiff ℝ ⊤ (fun y : Face (n := n) l u a b ↦ base l u a b y j) := by
  rcases j with (j | j) | j
  · cases j using Fin.cases <;> dsimp [base, GraphForms.interiorPoint, coarseMap] <;> fun_prop
  · exact Complex.ofRealCLM.contDiff.comp ((boundaryBaseCLM _ j).contDiff.comp contDiff_fst)
  · cases j using Fin.cases <;> dsimp [base, GraphForms.interiorPoint, coarseMap] <;> fun_prop

theorem contDiff_velocity (j : DoubledLabel (n+1) m) : ContDiff ℝ ⊤ (fun y : Face (n := n) l u a b ↦ velocity l u a b y j) := by
  rcases j with (j | j) | j
  · exact contDiff_const
  · exact Complex.ofRealCLM.contDiff.comp ((ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ).contDiff.comp ((contDiff_shapeVelocity _ a b).comp contDiff_snd))
  · exact contDiff_const

def ambient : Face (n := n) l u a b → CompactDRCoordinates.Ambient (n+1) m :=
  StaticCollisionFaceDR.ambient (pureBoundaryClusterPairCollapses l u) (pairBase l u a b) (pairVelocity l u a b)

variable (D : PureBoundaryClusterData (0 : Fin (n+1)) m l u a b)

theorem base_data (j : DoubledLabel (n+1) m) : base l u a b (dataCoarse D,dataShape D) j = D.doubledBase j := by
  rcases j with (j | j) | j
  · cases j using Fin.cases with
    | zero => simp [base, GraphForms.interiorPoint, PureBoundaryClusterData.doubledBase, D.interior_normalized]
    | succ j => rfl
  · change (boundaryBaseCLM _ j (dataCoarse D) : ℂ) = (D.boundaryBase j : ℂ)
    apply congrArg Complex.ofReal
    have h := congrArg (fun x : GraphForms.Coordinates n m ↦ x.2 j) (coarseMap_dataCoarse D)
    exact h
  · cases j using Fin.cases with
    | zero => simp [base, GraphForms.interiorPoint, PureBoundaryClusterData.doubledBase, D.interior_normalized]
    | succ j => rfl

theorem velocity_data (j : DoubledLabel (n+1) m) : velocity l u a b (dataCoarse D,dataShape D) j = D.doubledVelocity j := by
  rcases j with (j | j) | j
  · rfl
  · exact congrArg Complex.ofReal (congrFun (shapeVelocity_dataShape D) j)
  · rfl

theorem pairBase_data (p : DoubledPair (n+1) m) : pairBase l u a b p (dataCoarse D,dataShape D) = D.pairBase p := by
  simp only [pairBase, base_data, PureBoundaryClusterData.pairBase]

theorem pairVelocity_data (p : DoubledPair (n+1) m) : pairVelocity l u a b p (dataCoarse D,dataShape D) = D.pairVelocity p := by
  simp only [pairVelocity, velocity_data, PureBoundaryClusterData.pairVelocity]

theorem contDiffAt_ambient_data : ContDiffAt ℝ ⊤ (ambient (n := n) l u a b) (dataCoarse D,dataShape D) := by
  apply StaticCollisionFaceDR.contDiffAt_ambient
  · intro p
    rw [pairBase_data]
    exact D.pairBase_eq_zero_iff_pureBoundaryClusterPairCollapses p
  · intro p hp
    rw [pairVelocity_data]
    exact D.pairVelocity_ne_zero_of_pureBoundaryClusterPairCollapses p hp
  · intro p
    exact ((contDiff_base l u a b p.val.2).sub (contDiff_base l u a b p.val.1)).contDiffAt
  · intro p
    exact ((contDiff_velocity l u a b p.val.2).sub (contDiff_velocity l u a b p.val.1)).contDiffAt

theorem ambient_data : ambient l u a b (dataCoarse D,dataShape D) =
    CompactDRCoordinates.dataEmbedding (projectDR D.boundaryPoint.val) := by
  rw [ambient, StaticCollisionFaceDR.ambient_eq_limits]
  · change _ = CompactDRCoordinates.dataEmbedding (projectDR (D.resolvedCoordinates 0))
    rw [D.resolvedCoordinates_zero]
    apply Prod.ext
    · funext p
      simp only [pairBase_data, pairVelocity_data]
      rfl
    · funext t
      simp only [pairBase_data, pairVelocity_data]
      rfl
  · intro p
    rw [pairBase_data]
    exact D.pairBase_eq_zero_iff_pureBoundaryClusterPairCollapses p
  · intro p hp
    rw [pairVelocity_data]
    exact D.pairVelocity_ne_zero_of_pureBoundaryClusterPairCollapses p hp

end EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryFaceDR
