import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryFaceDR
import EnvelopingIsomorphism.Deformation.Kontsevich.AngularPhasePullback

/-! The actual pure-boundary face edge form is recovered from the two retained
DR pair directions. Internal-source edges never lie in the pure external mask. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryFaceEdgeForms
open Configuration ComplexConjugate PureBoundaryClusterForms PureBoundaryFaceDR
open scoped Classical
variable {n m : ℕ} (l u : Fin (m+1)) (a b : Fin m)

def resolvedPair (p : DoubledPair (n+1) m) : PureBoundaryFaceDR.Face (n := n) l u a b → ℂ :=
  StaticCollisionFaceDR.unit (pureBoundaryClusterPairCollapses l u) (pairBase l u a b) (pairVelocity l u a b) p

theorem contDiff_resolvedPair (p : DoubledPair (n+1) m) : ContDiff ℝ ⊤ (resolvedPair (n := n) l u a b p) := by
  unfold resolvedPair StaticCollisionFaceDR.unit
  split_ifs
  · exact (contDiff_velocity l u a b p.val.2).sub (contDiff_velocity l u a b p.val.1)
  · exact (contDiff_base l u a b p.val.2).sub (contDiff_base l u a b p.val.1)

def pairForm (p : DoubledPair (n+1) m) (y : PureBoundaryFaceDR.Face (n := n) l u a b) := angularPullback (resolvedPair l u a b p) y

def edgeForm (e : GraphForms.Edge n m) (he : e.target ≠ Sum.inl e.source)
    (y : PureBoundaryFaceDR.Face (n := n) l u a b) :=
  pairForm l u a b (harmonicNumeratorPair e.source e.target he) y -
    pairForm l u a b (harmonicDenominatorPair e.source e.target) y

theorem resolvedRatio (e : GraphForms.Edge n m) (he : e.target ≠ Sum.inl e.source) :
    (fun y : PureBoundaryFaceDR.Face (n := n) l u a b ↦
      resolvedPair l u a b (harmonicNumeratorPair e.source e.target he) y /
      resolvedPair l u a b (harmonicDenominatorPair e.source e.target) y) =
      (fun p : ℂ × ℂ ↦ harmonicRatio p.1 p.2) ∘ GraphForms.edgeMap e ∘
        faceMap (boundaryClusterBlock l u) a b := by
  funext y
  simp only [resolvedPair, StaticCollisionFaceDR.unit, pureBoundaryClusterPairCollapses,
    pureBoundaryClusterCollapses, harmonicNumeratorPair, harmonicDenominatorPair, false_and, if_false]
  rw [faceMap_eq_coarse]
  rcases e with ⟨s,t⟩
  cases t <;> rfl

variable (D : PureBoundaryClusterData (0 : Fin (n+1)) m l u a b)

theorem resolvedPair_ne_zero_data (p : DoubledPair (n+1) m) : resolvedPair l u a b p (dataCoarse D,dataShape D) ≠ 0 := by
  apply StaticCollisionFaceDR.unit_ne_zero
  · intro p
    rw [pairBase_data]
    exact D.pairBase_eq_zero_iff_pureBoundaryClusterPairCollapses p
  · intro p hp
    rw [pairVelocity_data]
    exact D.pairVelocity_ne_zero_of_pureBoundaryClusterPairCollapses p hp

theorem edgeForm_eq_face_data (e : GraphForms.Edge n m) (he : e.target ≠ Sum.inl e.source) :
    edgeForm l u a b e he (dataCoarse D,dataShape D) =
      faceEdgeForm (boundaryClusterBlock l u) a b e (dataCoarse D,dataShape D) := by
  let y := (dataCoarse D,dataShape D)
  have hm : ContDiff ℝ ⊤ (faceMap (n := n) (boundaryClusterBlock l u) a b) := by
    rw [faceMap_eq_coarse]
    exact (coarseMap _).contDiff.comp contDiff_fst
  have hd := ((GraphForms.contDiff_edgeMap e).comp hm).contDiffAt (x := y)
  unfold edgeForm pairForm
  rw [← angularPullback_div _ _ y
    ((contDiff_resolvedPair l u a b _).contDiffAt.differentiableAt (by simp))
    ((contDiff_resolvedPair l u a b _).contDiffAt.differentiableAt (by simp))
    (resolvedPair_ne_zero_data l u a b D _) (resolvedPair_ne_zero_data l u a b D _), resolvedRatio]
  have hn : (GraphForms.edgeMap e (faceMap _ a b y)).2 - conj (GraphForms.edgeMap e (faceMap _ a b y)).1 ≠ 0 := by
    simpa only [faceMap_eq_coarse, y, starRingEnd_apply] using (dataCoarse_regular D).edge_endpoints e he |>.1
  calc
    _ = (harmonicAngleForm (GraphForms.edgeMap e (faceMap _ a b y))).compContinuousLinearMap
        (fderiv ℝ (GraphForms.edgeMap e ∘ faceMap _ a b) y) :=
      (harmonicAngleForm_pullback _ y (hd.differentiableAt (by simp)) hn).symm
    _ = _ := by
      rw [fderiv_comp y (GraphForms.hasFDerivAt_edgeMap e _).differentiableAt
        (hm.contDiffAt.differentiableAt (by simp)), (GraphForms.hasFDerivAt_edgeMap e _).fderiv]
      ext v
      rfl

end EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryFaceEdgeForms
