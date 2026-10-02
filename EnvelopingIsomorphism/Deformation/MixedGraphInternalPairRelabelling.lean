import EnvelopingIsomorphism.Deformation.MixedGraphCanonicalSplitFibres
import EnvelopingIsomorphism.Deformation.MixedGraphBlockRelabelling
import EnvelopingIsomorphism.Deformation.MixedGraphCanonicalRelabelling
import EnvelopingIsomorphism.Deformation.GeneralGraphSplitPairRelabelling
import EnvelopingIsomorphism.Deformation.GraphCurvatureInternalRelabelling

/-! Actual internal pair covariance of the mixed source and curvature
profiles. The retained vector moves with its original label; correction
weights retain the compensating vector/trivector placement sign. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
namespace EnvelopingIsomorphism.Deformation.MixedGraphInternalPairRelabelling
open scoped BigOperators Classical
open KontsevichGraph.General KontsevichGraph.General.TwoVertexContraction
open MixedGraphProfileCarrier MixedGraphAveraging MixedGraphBlockRelabelling
open GraphCoefficientProfiles UniformBinaryGraphs
variable {n : ℕ}

/-- Actual weighted fibres reindex under a graph and data equivalence. -/
theorem pushforward_relabelling {k I J A : Type*} [CommRing k] [Fintype I] [Fintype J]
    (f : I → A) (g : J → A) (e : I ≃ J) (ρ : Equiv.Perm A) (w : I → k) (v : J → k)
    (hf : ∀ i, g (e i) = ρ (f i)) (hw : ∀ i, v (e i) = w i) (H : A) :
    pushforward g v (ρ H) = pushforward f w H := by
  unfold pushforward
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [hf, hw, ρ.injective.eq_iff]

namespace Source
open MixedGraphActionSplits

def dataEquiv (i : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1))) :
    SourceSplitData i ≃ SourceSplitData (σ i) :=
  Equiv.sigmaCongr (Graph.permuteInternalEquiv 2 2 σ) (fun Γ =>
    Equiv.arrowCongr (SlotRelabelling.splitIncomingEquiv i (σ i) (binaryRelabelling σ Γ) rfl)
      (Equiv.refl _))

def permutation (i : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1))) : Equiv.Perm (Fin (n + 2)) :=
  SlotRelabelling.splitVertices i (σ i) σ rfl (Equiv.refl _)

def templateDataGraph (i : Fin (n + 1)) (T : Graph vectorBivectorArity 2) (D : SourceSplitData i) :
    VectorGraph (n + 1) 2 :=
  ofProfile (vertexSplitChild i 0) (actionSplitArity i) (D.1.vertexSplit T i rfl D.2)

theorem templateDataGraph_internal (i : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1)))
    (T : Graph vectorBivectorArity 2) (D : SourceSplitData i) :
    templateDataGraph (σ i) T (dataEquiv i σ D) =
      internalGraphEquiv (permutation i σ) 2 (templateDataGraph i T D) := by
  let F := binaryRelabelling σ D.1
  let G := SlotRelabelling.refl T
  let FS := SlotRelabelling.vertexSplit i (σ i) F G rfl rfl rfl D.2
  let FM := (ofProfileRelabelling (vertexSplitChild i 0) (actionSplitArity i) _).symm.trans
    (FS.trans (ofProfileRelabelling (vertexSplitChild (σ i) 0) (actionSplitArity (σ i)) _))
  apply vectorGraph_eq_internal (permutation i σ) FM
  · simp only [FM, FS, SlotRelabelling.trans, SlotRelabelling.symm, ofProfileRelabelling_vertices]
    rfl
  · exact (SlotRelabelling.splitVertices_child i (σ i) σ rfl (Equiv.refl _) 0).symm

theorem forwardDataGraph_internal (i : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1)))
    (D : SourceSplitData i) :
    forwardDataGraph (σ i) (dataEquiv i σ D) =
      internalGraphEquiv (permutation i σ) 2 (forwardDataGraph i D) :=
  templateDataGraph_internal i σ vectorBivectorForward D

theorem backwardDataGraph_internal (i : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1)))
    (ρ : Equiv.Perm (Fin 2)) (D : SourceSplitData i) :
    backwardDataGraph (σ i) ρ (dataEquiv i σ D) =
      internalGraphEquiv (permutation i σ) 2 (backwardDataGraph i ρ D) :=
  templateDataGraph_internal i σ (vectorBivectorBackward ρ) D

variable {k : Type*} [Field k]

theorem forwardTemplateProfile_internal (w : BinaryGraph (n + 1) 2 → k)
    (hw : ∀ Γ σ, w (Γ.permuteInternal σ) = w Γ)
    (i : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1))) (H : VectorGraph (n + 1) 2) :
    forwardTemplateProfile (σ i) w (internalGraphEquiv (permutation i σ) 2 H) =
      forwardTemplateProfile i w H := by
  apply pushforward_relabelling _ _ (dataEquiv i σ) (internalGraphEquiv (permutation i σ) 2)
  · exact forwardDataGraph_internal i σ
  · intro D
    exact hw D.1 σ

theorem backwardTemplateProfile_internal (w : BinaryGraph (n + 1) 2 → k)
    (hw : ∀ Γ σ, w (Γ.permuteInternal σ) = w Γ)
    (i : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1))) (ρ : Equiv.Perm (Fin 2))
    (H : VectorGraph (n + 1) 2) :
    backwardTemplateProfile (σ i) ρ w (internalGraphEquiv (permutation i σ) 2 H) =
      backwardTemplateProfile i ρ w H := by
  apply pushforward_relabelling _ _ (dataEquiv i σ) (internalGraphEquiv (permutation i σ) 2)
  · exact backwardDataGraph_internal i σ ρ
  · intro D
    exact hw D.1 σ

/-- The genuine reduced source pair coefficient retains its backward factor two. -/
def pairProfile (w : BinaryGraph (n + 1) 2 → k) (i : Fin (n + 1)) : VectorGraph (n + 1) 2 → k :=
  forwardTemplateProfile i w - (2 : k) • backwardTemplateProfile i 1 w

theorem pairProfile_internal (w : BinaryGraph (n + 1) 2 → k)
    (hw : ∀ Γ σ, w (Γ.permuteInternal σ) = w Γ)
    (i : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1))) (H : VectorGraph (n + 1) 2) :
    pairProfile w (σ i) (internalGraphEquiv (permutation i σ) 2 H) = pairProfile w i H := by
  simp only [pairProfile, Pi.sub_apply, Pi.smul_apply,
    forwardTemplateProfile_internal w hw, backwardTemplateProfile_internal w hw]

theorem pairProfile_internal_root (w : BinaryGraph (n + 1) 2 → k)
    (hw : ∀ Γ σ, w (Γ.permuteInternal σ) = w Γ)
    (i j : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1))) (hr : σ i = j)
    (H : VectorGraph (n + 1) 2) :
    pairProfile w j (internalGraphEquiv (SlotRelabelling.splitVertices i j σ hr (Equiv.refl _)) 2 H) =
      pairProfile w i H := by
  subst j
  exact pairProfile_internal w hw i σ H

end Source

namespace Correction
open MixedGraphCorrectionProfiles MixedGraphBoundaryProfiles
open BinaryVertexContraction

private theorem cast_vertices {b m : ℕ} {q q' : Fin b → ℕ} (h : q = q') (Γ : Graph q m) :
    (Graph.slotRelabelling_castProfile Γ h).vertices = Equiv.refl _ := by cases h; rfl

def quotientRelabelling (p : Placement n) (σ : Equiv.Perm (Fin (n + 2))) (Γ : QuotientGraph p) :
    SlotRelabelling Γ (Graph.twoOddGraphEquiv p.1 p.2 σ 2 Γ) :=
  (Graph.slotRelabelling_permuteProfile Γ σ).trans
    (Graph.slotRelabelling_castProfile _ (profileArity_twoOdd p.1 p.2 σ))

@[simp] theorem quotientRelabelling_vertices (p : Placement n) (σ : Equiv.Perm (Fin (n + 2)))
    (Γ : QuotientGraph p) : (quotientRelabelling p σ Γ).vertices = σ := by
  simp only [quotientRelabelling, SlotRelabelling.trans, cast_vertices]
  rfl

def dataEquiv (p : Placement n) (σ : Equiv.Perm (Fin (n + 2))) (δ : Equiv.Perm (Fin 2)) :
    CorrectionSplitData p ≃ CorrectionSplitData (correctionPlacementEquiv σ p) :=
  Equiv.sigmaCongr (Graph.twoOddGraphEquiv p.1 p.2 σ 2) (fun Γ =>
    Equiv.arrowCongr (SlotRelabelling.splitIncomingEquiv p.2 (σ p.2) (quotientRelabelling p σ Γ)
      (by rw [quotientRelabelling_vertices])) δ)

def permutation (p : Placement n) (σ : Equiv.Perm (Fin (n + 2))) (δ : Equiv.Perm (Fin 2)) :
    Equiv.Perm (Fin (n + 3)) := SlotRelabelling.splitVertices p.2 (σ p.2) σ rfl δ

def canonicalDataGraph (p : Placement n) (a : Fin 2) (D : CorrectionSplitData p) : VectorGraph (n + 2) 2 :=
  ofProfile (expandedVector p) (splitArity p)
    (D.1.vertexSplit (canonicalTemplate a) p.2 (selectedArity p).symm D.2)

theorem canonicalDataGraph_internal (p : Placement n) (σ : Equiv.Perm (Fin (n + 2)))
    (δ : Equiv.Perm (Fin 2)) (a : Fin 2) (D : CorrectionSplitData p) :
    canonicalDataGraph (correctionPlacementEquiv σ p) (δ a) (dataEquiv p σ δ D) =
      internalGraphEquiv (permutation p σ δ) 2 (canonicalDataGraph p a D) := by
  let p' := correctionPlacementEquiv σ p
  let F := quotientRelabelling p σ D.1
  let G := GraphCurvatureInternalRelabelling.templateRelabelling a δ
  have hF : F.vertices p.2 = σ p.2 := by rw [quotientRelabelling_vertices]
  let FS := SlotRelabelling.vertexSplit p.2 (σ p.2) F G
    (selectedArity p).symm (selectedArity p').symm hF D.2
  let FM := (ofProfileRelabelling (expandedVector p) (splitArity p) _).symm.trans
    (FS.trans (ofProfileRelabelling (expandedVector p') (splitArity p') _))
  apply vectorGraph_eq_internal (permutation p σ δ) FM
  · simp only [FM, FS, SlotRelabelling.trans, SlotRelabelling.symm, ofProfileRelabelling_vertices,
      SlotRelabelling.vertexSplit, F, G, quotientRelabelling_vertices,
      GraphCurvatureInternalRelabelling.templateRelabelling]
    rfl
  · exact (SlotRelabelling.splitVertices_old p.2 (σ p.2) σ rfl δ p.1 p.2.property.symm).symm

/-- Canonical pair coefficient includes the genuine two-odd sign at every placement. -/
def canonicalProfile (p : Placement n) (a : Fin 2) : VectorGraph (n + 2) 2 → ℝ :=
  pushforward (canonicalDataGraph p a) (fun D => placementSign p * canonicalQuotientWeight ⟨p,D.1⟩)

theorem canonicalProfile_internal (p : Placement n) (σ : Equiv.Perm (Fin (n + 2)))
    (δ : Equiv.Perm (Fin 2)) (a : Fin 2) (H : VectorGraph (n + 2) 2) :
    canonicalProfile (correctionPlacementEquiv σ p) (δ a)
      (internalGraphEquiv (permutation p σ δ) 2 H) = canonicalProfile p a H := by
  apply pushforward_relabelling _ _ (dataEquiv p σ δ) (internalGraphEquiv (permutation p σ δ) 2)
  · exact canonicalDataGraph_internal p σ δ a
  · intro D
    exact signed_canonicalQuotientWeight_correctionGraphEquiv σ ⟨p,D.1⟩

def pairProfile (p : Placement n) : VectorGraph (n + 2) 2 → ℝ := ∑ a : Fin 2, canonicalProfile p a

theorem pairProfile_internal (p : Placement n) (σ : Equiv.Perm (Fin (n + 2)))
    (δ : Equiv.Perm (Fin 2)) (H : VectorGraph (n + 2) 2) :
    pairProfile (correctionPlacementEquiv σ p) (internalGraphEquiv (permutation p σ δ) 2 H) =
      pairProfile p H := by
  simp only [pairProfile, Finset.sum_apply]
  rw [← Equiv.sum_comp δ]
  simp only [canonicalProfile_internal]

theorem placementEquiv_eq (p p' : Placement n) (σ : Equiv.Perm (Fin (n + 2)))
    (hv : σ p.1 = p'.1) (hr : σ p.2 = p'.2) : correctionPlacementEquiv σ p = p' := by
  apply Sigma.ext hv
  apply (Subtype.heq_iff_coe_eq (fun x => ?_)).mpr hr
  change x ≠ σ p.1 ↔ x ≠ p'.1
  rw [hv]

theorem pairProfile_internal_root (p p' : Placement n) (σ : Equiv.Perm (Fin (n + 2)))
    (δ : Equiv.Perm (Fin 2)) (hv : σ p.1 = p'.1) (hr : σ p.2 = p'.2)
    (H : VectorGraph (n + 2) 2) :
    pairProfile p' (internalGraphEquiv (SlotRelabelling.splitVertices p.2 p'.2 σ hr δ) 2 H) =
      pairProfile p H := by
  have hp := placementEquiv_eq p p' σ hv hr
  subst p'
  exact pairProfile_internal p σ δ H

end Correction
end EnvelopingIsomorphism.Deformation.MixedGraphInternalPairRelabelling
