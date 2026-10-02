import EnvelopingIsomorphism.Deformation.InfinityBinaryShapeOrderSign
import EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeightRelabel

/-! Infinity extraction reorders source blocks. A single odd source block
introduces no row sign, including a vector placed at any internal vertex. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.InfinityProfileShapeOrderSign
open Kontsevich KontsevichGraph.General
open scoped Classical

theorem reindex_sign_of_even_off {N M d : ℕ} (q : Fin N → ℕ) (e : Fin M ≃ Fin N)
    (hN : (∑ v, q v) = d) (hM : (∑ v, q (e v)) = d)
    (v : Fin N) (heven : ∀ w, w ≠ v → Even (q w)) :
    Equiv.Perm.sign (((finCongr hN.symm).trans (vertexMajorEdgeEquiv q)).trans
      ((reindexEdgeEquiv q e).symm.trans
        ((finCongr hM.symm).trans (vertexMajorEdgeEquiv (fun v ↦ q (e v)))).symm)) = 1 := by
  have hn : M = N := Fintype.card_fin M ▸ Fintype.card_fin N ▸ Fintype.card_congr e
  subst M
  have he : (((finCongr hN.symm).trans (vertexMajorEdgeEquiv q)).trans
      ((reindexEdgeEquiv q e).symm.trans
        ((finCongr hM.symm).trans (vertexMajorEdgeEquiv (fun v ↦ q (e v)))).symm)) =
      (finCongr hN).permCongr (profileRowPerm q e.symm) := by
    apply Equiv.ext
    intro j
    rfl
  rw [he,Equiv.Perm.sign_permCongr]
  exact profileRowPerm_sign_eq_one_of_even_off q e.symm v heven

theorem canonicalWeight_reindex_of_even_off {N K m M : ℕ} {q : Fin (N+1) → ℕ}
    (G : Graph q m) (hK : K = N) (hM : M = m)
    (e : Fin (K+1) ≃ Fin (N+1)) (eB : Fin M ≃ Fin m)
    (heB : ∀ j, (eB j).val = j.val)
    (hq : ∑ v, q v = GraphForms.dimension N m)
    (hq' : ∑ v, q (e v) = GraphForms.dimension K M)
    (v : Fin (N+1)) (heven : ∀ w, w ≠ v → Even (q w)) :
    GeometricWeights.canonicalWeight (G.reindex e eB) hq' =
      GeometricWeights.canonicalWeight G hq := by
  subst K M
  have he : eB = Equiv.refl _ := by
    apply Equiv.ext
    intro j
    exact Fin.ext (heB j)
  subst eB
  exact GeometricWeights.canonicalWeight_permuteProfile_of_even_off G hq e.symm v heven

end EnvelopingIsomorphism.Deformation.InfinityProfileShapeOrderSign
