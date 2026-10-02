import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityBoundaryGraphMatching
import EnvelopingIsomorphism.Deformation.Kontsevich.BlockPermutationSign

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.InfinityBinaryShapeOrderSign
open Kontsevich KontsevichGraph.General
open scoped Classical

theorem binary_reindex_sign {N M d : ℕ} (e : Fin M ≃ Fin N)
    (hN : (∑ _ : Fin N, 2) = d) (hM : (∑ _ : Fin M, 2) = d) :
    Equiv.Perm.sign (((finCongr hN.symm).trans (vertexMajorEdgeEquiv (fun _ : Fin N ↦ 2))).trans
      ((reindexEdgeEquiv (fun _ : Fin N ↦ 2) e).symm.trans
        ((finCongr hM.symm).trans (vertexMajorEdgeEquiv (fun _ : Fin M ↦ 2))).symm)) = 1 := by
  have hn : M = N := Fintype.card_fin M ▸ Fintype.card_fin N ▸ Fintype.card_congr e
  subst M
  have he : (((finCongr hN.symm).trans (vertexMajorEdgeEquiv (fun _ : Fin N ↦ 2))).trans
      ((reindexEdgeEquiv (fun _ : Fin N ↦ 2) e).symm.trans
        ((finCongr hM.symm).trans (vertexMajorEdgeEquiv (fun _ : Fin N ↦ 2))).symm)) =
      (finCongr hN).permCongr (profileRowPerm (fun _ : Fin N ↦ 2) e.symm) := by
    apply Equiv.ext
    intro j
    rfl
  rw [he,Equiv.Perm.sign_permCongr]
  exact profileRowPerm_sign_eq_one_of_even _ _ (fun _ ↦ by decide)

end EnvelopingIsomorphism.Deformation.InfinityBinaryShapeOrderSign
