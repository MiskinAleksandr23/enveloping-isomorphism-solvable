import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterFaceBasisSign
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestOverlapJacobian

/-! The actual paired simple-collar physical sign, with no sign premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestOverlapJacobian
open PairedForestSimpleCluster
variable {n m : ℕ} (x : Compactification (0 : Fin (n+1)) m)
  (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : ForestRadialFaceClassification.kind 0 x o = .paired)

theorem simpleSign_eq_neg_one : simpleSign (m := m) x o ho = -1 := by
  classical
  have h := ClusterFaceBasisSign.sign_basisPermutation (n := n) (m := m) (i := (0 : Fin (n+1)))
    (anchor_mem x o ho) (reference_mem x o ho) (reference_ne_anchor x o ho) (anchor_global x o ho)
  unfold simpleSign
  convert congrArg (fun u : ℤˣ => -(u : ℝ)) h using 1 <;> norm_num
  congr 2
  congr 1
  exact Subsingleton.elim _ _


end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestOverlapJacobian
