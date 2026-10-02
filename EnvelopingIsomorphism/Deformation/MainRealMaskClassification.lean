import EnvelopingIsomorphism.Deformation.MainRealOrderedChartIntegral

/-! Actual physical nonempty real masks recover both original boundary-block
endpoints uniquely, so all supported charts share the same face parameters. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainRealMaskClassification
open Kontsevich Configuration ForestRadialFaceClassification
open RealForestCoarsePositions (labelsSet node)
open RealForestSimpleCluster (lower upper)
open MainFixedSimpleChartTransfer MainScalarBoundaryAssembly
open scoped Classical

theorem boundaryBlock_endpoints_eq {m : ℕ} (l u l' u' : Fin (m+1))
    (hlt : l < u) (he : boundaryClusterBlock l u = boundaryClusterBlock l' u') :
    l = l' ∧ u = u' := by
  have hlm : l.val < m := by have hu := u.isLt; omega
  have hfirst : (⟨l.val,hlm⟩ : Fin m) ∈ boundaryClusterBlock l' u' := by
    rw [← he,mem_boundaryClusterBlock]
    exact ⟨le_rfl,hlt⟩
  have hfirst' := (mem_boundaryClusterBlock l' u' _).mp hfirst
  change l'.val ≤ l.val ∧ l.val < u'.val at hfirst'
  have hlm' : l'.val < m := by omega
  have hlt' : l'.val < u'.val := by omega
  have hsecond : (⟨l'.val,hlm'⟩ : Fin m) ∈ boundaryClusterBlock l u := by
    rw [he,mem_boundaryClusterBlock]
    exact ⟨le_rfl,hlt'⟩
  have hsecond' := (mem_boundaryClusterBlock l u _).mp hsecond
  change l.val ≤ l'.val ∧ l'.val < u.val at hsecond'
  have hle : l = l' := Fin.ext (by omega)
  have hum : u.val - 1 < m := by have hu := u.isLt; omega
  have hlast : (⟨u.val-1,hum⟩ : Fin m) ∈ boundaryClusterBlock l' u' := by
    rw [← he,mem_boundaryClusterBlock]
    change l.val ≤ u.val - 1 ∧ u.val - 1 < u.val
    constructor <;> omega
  have hlast' := (mem_boundaryClusterBlock l' u' _).mp hlast
  change l'.val ≤ u.val - 1 ∧ u.val - 1 < u'.val at hlast'
  have hum' : u'.val - 1 < m := by have hu := u'.isLt; omega
  have hlast₂ : (⟨u'.val-1,hum'⟩ : Fin m) ∈ boundaryClusterBlock l u := by
    rw [he,mem_boundaryClusterBlock]
    change l'.val ≤ u'.val - 1 ∧ u'.val - 1 < u'.val
    constructor <;> omega
  have hlast₂' := (mem_boundaryClusterBlock l u _).mp hlast₂
  change l.val ≤ u'.val - 1 ∧ u'.val - 1 < u.val at hlast₂'
  exact ⟨hle,Fin.ext (by omega)⟩

theorem properReal_labels_of_mask {n m : ℕ}
    (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x)
    {S : Finset (Fin (n+1))} {l u : Fin (m+1)} (hlt : l < u)
    (hm : (representative 0 x o).val.val = collisionMask S l u) :
    labelsSet x o = S ∧ lower x o = l ∧ upper x o = u := by
  refine ⟨interiorLabels_of_mask x (node x o) S l u hm,?_⟩
  have he : boundaryClusterBlock l u = boundaryClusterBlock (lower x o) (upper x o) :=
    (boundaryLabels_of_mask x (node x o) S l u hm).symm.trans
      (ForestRadialClusterLabels.boundaryLabels_eq_block 0 x (node x o))
  obtain ⟨hl,hu⟩ := boundaryBlock_endpoints_eq l u (lower x o) (upper x o) hlt he
  exact ⟨hl.symm,hu.symm⟩

variable {n : ℕ} {H : UniformBinaryGraphs.BinaryGraph (n+2) 3}
    (P : MainPartition H) (j : P.charts)

/-- An original nonzero partition weight supplies a native source with the
same physical subset and the very same boundary-block endpoints. -/
theorem properReal_source_of_cutoff {i a : Fin (n+2)} {S : Finset (Fin (n+2))}
    {l u : Fin 4} (D : BoundaryClusterData i a 3 S l u) (hlt : l < u)
    (hρ : CompactDRAmbientPartition.cutoff 0 (P.partition j) (anchorHomeomorph i 0 D.boundaryPoint) ≠ 0) :
    ∃ (o : Orbit 0 j.val) (z : ForestRadialFaceLocalization.source (main_dimension n) j.val o),
      kind 0 j.val o = .properReal ∧ labelsSet j.val o = S ∧ lower j.val o = l ∧ upper j.val o = u ∧
      PairedForestSimpleOverlap.facePoint (main_dimension n) j.val o z = anchorHomeomorph i 0 D.boundaryPoint := by
  obtain ⟨o,z,ho,hm,hz⟩ := properReal_source_changeAnchor (main_dimension n) j.val D
    (MainPairedChartTransfer.mem_chart_of_cutoff_ne_zero P j _ hρ)
  obtain ⟨hS,hl,hu⟩ := properReal_labels_of_mask j.val o hlt hm
  exact ⟨o,z,ho,hS,hl,hu,hz⟩

end EnvelopingIsomorphism.Deformation.MainRealMaskClassification
