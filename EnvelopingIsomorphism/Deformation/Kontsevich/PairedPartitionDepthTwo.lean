import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterPartitionTree

/-! A finite, three-partition criterion for a hierarchy with two equally sized
nonroot internal clusters. The criterion inspects only the root partition and
the two cluster partitions, not the recursively generated hierarchy. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedPartitionDepthTwo

open ClusterPartitionTree
open scoped Classical

variable {I : Type*} [DecidableEq I]
variable (P : ∀ A : Finset I, Finpartition A)
variable (hp : ∀ A, 1 < A.card → ∀ B ∈ (P A).parts, B.card < A.card)
variable (R U V : Finset I)

/-- Exactly two prescribed large root parts, each partitioning into singletons.
The remaining root parts are singletons as well. -/
def ThreePartitions : Prop :=
  U ∈ (P R).parts ∧ V ∈ (P R).parts ∧
  (∀ B ∈ (P R).parts, 1 < B.card → B = U ∨ B = V) ∧
  (∀ B ∈ (P U).parts, B.card ≤ 1) ∧
  (∀ B ∈ (P V).parts, B.card ≤ 1)

theorem large_clusters_iff_threePartitions
    (hR : 1 < R.card) (hU : 1 < U.card) (hUV : U.card = V.card)
    (hUR : U ≠ R) (hVR : V ≠ R) :
    (U ∈ clusters P hp R ∧ V ∈ clusters P hp R ∧
      ∀ B ∈ clusters P hp R, B ≠ R → 1 < B.card → B = U ∨ B = V) ↔
      ThreePartitions P R U V := by
  constructor
  · rintro ⟨hu, hv, hall⟩
    have root_part (A : Finset I) (hA : A ∈ clusters P hp R)
        (hAR : A ≠ R) (hAc : A.card = U.card) : A ∈ (P R).parts := by
      rcases (mem_clusters P hp R A).mp hA with he | ⟨C, hC, hAC⟩
      · exact (hAR he).elim
      have hsub := subset_of_mem_clusters P hp C A hAC
      have hlarge : 1 < C.card := lt_of_lt_of_le (hAc ▸ hU) (Finset.card_le_card hsub)
      have hCroot : C ≠ R := (Finset.ssubset_iff_subset_ne.mp (child_ssubset P hp hC)).2
      have hCc : C.card = U.card := by
        rcases hall C (child_mem_clusters P hp hC) hCroot hlarge with rfl | rfl
        · rfl
        · exact hUV.symm
      have he : A = C := Finset.eq_of_subset_of_card_le hsub (by omega)
      exact he ▸ ((mem_children P R C).mp hC).2
    have inner_small (A : Finset I) (hA : A ∈ clusters P hp R)
        (hAc : A.card = U.card) (B : Finset I) (hB : B ∈ (P A).parts) : B.card ≤ 1 := by
      have hAlarge : 1 < A.card := hAc ▸ hU
      have hchild : B ∈ children P A := (mem_children P A B).mpr ⟨hAlarge, hB⟩
      have hBc := child_card_lt P hp hchild
      have hBmem := clusters_subset_of_mem P hp R A hA (child_mem_clusters P hp hchild)
      have hBR : B ≠ R := by
        intro he
        have hsub := Finset.card_le_card (subset_of_mem_clusters P hp R A hA)
        rw [he] at hBc
        omega
      by_contra hsmall
      rcases hall B hBmem hBR (by omega) with he | he
      · rw [he] at hBc
        omega
      · rw [he] at hBc
        omega
    refine ⟨root_part U hu hUR rfl, root_part V hv hVR hUV.symm, ?_,
      inner_small U hu rfl, inner_small V hv hUV.symm⟩
    intro B hB hlarge
    have hchild := (mem_children P R B).mpr ⟨hR, hB⟩
    exact hall B (child_mem_clusters P hp hchild)
      (Finset.ssubset_iff_subset_ne.mp (child_ssubset P hp hchild)).2 hlarge
  · rintro ⟨hu, hv, hroot, hupper, hlower⟩
    refine ⟨child_mem_clusters P hp ((mem_children P R U).mpr ⟨hR, hu⟩),
      child_mem_clusters P hp ((mem_children P R V).mpr ⟨hR, hv⟩), ?_⟩
    intro B hB hBR hlarge
    rcases (mem_clusters P hp R B).mp hB with he | ⟨C, hC, hBC⟩
    · exact (hBR he).elim
    have hCpart := ((mem_children P R C).mp hC).2
    have hClarge := lt_of_lt_of_le hlarge
      (Finset.card_le_card (subset_of_mem_clusters P hp C B hBC))
    have hCmask := hroot C hCpart hClarge
    rcases (mem_clusters P hp C B).mp hBC with rfl | ⟨D, hD, hBD⟩
    · exact hCmask
    have hDpart := ((mem_children P C D).mp hD).2
    have hDsmall : D.card ≤ 1 := by
      rcases hCmask with rfl | rfl
      · exact hupper D hDpart
      · exact hlower D hDpart
    have hBDcard := Finset.card_le_card (subset_of_mem_clusters P hp D B hBD)
    omega

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedPartitionDepthTwo
