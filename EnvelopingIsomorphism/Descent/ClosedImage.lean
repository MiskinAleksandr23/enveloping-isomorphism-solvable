import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Constructible
import Mathlib.RingTheory.Nullstellensatz

/-!
# Closed images: topological and polynomial ingredients

The Zariski topology on algebraic-group points need not make multiplication continuous
for the product topology. The group lemmas below use only separately continuous
multiplication and continuous inversion.
-/

namespace EnvelopingIsomorphism.Descent

open Set Topology

section Constructible

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous preimage of a constructible set has nowhere dense frontier.
The preimage need not itself be constructible in the retrocompact convention. -/
theorem interior_frontier_preimage_eq_empty {f : X → Y} (hf : Continuous f)
    {s : Set Y} (hs : IsConstructible s) :
    interior (frontier (f ⁻¹' s)) = ∅ := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
      rw [← frontier_compl]
      exact interior_frontier (hU.preimage hf).isClosed_compl
  | union s hs t ht ihs iht =>
      apply Set.eq_empty_of_subset_empty
      calc
        interior (frontier (f ⁻¹' (s ∪ t))) ⊆
            interior (frontier (f ⁻¹' s) ∪ frontier (f ⁻¹' t)) := by
          rw [preimage_union]
          exact interior_mono ((frontier_union_subset _ _).trans
            (union_subset_union inter_subset_left inter_subset_right))
        _ = ∅ := by
          rw [interior_union_isClosed_of_interior_empty isClosed_frontier iht, ihs]
  | compl s hs ih =>
      simpa only [preimage_compl, frontier_compl] using ih

end Constructible

section Topology

variable {G : Type*} [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G] [ContinuousInv G]

/-- Closure of a subgroup with the weaker continuity assumptions appropriate to
Zariski topologies. -/
def subgroupClosure (H : Subgroup G) : Subgroup G :=
  { H.toSubmonoid.topologicalClosure with
    carrier := closure (H : Set G)
    inv_mem' := fun hx => map_mem_closure continuous_inv hx fun _ hy => H.inv_mem hy }

private theorem closure_subgroup_separatelyContinuousMul (H : Subgroup G) :
    SeparatelyContinuousMul (subgroupClosure H) :=
  Topology.IsInducing.subtypeVal.separatelyContinuousMul (subgroupClosure H).subtype

/-- A locally closed subgroup is closed. Joint continuity of multiplication is not
needed. -/
theorem subgroup_isClosed_of_isLocallyClosed (H : Subgroup G)
    (hH : IsLocallyClosed (H : Set G)) : IsClosed (H : Set G) := by
  let K := subgroupClosure H
  letI : SeparatelyContinuousMul K := closure_subgroup_separatelyContinuousMul H
  have hopen : IsOpen (H.subgroupOf K : Set K) :=
    hH.isOpen_preimage_val_closure
  have hclosed := (H.subgroupOf K).isClosed_of_isOpen hopen
  have himage : Subtype.val '' (H.subgroupOf K : Set K) = (H : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, subset_closure hx⟩, hx, rfl⟩
  rw [← himage]
  exact isClosed_closure.isClosedMap_subtype_val _ hclosed

/-- A constructible subgroup is closed under separately continuous multiplication
and continuous inversion. In particular, no topological-group instance for the
product topology is required. -/
theorem subgroup_isClosed_of_isConstructible (H : Subgroup G)
    (hH : IsConstructible (H : Set G)) : IsClosed (H : Set G) := by
  let K := subgroupClosure H
  letI : SeparatelyContinuousMul K := closure_subgroup_separatelyContinuousMul H
  have himage : Subtype.val '' (H.subgroupOf K : Set K) = (H : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, subset_closure hx⟩, hx, rfl⟩
  have hdense : Dense (H.subgroupOf K : Set K) := by
    rw [Subtype.dense_iff]
    exact (congrArg closure himage).ge
  have hfront : interior (frontier (H.subgroupOf K : Set K)) = ∅ :=
    interior_frontier_preimage_eq_empty continuous_subtype_val hH
  have hne : (interior (H.subgroupOf K : Set K)).Nonempty := by
    by_contra h
    have hempty := Set.not_nonempty_iff_eq_empty.mp h
    have heq : frontier (H.subgroupOf K : Set K) = univ := by
      rw [frontier, hdense.closure_eq, hempty, sdiff_empty]
    rw [heq, interior_univ] at hfront
    exact Set.univ_nonempty.ne_empty hfront
  obtain ⟨x, hx⟩ := hne
  have hopen := (H.subgroupOf K).isOpen_of_mem_nhds (mem_interior_iff_mem_nhds.mp hx)
  have hclosed := (H.subgroupOf K).isClosed_of_isOpen hopen
  rw [← himage]
  exact isClosed_closure.isClosedMap_subtype_val _ hclosed

end Topology

section Polynomial

open MvPolynomial

variable {k K σ τ : Type*} [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
  [Finite σ]

/-- Equations valid on all base-field points of an affine algebraic set remain
valid at every point over an extension field. Nullstellensatz supplies radical
membership, so no reducedness assumption on the defining ideal is needed. -/
theorem aeval_eq_zero_of_zeroLocus (I : Ideal (MvPolynomial σ k))
    (p : MvPolynomial σ k)
    (hp : ∀ x ∈ zeroLocus k I, aeval x p = 0)
    (x : σ → K) (hx : x ∈ zeroLocus K I) : aeval x p = 0 := by
  have hrad : p ∈ I.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := k) I]
    exact hp
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
  have hpow : (aeval x p) ^ n = 0 := by simpa using hx (p ^ n) hn
  exact eq_zero_of_pow_eq_zero hpow

/-- A polynomial relation satisfied by the image on algebraically closed
base-field points is also satisfied by the image on extension-field points. -/
theorem polynomial_image_relation_baseChange (I : Ideal (MvPolynomial σ k))
    (F : τ → MvPolynomial σ k) (q : MvPolynomial τ k)
    (hq : ∀ x ∈ zeroLocus k I, aeval (fun i => aeval x (F i)) q = 0)
    (x : σ → K) (hx : x ∈ zeroLocus K I) :
    aeval (fun i => aeval x (F i)) q = 0 := by
  simpa only [MvPolynomial.comp_aeval_apply] using
    aeval_eq_zero_of_zeroLocus I (aeval F q)
      (by simpa only [MvPolynomial.comp_aeval_apply] using hq) x hx

/-- A finite system over an algebraically closed field with a solution in a
field extension already has a solution in the base field. -/
theorem zeroLocus_nonempty_of_extensionPoint (I : Ideal (MvPolynomial σ k))
    (x : σ → K) (hx : x ∈ zeroLocus K I) : (zeroLocus k I).Nonempty := by
  by_contra h
  have hone : aeval x (1 : MvPolynomial σ k) = 0 :=
    aeval_eq_zero_of_zeroLocus I 1 (fun y hy => False.elim (h ⟨y, hy⟩)) x hx
  exact one_ne_zero (by simpa only [map_one] using hone)

end Polynomial

end EnvelopingIsomorphism.Descent
