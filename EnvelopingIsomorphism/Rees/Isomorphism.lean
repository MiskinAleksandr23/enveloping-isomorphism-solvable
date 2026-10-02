import EnvelopingIsomorphism.Rees.EnvelopingScaling
import EnvelopingIsomorphism.Rees.RangeDescent

/-!
# The actual Rees enveloping-algebra isomorphism

The polynomial algebra equivalence is obtained by restricting the scalar-extended original
equivalence through the two proved injective scaling maps. Range membership is proved by
the explicit polynomial PBW lift, so all algebra relations and inverse identities are retained.
-/

noncomputable section

namespace EnvelopingIsomorphism.Rees

open Module
open scoped TensorProduct BigOperators EnvelopingFamily

attribute [local instance] EnvelopingIsomorphism.Rees.laurentBaseModule
attribute [local instance] EnvelopingIsomorphism.Rees.envelopingLaurentSMul

variable {k ι L M : Type*} [Field k] [Fintype ι] [LinearOrder ι]
    [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]
    {bL : Basis ι k L} {bM : Basis ι k M}

namespace EnvelopingFamily

/-- Scalar extension of the original algebra map, viewed over the polynomial parameter ring. -/
def ambientHom (f : UniversalEnvelopingAlgebra k L →ₐ[k] UniversalEnvelopingAlgebra k M) :
    Ambient (k := k) (L := L) →ₐ[Polynomial k] Ambient (k := k) (L := M) where
  toRingHom := (Algebra.TensorProduct.map (AlgHom.id (LaurentSeries k) (LaurentSeries k)) f).toRingHom
  commutes' p := by
    change (Algebra.TensorProduct.map (AlgHom.id (LaurentSeries k) (LaurentSeries k)) f)
      (algebraMap (LaurentSeries k) (Ambient (k := k) (L := L))
        (algebraMap (Polynomial k) (LaurentSeries k) p)) = _
    exact (Algebra.TensorProduct.map (AlgHom.id (LaurentSeries k) (LaurentSeries k)) f).commutes _

@[simp] theorem ambientHom_tmul
    (f : UniversalEnvelopingAlgebra k L →ₐ[k] UniversalEnvelopingAlgebra k M)
    (a : LaurentSeries k) (x : UniversalEnvelopingAlgebra k L) :
    ambientHom f (a ⊗ₜ[k] x) = a ⊗ₜ[k] f x := by
  change Algebra.TensorProduct.map (AlgHom.id (LaurentSeries k) (LaurentSeries k)) f (a ⊗ₜ[k] x) = _
  simp

/-- The original algebra equivalence extends to the Laurent ambient algebras. -/
def ambientEquiv (Φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) :
    Ambient (k := k) (L := L) ≃ₐ[Polynomial k] Ambient (k := k) (L := M) where
  toRingEquiv := (Algebra.TensorProduct.congr
    (AlgEquiv.refl : LaurentSeries k ≃ₐ[LaurentSeries k] LaurentSeries k) Φ).toRingEquiv
  commutes' p := (ambientHom Φ.toAlgHom).commutes p

@[simp] theorem ambientEquiv_apply
    (Φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    (x : Ambient (k := k) (L := L)) : ambientEquiv Φ x = ambientHom Φ.toAlgHom x := rfl

@[simp] theorem ambientEquiv_symm_apply
    (Φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    (y : Ambient (k := k) (L := M)) :
    (ambientEquiv Φ).symm y = ambientHom Φ.symm.toAlgHom y := rfl

variable (dL : WeightData bL) (dM : WeightData bM)

/-- Weighted support on the images of the finite Lie basis is the required filtered input. -/
def FilteredGenerators
    (f : UniversalEnvelopingAlgebra k L →ₐ[k] UniversalEnvelopingAlgebra k M) : Prop :=
  ∀ i, f (UniversalEnvelopingAlgebra.ι k (bL i)) ∈
    PBW.weightedLower bM dM.weight (dL.weight i)

theorem mapped_generator_mem_range
    (f : UniversalEnvelopingAlgebra k L →ₐ[k] UniversalEnvelopingAlgebra k M)
    (hf : FilteredGenerators dL dM f) (i : ι) :
    ambientHom f (scaling dL (UniversalEnvelopingAlgebra.ι (Polynomial k) (Family.basis dL i))) ∈
      (scaling dM).range := by
  rw [scaling_ι_basis, ambientHom_tmul]
  refine ⟨homogenize dM (dL.weight i) (f (UniversalEnvelopingAlgebra.ι k (bL i))), ?_⟩
  simpa [WeightData.scale] using scaling_homogenize dM (dL.weight i)
    (f (UniversalEnvelopingAlgebra.ι k (bL i))) (hf i)

/-- The scalar-extended map carries the entire polynomial Rees envelope into the target range. -/
theorem mapped_mem_range
    (f : UniversalEnvelopingAlgebra k L →ₐ[k] UniversalEnvelopingAlgebra k M)
    (hf : FilteredGenerators dL dM f) (a : U dL) :
    ambientHom f (scaling dL a) ∈ (scaling dM).range := by
  induction a using EnvelopingIsomorphism.Enveloping.induction with
  | scalar p =>
      simp only [AlgHom.commutes]
      exact (scaling dM).range.algebraMap_mem p
  | generator x =>
      rw [← (Family.basis dL).sum_repr x]
      simp only [map_sum, map_smul]
      apply (scaling dM).range.toSubmodule.sum_mem
      intro i hi
      exact (scaling dM).range.toSubmodule.smul_mem _ (mapped_generator_mem_range dL dM f hf i)
  | mul a b ha hb =>
      simpa only [map_mul] using (scaling dM).range.mul_mem ha hb
  | add a b ha hb =>
      simpa only [map_add] using (scaling dM).range.add_mem ha hb

/-- The actual associative polynomial Rees equivalence induced by a filtered equivalence. -/
def filteredEquiv
    (Φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    (hΦ : FilteredGenerators dL dM Φ.toAlgHom)
    (hΦ' : FilteredGenerators dM dL Φ.symm.toAlgHom) : U dL ≃ₐ[Polynomial k] U dM :=
  descendAlongEmbeddings (scaling dL) (scaling dM) (scaling_injective dL) (scaling_injective dM)
    (ambientEquiv Φ) (mapped_mem_range dL dM Φ.toAlgHom hΦ)
    (mapped_mem_range dM dL Φ.symm.toAlgHom hΦ')

/-- The comparison is the original Φ conjugated by the exact diagonal scaling embeddings. -/
theorem filteredEquiv_commutes
    (Φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    (hΦ : FilteredGenerators dL dM Φ.toAlgHom)
    (hΦ' : FilteredGenerators dM dL Φ.symm.toAlgHom) (a : U dL) :
    scaling dM (filteredEquiv dL dM Φ hΦ hΦ' a) = ambientHom Φ.toAlgHom (scaling dL a) :=
  descendAlongEmbeddings_commutes _ _ (scaling_injective dL) (scaling_injective dM) _ _ _ _

/-- The generator images have exactly the PBW polynomial formula in D3. -/
theorem filteredEquiv_ι_basis
    (Φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    (hΦ : FilteredGenerators dL dM Φ.toAlgHom)
    (hΦ' : FilteredGenerators dM dL Φ.symm.toAlgHom) (i : ι) :
    filteredEquiv dL dM Φ hΦ hΦ' (UniversalEnvelopingAlgebra.ι (Polynomial k) (Family.basis dL i)) =
      homogenize dM (dL.weight i) (Φ (UniversalEnvelopingAlgebra.ι k (bL i))) := by
  apply scaling_injective dM
  rw [filteredEquiv_commutes, scaling_ι_basis, ambientHom_tmul]
  simpa only [WeightData.scale, AlgEquiv.coe_toAlgHom] using
    (scaling_homogenize dM (dL.weight i)
      (Φ.toAlgHom (UniversalEnvelopingAlgebra.ι k (bL i))) (hΦ i)).symm

/-- The exact leading congruences supplied by the identification of the filtered Lie generators. -/
def LeadingGenerators
    (f : UniversalEnvelopingAlgebra k L →ₐ[k] UniversalEnvelopingAlgebra k M) : Prop :=
  ∀ i, f (UniversalEnvelopingAlgebra.ι k (bL i)) - UniversalEnvelopingAlgebra.ι k (bM i) ∈
    PBW.weightedLower bM dM.weight (dL.weight i + 1)

omit [Fintype ι] in
theorem filteredGenerators_of_leading
    (f : UniversalEnvelopingAlgebra k L →ₐ[k] UniversalEnvelopingAlgebra k M)
    (hw : dL.weight = dM.weight) (hf : LeadingGenerators dL dM f) :
    FilteredGenerators dL dM f := by
  intro i
  have hg : UniversalEnvelopingAlgebra.ι k (bM i) ∈
      PBW.weightedLower bM dM.weight (dL.weight i) := by
    simpa only [PBW.pbwBasis_single] using
      PBW.pbwBasis_mem_weightedLower bM dM.weight
        (m := Finsupp.single i 1) (d := dL.weight i) (by simp [hw, Finsupp.weight_single])
  have hd := PBW.weightedLower_antitone bM dM.weight (Nat.le_succ (dL.weight i)) (hf i)
  simpa only [sub_add_cancel] using
    (PBW.weightedLower bM dM.weight (dL.weight i)).add_mem hd hg

/-- D3's polynomial Rees equivalence from the two C5 leading congruences. -/
def ofLeading
    (Φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    (hw : dL.weight = dM.weight)
    (hΦ : LeadingGenerators dL dM Φ.toAlgHom)
    (hΦ' : LeadingGenerators dM dL Φ.symm.toAlgHom) : U dL ≃ₐ[Polynomial k] U dM :=
  filteredEquiv dL dM Φ (filteredGenerators_of_leading dL dM Φ.toAlgHom hw hΦ)
    (filteredGenerators_of_leading dM dL Φ.symm.toAlgHom hw.symm hΦ')

theorem ofLeading_ι_basis
    (Φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    (hw : dL.weight = dM.weight)
    (hΦ : LeadingGenerators dL dM Φ.toAlgHom)
    (hΦ' : LeadingGenerators dM dL Φ.symm.toAlgHom) (i : ι) :
    ofLeading dL dM Φ hw hΦ hΦ' (UniversalEnvelopingAlgebra.ι (Polynomial k) (Family.basis dL i)) =
      homogenize dM (dL.weight i) (Φ (UniversalEnvelopingAlgebra.ι k (bL i))) :=
  filteredEquiv_ι_basis _ _ _ _ _ _

section Marking

variable {B : Type*} [Ring B] [Algebra (Polynomial k) B]

/-- Every zero-parameter specialization sends the Rees image of a generator to its prescribed
target generator. The possible nonlinear corrections vanish by their strict weight bound. -/
theorem ofLeading_specializes_ι_basis
    (Φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    (hw : dL.weight = dM.weight)
    (hΦ : LeadingGenerators dL dM Φ.toAlgHom)
    (hΦ' : LeadingGenerators dM dL Φ.symm.toAlgHom)
    (χ : U dM →ₐ[Polynomial k] B)
    (hX : algebraMap (Polynomial k) B Polynomial.X = 0) (i : ι) :
    χ (ofLeading dL dM Φ hw hΦ hΦ'
      (UniversalEnvelopingAlgebra.ι (Polynomial k) (Family.basis dL i))) =
        χ (UniversalEnvelopingAlgebra.ι (Polynomial k) (Family.basis dM i)) := by
  rw [ofLeading_ι_basis, congrFun hw i]
  apply homogenize_leading_specializes dM _ i _ χ hX
  simpa only [AlgEquiv.coe_toAlgHom, congrFun hw i] using hΦ i

/-- The marking holds on the whole enveloping algebra after a common zero-fiber identification. -/
theorem ofLeading_specializes
    (Φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    (hw : dL.weight = dM.weight)
    (hΦ : LeadingGenerators dL dM Φ.toAlgHom)
    (hΦ' : LeadingGenerators dM dL Φ.symm.toAlgHom)
    (χL : U dL →ₐ[Polynomial k] B) (χM : U dM →ₐ[Polynomial k] B)
    (hX : algebraMap (Polynomial k) B Polynomial.X = 0)
    (hχ : ∀ i, χL (UniversalEnvelopingAlgebra.ι (Polynomial k) (Family.basis dL i)) =
      χM (UniversalEnvelopingAlgebra.ι (Polynomial k) (Family.basis dM i))) :
    χM.comp (ofLeading dL dM Φ hw hΦ hΦ').toAlgHom = χL := by
  apply EnvelopingIsomorphism.Enveloping.hom_ext_ι
  intro x
  change χM (ofLeading dL dM Φ hw hΦ hΦ' (UniversalEnvelopingAlgebra.ι (Polynomial k) x)) =
    χL (UniversalEnvelopingAlgebra.ι (Polynomial k) x)
  rw [← (Family.basis dL).sum_repr x]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun z ↦ (Family.basis dL).repr x i • z)
    ((ofLeading_specializes_ι_basis dL dM Φ hw hΦ hΦ' χM hX i).trans (hχ i).symm)

end Marking

end EnvelopingFamily

end EnvelopingIsomorphism.Rees
