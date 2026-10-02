import EnvelopingIsomorphism.Deformation.GeneralGraphOperators
import Mathlib.LinearAlgebra.Alternating.Basic

/-! Outgoing-edge permutation laws for the actual polynomial graph operators. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General

open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- The permutation sign as a scalar in the coefficient ring. -/
def permutationSign {q : ℕ} (τ : Equiv.Perm (Fin q)) : R := ((Equiv.Perm.sign τ : ℤ) : R)

/-- The coordinate transformation law supplied by an alternating tensor. -/
def TensorPermutationLaw {q d : ℕ} (T : Tensor q d R) : Prop :=
  ∀ τ : Equiv.Perm (Fin q), ∀ a : Fin q → Fin d,
    T (a ∘ τ) = permutationSign (R := R) τ • T a

/-- Actual coordinate coefficients of a native alternating multilinear map. -/
def tensorOfAlternating {q d : ℕ}
    (F : AlternatingMap R (Fin d → R) (Polynomial d R) (Fin q)) : Tensor q d R :=
  fun a ↦ F (fun i ↦ Pi.single (a i) 1)

theorem tensorOfAlternating_permutationLaw {q d : ℕ}
    (F : AlternatingMap R (Fin d → R) (Polynomial d R) (Fin q)) :
    TensorPermutationLaw (tensorOfAlternating F) := by
  intro τ a
  have h := F.map_perm (fun i ↦ Pi.single (a i) 1) τ
  simpa only [tensorOfAlternating, TensorPermutationLaw, permutationSign,
    Function.comp_def, Units.smul_def, ← Int.cast_smul_eq_zsmul R] using h

def permuteTensor {q d : ℕ} (τ : Equiv.Perm (Fin q)) : Tensor q d R →ₗ[R] Tensor q d R where
  toFun T a := T (a ∘ τ)
  map_add' T S := by funext a; rfl
  map_smul' r T := by funext a; rfl

@[simp] theorem permuteTensor_apply {q d : ℕ} (τ : Equiv.Perm (Fin q))
    (T : Tensor q d R) (a : Fin q → Fin d) : permuteTensor τ T a = T (a ∘ τ) := rfl

variable {n m d : ℕ} {q : Fin n → ℕ}

def outgoingEdgePerm (τ : (v : Fin n) → Equiv.Perm (Fin (q v))) : Equiv.Perm (Edge q) :=
  Equiv.sigmaCongrRight τ

@[simp] theorem outgoingEdgePerm_apply (τ : (v : Fin n) → Equiv.Perm (Fin (q v)))
    (v : Fin n) (a : Fin (q v)) : outgoingEdgePerm τ ⟨v, a⟩ = ⟨v, τ v a⟩ := rfl

@[simp] theorem outgoingEdgePerm_symm_apply (τ : (v : Fin n) → Equiv.Perm (Fin (q v)))
    (v : Fin n) (a : Fin (q v)) : (outgoingEdgePerm τ).symm ⟨v, a⟩ = ⟨v, (τ v).symm a⟩ := rfl

def outgoingLabelEquiv (τ : (v : Fin n) → Equiv.Perm (Fin (q v))) :
    (Edge q → Fin d) ≃ (Edge q → Fin d) where
  toFun lab e := lab ((outgoingEdgePerm τ).symm e)
  invFun lab e := lab (outgoingEdgePerm τ e)
  left_inv lab := by funext e; simp
  right_inv lab := by funext e; simp

@[simp] theorem outgoingLabelEquiv_apply (τ : (v : Fin n) → Equiv.Perm (Fin (q v)))
    (lab : Edge q → Fin d) (v : Fin n) (a : Fin (q v)) :
    outgoingLabelEquiv τ lab ⟨v, a⟩ = lab ⟨v, (τ v).symm a⟩ := rfl

namespace Graph

/-- Reorder the outgoing slots at each internal vertex, keeping the vertices fixed. -/
def permuteOutgoing (Γ : Graph q m) (τ : (v : Fin n) → Equiv.Perm (Fin (q v))) : Graph q m where
  target e := Γ.target (outgoingEdgePerm τ e)
  noLoops v a := Γ.noLoops v (τ v a)
  distinctTargets v := (Γ.distinctTargets v).comp (τ v).injective

theorem incoming_permuteOutgoing_perm (Γ : Graph q m)
    (τ : (v : Fin n) → Equiv.Perm (Fin (q v))) (v : Vertex n m) :
    (((Γ.permuteOutgoing τ).incoming v).toList.map (outgoingEdgePerm τ)).Perm (Γ.incoming v).toList := by
  classical
  apply (List.perm_ext_iff_of_nodup
    ((Finset.nodup_toList _).map (outgoingEdgePerm τ).injective) (Finset.nodup_toList _)).mpr
  intro e
  simp only [List.mem_map, Finset.mem_toList, incoming, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, heq⟩
    change Γ.target (outgoingEdgePerm τ a) = v at ha
    exact heq ▸ ha
  · intro he
    refine ⟨(outgoingEdgePerm τ).symm e, ?_, by simp⟩
    change Γ.target (outgoingEdgePerm τ ((outgoingEdgePerm τ).symm e)) = v
    simpa using he

theorem vertexDerivative_permuteOutgoing (Γ : Graph q m)
    (τ : (v : Fin n) → Equiv.Perm (Fin (q v))) (lab : Edge q → Fin d) (v : Vertex n m) :
    (Γ.permuteOutgoing τ).vertexDerivative (R := R) lab v =
      Γ.vertexDerivative (outgoingLabelEquiv τ lab) v := by
  apply iteratedPDeriv_perm
  have h := (incoming_permuteOutgoing_perm Γ τ v).map (outgoingLabelEquiv τ lab)
  rw [List.map_map] at h
  have hcomp : (outgoingLabelEquiv τ lab) ∘ outgoingEdgePerm τ = lab := by
    funext e
    change lab ((outgoingEdgePerm τ).symm (outgoingEdgePerm τ e)) = lab e
    rw [Equiv.symm_apply_apply]
  rwa [hcomp] at h

theorem labelledOperator_permuteOutgoing (Γ : Graph q m)
    (τ : (v : Fin n) → Equiv.Perm (Fin (q v))) (lab : Edge q → Fin d)
    (T : (v : Fin n) → Tensor (q v) d R) (f : Fin m → Polynomial d R) :
    ((Γ.permuteOutgoing τ).labelledOperator lab).currySum T f =
      (Γ.labelledOperator (outgoingLabelEquiv τ lab)).currySum
        (fun v ↦ permuteTensor (τ v) (T v)) f := by
  rw [MultilinearMap.currySum_apply, MultilinearMap.currySum_apply,
    labelledOperator_apply, labelledOperator_apply]
  apply Finset.prod_congr rfl
  intro v hv
  rw [vertexDerivative_permuteOutgoing]
  cases v with
  | inl v =>
    congr 1
    change T v (fun a ↦ lab ⟨v, a⟩) =
      T v ((fun a ↦ outgoingLabelEquiv τ lab ⟨v, a⟩) ∘ τ v)
    congr 1
    funext a
    simp
  | inr j => rfl

/-- Exact covariance before imposing alternation: outgoing permutations precompose the
ordered coordinate tensors, via an actual bijection of all edge labellings. -/
theorem cochainOperator_permuteOutgoing_covariance (Γ : Graph q m)
    (τ : (v : Fin n) → Equiv.Perm (Fin (q v))) (T : (v : Fin n) → Tensor (q v) d R) :
    (Γ.permuteOutgoing τ).cochainOperator T =
      Γ.cochainOperator (fun v ↦ permuteTensor (τ v) (T v)) := by
  apply MultilinearMap.ext
  intro f
  classical
  change ((∑ lab : Edge q → Fin d, (Γ.permuteOutgoing τ).labelledOperator lab).currySum T) f =
    ((∑ lab : Edge q → Fin d, Γ.labelledOperator lab).currySum
      (fun v ↦ permuteTensor (τ v) (T v))) f
  simp only [MultilinearMap.currySum_apply, sum_apply]
  apply Fintype.sum_equiv (outgoingLabelEquiv τ)
  intro lab
  exact labelledOperator_permuteOutgoing Γ τ lab T f

/-- Alternating coordinate tensors give precisely the product of the outgoing permutation signs. -/
theorem cochainOperator_permuteOutgoing_sign (Γ : Graph q m)
    (τ : (v : Fin n) → Equiv.Perm (Fin (q v))) (T : (v : Fin n) → Tensor (q v) d R)
    (hT : ∀ v, TensorPermutationLaw (T v)) :
    (Γ.permuteOutgoing τ).cochainOperator T =
      (∏ v : Fin n, permutationSign (R := R) (τ v)) • Γ.cochainOperator T := by
  rw [cochainOperator_permuteOutgoing_covariance]
  have heq : (fun v ↦ permuteTensor (τ v) (T v)) = fun v ↦ permutationSign (R := R) (τ v) • T v := by
    funext v a
    exact hT v (τ v) a
  rw [heq]
  exact (Γ.cochainOperator).map_smul_univ (fun v ↦ permutationSign (τ v)) T

/-- The sign law in particular holds for actual native alternating multilinear maps. -/
theorem cochainOperator_permuteOutgoing_of_alternating (Γ : Graph q m)
    (τ : (v : Fin n) → Equiv.Perm (Fin (q v)))
    (F : (v : Fin n) → AlternatingMap R (Fin d → R) (Polynomial d R) (Fin (q v))) :
    (Γ.permuteOutgoing τ).cochainOperator (fun v ↦ tensorOfAlternating (F v)) =
      (∏ v : Fin n, permutationSign (R := R) (τ v)) •
        Γ.cochainOperator (fun v ↦ tensorOfAlternating (F v)) :=
  cochainOperator_permuteOutgoing_sign Γ τ _ (fun v ↦ tensorOfAlternating_permutationLaw (F v))

end Graph

end EnvelopingIsomorphism.Deformation.KontsevichGraph.General
