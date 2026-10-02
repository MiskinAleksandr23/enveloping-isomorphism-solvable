import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card

/-!
# Actual reflected anchor choices for finite clusters

An involution acts on the nonempty finite subsets. On each two-element orbit,
the subset with smaller finite ordinal code chooses an arbitrary member and
the other subset uses its reflected member. A stable subset chooses any member;
there is no requirement that this member be fixed by the involution.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedClusterAnchors

abbrev NonemptySubset (I : Type*) := {A : Finset I // A.Nonempty}

variable {I : Type*}

local instance : DecidableEq I := Classical.decEq I

def reflectSubset (σ : I → I) (A : NonemptySubset I) : NonemptySubset I := by
  classical
  exact ⟨A.val.image σ, A.property.image σ⟩

@[simp] theorem reflectSubset_val (σ : I → I) (A : NonemptySubset I) :
    (reflectSubset σ A).val = A.val.image σ := by
  classical
  rfl

theorem reflectSubset_involutive (σ : I → I) (hσ : Function.Involutive σ) :
    Function.Involutive (reflectSubset σ) := by
  classical
  intro A
  apply Subtype.ext
  simp only [reflectSubset_val, Finset.image_image]
  have hcomp : σ ∘ σ = id := funext hσ
  rw [hcomp]
  exact Finset.image_id

theorem mem_reflectSubset_iff (σ : I → I) (hσ : Function.Involutive σ)
    (A : NonemptySubset I) (i : I) : i ∈ (reflectSubset σ A).val ↔ σ i ∈ A.val := by
  classical
  rw [reflectSubset_val, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [hσ j]
    exact hj
  · intro hi
    exact ⟨σ i, hi, hσ i⟩

@[simp] theorem card_reflectSubset (σ : I → I) (hσ : Function.Involutive σ)
    (A : NonemptySubset I) : (reflectSubset σ A).val.card = A.val.card := by
  classical
  rw [reflectSubset_val]
  exact Finset.card_image_of_injective _ hσ.injective

def reflectSubsetEquiv (σ : I → I) (hσ : Function.Involutive σ) :
    NonemptySubset I ≃ NonemptySubset I :=
  { toFun := reflectSubset σ
    invFun := reflectSubset σ
    left_inv := reflectSubset_involutive σ hσ
    right_inv := reflectSubset_involutive σ hσ }

private def chosenMember (A : NonemptySubset I) : {i : I // i ∈ A.val} :=
  ⟨A.property.choose, A.property.choose_spec⟩

private def subsetCode [Fintype I] (A : NonemptySubset I) : ℕ := by
  classical
  exact (Fintype.equivFin (NonemptySubset I) A).val

private theorem subsetCode_injective [Fintype I] :
    Function.Injective (subsetCode : NonemptySubset I → ℕ) := by
  classical
  intro A B h
  exact (Fintype.equivFin (NonemptySubset I)).injective (Fin.ext h)

/-- A genuine selector, using an arbitrary member only on the chosen side of
each orbit and transporting it on the other side. -/
def anchor [Fintype I] (σ : I → I) (hσ : Function.Involutive σ)
    (A : NonemptySubset I) : {i : I // i ∈ A.val} :=
  if subsetCode A ≤ subsetCode (reflectSubset σ A) then chosenMember A
  else ⟨σ (chosenMember (reflectSubset σ A)).val,
    (mem_reflectSubset_iff σ hσ A _).mp (chosenMember (reflectSubset σ A)).property⟩

private theorem anchor_val [Fintype I] (σ : I → I) (hσ : Function.Involutive σ)
    (A : NonemptySubset I) : (anchor σ hσ A).val =
      if subsetCode A ≤ subsetCode (reflectSubset σ A) then (chosenMember A).val
      else σ (chosenMember (reflectSubset σ A)).val := by
  unfold anchor
  split_ifs <;> rfl

theorem anchor_mem [Fintype I] (σ : I → I) (hσ : Function.Involutive σ)
    (A : NonemptySubset I) : (anchor σ hσ A).val ∈ A.val := (anchor σ hσ A).property

/-- On nonstable subsets the chosen anchors commute with the actual involution.
Stable subsets impose no fixed-point constraint on the selected member. -/
theorem anchor_reflectSubset [Fintype I] (σ : I → I) (hσ : Function.Involutive σ)
    (A : NonemptySubset I) (hA : (reflectSubset σ A).val ≠ A.val) :
    (anchor σ hσ (reflectSubset σ A)).val = σ (anchor σ hσ A).val := by
  have hne : reflectSubset σ A ≠ A := fun h => hA (congrArg Subtype.val h)
  have hcode : subsetCode (reflectSubset σ A) ≠ subsetCode A :=
    fun h => hne (subsetCode_injective h)
  rw [anchor_val, anchor_val, reflectSubset_involutive σ hσ A]
  by_cases hle : subsetCode A ≤ subsetCode (reflectSubset σ A)
  · have hnot : ¬ subsetCode (reflectSubset σ A) ≤ subsetCode A := by omega
    rw [if_neg hnot, if_pos hle]
  · have hreverse : subsetCode (reflectSubset σ A) ≤ subsetCode A := by omega
    rw [if_pos hreverse, if_neg hle, hσ]

/-- Existence form, with membership encoded by the actual selected subtype. -/
theorem exists_reflected_anchors [Fintype I] (σ : I → I) (hσ : Function.Involutive σ) :
    ∃ f : (A : NonemptySubset I) → {i : I // i ∈ A.val},
      ∀ A, (reflectSubset σ A).val ≠ A.val → (f (reflectSubset σ A)).val = σ (f A).val :=
  ⟨anchor σ hσ, anchor_reflectSubset σ hσ⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedClusterAnchors
