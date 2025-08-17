import OhMyBourbakiSoul.MyBasic.MySet.Basic
import OhMyBourbakiSoul.MyBasic.MySet.Subset

universe u
variable {α : Type u}

namespace MySet

variable {X X' : MySet α}

def lift_univ (x : α) : Subtype (univ α) := by
  apply Subtype.mk x
  rw [<-mem_def (s := univ α)]
  exact univ_def x

theorem lift_univ_def {x : α} :
  (lift_univ x).val = x := by rfl

def lift_subtype (h : X ⊆ X') (x : Subtype X) : Subtype X' := by
  apply Subtype.mk x.val
  rw [subset_def] at h
  exact h x x.property

theorem lift_subtype_def {h : X ⊆ X'} {x : Subtype X} :
  (lift_subtype h x).val = x.val := by rfl

def unlift_subtype (s : MySet (Subtype X)) : MySet α :=
  λ x => ∃ (x' : Subtype X), (x = x'.val) ∧ (x' ∈ s)

theorem unlift_subset {s : MySet (Subtype X)} :
  unlift_subtype s ⊆ X := by
  rw [subset_def]
  intro x hx
  unfold unlift_subtype at hx
  change ∃ (x' : Subtype X), (x = x'.val) ∧ (x' ∈ s) at hx
  rcases hx with ⟨x', hx'⟩
  have hxx' := x'.property
  rw [<-And.left hx'] at hxx'
  rw [mem_def]
  exact hxx'

end MySet
