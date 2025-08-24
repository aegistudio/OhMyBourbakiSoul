import OhMyBourbakiSoul.MyBasic.MyLogic.Exclusive
import OhMyBourbakiSoul.MyBasic.MySet.Basic
import OhMyBourbakiSoul.MyBasic.MySet.OpsDef

universe u
variable {α : Type u}

namespace MySet

abbrev exclusive (s : MySet α) := ExclusivePred s.pred

theorem complement_exclusive
  {s : MySet α} (h : s.exclusive) : ((sᶜ).exclusive) := by
  intro x
  exact Exclusive.not_intro (h x)

theorem intersect_exclusive
  {s₁ s₂ : MySet α}
  (hs₁ : s₁.exclusive) (hs₂ : s₂.exclusive):
  (s₁ ∩ s₂).exclusive := by
  intro x
  rw [<-mem_def]
  rw [intersect_def]
  exact Exclusive.and_intro (hs₁ x) (hs₂ x)

theorem union_exclusive
  {s₁ s₂ : MySet α}
  (hs₁ : s₁.exclusive) (hs₂ : s₂.exclusive):
  (s₁ ∪ s₂).exclusive := by
  intro x
  rw [<-mem_def]
  rw [union_def]
  exact Exclusive.or_intro (hs₁ x) (hs₂ x)

end MySet
