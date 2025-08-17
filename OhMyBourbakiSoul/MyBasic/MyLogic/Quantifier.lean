import OhMyBourbakiSoul.MyBasic.MyLogic.Exclusive

universe u
variable {α : Type u}

namespace MyLogic

variable {p q : α → Prop}

theorem forall_univ_iff :
  (∀ x, q x) ↔ (∀ x, True → q x) := by
  apply Iff.intro
  · intro h x hT
    exact h x
  · intro h x
    exact h x trivial

theorem exists_univ_iff :
  (∃ x, q x) ↔ (∃ x, True ∧ q x) := by
  apply Iff.intro
  · intro h
    rcases h with ⟨x, h'⟩
    exists x
  · intro h
    rcases h with ⟨x, h'⟩
    exists x
    exact And.right h'

theorem forall_in_not_iff_not_exists_in :
  (∀ x, p x → ¬q x) ↔ ¬(∃ x, p x ∧ q x) := by
  apply Iff.intro
  · intro hApxnqx hEpxqx
    rcases hEpxqx with ⟨x, hpxqx⟩
    rcases hpxqx with ⟨hpx, hqx⟩
    have hpxnqx := hApxnqx x
    have hnqx := hpxnqx hpx
    contradiction
  · intro hnExpx x hpx hqx
    have : ∃ x, p x ∧ q x := by exists x
    contradiction

theorem forall_not_iff_not_exists :
  (∀ x, ¬q x) ↔ ¬(∃ x, q x) := by
  rw [forall_univ_iff]
  rw [exists_univ_iff]
  exact forall_in_not_iff_not_exists_in

theorem forall_in_then_not_exists_in_not :
  (∀ x, p x → q x) → ¬(∃ x, p x ∧ ¬q x) := by
  intro hApxqx hEpxnqx
  rcases hEpxnqx with ⟨x, hpxnqx⟩
  rcases hpxnqx with ⟨hpx, hnqx⟩
  have hpxqx := hApxqx x
  have hqx := hpxqx hpx
  contradiction

theorem forall_then_not_exists_not :
  (∀ x, q x) → ¬(∃ x, ¬q x) := by
  rw [forall_univ_iff]
  rw [exists_univ_iff]
  exact forall_in_then_not_exists_in_not

theorem forall_in_iff_not_exists_in_not_if_lem_elem
  (h : ExclusivePred q) :
  (∀ x, p x → q x) ↔ ¬(∃ x, p x ∧ ¬q x) := by
  apply Iff.intro
  · exact forall_in_then_not_exists_in_not
  · intro hnExpx x hpx
    apply (h x).by_contra
    intro hnpx
    have : ∃ x, p x ∧ ¬q x := by exists x
    contradiction

theorem forall_iff_not_exists_not_if_lem_elem
  (h : ExclusivePred q) :
  (∀ x, q x) ↔ ¬(∃ x, ¬q x) := by
  rw [forall_univ_iff]
  rw [exists_univ_iff]
  exact forall_in_iff_not_exists_in_not_if_lem_elem h

theorem not_forall_in_if_exists_in_not :
  (∃ x, p x ∧ ¬q x) → ¬(∀ x, p x → q x) := by
  intro hEpxnqx hApxqx
  rcases hEpxnqx with ⟨x, hpxnqx⟩
  rcases hpxnqx with ⟨hpx, hnqx⟩
  have hqx := hApxqx x hpx
  contradiction

theorem not_forall_if_exists_not :
  (∃ x, ¬p x) → ¬(∀ x, p x) := by
  rw [forall_univ_iff]
  rw [exists_univ_iff]
  exact not_forall_in_if_exists_in_not

theorem not_forall_in_then_exists_in_not_if_lem_elem_exists
  (h₀ : ExclusivePred q)
  (h₁ : Exclusive (∃ x, p x ∧ ¬q x)) :
  ¬(∀ x, p x → q x) → (∃ x, p x ∧ ¬q x) := by
  intro hnApxqx
  apply h₁.by_contra
  intro hnEpxnqx
  rw [<-forall_in_iff_not_exists_in_not_if_lem_elem h₀] at hnEpxnqx
  contradiction

theorem not_forall_then_exists_not_if_lem_elem_exists
  (h₀ : ExclusivePred p)
  (h₁ : Exclusive (∃ x, ¬p x)) :
  ¬(∀ x, p x) → (∃ x, ¬p x) := by
  rw [forall_univ_iff]
  rw [exists_univ_iff]
  rw [exists_univ_iff] at h₁
  exact not_forall_in_then_exists_in_not_if_lem_elem_exists h₀ h₁

theorem not_forall_in_not_if_exists_in :
  (∃ x, p x ∧ q x) → ¬(∀ x, p x → ¬q x) := by
  intro hEpxqx hApxnqx
  rcases hEpxqx with ⟨x, hpxqx⟩
  rcases hpxqx with ⟨hpx, hqx⟩
  have hnqx := hApxnqx x hpx
  contradiction

theorem not_forall_not_if_exists :
  (∃ x, q x) → ¬(∀ x, ¬q x) := by
  rw [forall_univ_iff]
  rw [exists_univ_iff]
  exact not_forall_in_not_if_exists_in

theorem not_forall_in_not_iff_exists_in_if_lem_exists
  (h : Exclusive (∃ x, p x ∧ q x)) :
  ¬(∀ x, p x → ¬q x) ↔ (∃ x, p x ∧ q x) := by
  apply Iff.intro
  · intro hnApxnqx
    apply h.by_contra
    intro hnEpxqx
    rw [<-forall_in_not_iff_not_exists_in] at hnEpxqx
    contradiction
  · exact not_forall_in_not_if_exists_in

theorem not_forall_not_iff_exists_if_lem_exists
  (h : Exclusive (∃ x, p x)) :
  ¬(∀ x, ¬p x) ↔ (∃ x, p x) := by
  rw [forall_univ_iff]
  rw [exists_univ_iff]
  rw [exists_univ_iff] at h
  exact not_forall_in_not_iff_exists_in_if_lem_exists h

end MyLogic
