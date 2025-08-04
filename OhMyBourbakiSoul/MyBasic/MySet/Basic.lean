universe u
variable {α : Type u}

-- A set under type theory is fundamentally
-- a function from an element (a : α) to
-- the proposition (p a) about a. If it is
-- true then there's a proof of (p a), and
-- false otherwise.
def MySet (α : Type u) := α → Prop

namespace MySet

def mem (s : MySet α) (a : α) : Prop := s a

instance instMembership : Membership α (MySet α) where
  mem := mem

theorem mem_def {a : α} {s : MySet α} : (a ∈ s) ↔ (s a) :=
  by rfl

instance instDecidableMem {a : α} {s : MySet α}
  [I : Decidable (s a)]: Decidable (a ∈ s) := by
  rw [mem_def]
  exact I

theorem mem_iff {a : α} {s : MySet α} : (a ∈ s) ↔ (∃ b ∈ s, a = b) := by
  apply Iff.intro
  · intro has
    exists a
  · intro h
    rcases h with ⟨b, hb⟩
    rcases hb with ⟨hbs, heq⟩
    rw [heq]
    exact hbs

-- The axiom of extensionality, now follows
-- the functional extensionality, we will see.
theorem eq_iff {s₁ s₂ : MySet α} :
  (s₁ = s₂) ↔ (∀ (a : α), (a ∈ s₁) ↔ (a ∈ s₂)) := by
  apply Iff.intro
  · intro h a
    rw [h]
  · intro h
    -- Since a set is fundamentally a function, we
    -- would like to show the equality of function.
    funext a
    have h' := h a
    rw [<-mem_def (s := s₁)]
    rw [<-mem_def (s := s₂)]
    rw [h']

-- Every type has a corresponding universal set
-- for it, such that ∀ (a : α), a ∈ (univ α)
def univ (α : Type u) : MySet α := by
  intro a
  exact True

theorem univ_def : ∀ (a : α), a ∈ (univ α) := by
  intro a
  rw [mem_def]
  rw [univ]
  trivial

theorem univ_iff {U : MySet α} :
  (∀ (a : α), a ∈ U) ↔ (U = univ α) := by
  apply Iff.intro
  · intro h
    rw [eq_iff]
    intro a
    have h₁ := h a
    have h₂ := univ_def a
    apply Iff.intro <;> (intro ; trivial)
  · intro h a
    rw [eq_iff] at h
    have h' := h a
    rw [h']
    exact univ_def a

-- Similarly, every type has a corresponding
-- empty set, such that ∀ (a : α), a ∉ empty
def empty {α : Type u} : MySet α := by
  intro a
  exact False

theorem empty_def : ∀ (a : α), a ∉ empty := by
  intro a ha
  rw [mem_def] at ha
  rw [empty] at ha
  trivial

instance instEmpty : EmptyCollection (MySet α) where
  emptyCollection := empty

theorem emptyset_def : (∅ : MySet α) = empty := by
  change empty = empty
  rfl

theorem empty_iff {O : MySet α} :
  (∀ (a : α), a ∉ O) ↔ (O = ∅) := by
  apply Iff.intro
  · intro h
    rw [eq_iff]
    intro a
    have h₁ := h a
    have h₂ := empty_def a
    apply Iff.intro <;> (intro ; trivial)
  · intro h a
    rw [eq_iff] at h
    have h' := h a
    rw [h']
    exact empty_def a

end MySet
