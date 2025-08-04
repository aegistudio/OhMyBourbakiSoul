import OhMyBourbakiSoul.MyBasic.MySet.Basic

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

namespace MySet

def transform (s : MySet α) (f : α → β) : MySet β :=
  λ (b : β) => ∃ a ∈ s, b = f a

theorem transform_def {s : MySet α} {f : α → β} {y : β}:
  (y ∈ s.transform f) ↔ (∃ x ∈ s, y = f x) := by
  apply Iff.intro
  · intro hy
    unfold transform at hy
    change ∃ x ∈ s, y = f x at hy
    rcases hy with ⟨x, hx⟩
    exists x
  · intro h
    rcases h with ⟨x, hx⟩
    unfold transform
    change ∃ a ∈ s, y = f a
    exists x

theorem transform_mem {s : MySet α} {f : α → β} :
  (∀ a ∈ s, f a ∈ s.transform f) := by
  intro a has
  rw [mem_def]
  unfold transform
  exists a

-- { term || x ∈ s }
syntax "{ " withoutPosition(term " || " ident " ∈ " term) " }" : term

macro_rules
  | `({ $p || $x ∈ $s }) => ``(transform $s fun $x => $p)

theorem transform_compose {s : MySet α} {g : α → β} {f : β → γ} :
  { f b || b ∈ { g a || a ∈ s } } = { f (g a) || a ∈ s } := by
  rw [eq_iff]
  intro c
  apply Iff.intro
  · intro h
    rw [transform_def] at h
    rcases h with ⟨b, hb⟩
    rcases hb with ⟨hbTs, hcfb⟩
    rw [transform_def] at hbTs
    rcases hbTs with ⟨a, ha⟩
    rw [transform_def]
    exists a
    apply And.intro
    · exact And.left ha
    · rw [<-And.right ha]
      exact hcfb
  · intro h
    rw [transform_def] at h
    rcases h with ⟨a, ha⟩
    rw [transform_def]
    exists g a
    apply And.intro
    · exact transform_mem a (And.left ha)
    · exact And.right ha

end MySet
