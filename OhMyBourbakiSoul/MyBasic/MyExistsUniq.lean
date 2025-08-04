universe u
variable {α : Type u}

def ExistsUniq (p : α → Prop) :=
  ∃ (a : α), (p a) ∧ (∀ (b : α), (p b) → (a = b))
