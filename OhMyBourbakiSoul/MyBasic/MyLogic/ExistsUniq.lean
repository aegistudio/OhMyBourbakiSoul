universe u
variable {α : Type u}

def ExistsUniq (p : α → Prop) :=
  ∃ (a : α), (p a) ∧ (∀ (b : α), (p b) → (a = b))

namespace ExistsUniq

theorem unique_if
  {p : α → Prop} (eu : ExistsUniq p) {a b : α}:
  (p a) → (p b) → (a = b) := by
  intro hpa hpb
  rcases eu with ⟨c, hc⟩
  rcases hc with ⟨hpc, heq⟩
  have hac := heq a hpa
  have hbc := heq b hpb
  rw [<-hac, <-hbc]

end ExistsUniq
