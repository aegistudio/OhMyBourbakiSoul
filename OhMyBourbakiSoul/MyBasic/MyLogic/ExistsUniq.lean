universe u v
variable {α : Type u} {β : Type v}

def ExistsUniq (p : α → Prop) :=
  ∃ (a : α), (p a) ∧ (∀ (b : α), (p b) → (a = b))

-- ∃! x (: Type | ∈ Col)?, p x
syntax "∃!" withoutPosition(ident) "," term : term
syntax "∃!" withoutPosition(ident) ":" term "," term : term
syntax "∃!" withoutPosition(ident) "∈" term "," term : term

macro_rules
  | `(∃! $x, $p) => ``(ExistsUniq (fun $x => $p))
  | `(∃! $x : $t, $p) => ``(ExistsUniq (fun $x : $t => $p))
  | `(∃! $x ∈ $c, $p) => ``(ExistsUniq (fun $x : Subtype $c => $p))

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

def prop {p : α → Prop} (_ : ExistsUniq p) := p

end ExistsUniq

def ExistsUniqPred (p : β → α → Prop) :=
  ∀ (b : β), ExistsUniq (p b)

namespace ExistsUniqPred

def pred_prop {p : β → α → Prop} (_: ExistsUniqPred p) := p

end ExistsUniqPred

-- Axiom of unique choice.
--
-- This axiom states that for any unique
-- existential proposition that has been
-- proved to be true, there is a unique
-- function to choose that instance from
-- the specified proof.
--
-- This axiom is theorem under
-- Zermelo-Fraenkel set theory. When all
-- objects in the domain of discourse are
-- hereditary sets, this axiom can be
-- easily implemented by ⋃ {x | p x}.
--
-- This theorem is strictly weaker than
-- the axiom of choice, and thus strictly
-- weaker than the axiom of global choice.
class UC where
  uniq_choose {α : Type _} {p : α → Prop} : ExistsUniq p → Subtype p

-- We also offer some weaker form of
-- unique choice down to statement, so
-- that we can implement then when we
-- know how to do.
class UCProp (p : α → Prop) where
  uniq_choose : ExistsUniq p → Subtype p

class UCPred (p : β → α → Prop) where
  uniq_choose_pred (b : β) : UCProp (p b)
