universe u
variable {α : Type u}

-- For a proposition p, in intuitionistic logic,
-- we may assess the decidability state of p as:
--
-- * Totally Undecidable: there's currently no
-- proof of p or ¬p, and there's no proof of
-- (p ∨ ¬p) to be true. See also
-- "DoYouKnowEverything.lean" for more detail.
--
-- * Non-Deterministically Decidable: although
-- we have no proof of p or not p, but we do
-- derive (p ∨ ¬p) to be true from certain
-- context of hypothesis. This allow us to
-- do or-elimination with p → q and ¬p → q
-- to conclude q.
--
-- * Decidable: we have an algorithm to decide
-- whether p or not p is true, that is, to
-- construct the proof of p or ¬p.
--
-- A good proof writer should do good to
-- evaluate and discriminate the current
-- state of proposition. A theorem that
-- proves Exclusive p or p ∨ ¬p should be
-- named "*_exclusive", a theorem that
-- provides Decidable p should be
-- named "*_decidable".
def Exclusive (p : Prop) := p ∨ ¬p

def ExclusivePred (p : α → Prop) := (a : α) → Exclusive (p a)

def ExclusiveEq (α : Type u) :=
  (a : α) → (b : α) → Exclusive (a = b)

def ExclusiveLT (α : Type u) [LT α] :=
  (a : α) → (b : α) → Exclusive (a < b)

def ExclusiveLE (α : Type u) [LE α] :=
  (a : α) → (b : α) → Exclusive (a ≤ b)

theorem exclusive_if_decidable
  {p : Prop} [D : Decidable p] : Exclusive p := by
  match D with
    | isTrue (hp : p) => exact Or.inl hp
    | isFalse (hnp : ¬p) => exact Or.inr hnp

namespace Exclusive

variable {p q : Prop}

theorem dne (hx : Exclusive p) : (¬¬p ↔ p) := by
  apply Iff.intro
  · intro hnnp
    apply Or.elim hx
    · intro hp
      exact hp
    · intro hnp
      exfalso
      contradiction
  · intro hp hnp
    contradiction

theorem contrapositive (hx : Exclusive q) :
  (p → q) ↔ (¬q → ¬p):= by
  apply Iff.intro
  · intro hpq hnq hp
    have hnq := hpq hp
    contradiction
  · intro hnqnp hp
    apply Or.elim hx
    · intro hq
      exact hq
    · intro hnq
      exfalso
      have hnp := hnqnp hnq
      contradiction

theorem by_contra (hx : Exclusive p) :
  (¬p → False) → p := by
  change (¬¬p) → p
  exact (dne hx).mp

end Exclusive
