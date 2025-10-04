universe u
variable {α : Type u}

-- A set under type theory is fundamentally
-- a function from an element (a : α) to
-- the proposition (p a) about a. If it is
-- true then there's a proof of (p a), and
-- false otherwise.
structure MySet (α : Type u) where
  pred : α → Prop

-- { x | term }
-- { x : type | term }
-- { (term : type) | term }
syntax "{ " withoutPosition(ident " | " term) " }" : term
syntax "{ " withoutPosition(ident " : " term " | " term) " }" : term
syntax "{ " withoutPosition("(" term " : " term ")" " | " term) " }" : term
-- Grammar { x ∈ s | term } is defined in Subtype.lean

macro_rules
  | `({ $x | $p }) => ``(MySet.mk (fun $x => $p))
  | `({ $x : $t | $p }) => ``(MySet.mk (fun ($x : $t) => $p))
  | `({ ($x : $t) | $p }) => ``(MySet.mk (fun ($x : $t) => $p))

-- Pretty printing when matching MySet.mk.
@[app_unexpander MySet.mk]
def unexpand_myset : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident => $p) => `({ $x | $p })
  -- FIXME: $t always not shown.
  | `($_ fun $x:ident : $t => $p) => `({ $x : $t | $p })
  | `($_ fun ($x : $t) => $p) => `({ ($x : $t) | $p })
  | _ => throw ()

namespace MySet

def coe_pred (s : MySet α) : α → Prop := s.pred

instance instCoePred : Coe (MySet α) (α → Prop) where
  coe := coe_pred

def mem (s : MySet α) (a : α) : Prop := s.pred a

instance instMembership : Membership α (MySet α) where
  mem := mem

theorem mem_def {a : α} {s : MySet α} :
  (a ∈ s) ↔ (s.pred a) := by
  change mem s a ↔ s.pred a
  rfl

instance instDecidableMem {a : α} {s : MySet α}
  [I : Decidable (s.pred a)]: Decidable (a ∈ s) := by
  rw [mem_def]
  exact I

abbrev decidable (s : MySet α) := DecidablePred s.pred

theorem mem_iff {a : α} {s : MySet α} : (a ∈ s) ↔ (∃ b ∈ s, a = b) := by
  apply Iff.intro
  · intro has
    exists a
  · intro h
    rcases h with ⟨b, hb⟩
    rcases hb with ⟨hbs, heq⟩
    rw [heq]
    exact hbs

theorem eq_def {s₁ s₂ : MySet α} :
  (s₁ = s₂) ↔ (s₁.pred = s₂.pred) := by
  cases s₁
  cases s₂
  simp

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
    rw [eq_def]
    funext a
    have h' := h a
    repeat rw [<-mem_def]
    rw [h']

-- Let's also define the type defined by the set.
@[reducible]
def type (s : MySet α) := Subtype s.pred

instance instCoeType {s : MySet α} :
  Coe (Subtype s.pred) (s.type) where
  coe := id

instance instCoeSubtype {s : MySet α} :
  Coe (s.type) (Subtype s.pred) where
  coe := id

theorem type.membership {s : MySet α} (x : s.type) : x.val ∈ s := by
  rw [mem_def]
  exact x.property

def typed {s : MySet α} (a : α) (h : a ∈ s) : s.type := by
  apply Subtype.mk a
  rw [<-mem_def]
  exact h

theorem typed_eta {s : MySet α} {a : α} {h : a ∈ s} :
  (typed a h).val = a := by
  unfold typed
  rfl

-- Every type has a corresponding universal set
-- for it, such that ∀ (a : α), a ∈ (univ α)
def univ (α : Type u) : MySet α := by
  apply MySet.mk
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
  apply MySet.mk
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

abbrev nonempty (s : MySet α) := Nonempty s.type

theorem empty_not_nonempty :
  ¬((∅ : MySet α).nonempty) := by
  intro h
  rcases h with ⟨n, hn⟩
  rw [<-mem_def] at hn
  have := empty_def n
  contradiction

theorem not_empty_if_nonempty {s : MySet α} :
  (s.nonempty) -> (s ≠ ∅) := by
  intro hsn hse
  rcases hsn with ⟨x, hx⟩
  rw [eq_iff] at hse
  have hsx := hse x
  rw [<-mem_def] at hx
  rw [hsx] at hx
  have hxn := empty_def x
  contradiction

end MySet
